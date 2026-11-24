module LoL.Export.Rocq where

import Data.Char (ord)
import Control.Monad (foldM)
import Data.Functor.Const (Const (..))
import Data.List (intercalate, isPrefixOf, mapAccumL)
import Data.Monoid (Endo (..))
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import LoL.Core
import qualified LoL.Env as Env
import qualified LoL.Pretty as Pretty
import qualified LoL.Hol.Embed as Embed
import LoL.Hol.Session (Kernel, Limits (..), Verdict (..))
import qualified Hol.V2.Embedding as Hol
import Numeric (showHex)
import System.Timeout (timeout)

reserved :: Set.Set String
reserved = Pretty.rocqKeywords

-- The names that Rocq generates for an inductive family.
generated :: String -> [String]
generated family = map (family ++) ["_rect", "_ind", "_rec", "_sind"]

-- A keyword can name a source file but cannot follow Require Import. Escape
-- that component, and the escape prefix itself, so the mapping is injective
-- and independent of the set or order of files being exported.
moduleName :: String -> String
moduleName = intercalate "." . map component . pieces where
    pieces input = case break (== '.') input of
        (first, []) -> [first]
        (first, _ : rest) -> first : pieces rest
    component name
        | Set.member name reserved || "lol__module_" `isPrefixOf` name = "lol__module_" ++ concatMap (\char -> showHex (ord char) "_") name
        | otherwise = name

-- A global keeps its name, unless Rocq reserves it or generates it for an
-- inductive family: such a name gets underscores until no global has the
-- result. A family that is renamed has other generated names, so the renaming
-- is repeated until nothing changes.
namesFor :: [(Global, String)] -> Map.Map Global String
namesFor entries = Map.fromList (until (\current -> pass current == current) pass entries) where
    pass current = snd (mapAccumL rename (Set.fromList (map snd current)) current) where
        schemes = Set.fromList (concat [generated name | (GlobalInd _ _, name) <- current])
        avoided name = Set.member name reserved || Set.member name schemes
        rename taken (global, name)
            | avoided name = (Set.insert fresh taken, (global, fresh))
            | otherwise = (taken, (global, name))
            where
                fresh = until (\candidate -> Set.notMember candidate taken && not (avoided candidate)) (++ "_") (name ++ "_")

-- The names of the globals of the declarations `entries`, as Rocq gets them.
namesIn :: [(ConstId, Env.Entry)] -> Map.Map Global String
namesIn entries = namesFor [(global, name) | (c, entry) <- entries, (name, global) <- Env.declGlobals c (Env.entryName entry) (Env.entryDecl entry)]

namesOf :: Env.Env -> Map.Map Global String
namesOf = namesIn . Map.toAscList . Env.envDecls

-- What a printer of Rocq is told of the declarations `entries`. A binder is
-- not given a name that Rocq reserves, or that a global has.
namingFor :: [(ConstId, Env.Entry)] -> Pretty.Naming
namingFor entries = Pretty.Naming { Pretty.namingGlobal = (`Map.lookup` names), Pretty.namingParams = \block -> Map.findWithDefault 0 block parameters, Pretty.namingBanned = (`Set.member` unavailable), Pretty.namingLiteral = const False, Pretty.namingAtMark = const False, Pretty.namingInMark = \_ _ -> False, Pretty.namingTemplate = Pretty.templateIn (Map.fromList entries), Pretty.namingLevelHints = Pretty.levelHints (Map.fromList entries), Pretty.namingUniverses = [], Pretty.namingLocalBlock = Nothing } where
    names = namesIn entries
    parameters = Map.fromList [(c, count) | (c, Env.Entry { Env.entryDecl = Env.Inductive count _ }) <- entries]
    unavailable = Set.union reserved (Set.fromList (Map.elems names))

namingOf :: Env.Env -> Pretty.Naming
namingOf = namingFor . Map.toAscList . Env.envDecls

render :: Pretty.Naming -> Term -> Either String (Integer, String)
render = Pretty.renderWith Pretty.Rocq

term :: Env.Env -> Term -> Either String String
term env value = snd <$> render (namingOf env) value

preamble :: Integer -> String
preamble level
    | level == 0 = ""
    | otherwise = (showString "Universe" . foldr (.) id [showString " L" . shows n | n <- [1 .. level]] . showString ".\nConstraint Set < L1.\n" . foldr (.) id [showString "Constraint L" . shows n . showString " < L" . shows (n + 1) . showString ".\n" | n <- [1 .. level - 1]]) ""

exportEnvironment :: Env.Env -> Either String String
exportEnvironment = exportEnvironmentAt 0

-- The universes reach the given level at least: a file that goes on after
-- the export, as a test does, may need more of them than the declarations.
exportEnvironmentAt :: Integer -> Env.Env -> Either String String
exportEnvironmentAt level = exportEntriesAt level . Map.toAscList . Env.envDecls

-- The structural entry point also lets differential tests print rejected
-- candidates. It admits nothing; declaration identities follow list order.
exportDeclarations :: [(String, Env.Decl)] -> Either String String
exportDeclarations entries = exportEntriesAt 0 (zip [0 ..] [Env.Entry name declaration [] emptyUniverses | (name, declaration) <- entries])

exportEntriesAt :: Integer -> [(ConstId, Env.Entry)] -> Either String String
exportEntriesAt level entries = do
    rendered <- mapM (uncurry (Pretty.command Pretty.Rocq (namingFor entries))) entries
    return (preamble (maximum (level : map fst rendered)) ++ unlines (map snd rendered))

-- Each source file exports its own declarations. Imported globals keep the
-- qualified spelling chosen in that module, rather than being renamed again
-- in the importer's namespace. All files share the same closed LoL levels:
-- their Rocq universe names are explicitly equated at an import boundary.
-- `exposed` has the short names that the `Require Import` lines give the
-- globals of the other files. A binder gets none of them: Rocq reads such a
-- name in a pattern as the constructor that has it.
exportModule :: [(String, Integer)] -> Map.Map Global String -> Set.Set String -> [ConstId] -> Env.Env -> Either String (Integer, String)
exportModule imports globals exposed locals env = do
    rendered <- mapM (uncurry (Pretty.command Pretty.Rocq names)) entries
    let level = maximum (0 : map snd imports ++ map fst rendered)
        required = concat ["Require Import " ++ name ++ ".\n" | (name, _) <- imports]
        shared = concat ["Constraint " ++ name ++ ".L" ++ show n ++ " = L" ++ show n ++ ".\n" | (name, count) <- imports, n <- [1 .. count]]
    return (level, concat [required, preamble level, shared, unlines (map snd rendered)])
    where
        entries = [(constant, entry) | constant <- locals, Just entry <- [Map.lookup constant (Env.envDecls env)]]
        unavailable = Set.unions [reserved, Set.fromList (Map.elems globals), exposed]
        names = (namingOf env) { Pretty.namingGlobal = (`Map.lookup` globals), Pretty.namingBanned = (`Set.member` unavailable) }

-- A graph parameter denotes this expression in the original declaration's
-- universe coordinates. Every reference instantiates this same template.
data ExportScheme
    = ExportScheme
        { schemeArity      :: Int
        , schemeParameters :: [Level]
        }
    deriving (Eq, Show)

data GraphCertificate
    = GraphCertificate
        { graphNormalized :: [Level]
        , graphZeroes     :: Set.Set Level
        , graphRelations  :: [UniverseConstraint]
        }
    deriving (Eq, Show)

-- This creates export-only syntax, never a replacement admitted Env. Hol
-- supplies closed-level normalization, forced-zero and entailment evidence.
-- A source valuation extends to the graph by giving every added parameter
-- its expression's value; no extra assumption is imposed on that valuation.
prepareEntries :: Kernel -> Limits -> Env.Env -> IO (Either String (Map.Map ConstId Env.Entry))
prepareEntries kernel limits environment = prepareGroups kernel limits groups where
    groups = [(Env.admissionView identity environment, [(identity, entry)]) | (identity, entry) <- Map.toAscList (Env.envDecls environment)]

-- Export schemes accumulate in dependency order. Each module's certificates
-- must follow from its own imports, including when a sibling was loaded
-- earlier and pins a universe shared through a common ancestor.
prepareGroups :: Kernel -> Limits -> [(IO Env.Env, [(ConstId, Env.Entry)])] -> IO (Either String (Map.Map ConstId Env.Entry))
prepareGroups kernel limits groups = do
    outcome <- timeout (limitMicros limits) (foldM group (Right (Map.empty, Map.empty)) groups)
    return $ case outcome of
        Nothing -> Left "Rocq universe graph preparation exceeded its time limit"
        Just result -> fmap fst result
    where
        group (Left failure) _ = return (Left failure)
        group accumulated (scope, local) = do
            environment <- scope
            foldM (prepare environment) accumulated local
        prepare _ (Left failure) _ = return (Left failure)
        prepare environment (Right (entries, schemes)) (identity, entry) = do
            result <- prepareEntry kernel limits environment schemes identity entry
            return $ do
                (rewritten, scheme) <- result
                Right (Map.insert identity rewritten entries, Map.insert identity scheme schemes)

exportEnvironmentPrepared :: Map.Map ConstId Env.Entry -> Either String String
exportEnvironmentPrepared = exportEntriesAt 0 . Map.toAscList

exportModulePrepared :: Map.Map ConstId Env.Entry -> [(String, Integer)] -> Map.Map Global String -> Set.Set String -> [ConstId] -> Env.Env -> Either String (Integer, String)
exportModulePrepared prepared imports globals exposed locals = exportModuleSections "" prepared [(imports, locals)] globals exposed

-- A late Require Import may shadow an earlier local, including L1, L2, ...
-- The first section declares its local universes after its imports.
exportModuleSections :: String -> Map.Map ConstId Env.Entry -> [([(String, Integer)], [ConstId])] -> Map.Map Global String -> Set.Set String -> Env.Env -> Either String (Integer, String)
exportModuleSections owner prepared sections globals exposed environment = do
    groups <- render globals sections
    let level = maximum (0 : concat [map snd imports ++ map fst decls | (imports, decls) <- groups])
        header imports = concat ["Require Import " ++ name ++ ".\n" | (name, _) <- imports]
        shared prefix imports = concat ["Constraint " ++ name ++ ".L" ++ show n ++ " = " ++ prefix ++ "L" ++ show n ++ ".\n" | (name, count) <- imports, n <- [1 .. count]]
        emit (imports, decls) = concat [header imports, shared (owner ++ ".") imports, unlines (map snd decls)]
    return (level, case groups of
        [] -> ""
        (imports, decls) : later -> concat [header imports, preamble level, shared "" imports, unlines (map snd decls), concatMap emit later])
    where
        render _ [] = Right []
        render current ((imports, locals) : later) = do
            entries <- mapM selected locals
            let names = outer { Pretty.namingGlobal = (`Map.lookup` current) }
            written <- mapM (uncurry (Pretty.command Pretty.Rocq names)) entries
            let protected = [(global, owner ++ "." ++ name) | (c, entry) <- entries, (_, global) <- Env.declGlobals c (Env.entryName entry) (Env.entryDecl entry), Just name <- [Map.lookup global globals], Set.member name exposed]
            rest <- render (Map.union (Map.fromList protected) current) later
            return ((imports, written) : rest)
        selected identity = maybe (Left "a local declaration has no prepared Rocq universe graph") (Right . (,) identity) (Map.lookup identity prepared)
        unavailable = Set.unions [reserved, Set.fromList (Map.elems globals), exposed]
        outer = (namingOf environment) { Pretty.namingBanned = (`Set.member` unavailable) }

prepareEntry :: Kernel -> Limits -> Env.Env -> Map.Map ConstId ExportScheme -> ConstId -> Env.Entry -> IO (Either String (Env.Entry, ExportScheme))
prepareEntry kernel limits environment schemes identity entry = case mapDeclaration (expandReferences schemes identity Nothing) (Env.entryDecl entry) of
    Left failure -> return (Left failure)
    Right expanded
        | Pretty.templateIn (Env.envDecls environment) identity ->
            return (Right (entry { Env.entryDecl = expanded }, ExportScheme arity (map Parameter [0 .. arity - 1])))
        | original == emptyUniverses && all closed (concatMap termLevels (Env.declTerms expanded)) ->
            return (Right (entry { Env.entryDecl = expanded }, ExportScheme 0 []))
        | otherwise -> do
            consistent <- Env.checkUniversesBefore identity Env.Persistent kernel limits environment original
            case consistent of
                Left failure -> return (Left ("Rocq export of '" ++ Env.entryName entry ++ "': " ++ contextFailure failure))
                Right () -> case closure expanded of
                    Left failure -> return (Left failure)
                    Right levels -> do
                        prepared <- settleGraph kernel limits environment identity original levels id
                        return $ do
                            (nodes, certificate, normalized) <- prepared
                            let parameters = filter local nodes
                                scheme = ExportScheme arity parameters
                                positions = Map.fromList (zip parameters [0 ..])
                                project level = case normalized level of
                                    node@DefaultLevel {} -> Right node
                                    Closed number -> Right (Closed number)
                                    node -> maybe (Left "a universe expression is missing from its Rocq graph") (Right . Parameter) (Map.lookup node positions)
                            final <- mapDeclaration (expandReferences schemes identity (Just scheme)) (Env.entryDecl entry) >>= mapDeclaration (mapTermLevels project)
                            constraints <- mapM (mapConstraint (projectCoordinate (graphNormalized certificate) project)) (graphRelations certificate)
                            let useful = filter (not . closedConstraint) constraints
                                names =
                                    [ case level of
                                        Parameter index -> universeNames original !! index
                                        _ -> "u_expr" ++ show index
                                    | (index, level) <- zip [0 :: Int ..] parameters
                                    ]
                                context = UniverseContext names useful
                            Right (entry { Env.entryDecl = final, Env.entryUniverses = context }, scheme)
    where
        local DefaultLevel {} = False
        local level = not (closed level)
        original = Env.entryUniverses entry
        arity = length (universeNames original)
        closure declaration = closeSelf references starting where
            references = concatMap (selfInstances identity) (Env.declTerms declaration)
            starting = levelSet (map Closed [0 .. closedPeak] ++ map Parameter [0 .. arity - 1] ++ concatMap constraintLevels (universeConstraints original) ++ concatMap termLevels (Env.declTerms declaration))
        -- A referenced constant's type may mention a closed level absent
        -- from this declaration's syntax. Include every closed level up to
        -- the highest one of its dependencies (the chain `Set < L1 < L2 ...`
        -- of the Rocq preamble), independently of later or unrelated
        -- declarations. Hol, not this enumeration, decides every edge
        -- involving that chain.
        dependencies = Env.reachable Env.declBody environment (Set.singleton identity)
        relevant = entry : [existing | found <- Set.toList (Set.delete identity dependencies), Just existing <- [Map.lookup found (Env.envDecls environment)]]
        closedPeak = maximum (0 : [Pretty.closedUniversePeak level | existing <- relevant, level <- concatMap termLevels (Env.declTerms (Env.entryDecl existing)) ++ concatMap constraintLevels (universeConstraints (Env.entryUniverses existing))])
        closeSelf references levels = do
            additions <- sequence [substituteLevel instance_ level | instance_ <- references, level <- Set.toList levels]
            let next = Set.union levels (levelSet additions)
            if next == levels then Right (Set.toAscList levels) else closeSelf references next
        closedConstraint constraint = case constraint of
            UniverseLe (Successor left) right -> closed left && closed right
            _ -> all closed (constraintLevels constraint)

contextFailure :: Env.Refusal -> String
contextFailure failure = case failure of
    Env.KernelRejected report -> refusedGraph "the kernel rejected the universe context" report
    Env.KernelUndecided reason -> "universe consistency is undecided: " ++ reason
    Env.OracleRejected report reason -> refusedGraph ("the oracle rejected the universe context: " ++ reason) (Just report)
    Env.NotClosed -> "the universe context is not closed"
    Env.DuplicateName name -> "duplicate declaration: " ++ name

refusedGraph :: String -> Maybe Embed.Report -> String
refusedGraph message report = maybe message (\given -> "[" ++ Embed.reportRule given ++ "] " ++ message) report

-- The first pass may identify a parameter forced to Set. Rocq cannot declare
-- that local parameter with u<=Set, so substitute it and normalize again in
-- Hol. Ground extra instances also become ordinary closed levels here.
settleGraph :: Kernel -> Limits -> Env.Env -> ConstId -> UniverseContext -> [Level] -> (Level -> Level) -> IO (Either String ([Level], GraphCertificate, Level -> Level))
settleGraph kernel limits environment identity context levels previous = do
    checked <- graphCertificate kernel limits environment identity context levels
    case checked of
        Left failure -> return (Left failure)
        Right certificate -> do
            let normalization = Map.fromList (zip levels (graphNormalized certificate))
                zeroes = graphZeroes certificate
                rewrite value = zero (Map.findWithDefault value value normalization)
                zero value
                    | Set.member value zeroes = Closed 0
                    | otherwise = case value of
                        Successor inner -> Successor (zero inner)
                        Maximum left right -> Maximum (zero left) (zero right)
                        _ -> value
                next = Set.toAscList (levelSet (map rewrite levels))
            if all (\level -> rewrite level == level) levels then return (Right (levels, certificate, previous))
            else settleGraph kernel limits environment identity context next (rewrite . previous)

graphCertificate :: Kernel -> Limits -> Env.Env -> ConstId -> UniverseContext -> [Level] -> IO (Either String GraphCertificate)
graphCertificate kernel limits environment identity context levels = do
    let normalized = Hol.LV_Named "RocqNormalized"
        zeroes = Hol.LV_Named "RocqZeroes"
        relations = Hol.LV_Named "RocqRelations"
        goal = Hol.foldlNApp (Embed.named "u_export_graph")
            [ Embed.natural (toInteger (length (universeNames context)))
            , Embed.embedUniverseConstraints (universeConstraints context)
            , Embed.embedList (Embed.kindOf "lvl") (map Embed.embedLevel levels)
            , Hol.mkLVar normalized, Hol.mkLVar zeroes, Hol.mkLVar relations
            ]
    (verdict, _, _) <- Env.run Env.Persistent kernel limits environment [] (Env.beforeUniverseDeclaration environment identity goal) [normalized, zeroes, relations]
    return $ case verdict of
        Admitted [values, zeros, edges] -> do
            normalizedLevels <- Embed.recoverList values >>= mapM Embed.recoverLevel
            indices <- Embed.recoverList zeros >>= mapM index
            constraints <- Embed.recoverUniverseConstraints edges
            if length normalizedLevels /= length levels then Left "the kernel changed the Rocq graph node count" else do
                zeroLevels <- mapM (at normalizedLevels) indices
                if all (wellScopedLevel (length (universeNames context))) normalizedLevels && all (validGraphRelation (length levels)) constraints
                    then Right (GraphCertificate normalizedLevels (Set.fromList zeroLevels) constraints)
                    else Left "a Rocq graph level escaped the declaration context"
        Rejected report -> Left (refusedGraph "the kernel refused Rocq universe graph preparation" report)
        Undecided message -> Left ("Rocq universe graph preparation is undecided: " ++ message)
        _ -> Left "the kernel returned an incomplete Rocq universe graph certificate"
    where
        index value = case value of
            Hol.NCon (Hol.DC (Hol.DC_NatL number)) _
                | number >= 0 && number < toInteger (length levels) -> Right (fromInteger number)
            _ -> Left "a Rocq graph zero index is out of range"
        at values place = case drop place values of
            value : _ -> Right value
            _ -> Left "a Rocq graph coordinate is out of range"

-- Keep coordinates until projection: an edge whose left node happens to be
-- u+1 is not the strict edge from the node u. Their lifted nodes differ.
projectCoordinate :: [Level] -> (Level -> Either String Level) -> Level -> Either String Level
projectCoordinate levels project coordinate = case coordinate of
    Parameter index
        | index >= 0 -> case drop index levels of
            value : _ -> project value
            _ -> Left "a Rocq graph coordinate is out of range"
    _ -> Left "a Rocq graph coordinate is not a node index"

validGraphRelation :: Int -> UniverseConstraint -> Bool
validGraphRelation count constraint = case constraint of
    UniverseLe (Successor left) right -> coordinate left && coordinate right
    UniverseLe left right -> coordinate left && coordinate right
    UniverseEq left right -> coordinate left && coordinate right
    where
        coordinate (Parameter index) = index >= 0 && index < count
        coordinate _ = False

closed :: Level -> Bool
closed Closed {} = True
closed _ = False

levelSet :: [Level] -> Set.Set Level
levelSet = Set.unions . map nodes where
    nodes level = Set.insert level $ case level of
        Successor inner -> nodes inner
        Maximum left right -> Set.union (nodes left) (nodes right)
        _ -> Set.empty

constraintLevels :: UniverseConstraint -> [Level]
constraintLevels constraint = case constraint of
    UniverseLe left right -> [left, right]
    UniverseEq left right -> [left, right]

mapConstraint :: (Level -> Either String Level) -> UniverseConstraint -> Either String UniverseConstraint
mapConstraint transform constraint = case constraint of
    UniverseLe (Successor left) right -> UniverseLe <$> (Successor <$> transform left) <*> transform right
    UniverseLe left right -> UniverseLe <$> transform left <*> transform right
    UniverseEq left right -> UniverseEq <$> transform left <*> transform right

termLevels :: Term -> [Level]
termLevels input = appEndo (getConst (traverseTermLevels (Const . Endo . (:)) input)) []

selfInstances :: ConstId -> Term -> [UniverseInstance]
selfInstances identity input = appEndo (collect input) [] where
    collect term = Endo (own term ++) <> getConst (descend (\_ -> Const . collect) 0 term)
    own term = case term of
        Cst found instance_
            | found == identity -> [instance_]
        Ind found _ instance_
            | found == identity -> [instance_]
        Con found _ _ instance_
            | found == identity -> [instance_]
        PField found _ instance_
            | found == identity -> [instance_]
        Case found _ instance_ _ _ _ _ _
            | found == identity -> [instance_]
        _ -> []

mapDeclaration :: (Term -> Either String Term) -> Env.Decl -> Either String Env.Decl
mapDeclaration transform declaration = case declaration of
    Env.Axiom typ -> Env.Axiom <$> transform typ
    Env.Definition typ body -> Env.Definition <$> transform typ <*> transform body
    Env.Theorem typ body -> Env.Theorem <$> transform typ <*> transform body
    Env.Inductive count families -> Env.Inductive count <$> mapM family families
    where
        family value = do
            typ <- transform (Env.familyType value)
            constructors <- mapM (\(name, body) -> (,) name <$> transform body) (Env.familyCons value)
            Right value { Env.familyType = typ, Env.familyCons = constructors }

mapTermLevels :: (Level -> Either String Level) -> Term -> Either String Term
mapTermLevels = traverseTermLevels

expandReferences :: Map.Map ConstId ExportScheme -> ConstId -> Maybe ExportScheme -> Term -> Either String Term
expandReferences schemes own selected term = case term of
    Cst identity instance_ -> Cst identity <$> expand identity instance_
    Ind identity index instance_ -> Ind identity index <$> expand identity instance_
    Con identity index constructor instance_ -> Con identity index constructor <$> expand identity instance_
    PField identity field instance_ -> PField identity field <$> expand identity instance_
    Case identity index instance_ parameters hints motive value branches -> do
        universes <- expand identity instance_
        descend (\_ -> expandReferences schemes own selected) 0 (Case identity index universes parameters hints motive value branches)
    _ -> descend (\_ -> expandReferences schemes own selected) 0 term
    where
        expand identity instance_
            | identity == own, Nothing <- selected = Right instance_
            | otherwise = case if identity == own then selected else Map.lookup identity schemes of
                Nothing -> Left "a Rocq reference precedes its declaration's universe graph"
                Just scheme
                    | length instance_ == schemeArity scheme -> mapM (substituteLevel instance_) (schemeParameters scheme)
                    | otherwise -> Left "a Rocq reference has the wrong source universe arity"
