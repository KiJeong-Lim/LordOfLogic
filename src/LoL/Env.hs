{-# LANGUAGE PatternSynonyms #-}
module LoL.Env (Decl (..), Family (Family, familyName, familyType, familyCons, familyRecord, familyTemplate), RecordInfo (..), Entry (..), Env, Refusal (..), Mode (..), emptyEnv, envDecls, admissionView, selectUniverseScope, checkUniverseScope, envNames, withNames, envAmbiguous, withAmbiguous, constructorName, envFresh, envStamp, envSpecs, declTypes, declBody, reducibleBody, declTerms, declGlobals, reachable, factsFor, allFacts, appendedFacts, assumptions, declare, declareIn, declareWithUniverses, declareInWithUniverses, validUniverses, checkUniverses, checkUniversesBefore, beforeUniverseDeclaration, typeOfTerm, typeOfTermWithUniverses, shownType, shownTypeWithUniverses, visible, visibleEntry, normalForm, normalFormWithUniverses, argumentArity, universeGoal, askIn, oracleWorld, withProofOracle, run, Syntax (Syntax, syntaxArguments, syntaxInfix, syntaxNumerals, syntaxNever, syntaxProjectionParameters, syntaxRuleSites), syntaxRules, readerRules, syntaxReader, registerRule, withRulesFrom, notationWords, envSyntax, withSyntax, envArguments, envInfix, envNumerals, validOperator) where

import Control.Monad (when)
import Data.IORef
import Data.List (find)
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Hol.V2.Embedding (Context, Question, _QuestionName, _QuestionTerm, _QuestionHyps)
import Hol.V2.Embedding (LogicVar (..), TermNode, mkLVar, mkNApp, mkNCon, DataConstructor (..), LogicalOperator (..), foldlNApp)
import LoL.Core
import qualified LoL.Front.HostLexer as Lexer
import qualified LoL.Front.Notation as Notation
import LoL.Front.Syntax (Span, SyntaxRule (..), RulePart (..), RuleTarget (..))
import LoL.Hol.Embed
import LoL.Hol.Session
import LoL.Oracle (World (..), Failure (..), positive)
import LoL.Oracle.Guard (guarded)
import LoL.Oracle.Tree (Spec (..), Packet (..))

-- `Definition a t` and `Theorem a t` have type `a` and body `t`. `Inductive n fs`
-- is a block of families with `n` parameters.
data Decl
    = Axiom Term
    | Definition Term Term
    | Theorem Term Term
    | Inductive Int [Family]
    deriving (Eq, Show)

-- The type of a family and the types of its constructors include the
-- parameters of the block. The block refers to itself by the number that the
-- environment gives next (envFresh).
data RecordInfo
    = RecordInfo
        { recordEta    :: Bool
        , recordFields :: [String]
        }
    deriving (Eq, Show)

data Family
    = FamilyData
        { familyName     :: String
        , familyType     :: Term
        , familyCons     :: [(String, Term)]
        , familyRecord   :: Maybe RecordInfo
        , familyTemplate :: Bool
        }
    deriving (Eq, Show)

pattern Family :: String -> Term -> [(String, Term)] -> Family
pattern Family name typ constructors <- FamilyData name typ constructors _ _ where
    Family name typ constructors = FamilyData name typ constructors Nothing False
{-# COMPLETE Family #-}

-- entryInfo has what the kernel returned for each family of an inductive
-- block, and nothing for another declaration.
data Entry
    = Entry
        { entryName :: String
        , entryDecl :: Decl
        , entryInfo :: [Info]
        , entryUniverses :: UniverseContext
        }
    deriving (Eq, Show)

-- Surface operators have exactly the spelling recognized by the lexer.
validOperator :: String -> Bool
validOperator symbol = not (null symbol) && all Lexer.symbol symbol && symbol `notElem` [":", "|", ":=", "=>", "->"]

data Syntax
    = SyntaxData
        { syntaxArguments            :: !(Map.Map Global [Bool])
        , syntaxInfix                :: !(Map.Map String (Global, Integer, String))
        , syntaxNumerals             :: !(Maybe (Global, Global))
        , syntaxNever                :: !(Set.Set Global)
        , syntaxProjectionParameters :: !(Map.Map Global Int)
        , syntaxRuleIndex            :: !Notation.Rules
        , syntaxRuleSites            :: !(Map.Map (SyntaxRule Global) (String, Span))
        }
    deriving (Eq, Show)

-- Modules that declare no ordinary record accessors have the original syntax.
pattern Syntax :: Map.Map Global [Bool] -> Map.Map String (Global, Integer, String) -> Maybe (Global, Global) -> Set.Set Global -> Syntax
pattern Syntax arguments infixes numerals never <- SyntaxData arguments infixes numerals never _ _ _ where
    Syntax arguments infixes numerals never = SyntaxData arguments infixes numerals never Map.empty Notation.emptyRules Map.empty
{-# COMPLETE Syntax #-}

syntaxRules :: Syntax -> [SyntaxRule Global]
syntaxRules = Map.keys . syntaxRuleSites

-- Imported/exported metadata and parser lookup share this insertion path.
-- A second declaration may record a new source location for an existing rule.
registerRule :: SyntaxRule Global -> (String, Span) -> Syntax -> Syntax
registerRule rule site syntax = syntax
    { syntaxRuleIndex = Notation.addRule rule (syntaxRuleIndex syntax)
    , syntaxRuleSites = Map.insert rule site (syntaxRuleSites syntax)
    }

withRulesFrom :: Syntax -> Syntax -> Syntax
withRulesFrom source target = target { syntaxRuleIndex = syntaxRuleIndex source, syntaxRuleSites = syntaxRuleSites source }

syntaxReader :: Syntax -> Notation.Rules
syntaxReader syntax = (syntaxRuleIndex syntax) { Notation.infixRules = syntaxInfix syntax }

-- A mixed expression must compare the precedences of both notation families.
-- The compatibility reader diagnoses a legacy-only infix expression in Fixity.
readerRules :: Syntax -> [SyntaxRule Global]
readerRules syntax
    | any termRule rules = rules ++ [SyntaxRule [TermSlot, Literal op, TermSlot] level direction (TermTarget target) | (op, (target, level, direction)) <- Map.toAscList (syntaxInfix syntax)]
    | otherwise = rules
    where
        rules = syntaxRules syntax
        termRule (SyntaxRule _ _ _ (TermTarget _)) = True
        termRule _ = False

-- Protect both pretty-printed binders and automatic proof names from the
-- active term language. Non-identifier symbols cannot be local names.
notationWords :: Syntax -> Set.Set String
notationWords = Notation.termLiterals . syntaxRuleIndex

-- The declarations, their names, the next constant, the stamp of this
-- environment, and what the oracle kept of each inductive
-- block that it judged. Only `declare` makes an
-- environment with declarations, and it gives each one a stamp of its own: two
-- environments with the same stamp have the same declarations. The fields of
-- an environment and of its syntax are strict: one left unevaluated holds the
-- environment that it was made from, and so every environment before it.
-- Universe segments stay in the environment so cached modules keep their
-- identities. Only visible segments are installed as axioms for this module.
-- One previous selection is enough for a module that opens with an import.
-- It belongs to this exact declaration table and is cleared on every admission.
-- When an older loaded sibling is outside an entry's admission scope, save
-- the shared set of visible segment owners for later telescope inspection.
data UniverseScope
    = UniverseScope
        { scopeKnown        :: !(Set.Set ConstId)
        , scopeVisible      :: !(Set.Set ConstId)
        , scopePrevious     :: !(Maybe (Set.Set ConstId, Stamp))
        , scopeAtAdmission  :: !(Map.Map ConstId (Set.Set ConstId))
        , scopeDeclarations :: !(Maybe Stamp)
        }
    deriving (Show)

instance Eq UniverseScope where
    left == right = scopeKnown left == scopeKnown right && scopeVisible left == scopeVisible right && scopeAtAdmission left == scopeAtAdmission right

data Env
    = Env !(Map.Map ConstId Entry) !(Map.Map String Global) !ConstId !(Maybe Stamp) !(Map.Map ConstId Spec) !Syntax !(Set.Set String) !UniverseScope
    deriving (Show)

instance Eq Env where
    Env decls1 names1 fresh1 _ specs1 syntax1 hidden1 scope1 == Env decls2 names2 fresh2 _ specs2 syntax2 hidden2 scope2 = decls1 == decls2 && names1 == names2 && fresh1 == fresh2 && specs1 == specs2 && syntax1 == syntax2 && hidden1 == hidden2 && scope1 == scope2

envDecls :: Env -> Map.Map ConstId Entry
envDecls (Env decls _ _ _ _ _ _ _) = decls

selectUniverseScope :: Set.Set ConstId -> Env -> IO Env
selectUniverseScope allowed env@(Env decls names fresh old specs syntax hidden scope)
    | visible == active = return env
    | otherwise = do
        stamp <- case scopePrevious scope of
            Just (saved, identity)
                | saved == visible -> return identity
            _ -> newStamp
        return (Env decls names fresh (Just stamp) specs syntax hidden scope { scopeVisible = visible, scopePrevious = (,) active <$> old })
    where
        active = scopeVisible scope
        visible = Set.intersection (scopeKnown scope) allowed

activeUniverses :: Env -> Set.Set ConstId
activeUniverses (Env _ _ _ _ _ _ _ scope) = scopeVisible scope

extendScope :: ConstId -> [TermNode] -> Stamp -> Env -> UniverseScope
extendScope c facts base (Env _ _ _ _ _ _ _ scope) =
    UniverseScope (add known) (add active) Nothing history (Just base)
    where
        known = scopeKnown scope
        active = scopeVisible scope
        prior = scopeAtAdmission scope
        history = if Set.size active == Set.size known then prior else Map.insert c active prior
        add owners = if null facts then owners else Set.insert c owners

admissionView :: ConstId -> Env -> IO Env
admissionView c env@(Env _ _ _ _ _ _ _ scope) = case Map.lookup c (scopeAtAdmission scope) of
    Nothing
        | Set.size known == Set.size active -> return env
    saved -> selectUniverseScope (Set.insert c (maybe (fst (Set.split c known)) id saved)) env
    where
        known = scopeKnown scope
        active = scopeVisible scope

envNames :: Env -> Map.Map String Global
envNames (Env _ names _ _ _ _ _ _) = names

-- Module visibility changes names only, never the admitted declarations or
-- their kernel facts. Canonical qualified names survive shadowing of an alias.
withNames :: Map.Map String Global -> Env -> Env
withNames names (Env decls _ fresh stamp specs syntax hidden scope) = Env decls names fresh stamp specs syntax hidden scope

-- The short names that two or more declarations in scope have, one of them
-- a constructor. `envNames` has no such name: it is ambiguous.
envAmbiguous :: Env -> Set.Set String
envAmbiguous (Env _ _ _ _ _ _ hidden _) = hidden

withAmbiguous :: Set.Set String -> Env -> Env
withAmbiguous hidden (Env decls names fresh stamp specs syntax _ scope) = Env decls names fresh stamp specs syntax hidden scope

-- A short name that a constructor in scope has, alone or with another
-- declaration. A pattern cannot bind such a name.
constructorName :: Env -> String -> Bool
constructorName env name = Set.member name (envAmbiguous env) || found (Map.lookup name (envNames env)) where
    found (Just (GlobalCon {})) = True
    found _ = False

envFresh :: Env -> ConstId
envFresh (Env _ _ fresh _ _ _ _ _) = fresh

envStamp :: Env -> Maybe Stamp
envStamp (Env _ _ _ stamp _ _ _ _) = stamp

envSpecs :: Env -> Map.Map ConstId Spec
envSpecs (Env _ _ _ _ specs _ _ _) = specs

-- Surface metadata carries no authority for admission: all proposed terms
-- still go through a ground run, and object replay validates its references.
envSyntax :: Env -> Syntax
envSyntax (Env _ _ _ _ _ syntax _ _) = syntax

withSyntax :: Syntax -> Env -> Env
withSyntax syntax (Env decls names fresh stamp specs _ hidden scope) = Env decls names fresh stamp specs syntax hidden scope

envArguments :: Env -> Map.Map Global [Bool]
envArguments = syntaxArguments . envSyntax

envInfix :: Env -> Map.Map String (Global, Integer, String)
envInfix = syntaxInfix . envSyntax

envNumerals :: Env -> Maybe (Global, Global)
envNumerals = syntaxNumerals . envSyntax

-- Arguments metadata inspects a type returned and normalized by the kernel.
-- Counting the printed telescope is syntax inspection, not a host type rule.
argumentArity :: Kernel -> Limits -> Env -> Global -> IO (Either Refusal Int)
argumentArity kernel limits env global = do
    let identifier = case global of
            GlobalCst c -> c
            GlobalInd c _ -> c
            GlobalCon c _ _ -> c
            GlobalProj c _ -> c
        context = maybe emptyUniverses entryUniverses (Map.lookup identifier (envDecls env))
        instance' = map Parameter [0 .. length (universeNames context) - 1]
    scoped <- admissionView identifier env
    fmap (fmap count) (askUniversesIn (beforeUniverseDeclaration scoped identifier) "u_argument_signature" kernel limits scoped context (fromGlobalAt instance' global))
    where
        count (Pi _ _ rest) = 1 + count rest
        count _ = 0

-- How a ground run gets the facts of its environment. `Persistent`: from the
-- engine that the kernel keeps, which holds every fact of the environment.
-- `Reference`: a machine of its own with the facts of the declarations that the
-- run depends on. The two give the same verdict.
data Mode
    = Persistent
    | Reference
    deriving (Eq, Show)

-- `OracleRejected`: the kernel rejected under the rule of
-- the report because its oracle said no, for the given reason.
data Refusal
    = DuplicateName String
    | NotClosed
    | KernelRejected (Maybe Report)
    | OracleRejected Report String
    | KernelUndecided String
    deriving (Eq, Show)

emptyEnv :: Env
emptyEnv = Env Map.empty Map.empty 0 Nothing Map.empty (Syntax Map.empty Map.empty Nothing Set.empty) Set.empty (UniverseScope Set.empty Set.empty Nothing Map.empty Nothing)

declTypes :: Decl -> [Term]
declTypes decl
    = case decl of
        Axiom a -> [a]
        Definition a _ -> [a]
        Theorem a _ -> [a]
        Inductive _ families -> concat [familyType family : map snd (familyCons family) | family <- families]

declBody :: Decl -> Maybe Term
declBody decl
    = case decl of
        Definition _ t -> Just t
        Theorem _ t -> Just t
        _ -> Nothing

-- Only a `Definition` reduces ([R-Delta]): the kernel never sees the body of a `Theorem`.
reducibleBody :: Decl -> Maybe Term
reducibleBody decl
    = case decl of
        Definition _ t -> Just t
        _ -> Nothing

declTerms :: Decl -> [Term]
declTerms decl = declTypes decl ++ maybe [] pure (declBody decl)

-- The declaration with its terms replaced, in the order of `declTerms`.
withTerms :: Decl -> [Term] -> Decl
withTerms decl terms
    = case (decl, terms) of
        (Axiom _, [a]) -> Axiom a
        (Definition _ _, [a, t]) -> Definition a t
        (Theorem _ _, [a, t]) -> Theorem a t
        (Inductive parameters families, _) -> Inductive parameters (rebuild families terms)
        _ -> decl
    where
        rebuild families items = case (families, items) of
            (family : rest, arity : others) -> family { familyType = arity, familyCons = zip (map fst (familyCons family)) others } : rebuild rest (drop (length (familyCons family)) others)
            _ -> []

-- The names that declaration `c` gives, with what each one stands for. A block
-- has the names of its families and of their constructors, not `name`.
declGlobals :: ConstId -> String -> Decl -> [(String, Global)]
declGlobals c name decl
    = case decl of
        Inductive _ families -> concatMap familyNames (zip [0 ..] families)
        _ -> [(name, GlobalCst c)]
    where
        familyNames (index, family) = (familyName family, GlobalInd c index) : constructors ++ fields where
            constructors = [(constructor, GlobalCon c index j) | (j, (constructor, _)) <- zip [0 ..] (familyCons family)]
            fields = [(field, GlobalProj c j) | Just record <- [familyRecord family], (j, field) <- zip [0 ..] (recordFields record)]

-- The declarations a run can reach from `roots`: through types, and through the bodies that reduce.
reachable :: (Decl -> Maybe Term) -> Env -> Set.Set ConstId -> Set.Set ConstId
reachable bodyOf = declarationClosure dependencies where
    dependencies entry = Set.union (constraintOwners (entryUniverses entry)) (termDependencies constantsOf bodyOf (entryDecl entry))

termDependencies :: (Term -> Set.Set ConstId) -> (Decl -> Maybe Term) -> Decl -> Set.Set ConstId
termDependencies collect bodyOf decl = Set.unions (map collect (declTypes decl ++ maybe [] pure (bodyOf decl)))

declarationClosure :: (Entry -> Set.Set ConstId) -> Env -> Set.Set ConstId -> Set.Set ConstId
declarationClosure dependencies env roots = go Set.empty (Set.toList roots) where
    go seen [] = seen
    go seen (c : rest)
        | Set.member c seen = go seen rest
        | otherwise = case Map.lookup c (envDecls env) of
            Nothing -> go seen rest
            Just entry -> go (Set.insert c seen) (Set.toList (dependencies entry) ++ rest)

-- The facts that one declaration adds to the environment of the kernel.
declFacts :: ConstId -> Entry -> [TermNode]
declFacts c entry
    = case entryDecl entry of
        Axiom a -> [cstTypeSchemeFact universes c a]
        Definition a t -> [cstTypeSchemeFact universes c a, cstBodySchemeFact universes c t]
        Theorem a _ -> [cstTypeSchemeFact universes c a]
        Inductive count families -> templateFacts count families ++ recordFacts families ++ concat [indTypeSchemeFact universes c i (familyType family) : indInfoSchemeFact universes c i info : [conTypeSchemeFact universes c i j t | (j, (_, t)) <- zip [0 ..] (familyCons family)] | (i, family, info) <- zip3 [0 ..] families (entryInfo entry)]
    where
        universes = entryUniverses entry
        templateFacts count families =
            [foldlNApp (named "template_block") [natural c, natural (toInteger (length (universeNames universes))), embedUniverseConstraints (universeConstraints universes), natural (toInteger count), embedTerm (familyType family), terms (map (embedTerm . snd) (familyCons family))] | family <- families, familyTemplate family]
        recordFacts families = [recordInfoFact c (length (recordFields record)) (recordEta record) | family <- families, Just record <- [familyRecord family]]

-- Shared template defaults and the ground constraints an admitted entry
-- publishes about them. They also belong to a reference-mode ground run.
globalFacts :: ConstId -> Entry -> [TermNode]
globalFacts c entry
    | Inductive _ families <- entryDecl entry, any familyTemplate families = [scheme "u_template_segment"]
    | null (universeNames universes), not (Set.null (constraintOwners universes)) = [scheme "u_client_segment"]
    | otherwise = []
    where
        universes = entryUniverses entry
        scheme predicate = foldlNApp (named predicate) [natural c, natural (toInteger (length (universeNames universes))), embedUniverseConstraints (universeConstraints universes)]

-- The facts of the declarations that `terms` depend on.
factsFor :: Env -> [Term] -> [TermNode]
factsFor env terms = concat [facts c entry | (c, entry) <- Map.toAscList selected] where
    used = reachable reducibleBody env (Set.unions (map constantsOf terms))
    active = activeUniverses env
    selected = Map.restrictKeys (envDecls env) (Set.union used active)
    facts c entry = [fact | Set.member c active, fact <- globalFacts c entry] ++ [fact | Set.member c used, fact <- declFacts c entry]

-- The facts of every declaration and the current module's universe graph.
allFacts :: Env -> [TermNode]
allFacts env = concat [[fact | Set.member c active, fact <- globalFacts c entry] ++ declFacts c entry | (c, entry) <- Map.toAscList (envDecls env)] where
    active = activeUniverses env

-- The caller has just admitted one local declaration. A change to any older
-- universe segment needs a complete reload of the scoped proof environment.
appendedFacts :: Env -> Env -> Maybe (ConstId, Entry, [TermNode])
appendedFacts previous next
    | envFresh next == number + 1 && Set.delete number active == activeUniverses previous = do
        entry <- Map.lookup number (envDecls next)
        return (number, entry, [fact | Set.member number active, fact <- globalFacts number entry] ++ declFacts number entry)
    | otherwise = Nothing
    where
        number = envFresh previous
        active = activeUniverses next

-- Only declaration facts enter this cache. Make the selected graph facts
-- hypotheses of each query, so switching imports cannot leak a sibling's
-- constraints or require recompiling the common declaration prefix.
declarationStamp :: Env -> Maybe Stamp
declarationStamp (Env _ _ _ _ _ _ _ scope) = scopeDeclarations scope

declarationFacts :: Env -> [TermNode]
declarationFacts env = concatMap (uncurry declFacts) (Map.toAscList (envDecls env))

withSegments :: Env -> TermNode -> TermNode
withSegments env goal = foldr assume goal (Map.toAscList (Map.restrictKeys (envDecls env) (activeUniverses env))) where
    assume (c, entry) inner = foldr (\fact next -> foldlNApp (mkNCon LO_imply) [fact, next]) inner (globalFacts c entry)

-- An immutable per-query index. It does not add facts or widen the
-- persistent engine's current module scope.
universeGoal :: Kernel -> Env -> TermNode -> TermNode
universeGoal kernel env goal
    | Set.null segments || Map.notMember (DC_Named "u_global_ids") (kernelTypes kernel) = goal
    | otherwise = foldlNApp (mkNCon LO_imply) [mkNApp (named "u_global_ids") (embedList (kindOf "nat") (map natural (Set.toAscList segments))), goal]
    where
        segments = activeUniverses env

-- Each question back starts a separate query. Reinstall the same graph
-- on the aside engine, including when it was forked from the main engine.
scopedDialogue :: Kernel -> Env -> Dialogue -> Dialogue
scopedDialogue kernel env dialogue = Dialogue (\goal -> dialogueAsk dialogue (withSegments env (universeGoal kernel env goal)))

-- A ground run, with what the oracle kept of a block that the run admits and
-- why it said no. The oracle answers the kernel through Hol's FFI.
run :: Mode -> Kernel -> Limits -> Env -> [Term] -> TermNode -> [LogicVar] -> IO (Verdict, Maybe Spec, Maybe String)
run mode kernel limits env terms goal outputs = do
    found <- newIORef Nothing
    reason <- newIORef Nothing
    verdict <- withOracleDialogue kernel limits (declarationStamp env) (declarationFacts env) (judge env found reason . scopedDialogue kernel env) (\asked -> plain asked (universeGoal asked env goal))
    (,,) verdict <$> readIORef found <*> readIORef reason
    where
        plain selected query = case mode of
            Persistent -> loadedRun selected limits (declarationStamp env) (declarationFacts env) (withSegments env query) outputs
            Reference -> groundRun selected limits (factsFor env terms) query outputs

-- Proof programs may contain user tactics. Their oracle still asks the
-- independent base kernel, through exactly the ground admission dispatcher.
withProofOracle :: Kernel -> Limits -> Env -> ((Context -> Question -> IO Bool) -> IO a) -> IO a
withProofOracle kernel limits env action = do
    found <- newIORef Nothing
    reason <- newIORef Nothing
    let answer context question = withDialogue kernel limits (declarationStamp env) (declarationFacts env) (\dialogue -> judge env found reason (scopedDialogue kernel env dialogue) context question)
    action answer

-- The oracle. The kernel hands it a block under the name
-- "positive" and a block of functions, with the hypotheses of its goal, under
-- the name "guarded". Where the oracle needs a weak head normal form it asks
-- the kernel back, on the engine that no run is using. `found` gets what the
-- oracle keeps of a block, and `reason` why it said no. Hol hands over a term
-- that has variables too, with their scopes and constraints; this oracle
-- judges a complete Core term and kernel context. Unrelated Hol hypotheses
-- may contain open administrative cells without entering that judgment.
judge :: Env -> IORef (Maybe Spec) -> IORef (Maybe String) -> Dialogue -> Context -> Question -> IO Bool
judge env found reason dialogue _ question = do
    outcome <- case recoverOracleUniverses (_QuestionHyps question) (_QuestionTerm question) of
        Left message -> return (Left (Unavailable message))
        Right (universes, hypotheses, payload)
            | not (closedOracleInput payload hypotheses) -> return (Left (Refuted "the judged term or kernel context has a variable, and the oracle judges complete Core input"))
            | otherwise -> do
                consistent <- universeDialogue dialogue universes
                case consistent of
                    Left failure -> return (Left failure)
                    Right () -> let world = oracleWorldWithUniverses dialogue env universes in case _QuestionName question of
                        "positive" -> case recoverBlock payload of
                            Right (block, parameters, families) -> positive world block parameters families >>= either (return . Left) (\spec -> Right () <$ writeIORef found (Just spec))
                            Left message -> return (Left (Unavailable message))
                        "guarded" -> either (return . Left . Unavailable) (uncurry (guarded world)) (recoverLocal hypotheses payload)
                        name -> return (Left (Unavailable ("the oracle has no judgment named " ++ name)))
    case outcome of
        Right () -> True <$ writeIORef reason Nothing
        Left (Refuted message) -> False <$ writeIORef reason (Just message)
        Left (Unavailable message) -> ioError (userError ("oracle: " ++ message))

-- Inference-time tables are untrusted syntax. Their conjunction must be
-- consistent before it becomes an oracle reduction context, even when the
-- judged payload does not mention one of its level cells.
universeDialogue :: Dialogue -> UniverseContext -> IO (Either Failure ())
universeDialogue _ context | context == emptyUniverses = return (Right ())
universeDialogue dialogue context = do
    let output = LV_Named "OracleUniverseConsistency"
        request = foldlNApp (named "u_satisfiable")
            [natural (toInteger (length (universeNames context))), embedUniverseConstraints (universeConstraints context), mkLVar output]
    syntax <- dialogueAsk dialogue request [output]
    case syntax of
        Admitted [value] -> case universeFormula value of
            Left message -> return (Left (Unavailable message))
            Right formula -> do
                checked <- dialogueAsk dialogue formula []
                return $ case checked of
                    Admitted [] -> Right ()
                    Rejected _ -> Left (Refuted "the universe context is inconsistent")
                    Undecided message -> Left (Unavailable message)
                    _ -> Left (Unavailable "universe consistency returned unexpected outputs")
        Rejected _ -> return (Left (Unavailable "the kernel could not encode the oracle universe context"))
        Undecided message -> return (Left (Unavailable message))
        _ -> return (Left (Unavailable "the kernel did not return one closed universe formula"))

-- What the oracle knows of an environment, and how it asks the kernel back:
-- a run of `whnf` under the variables of the context, on the engine that the
-- run which asked the oracle is not using.
oracleWorld :: Dialogue -> Env -> World
oracleWorld dialogue env = oracleWorldWithUniverses dialogue env emptyUniverses

oracleWorldWithUniverses :: Dialogue -> Env -> UniverseContext -> World
oracleWorldWithUniverses dialogue env universes = World { worldHead = reduction False, worldHalt = reduction True, worldSpec = instanceSpec, worldFixp = permitsFix, worldBody = instanceBody } where
    -- Eta records are bifinite. The Inductive form of the same field
    -- telescope is an ordinary inductive family for structural recursion.
    permitsFix c index = case entryDecl <$> Map.lookup c (envDecls env) of
        Just (Inductive _ families)
            | family : _ <- drop index families -> maybe True (not . recordEta) (familyRecord family)
        _ -> False
    atInstance c instance' = do
        entry <- Map.lookup c (envDecls env)
        if length instance' == length (universeNames (entryUniverses entry)) then Just entry else Nothing
    instanceBody c instance' = do
        entry <- atInstance c instance'
        body <- reducibleBody (entryDecl entry)
        either (const Nothing) Just (substituteUniverses instance' body)
    instanceSpec c instance' = do
        _ <- atInstance c instance'
        spec <- Map.lookup c (envSpecs env)
        packets <- either (const Nothing) Just (mapM (packet instance') (specFams spec))
        return spec { specFams = packets }
    packet instance' value = do
        typ <- substituteUniverses instance' (packetType value)
        constructors <- mapM (\(count, body) -> (,) count <$> substituteUniverses instance' body) (packetCons value)
        return value { packetType = typ, packetCons = constructors }
    output = LV_Named "Out"
    reduction halting context term = do
        verdict <- dialogueAsk dialogue (headGoalWithUniverses universes halting context term output) [output]
        return $ case verdict of
            Admitted [answer] -> either (Left . Unavailable) Right (recoverHead (length context) answer)
            Admitted _ -> Left (Unavailable "the kernel did not return one weak head normal form")
            Rejected _ -> Left (Unavailable "the kernel has no weak head normal form for a term of the oracle")
            Undecided message -> Left (Unavailable message)

rejection :: Maybe Report -> Maybe String -> Refusal
rejection report reason
    = case (report, reason) of
        (Just found, Just why)
            | reportRule found `elem` ["I-Pos", "F-Guard"] -> OracleRejected found why
        _ -> KernelRejected report

-- The assumptions of c: the axioms that it depends on, through the bodies of
-- theorems too.
assumptions :: Env -> ConstId -> Set.Set ConstId
assumptions env c = Set.filter isAxiom (declarationClosure dependencies env (Set.singleton c)) where
    dependencies = termDependencies (constantsWith (const Set.empty)) declBody . entryDecl
    isAxiom d = case Map.lookup d (envDecls env) of
        Just (Entry { entryDecl = Axiom _ }) -> True
        _ -> False

-- The goal that admits declaration `c`, whose terms are `items` in the order
-- of `declTerms`. A block has one output, the info of its families.
admissionGoal :: ConstId -> Decl -> [LogicVar] -> [TermNode] -> TermNode
admissionGoal c decl outputs items
    = case decl of
        Axiom _ -> admitAxGoal (head items)
        Inductive parameters families -> admitIndGoal c parameters (familyTerms families items) (head outputs)
        _ -> admitDefGoal (head items) (items !! 1)

familyTerms :: [Family] -> [TermNode] -> [(TermNode, [TermNode])]
familyTerms (family : others) (arity : rest) = (arity, constructors) : familyTerms others more where
    (constructors, more) = splitAt (length (familyCons family)) rest
familyTerms _ _ = []

-- A run about terms. `build outputs items` is the
-- goal about the terms `items`. Terms without a match go to the kernel as they
-- are written. Otherwise the goal is first run about the written terms under
-- `pretyping`, with outputs of its own; then the kernel elaborates each term;
-- then the goal is run about the elaborated terms. The answer has the goal,
-- the variables that hold the elaborated terms, and the other variables of
-- the goal: every variable of a goal is an output of its run.
staged :: ([LogicVar] -> [TermNode] -> TermNode) -> [LogicVar] -> [Term] -> (TermNode, [LogicVar], [LogicVar])
staged build outputs written
    | not (any hasMatch written) = (build outputs (map embedTerm written), [], [])
    | otherwise = (elaborated (build spare embedded) (zip embedded forms) (build outputs (map mkLVar forms)), forms, spare ++ map holeVar [0 .. holes - 1])
    where
        (numbered, holes) = numberHoles written
        embedded = map embedTerm numbered
        forms = [LV_Named ("Form" ++ show place) | place <- [0 .. length written - 1]]
        spare = [LV_Named ("Spare" ++ show place) | place <- [0 .. length outputs - 1]]

declare :: Kernel -> Limits -> Env -> String -> Decl -> IO (Either Refusal (ConstId, Env))
declare = declareIn Persistent

declareWithUniverses :: Kernel -> Limits -> Env -> String -> UniverseContext -> Decl -> IO (Either Refusal (ConstId, Env))
declareWithUniverses = declareInWithUniverses Persistent

-- This is a structural well-formedness check, not a consistency or entailment
-- check. Those judgments are made by the independent Hol kernel below.
validUniverses :: UniverseContext -> Bool
validUniverses context = all constraint (universeConstraints context) where
    count = length (universeNames context)
    atom level = case level of
        Closed _ -> wellScopedLevel count level
        DefaultLevel {} -> wellScopedLevel count level
        Parameter _ -> wellScopedLevel count level
        _ -> False
    -- A proof may need a level several steps below another one (the least
    -- level of a universe that is private to it is a successor).
    constraint (UniverseLe (Successor left) right) = constraint (UniverseLe left right)
    constraint (UniverseLe left right) = atom left && atom right
    constraint (UniverseEq left right) = atom left && atom right

checkUniverses :: Mode -> Kernel -> Limits -> Env -> UniverseContext -> IO (Either Refusal ())
checkUniverses = checkUniversesIn id

-- An admitted declaration's telescope and export use exactly the segments
-- available when it was admitted. Later entries can further pin a default.
beforeUniverseDeclaration :: Env -> ConstId -> TermNode -> TermNode
beforeUniverseDeclaration env identity goal = case Set.lookupGE identity (activeUniverses env) of
    Nothing -> goal
    Just _ -> foldlNApp (mkNCon LO_imply) [mkNApp (named "u_global_before") (natural identity), goal]

checkUniversesBefore :: ConstId -> Mode -> Kernel -> Limits -> Env -> UniverseContext -> IO (Either Refusal ())
checkUniversesBefore identity mode kernel limits env = checkUniversesIn (beforeUniverseDeclaration env identity) mode kernel limits env

checkUniversesIn :: (TermNode -> TermNode) -> Mode -> Kernel -> Limits -> Env -> UniverseContext -> IO (Either Refusal ())
checkUniversesIn _ _ _ _ _ context | context == emptyUniverses = return (Right ())
checkUniversesIn scope mode kernel limits env context = checkConsistency scope mode kernel limits env context

-- The union of separately consistent imported graphs may be inconsistent.
checkUniverseScope :: Kernel -> Limits -> Env -> IO (Either Refusal ())
checkUniverseScope kernel limits env
    | Set.null (activeUniverses env) = return (Right ())
    | otherwise = checkConsistency id Persistent kernel limits env emptyUniverses

checkConsistency :: (TermNode -> TermNode) -> Mode -> Kernel -> Limits -> Env -> UniverseContext -> IO (Either Refusal ())
checkConsistency scope mode kernel limits env context = do
    let output = LV_Named "UniverseConsistency"
        request = foldlNApp (named "u_satisfiable")
            [natural (toInteger (length (universeNames context))), embedUniverseConstraints (universeConstraints context), mkLVar output]
        inconsistent = KernelRejected (Just (Report "U-Context" [] []))
    (prepared, _, reason) <- run mode kernel limits env [] (scope request) [output]
    case prepared of
        Admitted [syntax] -> case universeFormula syntax of
            Left message -> return (Left (KernelUndecided message))
            Right formula -> do
                (checked, _, _) <- run mode kernel limits env [] formula []
                return $ case checked of
                    Admitted [] -> Right ()
                    Rejected _ -> Left inconsistent
                    Undecided message -> Left (KernelUndecided message)
                    _ -> Left (KernelUndecided "universe consistency returned unexpected outputs")
        Rejected report -> return (Left (rejection report reason))
        Undecided message -> return (Left (KernelUndecided message))
        _ -> return (Left (KernelUndecided "the kernel did not return one closed universe formula"))

-- The environment grows only after a run of the kernel has admitted the
-- declaration. [I-Fresh] and the freshness of [D-Ax], [D-Def] and [D-Thm] are
-- the host's: the kernel sees numbers, not names. A declaration with a match
-- is elaborated in that run, and what the kernel admits and the environment
-- gets is the elaborated declaration.
declareIn :: Mode -> Kernel -> Limits -> Env -> String -> Decl -> IO (Either Refusal (ConstId, Env))
declareIn mode kernel limits env name = declareInWithUniverses mode kernel limits env name emptyUniverses

declareInWithUniverses :: Mode -> Kernel -> Limits -> Env -> String -> UniverseContext -> Decl -> IO (Either Refusal (ConstId, Env))
declareInWithUniverses mode kernel limits env name universes written
    | Just taken <- find (`Map.member` envNames env) names = return (Left (DuplicateName taken))
    | Just repeated <- find (\given -> length (filter (== given) names) > 1) names = return (Left (DuplicateName repeated))
    | not (validUniverses universes && all (wellScopedUniverses parameterCount 0) (declTerms written)) = return (Left NotClosed)
    | otherwise = do
        consistent <- checkUniverses mode kernel limits env universes
        case consistent of
            Left failure -> return (Left failure)
            Right () -> admit
    where
        admit = do
            (verdict, spec, reason) <- run mode kernel limits env (declTerms written) (attributeGoal goal) (outputs ++ forms ++ others)
            case verdict of
                Admitted answers -> case (mapM (\answer -> recoverList answer >>= mapM recoverInfo) (take (length outputs) answers), mapM recoverTerm (take (length forms) (drop (length outputs) answers))) of
                    (Right info, Right elaborated')
                        | map length info == [length families | Inductive _ families <- [written]] -> do
                            let entry = Entry { entryName = name, entryDecl = if null forms then written else withTerms written (zipWith hinted (declTerms written) elaborated'), entryInfo = concat info, entryUniverses = universes }
                            stamp <- newStamp
                            -- A run on a machine of its own leaves the kept engines
                            -- with the environment that they hold.
                            let segments = globalFacts c entry
                            base <- if null segments && Set.null (activeUniverses env) then return stamp else newStamp
                            when (mode == Persistent) $ do
                                loadedExtend kernel (declarationStamp env) base (declFacts c entry)
                                when (base /= stamp || declarationStamp env /= envStamp env) (loadedExtend kernel (envStamp env) stamp (segments ++ declFacts c entry))
                            return (Right (c, Env (Map.insert c entry (envDecls env)) (Map.union (Map.fromList globals) (envNames env)) (c + 1) (Just stamp) (maybe id (Map.insert c) spec (envSpecs env)) (envSyntax env) (envAmbiguous env) (extendScope c segments base env)))
                    _ -> return (Left (KernelUndecided "the run did not return the info of each family and the elaborated form of each term"))
                Rejected report -> return (Left (rejection report reason))
                Undecided message -> return (Left (KernelUndecided message))
        parameterCount = length (universeNames universes)
        c = envFresh env
        globals = declGlobals c name written
        names = map fst globals
        outputs = [LV_Named "Out" | Inductive _ _ <- [written]]
        (goal, forms, others)
            | universes == emptyUniverses = staged (admissionGoal c written) outputs (declTerms written)
            | otherwise = (schemeGoal, [], [])
        attributeGoal admission = case written of
            Inductive parameters families -> record (template admission) where
                items = if null forms then map embedTerm (declTerms written) else map mkLVar forms
                block = blockOf c parameters (familyTerms families items)
                template = if any familyTemplate families then withTemplateShape universes block else id
                record = case [descriptor | family <- families, Just descriptor <- [familyRecord family]] of
                    descriptor : _ -> withRecordShape universes block (length (recordFields descriptor)) (recordEta descriptor) (head outputs)
                    [] -> id
            _ -> admission
        schemeGoal = case written of
            Axiom typ -> apply "u_admit_ax" [embedTerm typ]
            Definition typ body -> apply "u_admit_def" [embedTerm typ, embedTerm body]
            Theorem typ body -> apply "u_admit_def" [embedTerm typ, embedTerm body]
            Inductive parameters families -> apply "u_admit_ind"
                [embedBlock c parameters [(familyType family, map snd (familyCons family)) | family <- families], mkLVar (head outputs)]
        apply predicate arguments = foldlNApp (named predicate)
            (natural (toInteger parameterCount) : embedUniverseConstraints (universeConstraints universes) : arguments)

typeOfTerm :: Kernel -> Limits -> Env -> Term -> IO (Either Refusal Term)
typeOfTerm = askIn Persistent 1 (\outputs item -> typeGoal item (head outputs))

typeOfTermWithUniverses :: Kernel -> Limits -> Env -> UniverseContext -> Term -> IO (Either Refusal Term)
typeOfTermWithUniverses kernel limits env context term
    | context == emptyUniverses = typeOfTerm kernel limits env term
    | otherwise = askUniverses "u_infer" kernel limits env context term

-- The type of a term as `Check` shows it: in normal form by beta and iota,
-- and so without a cast (Rocq: `nf_betaiota`). The kernel builds that form
-- anew, so its binders get the names of the type as it is before that.
shownType :: Kernel -> Limits -> Env -> Term -> IO (Either Refusal Term)
shownType kernel limits env term = withWrittenNames (typeOfTerm kernel limits env term) (askIn Persistent 2 (\outputs item -> shownGoal item (outputs !! 1) (head outputs)) kernel limits env term)

shownTypeWithUniverses :: Kernel -> Limits -> Env -> UniverseContext -> Term -> IO (Either Refusal Term)
shownTypeWithUniverses kernel limits env context term
    | context == emptyUniverses = shownType kernel limits env term
    | otherwise = withWrittenNames (askUniverses "u_infer" kernel limits env context term) (askUniverses "u_shown" kernel limits env context term)

withWrittenNames :: IO (Either Refusal Term) -> IO (Either Refusal Term) -> IO (Either Refusal Term)
withWrittenNames written shown = do
    typed <- written
    case typed of
        Left refusal -> return (Left refusal)
        Right typ -> fmap (hinted typ) <$> shown

-- A term as it is shown: Rocq prints the type of a `let` when that type is a
-- proposition (detyping.ml). The kernel says which types those are, and the
-- others are holes for the printer. A term that has no `let`, and one that
-- the kernel does not answer for, is shown as it is.
visible :: Kernel -> Limits -> Env -> UniverseContext -> Term -> IO Term
visible kernel limits env context term
    | not (hasLet term && validUniverses context && wellScopedUniverses count 0 term) = return term
    | otherwise = do
        let output = LV_Named "VisibleOutput"
            goal = foldlNApp (named (if count == 0 then "visible" else "u_visible")) ([natural (toInteger count) | count > 0] ++ [embedUniverseConstraints (universeConstraints context) | count > 0] ++ [embedTerm term, mkLVar output])
        (verdict, _, _) <- run Persistent kernel limits env [term] goal [output]
        return $ case verdict of
            Admitted [answer]
                | Right shown <- recoverTerm answer -> hinted term shown
            _ -> term
    where
        count = length (universeNames context)

visibleEntry :: Kernel -> Limits -> Env -> Entry -> IO Entry
visibleEntry kernel limits env entry = (\terms -> entry { entryDecl = withTerms (entryDecl entry) terms }) <$> mapM (visible kernel limits env (entryUniverses entry)) (declTerms (entryDecl entry))

-- The term is typed in the run that gives its normal form.
normalForm :: Kernel -> Limits -> Env -> Term -> IO (Either Refusal Term)
normalForm = askIn Persistent 2 (\outputs item -> normalGoal item (outputs !! 1) (head outputs))

normalFormWithUniverses :: Kernel -> Limits -> Env -> UniverseContext -> Term -> IO (Either Refusal Term)
normalFormWithUniverses kernel limits env context term
    | context == emptyUniverses = normalForm kernel limits env term
    | otherwise = askUniverses "u_normal" kernel limits env context term

askUniverses :: String -> Kernel -> Limits -> Env -> UniverseContext -> Term -> IO (Either Refusal Term)
askUniverses = askUniversesIn id

askUniversesIn :: (TermNode -> TermNode) -> String -> Kernel -> Limits -> Env -> UniverseContext -> Term -> IO (Either Refusal Term)
askUniversesIn scope predicate kernel limits env context written
    | not (validUniverses context && wellScopedUniverses count 0 written) = return (Left NotClosed)
    | otherwise = do
        consistent <- checkUniversesIn scope Persistent kernel limits env context
        case consistent of
            Left failure -> return (Left failure)
            Right () -> do
                let output = LV_Named "UniverseQueryOutput"
                    goal = foldlNApp (named predicate) [natural (toInteger count), embedUniverseConstraints (universeConstraints context), embedTerm written, mkLVar output]
                (verdict, _, reason) <- run Persistent kernel limits env [written] (scope goal) [output]
                return $ case verdict of
                    Admitted [answer] -> case recoverTerm answer of
                        Right term | wellScopedUniverses count 0 term -> Right term
                        _ -> Left (KernelUndecided "the kernel returned a term outside the query universe context")
                    Admitted _ -> Left (KernelUndecided "the kernel did not return one universe query output")
                    Rejected report -> Left (rejection report reason)
                    Undecided message -> Left (KernelUndecided message)
    where
        count = length (universeNames context)

-- `build outputs item` is the goal about the term `item`, with that many
-- outputs: the first one is the answer.
askIn :: Mode -> Int -> ([LogicVar] -> TermNode -> TermNode) -> Kernel -> Limits -> Env -> Term -> IO (Either Refusal Term)
askIn mode count build kernel limits env written
    | not (wellScoped 0 written) = return (Left NotClosed)
    | otherwise = do
        (verdict, _, reason) <- run mode kernel limits env [written] goal (outputs ++ forms ++ others)
        return $ case verdict of
            Admitted (answer : _) -> either (Left . KernelUndecided) Right (recoverTerm answer)
            Admitted [] -> Left (KernelUndecided "the run did not return one output")
            Rejected report -> Left (rejection report reason)
            Undecided message -> Left (KernelUndecided message)
    where
        outputs = [LV_Named ("Out" ++ show place) | place <- [0 .. count - 1]]
        (goal, forms, others) = staged (\given items -> build given (head items)) outputs [written]
