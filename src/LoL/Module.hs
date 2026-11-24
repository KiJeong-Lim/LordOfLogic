module LoL.Module where

import Control.Concurrent (threadDelay)
import Control.Exception (IOException, bracket, evaluate, mask, onException, try)
import Control.Monad (foldM, unless, when)
import Data.Char (ord)
import Data.List (foldl', intercalate, isPrefixOf, sortOn, stripPrefix)
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import GHC.Clock (getMonotonicTimeNSec)
import GHC.IO.Handle.Lock (FileLockingNotSupported, LockMode (ExclusiveLock), hTryLock)
import LoL.Core (ConstId, Global (..), constantsOf)
import qualified LoL.Core as Core
import LoL.Diagnostic
import qualified LoL.Env as Env
import qualified LoL.Front.Notation as Notation
import qualified LoL.Front.Template as Template
import LoL.Front.Parse (commandChunks, inputLimit, parseChunkIndexed)
import LoL.Front.Syntax
import qualified LoL.Front.Vernac as Vernac
import LoL.Front.Fixity (replayScope, resolveRule, validateArgumentsOwner)
import LoL.Hol.Session (Kernel, Limits)
import qualified LoL.Object as Object
import qualified LoL.Pretty as Pretty
import qualified LoL.Proof.Section as Section
import Numeric (showHex)
import System.Directory (canonicalizePath, copyFileWithMetadata, copyPermissions, createDirectoryIfMissing, doesPathExist, getPermissions, pathIsSymbolicLink, readable, removeFile, renameFile, writable)
import System.FilePath ((</>), addExtension, dropExtension, equalFilePath, isAbsolute, makeRelative, splitDirectories, takeDirectory, takeExtension, takeFileName)
import System.IO (IOMode (AppendMode, ReadMode), hClose, hFileSize, hGetContents, hPutStr, hSetEncoding, openBinaryFile, openTempFile, openTempFileWithDefaultPermissions, utf8, withBinaryFile, withFile)
import System.IO.Error (ioeGetErrorString, isAlreadyInUseError, isDoesNotExistError)

data Failure
    = Failure
        { failurePath       :: FilePath
        , failureSource     :: String
        , failureDiagnostic :: Diagnostic
        }
    deriving (Eq, Show)

data Unit
    = Unit
        { unitName    :: String
        , unitPath    :: FilePath
        , unitSource  :: Maybe String
        , unitImports :: [String]
        , unitLocals  :: [ConstId]
        , unitNames   :: !(Map.Map String Global)
        , unitSyntax  :: !Env.Syntax
        , unitObject  :: Object.ObjectFile
        , unitDigest  :: String
        }
    deriving (Eq, Show)

data Loaded
    = Loaded
        { loadedEnv   :: Env.Env
        , loadedUnits :: Map.Map String Unit
        , loadedOrder :: [String]
        , loadedMain  :: String
        }
    deriving (Show)

emptyLoaded :: String -> Loaded
emptyLoaded name = Loaded Env.emptyEnv Map.empty [] name

origin :: Span
origin = Span (1, 1) (1, 1)

failure :: FilePath -> String -> Span -> String -> String -> Failure
failure path source position code message = Failure path source (Diagnostic position category code message []) where
    category = case code of
        "I-Object" -> "LoL-ObjectError"
        "I-Write" -> "LoL-OutputError"
        "I-Output" -> "LoL-OutputError"
        _ -> "LoL-ImportError"

readSource :: FilePath -> IO (Either IOException String)
readSource = readInput inputLimit

readInput :: Int -> FilePath -> IO (Either IOException String)
readInput limit path = try (withFile path ReadMode readBounded) where
    readBounded handle = do
        hSetEncoding handle utf8
        source <- hGetContents handle
        let prefix = take (limit + 1) source
        count <- evaluate (length prefix)
        if count > limit then ioError (userError ("input exceeds the resource limit of " ++ show limit ++ " characters")) else return prefix

inputFailure :: FilePath -> IOException -> Failure
inputFailure path problem
    | "input exceeds the resource limit" `isPrefixOf` ioeGetErrorString problem = Failure path "" (Diagnostic origin "LoL-KernelUndecided" "R5" (ioeGetErrorString problem) [])
    | isDoesNotExistError problem = failure path "" origin "I-Missing" "File does not exist."
    | otherwise = failure path "" origin "I-Read" (ioeGetErrorString problem)

canonicalNames :: Loaded -> Map.Map Global String
canonicalNames loaded = Map.fromList [(global, name) | unit <- Map.elems (loadedUnits loaded), (name, global) <- Map.toList (unitNames unit)]

-- Source scope contains this module and its direct imports only. Updating
-- one declaration changes just its qualified names and short-name candidates.
-- `scopeAmbiguous` has the ambiguous short names that a constructor has: a
-- pattern must not take one for a variable. The fields are
-- strict: one left unevaluated holds the scope that it was made from, and
-- through it every earlier scope of the module.
data NameScope
    = NameScope
        { scopeCanonical :: !(Map.Map String Global)
        , scopeCandidate :: !(Map.Map String (Set.Set Global))
        , scopeAvailable :: !(Map.Map String Global)
        , scopeAmbiguous :: !(Set.Set String)
        }
    deriving ()

emptyScope :: NameScope
emptyScope = NameScope Map.empty Map.empty Map.empty Set.empty

introduce :: NameScope -> Map.Map String Global -> NameScope
introduce = Map.foldlWithKey' add where
    add scope name global = NameScope canonical candidates available ambiguous where
        canonical = Map.insert name global (scopeCanonical scope)
        alias = short name
        choices = Set.insert global (Map.findWithDefault Set.empty alias (scopeCandidate scope))
        candidates = Map.insert alias choices (scopeCandidate scope)
        available = Map.insert name global (if Set.size choices == 1 then Map.insert alias global (scopeAvailable scope) else Map.delete alias (scopeAvailable scope))
        ambiguous = if Set.size choices > 1 && any constructor (Set.toList choices) then Set.insert alias (scopeAmbiguous scope) else scopeAmbiguous scope
    constructor global = case global of
        GlobalCon {} -> True
        _ -> False

visibleNames :: Map.Map String Global -> Map.Map String Global -> Map.Map String Global
visibleNames _ = scopeAvailable . introduce emptyScope

-- The part of a name after its last dot. It is a tail of the name itself: an
-- alias of a scope shares the text of its qualified name.
short :: String -> String
short name = after name name where
    after rest [] = rest
    after _ ('.' : following) = after following following
    after rest (_ : following) = after rest following

emptySyntax :: Env.Syntax
emptySyntax = Env.Syntax Map.empty Map.empty Nothing Set.empty

moduleGrammar :: String -> Env.Syntax
moduleGrammar name = emptySyntax { Env.syntaxOwner = name }

-- Only an explicit public declaration re-exports a rule. In particular
-- importing a module, or using its notation in a definition, exports none.
recordSyntax :: String -> Bool -> Int -> Int -> [Global] -> Command -> Env.Env -> Env.Syntax -> (Env.Syntax, Env.Syntax)
recordSyntax owner inside imports offset newGlobals command next exported = (live, policies { Env.syntaxSchedule = reversed ++ Env.syntaxSchedule exported }) where
    born = copyPolicies newGlobals live published
    policies = case command of
        CSetArguments _ loc name _ _ | loc == GlobalSyntax || loc == DefaultSyntax && not inside, Just g <- lookupReference (Env.envNames next) name -> copyArgument command g live born
        _ -> born
    (live, published) = recordGrammar owner command next exported
    reversed = [(imports, offset, event) | event <- reverse (implicit ++ steps)]
    implicit = [ArgumentStep False g flags Nothing | g <- newGlobals, Just flags <- [Map.lookup g (Env.syntaxArguments live)], or flags]
    steps = case command of
        CWhere _ _ clauses -> replicate (length clauses) PublicSyntax
        CRocqNotation _ loc _ _ _ _ _ _ _ _ -> [PublicSyntax | loc /= LocalSyntax]
        CSelectNotation _ LocalSyntax _ _ _ | Left op : _ <- Env.syntaxHistory live -> [PrivateScope op]
        CSelectNotation {} -> [PublicSyntax]
        CScope _ LocalSyntax _ | Left op : _ <- Env.syntaxHistory live -> [PrivateScope op]
        CScope {} -> [PublicSyntax]
        CSetArguments _ loc name args options
            | Just g <- lookupReference (Env.envNames next) name
            , not (null args) || clear ->
                [ArgumentStep (loc == LocalSyntax) g (if null args then [] else Map.findWithDefault [] g (Env.syntaxArguments live)) (if clear || scoped then Map.lookup g (Env.syntaxArgScopes live) else Nothing)]
            where
                clear = map nameText options == ["clear", "scopes"]
                scoped = any (\(Argument _ _ _ scopes) -> not (null scopes)) args
        _ -> []

copyPolicies :: [Global] -> Env.Syntax -> Env.Syntax -> Env.Syntax
copyPolicies keys source initial = foldl' copyTo initial keys where
    copyTo target g = target
        { Env.syntaxArguments = field Env.syntaxArguments
        , Env.syntaxArgScopes = field Env.syntaxArgScopes
        , Env.syntaxArgPrefixes = field Env.syntaxArgPrefixes
        , Env.syntaxNever = (if Set.member g (Env.syntaxNever source) then Set.insert else Set.delete) g (Env.syntaxNever target)
        , Env.syntaxProjectionParameters = field Env.syntaxProjectionParameters
        }
        where
            field get = Map.alter (const (Map.lookup g (get source))) g (get target)

-- A public hint about reduction must not publish an earlier Local scope
-- setting on the same constant. Copy only the metadata this command wrote.
copyArgument :: Command -> Global -> Env.Syntax -> Env.Syntax -> Env.Syntax
copyArgument (CArguments _ _ args opts) g source target = target
    { Env.syntaxArguments = select (not (null args)) Env.syntaxArguments
    , Env.syntaxArgPrefixes = select scoped Env.syntaxArgPrefixes
    , Env.syntaxArgScopes = select scoped Env.syntaxArgScopes
    , Env.syntaxNever = select (options `elem` [["clear","simpl"],["simpl","never"]]) Env.syntaxNever
    , Env.syntaxProjectionParameters = select (take 1 options == ["projection"]) Env.syntaxProjectionParameters
    }
    where
        after = copyPolicies [g] source target
        options = map nameText opts
        scoped = options == ["clear","scopes"] || any (\(Argument _ _ _ scopes) -> not (null scopes)) args
        select changed field = field (if changed then after else target)
copyArgument _ _ _ target = target

ownedSyntax :: Set.Set Global -> Env.Syntax -> Env.Syntax -> Env.Syntax
ownedSyntax own active exported = Object.ownedArguments own exported { Env.syntaxDefaults = Env.syntaxDefaults active } exported

recordGrammar :: String -> Command -> Env.Env -> Env.Syntax -> (Env.Syntax, Env.Syntax)
recordGrammar owner command next exported = case command of
    CWhere _ _ clauses -> foldl install (active,exported) (zip clauses recent) where
        recent = reverse [r | Right r <- take (length clauses) (Env.syntaxHistory active)]
        install (syntax,out) (clause,rule) = (syntax { Env.syntaxRuleSites = Map.insert rule loc (Env.syntaxRuleSites syntax) }, Env.registerRule rule loc out)
            where loc = (owner,commandSpan clause)
    CRocqNotation position local _ _ _ _ _ _ _ _
        | Right rule : _ <- Env.syntaxHistory active -> (active { Env.syntaxRuleSites = Map.insert rule site (Env.syntaxRuleSites active), Env.syntaxAliases = Env.syntaxAliases (Env.registerRule rule site active) }, if local == LocalSyntax then exported else publish rule site)
        where site = (owner, position)
    CSelectNotation _ local _ _ _ | Left op : _ <- Env.syntaxHistory active -> (active, if local == LocalSyntax then exported else replayScope op exported)
    CScope _ local _
        | Left op : _ <- Env.syntaxHistory active -> (active, if local == LocalSyntax then exported else replayScope op exported)
    CNotation position local written
        | Right rule <- resolveRule next written ->
            (active { Env.syntaxRuleSites = Map.insert rule site (Env.syntaxRuleSites active) }, if local then exported else publish rule site)
        where site = (owner, position)
    CInfix _ symbol _ _ _ -> (active, exported { Env.syntaxInfix = Map.union (Map.restrictKeys (Env.envInfix next) (Set.singleton (nameText symbol))) (Env.syntaxInfix exported) })
    CNumerals {} -> (active, exported { Env.syntaxNumerals = Env.envNumerals next })
    _ -> (active, exported)
    where
        active = Env.envSyntax next
        publish rule site = Env.registerRule rule site exported

-- This closure is for stored Core and output only, never source resolution.
dependencyModules :: Loaded -> [String] -> [String]
dependencyModules loaded roots = filter (`Set.member` closure Set.empty roots) (loadedOrder loaded) where
    closure seen [] = seen
    closure seen (name : rest)
        | Set.member name seen = closure seen rest
        | otherwise = closure (Set.insert name seen) (maybe [] unitImports (Map.lookup name (loadedUnits loaded)) ++ rest)

-- Default levels are declaration-owned; learned constraints are module-local
-- until imported. Cached siblings contribute no assumptions to this view.
universeView :: Loaded -> [String] -> [ConstId] -> IO Env.Env
universeView loaded imports locals = Env.selectUniverseScope (Set.fromList (locals ++ imported)) (loadedEnv loaded) where
    imported = concat [unitLocals unit | name <- dependencyModules loaded imports, Just unit <- [Map.lookup name (loadedUnits loaded)]]

joinedUniverseView :: Kernel -> Limits -> Loaded -> [String] -> [ConstId] -> IO (Either Env.Refusal Env.Env)
joinedUniverseView kernel limits loaded imports locals = do
    view <- universeView loaded imports locals
    if Env.envStamp view == Env.envStamp (loadedEnv loaded)
        then return (Right view)
        else fmap (view <$) (Env.checkUniverseScope kernel limits view)

dependencyNames :: Loaded -> [String] -> Map.Map String Global
dependencyNames loaded imports = Map.unions [unitNames unit | name <- dependencyModules loaded imports, Just unit <- [Map.lookup name (loadedUnits loaded)]]

-- The implicit status that the modules `roots` and those that they depend on
-- export, each for its own declarations.
importArguments :: Loaded -> [String] -> Env.Syntax -> Env.Syntax
importArguments loaded roots syntax = (Env.withEntryDependencies (tail policies) syntax) { Env.syntaxArgPrefixes = Map.unions (map Env.syntaxArgPrefixes policies), Env.syntaxDefaults = Map.unions (map Env.syntaxDefaults policies), Env.syntaxArgScopes = Map.unions (map Env.syntaxArgScopes policies), Env.syntaxArguments = Map.unions (map Env.syntaxArguments policies), Env.syntaxNever = Set.unions (map Env.syntaxNever policies), Env.syntaxProjectionParameters = Map.unions (map Env.syntaxProjectionParameters policies) } where
    policies = syntax : [unitSyntax unit | name <- dependencyModules loaded roots, Just unit <- [Map.lookup name (loadedUnits loaded)]]

importView :: Loaded -> [String] -> Either (String, String) (Map.Map String Global, Env.Syntax)
importView loaded = foldM include (Map.empty, emptySyntax) where
    include (names, syntax) name = case Map.lookup name (loadedUnits loaded) of
        Nothing -> Right (names, syntax)
        Just unit -> do
            merged <- Object.joinSyntax syntax (unitSyntax unit)
            return (Map.union (unitNames unit) names, merged)

moduleIdentity :: FilePath -> FilePath -> String
moduleIdentity root path = intercalate "." (map identifier (splitDirectories (dropExtension relative))) where
    within = makeRelative root path
    relative = if inside within then within else takeFileName path
    identifier value = if Object.localName value then value else "lol_" ++ concatMap (\char -> showHex (ord char) "_") value

inside :: FilePath -> Bool
inside path = not (isAbsolute path) && all (/= "..") (splitDirectories path)

modulePath :: FilePath -> String -> FilePath
modulePath root name = addExtension (root </> map (\char -> if char == '.' then '/' else char) name) "lol"

commandNames :: Command -> [String]
commandNames command = case command of
    CWhere _ inner _ -> commandNames inner
    CDefinition _ _ name _ _ _ -> [nameText name]
    CAxiom _ name _ -> [nameText name]
    CInductive _ bodies -> concat [[nameText name] ++ [nameText given | Constructor _ given _ <- constructors] | IndBody _ name _ _ constructors <- bodies]
    CFixpoint _ bodies -> [nameText name | FixBody _ name _ _ _ _ <- bodies]
    CUniverses _ _ inner -> commandNames inner
    CTemplate _ inner -> commandNames inner
    CPrimitive _ _ fields inner -> commandNames inner ++ map nameText fields
    COrdinaryRecord _ fields inner -> commandNames inner ++ map (nameText . fst) fields
    CRecordDefinitions _ _ inner definitions -> commandNames inner ++ concat [commandNames accessor | RecordDefinition accessor _ _ _ <- definitions]
    _ -> []

loadSource :: Kernel -> Limits -> FilePath -> FilePath -> Bool -> ([String] -> IO ()) -> IO (Either Failure Loaded)
loadSource = loadSourceFrom Nothing

-- Incremental documents reuse admitted module identities and the existing
-- loader. Imported modules still run with their own lexical name scope.
loadSourceInto :: Loaded -> Kernel -> Limits -> FilePath -> FilePath -> IO (Either Failure Loaded)
loadSourceInto loaded kernel limits root path = loadSourceFrom (Just loaded) kernel limits root path False (const (return ()))

loadSourceFrom :: Maybe Loaded -> Kernel -> Limits -> FilePath -> FilePath -> Bool -> ([String] -> IO ()) -> IO (Either Failure Loaded)
loadSourceFrom initial kernel limits project top explicit emit = do
    paths <- try ((,) <$> canonicalizePath project <*> canonicalizePath top) :: IO (Either IOException (FilePath, FilePath))
    case paths of
        Left message -> return (Left (failure top "" origin "I-Read" (show message)))
        Right (root, path)
            | takeExtension path /= ".lol" -> return (Left (failure top "" origin "I-Format" "a source module must have extension .lol"))
            | Just _ <- initial, not (inside (makeRelative root path)) -> return (Left (failure top "" origin "I-Root" "an imported module resolves outside the project root"))
            | otherwise -> do
                result <- visit root (maybe [] (\loaded -> [loadedMain loaded]) initial) (maybe True (const False) initial) (moduleIdentity root path) path (maybe (emptyLoaded (moduleIdentity root path)) id initial)
                displayed <- case result of
                    Right loaded
                        | explicit -> case explicitModule loaded of
                            Left message -> return (Left (failure path "" origin "I-Output" message))
                            Right messages -> emit messages >> return result
                    _ -> return result
                return (case displayed of
                    Left problem
                        | failurePath problem == path -> Left problem { failurePath = top }
                    _ -> displayed)
    where
        visit root active output name path loaded
            | name `elem` active = return (Left (failure path "" origin "I-Cycle" ("import cycle: " ++ intercalate " -> " (reverse (name : active)))))
            | Just old <- Map.lookup name (loadedUnits loaded) = return (if unitPath old == path then Right loaded else Left (failure path "" origin "I-ModuleName" ("two files have module name " ++ name)))
            | otherwise = do
                input <- readSource path
                case input of
                    Left message -> return (Left (inputFailure path message))
                    Right source -> do
                        env <- universeView loaded [] []
                        commands root (name : active) output name path source [] [] Map.empty emptyScope (moduleGrammar name) (moduleGrammar name) loaded { loadedEnv = env } (map reader (commandChunks source))
        commands _ _ _ name path source events localRev own scope syntax exported loaded [] = do
            let env = Env.withAmbiguous Set.empty (Env.withSyntax syntax (Env.withNames (scopeAvailable scope) (loadedEnv loaded)))
                imports = map fst events
                locals = reverse localRev
                canonical = Map.mapKeys ((name ++ ".") ++) own
                names = Map.union (Map.fromList [(global, given) | (given, global) <- Map.toList canonical]) (canonicalNames loaded)
                public = ownedSyntax (Set.fromList (Map.elems own)) syntax exported
                pins = mapM (\dependency -> maybe (Left ("missing captured dependency: " ++ dependency)) (\unit -> Right (dependency, unitDigest unit)) (Map.lookup dependency (loadedUnits loaded))) imports
            case pins >>= \dependencies -> Object.captureNamedObject name dependencies names locals (Env.withSyntax public env) of
                Left message -> return (Left (failure path source origin "I-Object" message))
                Right stored -> do
                    let object = Object.withImportOffsets (map snd events) stored
                        unit = Unit name path (Just source) imports locals canonical public object (Object.fingerprint object)
                    return (Right loaded { loadedEnv = env, loadedUnits = Map.insert name unit (loadedUnits loaded), loadedOrder = loadedOrder loaded ++ [name] })
        commands root active output name path source imports localRev own scope syntax exported loaded (readChunk : later) = case readChunk syntax of
            Left problem -> return (Left (Failure path source (fromFrontError problem)))
            Right [] -> commands root active output name path source imports localRev own scope syntax exported loaded later
            Right (command : extra) -> execute root active output name path source imports localRev own scope syntax exported loaded command (map (const . Right . pure) extra ++ later)
        reader chunk syntax = parseChunkIndexed (Env.syntaxReader syntax) chunk
        execute root active output name path source imports localRev own scope syntax exported loaded command rest = case command of
            CImport position imported
                | nameText imported `elem` map fst imports -> return (Left (failure path source position "I-Duplicate" ("module imported twice in this file: " ++ nameText imported)))
                | not (Object.qualified (nameText imported)) -> return (Left (failure path source position "I-Name" "invalid import module name"))
                | nameText imported `elem` active -> return (Left (failure path source position "I-Cycle" ("import cycle: " ++ intercalate " -> " (reverse active ++ [nameText imported]))))
                | otherwise -> do
                    resolved <- try (canonicalizePath (modulePath root (nameText imported))) :: IO (Either IOException FilePath)
                    case resolved of
                        Left message -> return (Left (failure path source position "I-Missing" (show message)))
                        Right requested
                            | not (inside (makeRelative root requested)) -> return (Left (failure path source position "I-Root" "an imported module resolves outside the project root"))
                            | otherwise -> do
                                child <- visit root active False (nameText imported) requested loaded
                                case child of
                                    Left problem -> return (Left problem)
                                    Right next -> case Map.lookup (nameText imported) (loadedUnits next) of
                                        Nothing -> return (Left (failure path source position "I-Import" "the imported module produced no environment"))
                                        Just unit -> case Object.joinSyntax syntax (unitSyntax unit) of
                                            Left (code, message) -> return (Left (Failure path source (Diagnostic position "LoL-ScopeError" code message [])))
                                            -- A notation of the import may name a constant of a module that this
                                            -- file does not import. That constant has the implicit status that its
                                            -- own module exports, whatever was loaded before this file.
                                            Right merged -> do
                                                let dependencies = imports ++ [(nameText imported, length localRev)]
                                                joined <- joinedUniverseView kernel limits next (map fst dependencies) localRev
                                                case joined of
                                                    Left rejected -> return (Left (Failure path source (Vernac.refusalIn (loadedEnv next) position rejected)))
                                                    Right env -> commands root active output name path source dependencies localRev own (introduce scope (unitNames unit)) (importArguments next [nameText imported] merged) exported next { loadedEnv = env } rest
            _ -> do
                let env = Env.withAmbiguous (scopeAmbiguous scope) (Env.withSyntax syntax (Env.withNames (scopeAvailable scope) (loadedEnv loaded)))
                    newNames = commandNames command
                    display current = Env.withNames (Map.union (Env.envNames current) (Map.union (Map.mapKeys ((name ++ ".") ++) own) (Map.fromList [(given, global) | (global, given) <- Map.toList (canonicalNames loaded)]))) current
                    duplicates = filter (`Map.member` own) newNames ++ [given | (given, count) <- Map.toList (Map.fromListWith (+) [(given, 1 :: Int) | given <- newNames]), count > 1]
                    declare engine budget current given universes declaration = Env.declareWithUniverses engine budget (Env.withNames (foldr Map.delete (Env.envNames current) (map fst (Env.declGlobals (Env.envFresh current) given declaration))) current) given universes declaration
                    checked = case duplicates of
                        given : _ -> Left (Vernac.refusalIn env (commandSpan command) (Env.DuplicateName given))
                        [] -> validateArgumentsOwner (Map.elems own) env command
                result <- either (return . Left) (const (Vernac.executeWithDisplay display declare kernel limits env command)) checked
                case result of
                    Left diagnostic -> return (Left (Failure path source (ambiguous (scopeCanonical scope) diagnostic)))
                    Right (next, rendered) -> do
                        let identities = [Env.envFresh env .. Env.envFresh next - 1]
                            globals = [(given, global) | identity <- identities, Just entry <- [Map.lookup identity (Env.envDecls next)], (given, global) <- Env.declGlobals identity (Env.entryName entry) (Env.entryDecl entry)]
                            own' = Map.union (Map.fromList globals) own
                            scope' = introduce scope (Map.fromList [(name ++ "." ++ given, global) | (given, global) <- globals])
                            (activeSyntax, exported') = recordSyntax name False (length imports) (length localRev + length identities) (map snd globals) command next exported
                        when (output && not explicit) (emit rendered)
                        commands root active output name path source imports (reverse identities ++ localRev) own' scope' activeSyntax exported' loaded { loadedEnv = next } rest
ambiguous :: Map.Map String Global -> Diagnostic -> Diagnostic
ambiguous canonical diagnostic
    | diagnosticCode diagnostic == "H-Name", "unknown name: " `isPrefixOf` diagnosticText diagnostic =
        if length choices > 1 then diagnostic { diagnosticText = "ambiguous name: " ++ given ++ "; use " ++ intercalate " or " choices } else diagnostic
    | otherwise = diagnostic
    where
        given = drop (length ("unknown name: " :: String)) (diagnosticText diagnostic)
        choices = [name | (name, _) <- Map.toList canonical, short name == given]

-- The explicit text of the main module: its imports and its declarations.
-- It imports what the source imports and, after those, each module that the
-- source does not import and whose declaration a printed term mentions, such
-- as the inferred type of a value of an imported module. A module that the
-- text does not need is not imported, so its notations cannot conflict
-- there. The names are those that the text has in scope when it is read
-- again: a short name that two of its modules give a constructor is no name
-- for a binder.
explicitModule :: Loaded -> Either String [String]
explicitModule = printedModule Pretty.declaration

-- The same with every theorem as its statement alone (Pretty.statement):
-- what the module says, by the names and the terms that the kernel admitted.
statedModule :: Loaded -> Either String [String]
statedModule = printedModuleWith False statedTerms Pretty.statement where
    statedTerms declaration = case declaration of
        Env.Theorem {} -> Env.declTypes declaration
        _ -> Env.declTerms declaration

printedModule :: (Env.Env -> ConstId -> Env.Entry -> Either String String) -> Loaded -> Either String [String]
printedModule = printedModuleWith True Env.declTerms

printedModuleWith :: Bool -> (Env.Decl -> [Core.Term]) -> (Env.Env -> ConstId -> Env.Entry -> Either String String) -> Loaded -> Either String [String]
printedModuleWith fullText printedTerms printer loaded = do
    unit <- maybe (Left "missing main module") Right (Map.lookup (loadedMain loaded) (loadedUnits loaded))
    entries <- mapM (\identity -> maybe (Left "missing admitted declaration") (Right . (,) identity) (Map.lookup identity (Env.envDecls (loadedEnv loaded)))) (unitLocals unit)
    (imports, chunks) <- foldM (section unit) ([], []) (Object.importGroups (unitObject unit) entries)
    (env, imported) <- printingEnv unit imports
    let syntax = unitSyntax unit
        timed = fullText && Object.scheduled syntax && not (null (Env.syntaxSchedule syntax))
        metadata (identity, entry) = concatMap policy (Env.declGlobals identity (Env.entryName entry) (Env.entryDecl entry)) where
            marked = case Env.entryDecl entry of
                Env.Inductive _ families -> any (\family -> Env.familyTemplate family || Env.familyRecord family /= Nothing) families
                _ -> False
            policy (_, global)
                | not (fullText || marked || Map.member global (Env.syntaxProjectionParameters syntax)) = []
            policy (name, global) = concat
                [ [header ++ " : projection " ++ show count ++ "." | Just count <- [Map.lookup global (Env.syntaxProjectionParameters syntax)]]
                , [unwords (header : zipWith argument [0 :: Int ..] flags) ++ "." | Just flags <- [Map.lookup global (Env.syntaxArguments syntax)], or flags, not timed]
                , [header ++ " : simpl never." | Set.member global (Env.syntaxNever syntax)]
                ]
                where
                    header = "Arguments " ++ maybe name id (Pretty.globalName env global)
                    argument index implicit = if implicit then "{" ++ label ++ "}" else label where
                        label = "x" ++ show index
    let blocks = reverse chunks
        placed = staged 0 0 blocks
        schedule = zip [0 :: Int ..] (reverse (Env.syntaxSchedule syntax))
        views = entryViews loaded placed schedule (reverse (Env.syntaxHistory syntax))
        publicViews = if timed then [Just (Map.findWithDefault Map.empty k views) | (k,(_,_,PublicSyntax)) <- schedule] else repeat Nothing
    grammar <- if fullText then do
        _ <- checkGrammar (Object.joinSyntax imported syntax)
        publicGrammar publicViews env syntax
    else Right []
    let boundArguments = [unwords ("Arguments" : label : (if all null slots then [":", "clear", "scopes"] else zipWith decorate flags slots)) ++ "." | (g, slots) <- Map.toAscList (Env.syntaxArgScopes syntax), Just label <- [Pretty.globalName env g], let flags = zip [0 :: Int ..] (Map.findWithDefault [] g (Env.syntaxArguments syntax) ++ repeat False)]
        decorate (index, implicit) scopes = (if implicit then "{" ++ label ++ "}" else label) ++ concatMap ("%_" ++) scopes where
            label = "x" ++ show index
    let originals = concat [concat importsHere ++ hidden ++ decls | (importsHere, hidden, decls) <- blocks]
    if timed then do
        let (legacy, public) = splitAt (length grammar - length (Env.syntaxHistory syntax)) grammar
        steps <- sourceSteps env views public schedule
        Right (map snd (sortOn fst (steps ++ placed)) ++ concatMap metadata entries ++ legacy)
    else return (originals ++ concatMap metadata entries ++ grammar ++ if fullText then boundArguments else [])
    where
        section unit (prior, chunks) (added, entries) = do
            let mentioned = Set.unions [Set.union (Core.constraintOwners (Env.entryUniverses entry)) (Set.unions (map constantsOf (printedTerms (Env.entryDecl entry)))) | (_, entry) <- entries]
                hidden = [name | name <- loadedOrder loaded, name /= unitName unit, name `notElem` (prior ++ added), Just other <- [Map.lookup name (loadedUnits loaded)], any (`Set.member` mentioned) (unitLocals other)]
                fresh = filter (`notElem` prior) added ++ hidden
                imports = prior ++ fresh
            (env, _) <- printingEnv unit imports
            let reserved = Notation.binderWords (Env.syntaxReader (Env.envSyntax env))
                declarationsHere = [name | (identity, entry) <- entries, (name, _) <- Env.declGlobals identity (Env.entryName entry) (Env.entryDecl entry)]
            case filter (`Set.member` reserved) declarationsHere of
                name : _ -> Left ("H-Notation: an import needed by explicit output reserves the declaration name " ++ quoted name)
                [] -> Right ()
            let sectionPolicies = Map.fromList [(g, (n, fs, slots)) | fullText, (_, _, SectionStep g n fs slots) <- Env.syntaxSchedule (unitSyntax unit)]
            declarations <- mapM (\(c, entry) -> Section.explicit printer env c entry sectionPolicies) entries
            let importLine n = "Import " ++ n ++ "."
            return (imports, ([[importLine n | n `notElem` prior] | n <- added], map importLine hidden, declarations) : chunks)
        staged _ _ [] = []
        staged i d ((importsHere, hidden, decls) : later) = importsAt ++ hiddenAt ++ declsAt ++ staged j (d + length decls) later where
            importsAt = [((d, n, 2), line) | (n, lines) <- zip [i..] importsHere, line <- lines]
            j = i + length importsHere
            hiddenAt = [((d, j, 0), line) | line <- hidden]
            declsAt = [((n, j, 2), line) | (n, line) <- zip [d..] decls]
        sourceSteps _ _ [] [] = Right []
        sourceSteps env views public ((index,(i, d, event)) : more) = case event of
            PublicSyntax | line : rest <- public -> add line rest
            PrivateScope op -> do
                lines <- publicGrammar [Map.lookup index views] env (replayScope op (moduleGrammar (loadedMain loaded)))
                case lines of
                    [line] -> add ("Local " ++ line) public
                    _ -> Left "invalid private scope in explicit module schedule"
            ScopeLookup global -> do
                label <- maybe (Left "a scope lookup has no printable name") Right (Pretty.globalName env global)
                add ("Print " ++ label ++ ".") public
            SectionStep {} -> sourceSteps env views public more
            ArgumentStep local global flags policy -> do
                label <- maybe (Left "a scheduled Arguments target has no printable name") Right (Pretty.globalName env global)
                let scopes = maybe [] id policy
                    count = max (length flags) (length scopes)
                    specs = take count (zipWith decorate (zip [0 :: Int ..] (flags ++ repeat False)) (scopes ++ repeat []))
                    suffix
                        | Just sets <- policy, all null sets = " : clear scopes"
                        | length scopes > length flags = " : extra scopes"
                        | otherwise = ""
                    decorate (n, implicit) keys = (if implicit then "{" ++ x ++ "}" else x) ++ concatMap ("%_" ++) keys where x = "x" ++ show n
                add ((if local then "Local " else "") ++ unwords ("Arguments" : label : specs) ++ suffix ++ ".") public
            _ -> Left "invalid public grammar order in explicit module schedule"
            where
                add line rest = (((d, i, 1 :: Int), line) :) <$> sourceSteps env views rest more
        sourceSteps _ _ _ _ = Left "missing public grammar step in explicit module schedule"
        checkGrammar = either (\(code, message) -> Left (code ++ ": explicit output needs imports with conflicting notation; " ++ message)) Right
        printingEnv unit imports = do
            (_, visibleSyntax) <- checkGrammar (importView loaded imports)
            let view = introduce emptyScope (Map.unions [unitNames found | name <- imports ++ [unitName unit], Just found <- [Map.lookup name (loadedUnits loaded)]])
                final = loadedEnv loaded
                syntax = Env.withRulesFrom visibleSyntax (Env.envSyntax final)
                -- Keep printed binders stable if a later import introduces
                -- a constructor with their name. Only active imports can
                -- resolve a global or contribute notation at this point.
                constructors = Set.fromList [short given | name <- unitImports unit, Just found <- [Map.lookup name (loadedUnits loaded)], (given, GlobalCon {}) <- Map.toList (unitNames found)]
            return (Env.withSyntax syntax (Env.withAmbiguous (Set.union constructors (scopeAmbiguous view)) (Env.withNames (scopeAvailable view) final)), visibleSyntax)

-- Follow the same order as the emitted imports and syntax commands, including
-- imports inserted for inferred types. Shorten a local entry only while its
-- declaration is the current meaning of that short name in the replay text.
entryViews :: Loaded -> [((Int,Int,Int),String)] -> [(Int,(Int,Int,SyntaxStep Global))] -> [Either (ScopeAction Global) (SyntaxRule Global)] -> Map.Map Int (Map.Map String String)
entryViews loaded placed schedule history = snd (foldl' visit (Map.empty, Map.empty) (sortOn fst (imports ++ steps history schedule))) where
    imports = [(key, (Nothing, paths)) | (key, line) <- placed, Just file <- [stripPrefix "Import " line], not (null file), last file == '.', Just unit <- [Map.lookup (init file) (loadedUnits loaded)], let paths = [n | Left (DeclareCustomEntry n) <- reverse (Env.syntaxHistory (unitSyntax unit))]]
    steps _ [] = []
    steps (rule:rules) ((k,(i,d,PublicSyntax)):more) = ((d,i,1), (Just k, paths)) : steps rules more where
        paths = case rule of { Left (DeclareCustomEntry n) -> [n]; _ -> [] }
    steps rules ((k,(i,d,PrivateScope op)):more) = ((d,i,1), (Just k, paths)) : steps rules more where
        paths = case op of { DeclareCustomEntry n -> [n]; _ -> [] }
    steps rules (_:more) = steps rules more
    visit (visible, snapshots) (_, (index, paths)) = (foldl' (\scope n -> Map.insert (short n) n scope) visible paths, maybe snapshots (\k -> Map.insert k visible snapshots) index)

-- Declarations have already been expanded. Restore the module's public reader
-- only at the end, so replacing a module preserves its clients' syntax.
publicGrammar :: [Maybe (Map.Map String String)] -> Env.Env -> Env.Syntax -> Either String [String]
publicGrammar publicViews env syntax = do
    operators <- mapM infixLine (Map.toAscList (Env.syntaxInfix syntax))
    numerals <- case Env.syntaxNumerals syntax of
        Nothing -> Right []
        Just (zero, successor) -> do
            z <- reference zero
            s <- reference successor
            return [unwords ["Numerals", z, s ++ "."]]
    rules <- mapM (notation Nothing) [r | r@(SyntaxRule _ _ _ target) <- Env.syntaxRules syntax, case target of { RocqTarget {} -> False; _ -> True }]
    v1 <- sequence [either (scopeLine view) (notation view) item | (view,item) <- zip publicViews (reverse (Env.syntaxHistory syntax))]
    return (operators ++ numerals ++ rules ++ v1)
    where
        scopeLine _ (BindScope name placement classes) = do
            labels <- mapM className classes
            let prefix = case placement of { ReplaceScopes -> ""; AddTop -> "#[add_top] "; AddBottom -> "#[add_bottom] " }
            return (prefix ++ "Bind Scope " ++ name ++ " with " ++ unwords labels ++ ".")
        scopeLine view (ToggleInterpretation setting@(Activation _ _ _ selector _ _) params query) = do
            body <- traverse reference query
            let binders = case selector of { AliasSelector _ -> params; _ -> [] }
            return (activationText (binders ++ [":=", "(" ++ Template.expression body ++ ")"]) (entrySetting view setting))
        scopeLine view action = Right $ case action of
            ToggleNotation setting -> activationText [] (entrySetting view setting)
            DeclareCustomEntry n -> "Declare Custom Entry " ++ short n ++ "."
            DeclareScope n -> "Declare Scope " ++ n ++ "."
            DelimitScope n key -> unwords ["Delimit Scope",n,"with",key ++ "."]
            OpenScope n -> "Open Scope " ++ n ++ "."
            UndelimitScope n -> "Undelimit Scope " ++ n ++ "."
            CloseScope n -> "Close Scope " ++ n ++ "."
        className SortClass = Right "Sortclass"
        className FunClass = Right "Funclass"
        className (ReferenceClass g) = reference g
        reference global = maybe (Left "a public notation target has no printable name") Right (Pretty.globalName env global)
        options level assoc = " (at level " ++ show level ++ ", " ++ assoc ++ " associativity)."
        -- The lexer reads a notation pattern literally, including backslashes.
        literal word = '"' : word ++ "\""
        infixLine (symbol, (global, level, assoc)) = do
            name <- reference global
            return ("Infix " ++ literal symbol ++ " := " ++ name ++ options level assoc)
        entrySetting view (Activation on direction many selector sc table) = Activation on direction many selector sc (fmap (entryText view) table)
        entryText view n
            | n == Env.syntaxOwner syntax ++ "." ++ short n
            , maybe True ((== Just n) . Map.lookup (short n)) view = short n
            | otherwise = n
        notation view (SyntaxRule parts level assoc target) = case target of
            RocqTarget {} -> Template.render reference (SyntaxRule (map (mapRuleEntry (entryText view)) parts) level assoc target)
            TacticTarget name -> Right ("Tactic " ++ headText ++ name ++ ".")
            TermTarget global -> do
                name <- reference global
                return (headText ++ name ++ options level assoc)
            where
                headText = "Notation " ++ literal (unwords (map part parts)) ++ " := "
        part (Literal word) = word
        part TermSlot = "$term"
        part NameSlot = "$name"
        part (ScopedSlot n) = "$body" ++ show n
        part TacticSlot = "$tactic"

-- Each module has its own object. The entry file pins its direct imports;
-- shared dependency files are immutable and addressed by canonical content.
objectPath :: FilePath -> String -> FilePath
objectPath directory digest = directory </> ".lolo" </> digest ++ ".lolo"

readObject :: FilePath -> IO (Either Failure Object.ObjectFile)
readObject path = do
    input <- readInput Object.objectTextLimit path
    return $ case input of
        Left message -> Left (inputFailure path message)
        Right source -> either (Left . failure path "" origin "I-Object") Right (Object.decodeObject source)

loadObject :: Kernel -> Limits -> FilePath -> IO (Either Failure Loaded)
loadObject kernel limits path = do
    resolved <- try (canonicalizePath path) :: IO (Either IOException FilePath)
    case resolved of
        Left message -> return (Left (inputFailure path message))
        Right actual -> do
            first <- readObject actual
            case first of
                Left problem -> return (Left problem)
                Right object -> visit (takeDirectory actual) [] actual object (Object.fingerprint object) (emptyLoaded (Object.objectModule object))
    where
        dependency _ _ (Left problem) _ = return (Left problem)
        dependency directory active (Right loaded) (name, digest)
            | name `elem` active = return (Left (failure (objectPath directory digest) "" origin "I-Cycle" ("object import cycle: " ++ intercalate " -> " (reverse active ++ [name]))))
            | Just unit <- Map.lookup name (loadedUnits loaded) = return (if unitDigest unit == digest then Right loaded else Left (failure (unitPath unit) "" origin "I-VersionConflict" ("two different object versions of module " ++ name)))
            | otherwise = do
                let requested = objectPath directory digest
                resolved <- try (canonicalizePath requested) :: IO (Either IOException FilePath)
                case resolved of
                    Left message -> return (Left (inputFailure requested message))
                    Right actual
                        | not (inside (makeRelative directory actual)) -> return (Left (failure requested "" origin "I-Root" "an object dependency resolves outside the object directory"))
                        | otherwise -> do
                            input <- readObject actual
                            case input of
                                Left problem -> return (Left problem)
                                Right object
                                    | Object.objectModule object /= name -> return (Left (failure actual "" origin "I-ModuleName" ("expected object module " ++ name ++ ", found " ++ Object.objectModule object)))
                                    | Object.fingerprint object /= digest -> return (Left (failure actual "" origin "I-Hash" ("object content does not match the dependency hash of " ++ name)))
                                    | otherwise -> visit directory active actual object digest loaded
        visit directory active actual object digest loaded = do
            dependencies <- foldM (dependency directory (Object.objectModule object : active)) (Right loaded) (Object.objectImports object)
            case dependencies of
                Left problem -> return (Left problem)
                Right current -> replayImport kernel limits actual Nothing object digest current

-- Both an explicit .lolo and a cached source import admit every declaration
-- under the actual dependency environments and lexical import positions.
replayImport :: Kernel -> Limits -> FilePath -> Maybe String -> Object.ObjectFile -> String -> Loaded -> IO (Either Failure Loaded)
replayImport kernel limits actual source object digest current = do
    let imports = map fst (Object.objectImports object)
    case importView current imports of
        Left (_, message) -> return (Left (failure actual (maybe "" id source) origin "I-Object" message))
        Right (canonical, direct) -> do
            let grammar = importArguments current imports direct
            view <- universeView current [] []
            replay imports canonical grammar view
    where
        replay imports canonical grammar view = do
            let owner = Object.objectModule object
                env = Env.withSyntax (moduleGrammar owner) (Env.withNames Map.empty view)
                activate previous [] = return (Right previous)
                activate previous added@(first : _) = do
                    let roots = takeWhile (/= first) imports ++ added
                        locals = [Env.envFresh env .. Env.envFresh previous - 1]
                    joined <- joinedUniverseView kernel limits current { loadedEnv = previous } roots locals
                    return $ case joined of
                        Left refusal -> Left (Object.ObjectRejected ("Import " ++ last added) refusal previous)
                        Right scoped -> case importView current roots of
                            Left (_, message) -> Left (Object.ObjectFormat message)
                            Right (_, active) -> Right (Env.withSyntax (importArguments current roots active { Env.syntaxOwner = owner }) (Env.withNames (Map.union (dependencyNames current roots) (Env.envNames previous)) scoped))
            replayed <- Object.replayGroups kernel limits env object activate
            return $ case replayed of
                Left (Object.ObjectFormat message) -> Left (failure actual "" origin "I-Object" message)
                Left (Object.ObjectRejected name rejected context) -> Left (Failure actual "" (annotated name (Vernac.refusalIn context origin rejected)))
                Right next -> do
                    let identities = [Env.envFresh env .. Env.envFresh next - 1]
                        own = Map.fromList [(given, global) | identity <- identities, Just entry <- [Map.lookup identity (Env.envDecls next)], (given, global) <- Env.declGlobals identity (Env.entryName entry) (Env.entryDecl entry)]
                        ownCanonical = Map.mapKeys ((Object.objectModule object ++ ".") ++) own
                        visible = Env.withNames (visibleNames own (Map.union ownCanonical canonical)) next
                    exported <- either (Left . failure actual "" origin "I-Object") Right (Object.loadSyntaxWith (Object.objectModule object) grammar (Map.union ownCanonical canonical) (Object.objectSyntax object))
                    let unit = Unit (Object.objectModule object) actual source imports identities ownCanonical exported object digest
                    Right current { loadedEnv = visible, loadedUnits = Map.insert (unitName unit) unit (loadedUnits current), loadedOrder = loadedOrder current ++ [unitName unit] }
        annotated name diagnostic = diagnostic { diagnosticBody = ("object declaration: " ++ name) : diagnosticBody diagnostic }

-- Validate the complete graph before publishing anything. This checks file
-- structure and pins; only loadObject performs kernel admission on reading.
objectGraph :: Loaded -> Either String [(Object.ObjectFile, String)]
objectGraph loaded = do
    table <- foldM entry Map.empty (loadedOrder loaded)
    reachable <- closure table Set.empty (loadedMain loaded)
    unless (Map.keysSet table == Map.keysSet (loadedUnits loaded) && reachable == Map.keysSet table) (Left "the object graph does not match the main module's dependency closure")
    mapM (\name -> maybe (Left ("missing object module: " ++ name)) Right (Map.lookup name table)) (loadedOrder loaded)
    where
        entry table name = do
            unless (Map.notMember name table) (Left ("repeated object module: " ++ name))
            unit <- maybe (Left ("missing object module: " ++ name)) Right (Map.lookup name (loadedUnits loaded))
            object <- Object.decodeObject (Object.encodeObject (unitObject unit))
            unless (Object.objectModule object == name && unitName unit == name && map fst (Object.objectImports object) == unitImports unit) (Left "the object's name or direct imports do not match its module")
            mapM_ (\(dependency, expected) -> case Map.lookup dependency table of
                Nothing -> Left ("object dependency is absent or out of order: " ++ dependency)
                Just (_, actual) -> unless (actual == expected) (Left ("object dependency hash changed: " ++ dependency))) (Object.objectImports object)
            return (Map.insert name (object, Object.fingerprint object) table)
        closure table seen name
            | Set.member name seen = Right seen
            | otherwise = case Map.lookup name table of
                Nothing -> Left ("missing object module: " ++ name)
                Just (object, _) -> foldM (closure table) (Set.insert name seen) (map fst (Object.objectImports object))

writeObject :: FilePath -> Loaded -> IO (Either Failure ())
writeObject path = writeProducts Nothing (Just path)

-- Materialize every requested product beside its destination before changing
-- any destination. Existing dependency objects must match their content pin.
writeProducts :: Maybe (FilePath, [(FilePath, String)]) -> Maybe FilePath -> Loaded -> IO (Either Failure ())
writeProducts rocq artifact loaded = case traverse (const (objectGraph loaded)) artifact of
    Left message -> return (Left (failure location "" origin "I-Object" message))
    Right objects -> do
        published <- try $ do
            exports <- maybe (return []) rocqFiles rocq
            saved <- case (artifact, objects) of
                (Just path, Just entries) -> objectFiles path entries
                _ -> return []
            publishFiles ([(path, source, TextFile) | (path, source) <- exports] ++ saved)
        return (either (Left . failure location "" origin "I-Write" . show) Right (published :: Either IOException ()))
    where
        location = maybe (maybe "" fst rocq) id artifact
        rocqFiles (base, modules) = do
            directory <- canonicalizePath base
            mapM (\(name, source) -> (,) <$> confined directory (directory </> name) <*> pure source) modules
        objectFiles path entries = do
            directory <- canonicalizePath (takeDirectory path)
            dependencies <- mapM (dependency directory) [(object, digest) | (object, digest) <- entries, Object.objectModule object /= loadedMain loaded]
            case [(object, digest) | (object, digest) <- entries, Object.objectModule object == loadedMain loaded] of
                [(object, digest)] -> do
                    let name = dropExtension (takeFileName path)
                        store = ".lolo" `elem` [takeFileName directory, takeFileName (takeDirectory path)]
                    entry <- if store && takeExtension path == ".lolo" && Object.validFingerprint name then do
                        unless (digest == name) (ioError (userError ("entry content does not match the immutable object path: " ++ path)))
                        immutable path object
                        else return [(path, Object.encodeObject object, EntryFile)]
                    return (concat dependencies ++ entry)
                _ -> ioError (userError "the object graph has no unique main module")
        dependency directory (object, digest) = confined directory (objectPath directory digest) >>= \path -> immutable path object
        immutable path object = do
            exists <- doesPathExist path
            if exists then do
                _ <- withBinaryFile path ReadMode hFileSize
                previous <- readObject path
                unless (previous == Right object) (ioError (userError ("an immutable dependency object has different content: " ++ path)))
                return []
            else return [(path, Object.encodeObject object, SharedFile)]
        confined directory path = do
            actual <- canonicalizePath path
            unless (inside (makeRelative directory actual)) (ioError (userError ("output resolves outside its directory: " ++ path)))
            return path

publishText :: FilePath -> String -> IO ()
publishText path source = publishFiles [(path, source, TextFile)]

data OutputKind = TextFile | EntryFile | SharedFile deriving (Eq)

-- Text output follows the creation mask and preserves existing permissions.
-- Newly emitted object files are private, as in the original object store.
publishFiles :: [(FilePath, String, OutputKind)] -> IO ()
publishFiles targets = do
    paths <- mapM (\(path, _, _) -> canonicalizePath path) targets
    let names = Set.fromList paths
    unless (length paths == Set.size names && all (separate names) paths) (ioError (userError "requested output paths overlap"))
    when (any (elem publicationLock . splitDirectories) paths) (ioError (userError "an output path uses the reserved publication lock name"))
    -- The entry object is installed last. A plain transcript has only one
    -- destination. Only Rocq files can be replaced and then rolled back.
    -- A single writer of a .v takes part in that same coordination.
    let directories = Set.fromList [takeDirectory path | (path, (_, _, kind)) <- zip paths targets, kind /= SharedFile, equalFilePath (takeExtension path) ".v"]
    withPublicationLocks (Set.toAscList directories) (staged targets [])
    where
        separate names path = parent == path || (Set.notMember parent names && separate names parent) where
            parent = takeDirectory path
        staged [] files = install (reverse files)
        staged ((path, source, kind) : rest) files = do
            createDirectoryIfMissing True (takeDirectory path)
            rejectLink path
            exists <- doesPathExist path
            when exists $ do
                permissions <- getPermissions path
                unless (writable permissions) (ioError (userError ("output needs a writable file: " ++ path)))
                _ <- withBinaryFile path (if readable permissions then ReadMode else AppendMode) hFileSize
                return ()
            let open = if kind == TextFile then openTempFileWithDefaultPermissions else openTempFile
            bracket (open (takeDirectory path) (takeFileName path ++ ".tmp")) cleanup $ \(temporary, handle) -> do
                when (kind == TextFile && exists) (copyPermissions path temporary)
                hSetEncoding handle utf8
                hPutStr handle source
                hClose handle
                staged rest ((temporary, path, exists, kind) : files)
        cleanup (temporary, handle) = do
            _ <- try (hClose handle) :: IO (Either IOException ())
            discard temporary
        discard path = do
            _ <- try (removeFile path) :: IO (Either IOException ())
            return ()
        install [] = return ()
        install [(temporary, path, _, _)] = renameFile temporary path
        -- Other entry files can already pin this exact object. Its lifetime
        -- is independent of the transaction that first populated the cache.
        install ((temporary, path, _, SharedFile) : rest) = renameFile temporary path >> install rest
        install ((temporary, path, exists, _) : rest) = mask $ \restore -> do
            if exists then do
                (original, handle) <- openTempFile (takeDirectory path) (takeFileName path ++ ".backup")
                (hClose handle >> restore (copyFileWithMetadata path original) >> renameFile temporary path) `onException` discard original
                restore (install rest) `onException` renameFile original path
                discard original
            else do
                renameFile temporary path
                restore (install rest) `onException` removeFile path

-- Keep the inode: removing a lock file could split existing and new waiters
-- across two locks. Closing the handle (also on process death) drops the lock.
publicationLock :: FilePath
publicationLock = ".lol-publish.lock"

rejectLink :: FilePath -> IO ()
rejectLink path = do
    linked <- try (pathIsSymbolicLink path)
    case linked of
        Left problem -> unless (isDoesNotExistError problem) (ioError problem)
        Right True -> ioError (userError ("output path is a symbolic link: " ++ path))
        Right False -> return ()

-- Acquire canonical parent directories in one order, before inspecting or
-- staging mutable files. One deadline covers acquisition of the whole set.
withPublicationLocks :: [FilePath] -> IO a -> IO a
withPublicationLocks [] action = action
withPublicationLocks directories action = do
    start <- getMonotonicTimeNSec
    acquire (start + 30000000000) directories
    where
        acquire _ [] = action
        acquire deadline (directory : rest) = do
            createDirectoryIfMissing True directory
            let path = directory </> publicationLock
            rejectLink path
            bracket (open deadline path) hClose $ \handle -> do
                size <- hFileSize handle
                unless (size == 0) (ioError (userError ("publication lock is not empty: " ++ path)))
                lock deadline path handle
                acquire deadline rest
        open deadline path = do
            opened <- try (openBinaryFile path AppendMode)
            case opened of
                Left problem
                    | isAlreadyInUseError problem -> wait deadline path >> open deadline path
                    | otherwise -> ioError problem
                Right handle -> return handle
        lock deadline path handle = do
            result <- try (hTryLock handle ExclusiveLock) :: IO (Either FileLockingNotSupported Bool)
            case result of
                Left _ -> ioError (userError ("file locking is unavailable: " ++ path))
                Right False -> wait deadline path >> lock deadline path handle
                Right True -> return ()
        wait deadline path = do
            now <- getMonotonicTimeNSec
            when (now >= deadline) (ioError (userError ("timed out waiting for publication lock: " ++ path)))
            threadDelay 20000
