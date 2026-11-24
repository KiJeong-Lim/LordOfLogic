module LoL.Proof.Module where

import Control.Monad (unless)
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import qualified LoL.Core as Core
import LoL.Diagnostic
import qualified LoL.Env as Env
import LoL.Front.Fixity (validateArgumentsOwner)
import LoL.Front.Syntax
import qualified LoL.Front.Vernac as Vernac
import qualified LoL.Hol.Elab as Elab
import LoL.Hol.Session (Kernel, Limits)
import qualified LoL.Module as Module
import qualified LoL.Object as Object

data ModuleState
    = ModuleState
        { moduleLoaded  :: Module.Loaded
        , moduleImports :: [String]
        , moduleOffsets :: [Int]
        , moduleLocals  :: [Core.ConstId]
        , moduleOwn     :: Map.Map String Core.Global
        , moduleScope   :: Module.NameScope
        , moduleSyntax  :: Env.Syntax
        , moduleExports :: Env.Syntax
        }
    deriving ()

emptyModule :: String -> ModuleState
emptyModule name = ModuleState (Module.emptyLoaded name) [] [] [] Map.empty Module.emptyScope Module.emptySyntax Module.emptySyntax

environment :: ModuleState -> Env.Env
environment state = Env.withAmbiguous (Module.scopeAmbiguous scope) (Env.withSyntax (moduleSyntax state) (Env.withNames (Module.scopeAvailable scope) (Module.loadedEnv (moduleLoaded state)))) where
    scope = moduleScope state

displayEnvironment :: ModuleState -> Env.Env -> Env.Env
displayEnvironment state env = Env.withNames (Map.union (Env.envNames env) (Map.union qualified imported)) env where
    qualified = Map.mapKeys ((Module.loadedMain (moduleLoaded state) ++ ".") ++) (moduleOwn state)
    imported = Map.fromList [(given, global) | (global, given) <- Map.toList (Module.canonicalNames (moduleLoaded state))]

execute :: Kernel -> Limits -> FilePath -> ModuleState -> Command -> IO (Either Diagnostic (ModuleState, [String]))
execute kernel limits root = executeWith (\loaded name -> Module.loadSourceInto loaded kernel limits root (Module.modulePath root name)) kernel limits

type Importer = Module.Loaded -> String -> IO (Either Module.Failure Module.Loaded)

executeWith :: Importer -> Kernel -> Limits -> ModuleState -> Command -> IO (Either Diagnostic (ModuleState, [String]))
executeWith importer kernel limits state command = case command of
    CImport position name -> importModule position (nameText name)
    _ -> case namesAvailable state (commandSpan command) (Module.commandNames command) >> validateArgumentsOwner (Map.elems (moduleOwn state)) env command of
        Left failure -> return (Left failure)
        Right () -> do
            result <- Vernac.executeWithDisplay (displayEnvironment state) declare kernel limits env command
            return $ case result of
                Left failure -> Left (Module.ambiguous (Module.scopeCanonical (moduleScope state)) failure)
                Right (next, messages) -> Right (record state command next, messages)
    where
        env = environment state
        declare engine budget current given universes declaration = Env.declareWithUniverses engine budget (Env.withNames (foldr Map.delete (Env.envNames current) (map fst (Env.declGlobals (Env.envFresh current) given declaration))) current) given universes declaration
        importModule position name
            | name `elem` moduleImports state = return (Left (problem position "I-Duplicate" ("Module imported twice in this document: " ++ name)))
            | not (Object.qualified name) = return (Left (problem position "I-Name" "Invalid import module name."))
            | name == Module.loadedMain (moduleLoaded state) = return (Left (problem position "I-Cycle" "A document cannot import itself."))
            | otherwise = do
                loaded <- importer (moduleLoaded state) name
                case loaded of
                    Left failure -> return (Left ((Module.failureDiagnostic failure) { diagnosticSpan = position, diagnosticText = "Importing " ++ name ++ " failed.", diagnosticBody = [renderDiagnostic (Module.failurePath failure) (Module.failureSource failure) (Module.failureDiagnostic failure)] }))
                    Right next -> case Map.lookup name (Module.loadedUnits next) of
                        Nothing -> return (Left (problem position "I-Import" "The imported module produced no environment."))
                        Just unit -> case Object.joinSyntax (moduleSyntax state) (Module.unitSyntax unit) of
                            Left (code, message) -> return (Left (Diagnostic position "LoL-ScopeError" code message []))
                            Right syntax -> do
                                let imports = moduleImports state ++ [name]
                                merged <- Module.joinedUniverseView kernel limits next imports (moduleLocals state)
                                return $ case merged of
                                    Left refusal -> Left (Vernac.refusalIn (displayEnvironment state env) position refusal)
                                    Right scoped -> Right (state
                                        { moduleLoaded = next { Module.loadedEnv = scoped }
                                        , moduleImports = imports
                                        , moduleOffsets = moduleOffsets state ++ [length (moduleLocals state)]
                                        , moduleScope = Module.introduce (moduleScope state) (Module.unitNames unit)
                                        , moduleSyntax = Module.importArguments next [name] syntax
                                        }, [])
        problem position code message = Diagnostic position "LoL-ImportError" code message []

namesAvailable :: ModuleState -> Span -> [String] -> Either Diagnostic ()
namesAvailable state position names = case duplicated of
    name : _ -> Left (Vernac.refusalIn (environment state) position (Env.DuplicateName name))
    [] -> Right ()
    where
        duplicated = filter (`Map.member` moduleOwn state) names ++ [name | (name, count) <- Map.toList (Map.fromListWith (+) [(name, 1 :: Int) | name <- names]), count > 1]

record :: ModuleState -> Command -> Env.Env -> ModuleState
record state command next = state
    { moduleLoaded = (moduleLoaded state) { Module.loadedEnv = next }
    , moduleLocals = reverse identities ++ moduleLocals state
    , moduleOwn = Map.union (Map.fromList globals) (moduleOwn state)
    , moduleScope = Module.introduce (moduleScope state) qualified
    , moduleSyntax = activeSyntax
    , moduleExports = exported
    }
    where
        previous = environment state
        identities = [Env.envFresh previous .. Env.envFresh next - 1]
        globals = [(given, global) | identity <- identities, Just entry <- [Map.lookup identity (Env.envDecls next)], (given, global) <- Env.declGlobals identity (Env.entryName entry) (Env.entryDecl entry)]
        qualified = Map.fromList [(Module.loadedMain (moduleLoaded state) ++ "." ++ given, global) | (given, global) <- globals]
        (activeSyntax, exported) = Module.recordSyntax (Module.loadedMain (moduleLoaded state)) command next (moduleExports state)

-- Only the clean base kernel reaches this admission path. The proof worker
-- provides a proposal, not a declaration or a trusted checking result.
admitTheorem :: Kernel -> Limits -> ModuleState -> Command -> Core.Term -> Core.Term -> IO (Either Diagnostic ModuleState)
admitTheorem kernel limits state header = admitTheoremWithUniverses kernel limits state header Core.emptyUniverses

admitTheoremWithUniverses :: Kernel -> Limits -> ModuleState -> Command -> Core.UniverseContext -> Core.Term -> Core.Term -> IO (Either Diagnostic ModuleState)
admitTheoremWithUniverses kernel limits state header universes signature value = case header of
    -- The universes that a header writes are those of the theorem, and so
    -- are its constraints when it closes them, whoever proposes the theorem.
    CUniverses position (Just written) inner -> case Elab.universeRequest (environment state) written of
        Left failure -> return (Left failure)
        Right (Elab.ClosedUniverses context) | universes /= context -> return (Left (undeclared position))
        Right (Elab.OpenUniverses context) | Core.universeNames universes /= Core.universeNames context -> return (Left (undeclared position))
        Right _ -> admitTheoremWithUniverses kernel limits state inner universes signature value
    CUniverses _ Nothing inner -> admitTheoremWithUniverses kernel limits state inner universes signature value
    CDefinition position _ name _ _ _ -> case namesAvailable state position [nameText name] >> visibleReferences state position universes [signature, value] of
        Left failure -> return (Left failure)
        Right () -> do
            let env = environment state
                given = nameText name
                visible = Env.withNames (Map.delete given (Env.envNames env)) env
            admitted <- Env.declareWithUniverses kernel limits visible given universes (Env.Theorem signature value)
            return $ case admitted of
                Left refusal -> Left (Vernac.refusalIn (displayEnvironment state env) position refusal)
                Right (_, next) -> Right (record state header (Vernac.implicitMetadata next header))
    _ -> return (Left (Diagnostic (commandSpan header) "LoL-ProofError" "P-Header" "Expected a theorem header." []))

undeclared :: Span -> Diagnostic
undeclared position = Diagnostic position "LoL-ProofError" "P-Statement" "The theorem was proposed with universes or constraints that its header does not declare." []

allowedConstants :: ModuleState -> Set.Set Core.ConstId
allowedConstants state = Set.fromList (moduleLocals state ++ imported) where
    loaded = moduleLoaded state
    imported = concat [Module.unitLocals unit | name <- Module.dependencyModules loaded (moduleImports state), Just unit <- [Map.lookup name (Module.loadedUnits loaded)]]

-- A user tactic can write raw global IDs. Module visibility is a structural
-- ownership check, independent of the clean kernel's later typing judgment.
visibleReferences :: ModuleState -> Span -> Core.UniverseContext -> [Core.Term] -> Either Diagnostic ()
visibleReferences state position context terms = unless (Set.unions (Core.constraintOwners context : map Core.constantsOf terms) `Set.isSubsetOf` allowedConstants state) (Left (Diagnostic position "LoL-ScopeError" "H-HiddenReference" "The proof refers to a declaration outside this module's imports." []))

finish :: FilePath -> String -> ModuleState -> Either String Module.Loaded
finish path source state = do
    let loaded = moduleLoaded state
        name = Module.loadedMain loaded
        env = environment state
        locals = reverse (moduleLocals state)
        canonical = Map.mapKeys ((name ++ ".") ++) (moduleOwn state)
        dependenciesInScope = Set.fromList (Module.dependencyModules loaded (moduleImports state))
        importedNames = Map.fromList [(global, given) | (unitName, unit) <- Map.toList (Module.loadedUnits loaded), Set.member unitName dependenciesInScope, (given, global) <- Map.toList (Module.unitNames unit)]
        names = Map.union (Map.fromList [(global, given) | (given, global) <- Map.toList canonical]) importedNames
        syntax = Object.ownedArguments (Set.fromList (Map.elems (moduleOwn state))) (moduleSyntax state) (moduleExports state)
    unless (Map.notMember name (Module.loadedUnits loaded)) (Left "The document module name is already loaded.")
    dependencies <- mapM (\dependency -> maybe (Left ("Missing captured dependency: " ++ dependency)) (\unit -> Right (dependency, Module.unitDigest unit)) (Map.lookup dependency (Module.loadedUnits loaded))) (moduleImports state)
    stored <- Object.captureNamedObject name dependencies names locals (Env.withSyntax syntax env)
    let object = Object.withImportOffsets (moduleOffsets state) stored
        unit = Module.Unit name path source (moduleImports state) locals canonical syntax object (Object.fingerprint object)
    return loaded { Module.loadedEnv = env, Module.loadedUnits = Map.insert name unit (Module.loadedUnits loaded), Module.loadedOrder = Module.loadedOrder loaded ++ [name] }
