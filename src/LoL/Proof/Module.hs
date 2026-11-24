module LoL.Proof.Module where

import Control.Monad (foldM, unless)
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import qualified LoL.Core as Core
import LoL.Diagnostic
import qualified LoL.Env as Env
import qualified LoL.Front.ArgumentScopes as ArgScopes
import LoL.Front.Fixity (replayScope, validateArgumentsOwner)
import LoL.Front.Syntax
import qualified LoL.Front.Vernac as Vernac
import qualified LoL.Hol.Elab as Elab
import LoL.Hol.Session (Kernel, Limits)
import qualified LoL.Module as Module
import qualified LoL.Object as Object
import qualified LoL.Proof.Section as Section

data SectionFrame
    = SectionFrame
        { sectionLabel :: String
        , sectionStart :: ModuleState
        , sectionNames :: Section.Variables
        , sectionOpens :: [ScopeAction Core.Global]
        , sectionArgs  :: [(Core.Global, Command)]
        }

data ModuleState
    = ModuleState
        { moduleLoaded  :: Module.Loaded
        , moduleImports :: [String]
        , moduleHidden  :: Set.Set String
        , moduleOffsets :: [Int]
        , moduleLocals  :: [Core.ConstId]
        , moduleOwn     :: Map.Map String Core.Global
        , moduleScope   :: Module.NameScope
        , moduleSyntax  :: Env.Syntax
        , moduleExports :: Env.Syntax
        , moduleFrames  :: [SectionFrame]
        }
    deriving ()

emptyModule :: String -> ModuleState
emptyModule name = ModuleState (Module.emptyLoaded name) [] Set.empty [] [] Map.empty Module.emptyScope (Module.moduleGrammar name) (Module.moduleGrammar name) []

contextVariables :: ModuleState -> Section.Variables
contextVariables = Map.unions . map sectionNames . moduleFrames

environment :: ModuleState -> Env.Env
environment state = Env.withAmbiguous hidden (Env.withSyntax (moduleSyntax state) (Env.withNames available (Module.loadedEnv (moduleLoaded state)))) where
    scope = moduleScope state
    context = Map.fromList [(given, Core.GlobalCst c) | (c, (given, _)) <- Map.toList (contextVariables state)]
    hidden = Module.scopeAmbiguous scope `Set.difference` Map.keysSet context
    available = Map.union context (Module.scopeAvailable scope)

displayEnvironment :: ModuleState -> Env.Env -> Env.Env
displayEnvironment state env = Env.withNames (Map.union (Env.envNames env) (Map.union qualified imported)) env where
    qualified = Map.mapKeys ((Module.loadedMain (moduleLoaded state) ++ ".") ++) (moduleOwn state)
    imported = Map.fromList [(given, global) | (global, given) <- Map.toList (Module.canonicalNames (moduleLoaded state))]

execute :: Kernel -> Limits -> FilePath -> ModuleState -> Command -> IO (Either Diagnostic (ModuleState, [String]))
execute kernel limits root = executeWith (\loaded name -> Module.loadSourceInto loaded kernel limits root (Module.modulePath root name)) kernel limits

type Importer = Module.Loaded -> String -> IO (Either Module.Failure Module.Loaded)

executeWith :: Importer -> Kernel -> Limits -> ModuleState -> Command -> IO (Either Diagnostic (ModuleState, [String]))
executeWith importer kernel limits state command = do
    result <- execute
    case result of
        Right (next, messages) -> do
            cached <- prepareClasses kernel limits (commandSpan command) state command next
            return (fmap (\ready -> (ready, messages)) cached)
        Left failure -> return (Left failure)
    where
        execute = dispatch importer kernel limits state command

dispatch :: Importer -> Kernel -> Limits -> ModuleState -> Command -> IO (Either Diagnostic (ModuleState, [String]))
dispatch importer kernel limits state command = case command of
    CSection position name
        | any ((== nameText name) . sectionLabel) (moduleFrames state) -> return (Left (sectionError position "A section with this name is already open."))
        | otherwise -> return (Right (state { moduleFrames = SectionFrame (nameText name) state Map.empty [] [] : moduleFrames state }, []))
    CContext position binders -> declareContext kernel limits position state binders
    CEnd position name -> closeSection kernel limits position state (nameText name)
    CImport position name -> importModule position (nameText name)
    CRocqNotation position GlobalSyntax _ _ _ _ _ _ _ _ | inside -> rejectedGlobal position
    CSelectNotation position GlobalSyntax _ _ _ | inside -> rejectedGlobal position
    CScope position GlobalSyntax action | inside, not (opensScope action) -> rejectedGlobal position
    _ -> case namesAvailable state (commandSpan command) (Module.commandNames command) >> validateArgumentsOwner (Map.elems (moduleOwn state)) env command of
        Left failure -> return (Left failure)
        Right () -> do
            result <- Vernac.executeWithDisplay (displayEnvironment state) declare kernel limits env command
            return $ case result of
                Left failure -> Left (Module.ambiguous (Module.scopeCanonical (moduleScope state)) failure)
                Right (next, messages) -> Right (record state command next, messages)
    where
        env = environment state
        inside = not (null (moduleFrames state))
        opensScope (OpenScope _) = True
        opensScope (CloseScope _) = True
        opensScope _ = False
        rejectedGlobal position = return (Left (sectionError position "This command does not support Global inside a section."))
        declare engine budget current given universes declaration = Env.declareWithUniverses engine budget (Env.withNames (foldr Map.delete (Env.envNames current) (map fst (Env.declGlobals (Env.envFresh current) given declaration))) current) given universes declaration
        importModule position name
            | name `elem` moduleImports state, Set.notMember name (moduleHidden state) = return (Left (problem position "I-Duplicate" ("Module imported twice in this document: " ++ name)))
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
                                let fresh = name `notElem` moduleImports state
                                    imports = moduleImports state ++ [name | fresh]
                                merged <- Module.joinedUniverseView kernel limits next imports (moduleLocals state)
                                return $ case merged of
                                    Left refusal -> Left (Vernac.refusalIn (displayEnvironment state env) position refusal)
                                    Right scoped -> Right (state
                                        { moduleLoaded = next { Module.loadedEnv = scoped }
                                        , moduleImports = imports
                                        , moduleHidden = Set.delete name (moduleHidden state)
                                        , moduleOffsets = moduleOffsets state ++ [length (moduleLocals state) | fresh]
                                        , moduleScope = Module.introduce (moduleScope state) (Module.unitNames unit)
                                        , moduleSyntax = Module.importArguments next [name] syntax
                                        }, [])
        problem position code message = Diagnostic position "LoL-ImportError" code message []

prepareClasses :: Kernel -> Limits -> Span -> ModuleState -> Command -> ModuleState -> IO (Either Diagnostic ModuleState)
prepareClasses kernel limits position previous command next
    | Map.null (Env.syntaxBindings syntax) = return (Right next)
    | otherwise = do
        result <- ArgScopes.prepare kernel limits env globals
        return (either (Left . Vernac.refusalIn (displayEnvironment next env) position) (\updated -> Right (observe old (ArgScopes.commandLookups old command) next { moduleSyntax = saveDefaults updated })) result)
    where
        old = environment previous
        env = environment next
        syntax = moduleSyntax next
        floorId = case command of
            _ | Map.null (Env.syntaxBindings (moduleSyntax previous)) -> 0
            CImport {} -> 0
            CEnd {} | frame : _ <- moduleFrames previous -> Env.envFresh (environment (sectionStart frame))
            _ -> Env.envFresh (environment previous)
        captureFrom = case command of
            CEnd {} -> floorId
            _ -> Env.envFresh (environment previous)
        saveDefaults updated = updated { Env.syntaxDefaults = Map.union captured (Env.syntaxDefaults updated) } where
            eligible g = case command of
                CImport {} -> False
                CEnd {} -> Set.member g (Set.fromList (Map.elems (moduleOwn next)))
                _ -> True
            captured = Map.fromList [(g, scopes) | g <- globals, ArgScopes.globalOwner g >= captureFrom, eligible g, Just classes <- [Map.lookup g (Env.syntaxClasses updated)], let scopes = map (maybe [] (ArgScopes.classScopes env)) classes, any (not . null) scopes]
        entries = snd (Map.split (floorId - 1) (Env.envDecls env))
        globals = [g | (c, entry) <- Map.toAscList entries, (_, g) <- Env.declGlobals c (Env.entryName entry) (Env.entryDecl entry)]

-- Called only for a successful command. The document owns the observed
-- scopes; an imported object starts with its declaration-time defaults.
observe :: Env.Env -> Set.Set Core.Global -> ModuleState -> ModuleState
observe old used state
    | Map.null rows = state
    | otherwise = state
        { moduleSyntax = syntax { Env.syntaxObserved = Map.union rows (Env.syntaxObserved syntax) }
        , moduleExports = exported { Env.syntaxSchedule = steps ++ Env.syntaxSchedule exported }
        }
    where
        syntax = moduleSyntax state
        exported = moduleExports state
        rows = ArgScopes.observedScopes (Env.envSyntax old) used
        steps = [(length (moduleImports state), length (moduleLocals state), ScopeLookup g) | g <- Map.keys rows]

namesAvailable :: ModuleState -> Span -> [String] -> Either Diagnostic ()
namesAvailable state position names = case duplicated of
    name : _ -> Left (Vernac.refusalIn (environment state) position (Env.DuplicateName name))
    [] -> Right ()
    where
        duplicated = [name | name <- names, Map.member name (moduleOwn state) || Set.member name section] ++ [name | (name, count) <- Map.toList (Map.fromListWith (+) [(name, 1 :: Int) | name <- names]), count > 1]
        section = Set.fromList [name | (name, _) <- Map.elems (contextVariables state)]

sectionError :: Span -> String -> Diagnostic
sectionError position message = Diagnostic position "LoL-ScopeError" "H-Section" message []

declareContext :: Kernel -> Limits -> Span -> ModuleState -> [Binder] -> IO (Either Diagnostic (ModuleState, [String]))
declareContext kernel limits position state binders = case moduleFrames state of
    [] -> return (Left (sectionError position "Open a section before declaring a context."))
    _ -> do
        next <- foldM group (Right state) binders
        return (fmap (\result -> (result, [])) next)
    where
        group (Left failure) _ = return (Left failure)
        group (Right current) (Binder at names@(first : others) (Just typ) implicit) = case namesAvailable current at (map nameText names) of
            Left failure -> return (Left failure)
            Right () -> do
                let env = environment current
                    admitParameter engine budget view given universes decl = Env.declareWithUniverses engine budget (Env.withNames (Map.delete given (Env.envNames view)) view) given universes decl
                result <- Vernac.executeWithDisplay (displayEnvironment current) admitParameter kernel limits env (CAxiom at first typ)
                case result of
                    Left failure -> return (Left failure)
                    Right (checked, _) -> case Map.lookup (Env.envFresh env) (Env.envDecls checked) of
                        Nothing -> return (Left (sectionError at "Missing checked context entry."))
                        Just entry -> foldM (another entry) (Right (insert current first implicit checked)) others
            where
                another _ (Left failure) _ = return (Left failure)
                another entry (Right previous) name = do
                    let env = environment previous
                    admitted <- Env.declareWithUniverses kernel limits (Env.withNames (Map.delete (nameText name) (Env.envNames env)) env) (nameText name) (Env.entryUniverses entry) (Env.entryDecl entry)
                    return $ case admitted of
                        Left failure -> Left (Vernac.refusalIn (displayEnvironment previous env) at failure)
                        Right (_, checked) -> Right (insert previous name implicit checked)
        group _ (Binder at [] _ _) = return (Left (sectionError at "A context binder needs a name."))
        group _ (Binder at _ Nothing _) = return (Left (sectionError at "A context binder needs a type."))
        insert previous name implicit checked = previous
            { moduleLoaded = (moduleLoaded previous) { Module.loadedEnv = checked }
            , moduleLocals = identity : moduleLocals previous
            , moduleFrames = case moduleFrames previous of
                frame : outer -> frame { sectionNames = Map.insert identity (nameText name, implicit) (sectionNames frame) } : outer
                [] -> []
            }
            where
                identity = Env.envFresh checked - 1

closeSection :: Kernel -> Limits -> Span -> ModuleState -> String -> IO (Either Diagnostic (ModuleState, [String]))
closeSection kernel limits position state label = case moduleFrames state of
    [] -> return (Left (sectionError position "There is no section to close."))
    frame : outer
        | sectionLabel frame /= label -> return (Left (sectionError position ("Expected End " ++ sectionLabel frame ++ ".")))
        | otherwise -> do
            let opened = sectionStart frame
                variables = sectionNames frame
                loaded = moduleLoaded state
                env = environment state
                imports = drop (length (moduleImports opened)) (moduleImports state)
                imported = [unit | name <- imports, Just unit <- [Map.lookup name (Module.loadedUnits loaded)]]
                qualified = Map.unions (map Module.unitNames imported)
                newNames = Map.mapKeys ((Module.loadedMain loaded ++ ".") ++) (Map.difference (moduleOwn state) (moduleOwn opened))
                scope = Module.introduce (moduleScope opened) newNames
                before = Module.importArguments loaded imports (moduleSyntax opened)
                restored = foldr replayScope before { Env.syntaxScopes = Set.unions (Env.syntaxScopes before : map (Env.syntaxScopes . Module.unitSyntax) imported) } (sectionOpens frame)
                propagate [] = []
                propagate (parent : other) = parent { sectionOpens = sectionOpens frame ++ sectionOpens parent, sectionArgs = sectionArgs frame ++ sectionArgs parent } : other
                copied target = foldr (\(g, cmd) -> Module.copyArgument cmd g (moduleExports state)) target (sectionArgs frame)
            rebuilt <- Section.discharge kernel limits (environment opened) env variables
            return $ case rebuilt of
                Left failure -> Left (Vernac.refusalIn (displayEnvironment state env) position failure)
                Right (checked, deps) -> let
                    release = Section.dischargedSyntax variables deps checked (moduleExports state) . copied
                    syntax = release restored
                    locals = filter (`Map.notMember` variables) (moduleLocals state)
                    inc event = (length (moduleImports state), length locals, event)
                    previous = moduleExports opened
                    toward g flags (Just slots) | Just n <- Map.lookup g (Env.syntaxArgPrefixes syntax) = SectionStep g n flags slots
                    toward g flags policy = ArgumentStep False g flags policy
                    scopedArgs = [toward g flags policy | g <- Set.toAscList (Map.keysSet (Env.syntaxArguments syntax) `Set.union` Map.keysSet (Env.syntaxArgScopes syntax)), Map.member (ArgScopes.globalOwner g) deps, let flags = Map.findWithDefault [] g (Env.syntaxArguments syntax), let policy = Map.lookup g (Env.syntaxArgScopes syntax), or flags || policy /= Nothing]
                    exported = release (foldr replayScope previous (sectionOpens frame))
                    schedule = map inc (reverse scopedArgs ++ map (const PublicSyntax) (sectionOpens frame)) ++ Env.syntaxSchedule previous
                    in Right (state
                    { moduleLoaded = loaded { Module.loadedEnv = checked }
                    , moduleLocals = locals
                    , moduleOffsets = correctedOffsets variables (moduleLocals state) (moduleOffsets state)
                    , moduleHidden = Set.union (Set.fromList imports) (moduleHidden opened)
                    , moduleScope = scope { Module.scopeCanonical = Map.union qualified (Module.scopeCanonical scope), Module.scopeAvailable = Map.union qualified (Module.scopeAvailable scope) }
                    , moduleSyntax = syntax
                    , moduleExports = exported { Env.syntaxSchedule = schedule }
                    , moduleFrames = propagate outer
                    }, [])

-- Import offsets count module declarations, including the temporary variables
-- until End. Walk the ordered offsets and declarations once when closing.
correctedOffsets :: Section.Variables -> [Core.ConstId] -> [Int] -> [Int]
correctedOffsets variables locals = go 0 0 (reverse locals) where
    go _ _ _ [] = []
    go old kept rest (offset : more) = next : go offset next after more where
        (prefix, after) = splitAt (offset - old) rest
        next = kept + length (filter (`Map.notMember` variables) prefix)

record :: ModuleState -> Command -> Env.Env -> ModuleState
record state command next = state
    { moduleLoaded = (moduleLoaded state) { Module.loadedEnv = next }
    , moduleLocals = reverse identities ++ moduleLocals state
    , moduleOwn = Map.union (Map.fromList globals) (moduleOwn state)
    , moduleScope = Module.introduce (moduleScope state) qualified
    , moduleSyntax = activeSyntax
    , moduleExports = exported
    , moduleFrames = case (moduleFrames state, command, Env.syntaxHistory activeSyntax) of
        (frame : outer, CSetArguments _ GlobalSyntax name _ _, _) | Just g <- lookupReference (Env.envNames next) name -> frame { sectionArgs = (g, command) : sectionArgs frame } : outer
        (frame : outer, CScope _ GlobalSyntax _, Left op : _) -> frame { sectionOpens = op : sectionOpens frame } : outer
        (frames, _, _) -> frames
    }
    where
        previous = environment state
        identities = [Env.envFresh previous .. Env.envFresh next - 1]
        globals = [(given, global) | identity <- identities, Just entry <- [Map.lookup identity (Env.envDecls next)], (given, global) <- Env.declGlobals identity (Env.entryName entry) (Env.entryDecl entry)]
        qualified = Map.fromList [(Module.loadedMain (moduleLoaded state) ++ "." ++ given, global) | (given, global) <- globals]
        (activeSyntax, exported) = Module.recordSyntax (Module.loadedMain (moduleLoaded state)) (not (null (moduleFrames state))) (length (moduleImports state)) (length (moduleLocals state) + length identities) (map snd globals) command next (moduleExports state)

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
            case admitted of
                Left refusal -> return (Left (Vernac.refusalIn (displayEnvironment state env) position refusal))
                Right (_, next) -> prepareClasses kernel limits position state header (record state header (Vernac.implicitMetadata next header))
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
    case moduleFrames state of
        frame : _ -> Left ("The source ends inside section " ++ sectionLabel frame ++ ".")
        [] -> Right ()
    let loaded = moduleLoaded state
        name = Module.loadedMain loaded
        env = environment state
        locals = reverse (moduleLocals state)
        canonical = Map.mapKeys ((name ++ ".") ++) (moduleOwn state)
        dependenciesInScope = Set.fromList (Module.dependencyModules loaded (moduleImports state))
        importedNames = Map.fromList [(global, given) | (unitName, unit) <- Map.toList (Module.loadedUnits loaded), Set.member unitName dependenciesInScope, (given, global) <- Map.toList (Module.unitNames unit)]
        names = Map.union (Map.fromList [(global, given) | (given, global) <- Map.toList canonical]) importedNames
        syntax = Module.ownedSyntax (Set.fromList (Map.elems (moduleOwn state))) (moduleSyntax state) (moduleExports state)
    unless (Map.notMember name (Module.loadedUnits loaded)) (Left "The document module name is already loaded.")
    dependencies <- mapM (\dependency -> maybe (Left ("Missing captured dependency: " ++ dependency)) (\unit -> Right (dependency, Module.unitDigest unit)) (Map.lookup dependency (Module.loadedUnits loaded))) (moduleImports state)
    stored <- Object.captureNamedObject name dependencies names locals (Env.withSyntax syntax env)
    let object = Object.withImportOffsets (moduleOffsets state) stored
        unit = Module.Unit name path (Just source) (moduleImports state) locals canonical syntax object (Object.fingerprint object)
    return loaded { Module.loadedEnv = env, Module.loadedUnits = Map.insert name unit (Module.loadedUnits loaded), Module.loadedOrder = Module.loadedOrder loaded ++ [name] }
