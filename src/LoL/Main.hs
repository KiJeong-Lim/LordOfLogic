module LoL.Main where

import Control.Exception (IOException, finally, try)
import Control.Monad (foldM, mapM_, when)
import Data.Int (Int64)
import Data.IORef
import Data.List (partition, stripPrefix)
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.Word (Word64)
import LoL.Core (ConstId, Global (GlobalInd))
import LoL.Diagnostic
import qualified LoL.Env as Env
import qualified LoL.Export.Rocq as Rocq
import LoL.Front.Parse (commandChunks, parseChunkIndexed)
import LoL.Front.Syntax
import LoL.Front.Vernac (Declare, executeWith)
import LoL.Hol.Session
import qualified LoL.Module as Module
import qualified LoL.Object as Object
import qualified LoL.Pretty as Pretty
import qualified LoL.Proof.Main as Proof
import System.Exit (exitFailure)
import System.Directory (getCurrentDirectory)
import System.FilePath (addExtension, takeExtension)
import System.IO (hIsSeekable, hPutStrLn, hSetEncoding, stderr, stdout, utf8)
import Text.Read (readMaybe)

-- Emit after each successful command: a later error does not hide earlier
-- output. The parser supplies the successfully parsed prefix before an error.
processSource :: Kernel -> Limits -> Bool -> FilePath -> String -> Env.Env -> ([String] -> IO ()) -> IO (Either Diagnostic Env.Env)
processSource = processWith Env.declareWithUniverses

processWith :: Declare -> Kernel -> Limits -> Bool -> FilePath -> String -> Env.Env -> ([String] -> IO ()) -> IO (Either Diagnostic Env.Env)
processWith declare kernel limits explicit _ source = loop (commandChunks source) where
    loop [] env _ = return (Right env)
    loop (chunk : rest) env emit = case parseChunkIndexed (Env.syntaxReader (Env.envSyntax env)) chunk of
        Left failure -> return (Left (fromFrontError failure))
        Right commands -> run commands rest env emit
    run [] rest env emit = loop rest env emit
    run (command : more) rest env emit = do
        result <- executeWith declare kernel limits env command
        case result of
            Left failure -> return (Left failure)
            Right (next, output) -> case if explicit then declarations env next else Right output of
                Left message -> return (Left (Diagnostic (commandSpan command) "LoL-Unsupported" "M2-Output" message []))
                Right rendered -> do
                    emit rendered
                    run more rest next emit
    declarations old next = sequence [Pretty.declaration next constant entry | constant <- [Env.envFresh old .. Env.envFresh next - 1], Just entry <- [Map.lookup constant (Env.envDecls next)]]

runSource :: Kernel -> Limits -> Bool -> FilePath -> String -> Env.Env -> IO (Either Diagnostic (Env.Env, [String]))
runSource kernel limits explicit path source env = do
    output <- newIORef id
    result <- processSource kernel limits explicit path source env (\items -> modifyIORef' output (. (items ++)))
    rendered <- ($ []) <$> readIORef output
    return ((\next -> (next, rendered)) <$> result)

data Options
    = Options
        { optionExplicit :: Bool
        , optionStated   :: Bool
        , optionRocqOuts :: Bool
        , optionRocqPath :: Maybe FilePath
        , optionOnlyCore :: Bool
        , optionArtifact :: Maybe FilePath
        , optionResource :: Limits
        , optionMode     :: ExecutionMode
        }
    deriving (Eq, Show)

data ExecutionMode = BatchMode | InteractiveMode | ServerMode deriving (Eq, Show)

parseOptions :: [String] -> Either String Options
parseOptions arguments = foldM option (Options False False False Nothing False Nothing defaultLimits BatchMode) arguments >>= compatible where
    option selected argument = case argument of
        "--explicit" -> Right selected { optionExplicit = True }
        "--statements" -> Right selected { optionExplicit = True, optionStated = True }
        "--rocq" -> Right selected { optionRocqOuts = True }
        "--check-only" -> Right selected { optionOnlyCore = True }
        "--interactive" -> selectMode InteractiveMode selected
        "--server" -> selectMode ServerMode selected
        _
            | Just path <- stripPrefix "--emit-object=" argument
            , takeExtension path == ".lolo" -> Right selected { optionArtifact = Just path }
            | Just path <- stripPrefix "--rocq-dir=" argument
            , not (null path) -> Right selected { optionRocqPath = Just path }
            | Just text <- stripPrefix "--work-limit=" argument -> do
                value <- bounded (toInteger (maxBound :: Word64)) text
                Right selected { optionResource = (optionResource selected) { limitVisits = Just (fromInteger value) } }
            | Just text <- stripPrefix "--timeout-ms=" argument -> do
                value <- bounded (toInteger (maxBound :: Int) `div` 1000) text
                Right selected { optionResource = (optionResource selected) { limitMicros = fromInteger (value * 1000) } }
            | Just text <- stripPrefix "--host-allocation-mib=" argument -> case readMaybe text :: Maybe Integer of
                Just value
                    | value >= 0 && value <= toInteger (maxBound :: Int64) `div` (1024 * 1024) ->
                        Right selected { optionResource = (optionResource selected) { limitAllocBytes = fromInteger (value * 1024 * 1024) } }
                _ -> Left "--host-allocation-mib requires a nonnegative, representable integer"
            | Just text <- stripPrefix "--memory-mib=" argument -> case readMaybe text :: Maybe Integer of
                Just value
                    | value >= 0 && value <= toInteger (maxBound :: Word64) `div` (1024 * 1024) ->
                        Right selected { optionResource = (optionResource selected) { limitBytes = fromInteger (value * 1024 * 1024) } }
                _ -> Left "--memory-mib requires a nonnegative, representable integer"
            | otherwise -> Left ("unknown option: " ++ argument)
    bounded maximum text = case readMaybe text :: Maybe Integer of
        Just value
            | value > 0 && value <= maximum -> Right value
        _ -> Left "resource limits must be positive, representable integers"
    selectMode mode selected
        | optionMode selected /= BatchMode && optionMode selected /= mode = Left "choose --interactive or --server"
        | otherwise = Right selected { optionMode = mode }
    compatible selected
        | optionMode selected /= BatchMode && (optionOnlyCore selected || optionExplicit selected || optionRocqOuts selected || optionRocqPath selected /= Nothing || optionArtifact selected /= Nothing) = Left "interactive and server modes take resource options only"
        | optionExplicit selected && (optionRocqOuts selected || optionRocqPath selected /= Nothing) = Left "choose --explicit or a Rocq output option"
        | optionOnlyCore selected && (optionExplicit selected || optionRocqOuts selected || optionRocqPath selected /= Nothing || optionArtifact selected /= Nothing) = Left "--check-only takes an object and no source-output option"
        | otherwise = Right selected

usage :: String
usage = unlines
    [ "Usage: lol [OPTIONS] FILE.lol"
    , "       lol --check-only FILE.lolo"
    , "       lol --interactive [FILE.lol] | lol --server"
    , "  --explicit | --statements     Print checked declarations, with or without theorem proofs."
    , "  --rocq  --rocq-dir=DIR        Print the main Rocq module or write the module tree."
    , "  --emit-object=FILE.lolo       Write a checked LoL object."
    , "  --work-limit=N  --timeout-ms=N  --memory-mib=N  --host-allocation-mib=N"
    , "Run from a project root containing the release's lol/hol directory."
    ]

mainWithArgs :: [String] -> IO ()
mainWithArgs arguments = do
    -- GHC can reuse descriptor 1 for its timer before main. Querying its
    -- device type fails immediately in that case; a normal pipe returns False.
    device <- try (hIsSeekable stdout) :: IO (Either IOException Bool)
    case device of
        Left _ -> abort "standard output is unavailable"
        Right _ -> return ()
    mapM_ (\handle -> hSetEncoding handle utf8) [stdout, stderr]
    if arguments == ["--help"] then putStr usage else case parseOptions flags of
        Left problem -> badArguments problem
        Right options -> case (optionMode options, paths) of
            (BatchMode, [path]) -> runFile options path
            (InteractiveMode, []) -> Proof.interactive (optionResource options) Nothing
            (InteractiveMode, [path])
                | takeExtension path == ".lol" -> Proof.interactive (optionResource options) (Just path)
                | otherwise -> badArguments "--interactive requires a .lol source file"
            (ServerMode, []) -> Proof.server (optionResource options)
            (BatchMode, _) -> badArguments "expected one input file; use lol --help"
            (InteractiveMode, _) -> badArguments "--interactive takes at most one source file"
            (ServerMode, _) -> badArguments "--server takes no source file"
    where
        (beforeMarker, afterMarker) = break (== "--") arguments
        (flags, names) = partition ((== "--") . take 2) beforeMarker
        paths = names ++ drop 1 afterMarker
        origin = Span (1, 1) (1, 1)
        badArguments message = reject "<arguments>" (unwords arguments) (Diagnostic origin "LoL-Unsupported" "M2-Unsupported" message [])
        runFile options path
            | takeExtension path /= expected = reject path "" (unsupported origin ("file format " ++ takeExtension path ++ "; expected " ++ expected))
            | otherwise = do
                ready <- if optionOnlyCore options then loadKernel "lol/hol/kernel.hol" else loadSurfaceKernel
                case ready of
                    Left failure -> abort ("the Hol programs were not loaded from the project root: " ++ failure)
                    Right kernel -> flip finally (closeKernel kernel) $ do
                        root <- getCurrentDirectory
                        outcome <- if optionOnlyCore options then
                            Module.loadObject kernel (optionResource options) path
                        else
                            Proof.loadSource kernel (optionResource options) root path (if optionExplicit options || optionRocqOuts options || optionRocqPath options /= Nothing then const (return ()) else mapM_ putStrLn)
                        case outcome of
                            Left failure -> rejectModule failure
                            Right loaded -> do
                                explicit <- if optionExplicit options then either (rejectModule . Module.failure path "" origin "I-Output") return ((if optionStated options then Module.statedModule else Module.explicitModule) loaded) else return []
                                modules <- if optionRocqOuts options || optionRocqPath options /= Nothing then exportModules kernel (optionResource options) loaded >>= either abort return else return Map.empty
                                let exports = [(addExtension (map modulePath (Rocq.moduleName name)) "v", source) | (name, (_, source)) <- Map.toList modules]
                                Module.writeProducts (fmap (\directory -> (directory, exports)) (optionRocqPath options)) (optionArtifact options) loaded >>= either rejectModule return
                                mapM_ putStrLn explicit
                                when (optionRocqOuts options) (maybe (abort "the main module has no export") (putStr . snd) (Map.lookup (Module.loadedMain loaded) modules))
            where
                expected = if optionOnlyCore options then ".lolo" else ".lol"
        rejectModule failure = reject (Module.failurePath failure) (Module.failureSource failure) (Module.failureDiagnostic failure)
        reject path source failure = putStrLn (renderDiagnostic path source failure) >> exitFailure
        abort message = hPutStrLn stderr ("LoL: " ++ message) >> exitFailure
        modulePath '.' = '/'
        modulePath other = other

-- `Import M.` is exported as `Require Import M.`: each file contributes only
-- its local declarations. The name
-- chosen for a dependency is fixed when that module is exported.
exportLoaded :: Kernel -> Limits -> Module.Loaded -> IO (Either String String)
exportLoaded kernel limits loaded = do
    result <- exportModules kernel limits loaded
    return (result >>= \exports -> maybe (Left "the main module has no export") (Right . snd) (Map.lookup (Module.loadedMain loaded) exports))

exportModules :: Kernel -> Limits -> Module.Loaded -> IO (Either String (Map.Map String (Integer, String)))
exportModules kernel limits loaded = do
    let entries = Env.envDecls (Module.loadedEnv loaded)
        sections unit = walk [] [] (Object.importGroups (Module.unitObject unit) (Module.unitLocals unit)) where
            walk _ _ [] = []
            walk imported previous ((added, locals) : rest) =
                (Module.universeView loaded roots visible, [(identity, entry) | identity <- locals, Just entry <- [Map.lookup identity entries]]) : walk roots visible rest
                where
                    roots = imported ++ added
                    visible = locals ++ previous
        groups = concat [sections unit | name <- Module.loadedOrder loaded, Just unit <- [Map.lookup name (Module.loadedUnits loaded)]]
    prepared <- Rocq.prepareGroups kernel limits groups
    return (prepared >>= \entries -> exportPreparedModules entries loaded)

exportPreparedModules :: Map.Map ConstId Env.Entry -> Module.Loaded -> Either String (Map.Map String (Integer, String))
exportPreparedModules prepared loaded = snd <$> foldM output (Map.empty, Map.empty) (Module.loadedOrder loaded)
    where
        env = Module.loadedEnv loaded
        output (canonical, exports) name = case Map.lookup name (Module.loadedUnits loaded) of
            Nothing -> Left ("missing loaded module: " ++ name)
            Just unit -> do
                let entries = [(c, entry) | c <- Module.unitLocals unit, Just entry <- [Map.lookup c (Env.envDecls env)]]
                    local = Rocq.namesIn entries
                    globals = Map.union local canonical
                let groups = Object.importGroups (Module.unitObject unit) (Module.unitLocals unit)
                    requireGroups seen (roots, locals) = do
                        let closure = Module.dependencyModules loaded roots
                            needed = filter (`Set.notMember` seen) closure
                        imported <- mapM (\dependency -> maybe (Left ("missing exported dependency: " ++ dependency)) (\(level, _) -> Right (Rocq.moduleName dependency, level)) (Map.lookup dependency exports)) needed
                        return (Set.union seen (Set.fromList needed), (imported, locals))
                    exposed = Set.fromList [name | global <- Map.elems (Module.dependencyNames loaded (Module.unitImports unit)), Just spelling <- [Map.lookup global canonical], let leaf = Module.short spelling, name <- leaf : schemes global leaf]
                    schemes GlobalInd {} = Rocq.generated
                    schemes _ = const []
                (_, sections) <- foldM (\(seen, prior) section -> do
                    (more, part) <- requireGroups seen section
                    return (more, part : prior)) (Set.empty, []) groups
                rendered <- Rocq.exportModuleSections (Rocq.moduleName name) prepared (reverse sections) globals exposed env
                return (Map.union (Map.map ((Rocq.moduleName name ++ ".") ++) local) canonical, Map.insert name rendered exports)
