module LoL.Hol.Session where

import Control.Monad (void, when)
import Control.Concurrent.MVar
import Control.Concurrent (ThreadId, forkIOWithUnmask, killThread, myThreadId)
import Control.Exception (AllocationLimitExceeded (..), IOException, SomeException, catch, evaluate, finally, fromException, mask, mask_, onException, throwIO, try)
import Data.Int (Int64)
import Data.IORef
import qualified Data.Map.Strict as Map
import Data.Maybe (listToMaybe, mapMaybe)
import qualified Data.Set as Set
import qualified Data.Unique as Token
import Data.Word (Word64)
import GHC.Conc (disableAllocationLimit, enableAllocationLimit, setAllocationCounter)
import Hol.V2.Embedding
import qualified Hol.V2.Embedding as Full
import LoL.Hol.Embed
import System.Timeout (timeout)

-- The clauses of the kernel are compiled once, when it is loaded. The cache
-- is an engine that holds them together with the facts of one environment.
-- `kernelAside` is another such engine: the oracle asks the kernel on it
-- while a run that asked the oracle is under way on the first.
data Kernel
    = Kernel
        { kernelKinds      :: KindEnv
        , kernelTypes      :: TypeEnv
        , kernelReady      :: Program
        , kernelFresh      :: Supply
        , kernelCache      :: MVar (Maybe Loaded)
        , kernelAside      :: MVar (Maybe Loaded)
        , kernelBundled    :: Bool
        , kernelAsked      :: Maybe (Context -> Question -> IO Bool)
        , kernelElaborator :: Maybe Kernel
        }
    deriving ()

-- Only this bundled program consumes the prechecked header handshake.
loadProofProgram :: IO (Either String Kernel)
loadProofProgram = fmap (fmap (\program -> program { kernelBundled = True })) (loadKernel "lol/hol/tactics.hol")

-- The name of one environment that has declarations. No two environments share
-- a stamp, whichever kernel admitted their declarations.
newtype Stamp
    = Stamp Token.Unique
    deriving (Eq)

instance Show Stamp where
    show (Stamp unique) = "Stamp " ++ show (Token.hashUnique unique)

newStamp :: IO Stamp
newStamp = Stamp <$> Token.newUnique

-- The engine holds exactly the facts of the environment `loadedSource`; the
-- environment without declarations is Nothing.
data Loaded
    = Loaded
        { loadedEngine :: Full.Engine
        , loadedSource :: Maybe Stamp
        }
    | PreparedProof
        { loadedEngine :: Full.Engine
        , loadedSource :: Maybe Stamp
        , loadedNames  :: Set.Set String
        }
    deriving ()

data Limits
    = Limits
        { limitMicros     :: Int
        , limitVisits     :: Maybe Word64
        , limitBytes      :: Word64
        , limitAllocBytes :: Int64
        }
    deriving (Eq, Show)

-- The three results of a ground run: admitted, with its outputs; rejected,
-- with the first report of the kernel when it made one; undecided, when the
-- engine stopped on a resource limit or an error, which is neither admission
-- nor rejection.
data Verdict
    = Admitted [TermNode]
    | Rejected (Maybe Report)
    | Undecided String
    deriving (Eq, Show)

-- The allocation limit bounds what one operation can keep alive, as nothing
-- lives that was not allocated: it has the value of the native limit. A
-- smaller one ends ordinary long operations (512 MiB is the allocation of
-- well under a second).
defaultLimits :: Limits
defaultLimits = Limits { limitMicros = 60000000, limitVisits = Nothing, limitBytes = 4 * 1024 * 1024 * 1024, limitAllocBytes = 4 * 1024 * 1024 * 1024 }

-- These two operations belong only to dedicated LoL worker threads. Never
-- change an embedding caller's allocation counter or its enabled state.
resetHostBudget :: Limits -> IO ()
resetHostBudget limits = do
    disableHostBudget
    when (limitAllocBytes limits > 0) $ do
        setAllocationCounter (limitAllocBytes limits)
        enableAllocationLimit

disableHostBudget :: IO ()
disableHostBudget = disableAllocationLimit

-- A publication changes what `published` reads. The allocation limit can run
-- out while something is being published, and its exception then arrives
-- when the publication unmasks: what was published stands, and the exception
-- is dropped. One that arrives before anything was published is passed on,
-- whatever else the caller knows: that nothing is pending is no sign of a
-- publication. The limit is off when the exception has been seen.
afterPublication :: Eq mark => IO mark -> IO () -> IO ()
afterPublication published action = do
    before <- published
    action `catch` \failure -> case failure of
        AllocationLimitExceeded -> do
            disableHostBudget
            after <- published
            if after == before then throwIO failure else return ()

-- Cumulative Haskell allocations, not live RSS and not the native arena cap.
-- Join a cancelled child before returning: it may still own a cached engine.
-- Oracle dialogue requests stay on this child and share its remaining budget.
withHostBudget :: Limits -> IO a -> IO (Either String a)
withHostBudget limits action = mask $ \restore -> do
    result <- newEmptyMVar
    worker <- forkIOWithUnmask $ \unmask -> do
        outcome <- try (resetHostBudget limits >> unmask (action >>= evaluate))
        disableHostBudget
        putMVar result outcome
    outcome <- restore (readMVar result) `onException` (killThread worker >> readMVar result >> return ())
    case outcome of
        Right value -> return (Right value)
        Left exception -> case fromException exception of
            Just AllocationLimitExceeded -> return (Left "the Haskell allocation limit was reached")
            Nothing -> throwIO (exception :: SomeException)

hostVerdict :: Limits -> IO Verdict -> IO Verdict
hostVerdict limits action = either Undecided id <$> withHostBudget limits action

loadKernel :: FilePath -> IO (Either String Kernel)
loadKernel path = do
    fresh <- newSupply
    loadKernelWith fresh path

loadKernelWith :: Supply -> FilePath -> IO (Either String Kernel)
loadKernelWith fresh path = do
    loaded <- loadProgramCached fresh path
    cache <- newMVar Nothing
    aside <- newMVar Nothing
    return $ case loaded of
        Left failure -> Left (describeFailure failure)
        Right ready
            | path `elem` ["lol/hol/kernel.hol", "lol/hol/elab.hol", "lol/hol/tactics.hol"]
            , Map.lookup (DC_Named "template_block") (programTypes ready) /= Just templateSignature -> Left ("Incompatible Hol kernel in " ++ path ++ ": template_block has a missing or incompatible signature. Use the lol/hol directory shipped with this executable.")
        Right ready -> Right Kernel { kernelKinds = programKinds ready, kernelTypes = programTypes ready, kernelReady = ready, kernelFresh = fresh, kernelCache = cache, kernelAside = aside, kernelAsked = Nothing, kernelElaborator = Nothing, kernelBundled = False }
    where
        tm = TyCon (TCon (TC_Named "tm") Star)
        constraints = mkTyList (TyCon (TCon (TC_Named "uconstraint") Star))
        templateSignature = Forall [] (foldr mkTyArrow mkTyO [mkTyNat, mkTyNat, constraints, mkTyNat, tm, mkTyList tm])

-- Raw elaboration runs in an independent program. The base returned
-- here admits declarations using kernel.hol alone, even if elab.hol is bad.
loadSurfaceKernel :: IO (Either String Kernel)
loadSurfaceKernel = do
    fresh <- newSupply
    base <- loadKernelWith fresh "lol/hol/kernel.hol"
    case base of
        Left message -> return (Left message)
        Right kernel -> do
            proposal <- loadKernelWith fresh "lol/hol/elab.hol"
            return ((\engine -> kernel { kernelElaborator = Just engine }) <$> proposal)

-- The action receives a kernel with this answer, sharing the cached engines.
-- Nested and concurrent callers cannot replace another run's callback.
withOracle :: Kernel -> (Context -> Question -> IO Bool) -> (Kernel -> IO a) -> IO a
withOracle kernel answer action = action kernel { kernelAsked = Just answer }

-- One FFI call may ask the kernel repeatedly before returning its Bool.
-- The request action retains only its cell when that call has ended.
newtype Dialogue
    = Dialogue { dialogueAsk :: TermNode -> [LogicVar] -> IO Verdict }
    deriving ()

data DialogueState
    = DialogueState
        { dialogueOwner :: ThreadId
        , dialogueInUse :: Bool
        , dialogueFault :: Maybe String
        , dialogueQuery :: TermNode -> [LogicVar] -> IO Verdict
        }
    deriving ()

withOracleDialogue :: Kernel -> Limits -> Maybe Stamp -> [TermNode] -> (Dialogue -> Context -> Question -> IO Bool) -> (Kernel -> IO a) -> IO a
withOracleDialogue kernel limits source facts answer
    = withOracle kernel (\context question -> withDialogue kernel limits source facts (\dialogue -> answer dialogue context question))

withDialogue :: Kernel -> Limits -> Maybe Stamp -> [TermNode] -> (Dialogue -> IO Bool) -> IO Bool
withDialogue kernel limits source facts action = mask $ \restore -> do
    owner <- myThreadId
    cell <- newIORef (Just (DialogueState owner False Nothing query))
    let finish = do
            answer <- action (Dialogue (dialogueRequest cell)) >>= evaluate
            state <- readIORef cell
            case state >>= dialogueFault of
                Nothing -> return answer
                Just message -> ioError (userError ("oracle dialogue: " ++ message))
    restore finish `finally` writeIORef cell Nothing
    where
        query = asideRun kernel { kernelAsked = Just (\_ _ -> ioError (userError "an oracle dialogue request cannot call another oracle")) } limits source facts

dialogueRequest :: IORef (Maybe DialogueState) -> TermNode -> [LogicVar] -> IO Verdict
dialogueRequest cell goal outputs = mask $ \restore -> do
    caller <- myThreadId
    state <- readIORef cell
    case state of
        Just active
            | caller == dialogueOwner active && not (dialogueInUse active) -> do
                writeIORef cell (Just active { dialogueInUse = True })
                let request = do
                        verdict <- restore (dialogueQuery active goal outputs >>= evaluate) `onException` failed "a kernel request raised an exception"
                        case verdict of
                            Undecided message -> failed message
                            _ -> return ()
                        return verdict
                request `finally` modifyIORef' cell (fmap (\current -> current { dialogueInUse = False }))
            | caller == dialogueOwner active -> ioError (userError "an oracle dialogue request is already active")
        _ -> ioError (userError "oracle dialogue is outside its callback or on another thread")
    where
        failed message = modifyIORef' cell (fmap (\current -> current { dialogueFault = firstFault (dialogueFault current) })) where
            firstFault fault = case fault of
                Nothing -> Just message
                earlier -> earlier

-- The query has no logic variable other than its outputs. The run gets a
-- machine of its own, with the kernel and the given facts.
groundRun :: Kernel -> Limits -> [TermNode] -> TermNode -> [LogicVar] -> IO Verdict
groundRun kernel limits facts goal outputs
    | Set.null (getLVars facts) && Set.isSubsetOf (getLVars goal) (Set.fromList outputs) = runGoal kernel limits facts goal outputs
    | otherwise = return (Undecided "the query has a logic variable that is not an output")

-- Opt in once when loading a LoL host engine. Direct Hol clients keep the
-- specified rep L Ts report, and a historical kernel needs no extra fact.
diagnosticFacts :: Kernel -> [TermNode] -> [TermNode]
diagnosticFacts kernel facts
    | Map.member (DC_Named "report_descriptions") (kernelTypes kernel) = named "report_descriptions" : facts
    | otherwise = facts

runGoal :: Kernel -> Limits -> [TermNode] -> TermNode -> [LogicVar] -> IO Verdict
runGoal kernel limits facts goal outputs = hostVerdict limits $ do
    printed <- newIORef []
    outcome <- timeout (limitMicros limits) (try (run printed))
    reports <- readIORef printed
    return (verdictOf outputs reports (fmap (fmap (either (Left . describeFailure) id)) outcome))
    where
        run printed = do
            inferred <- inferGoalTypes (kernelFresh kernel) (kernelReady kernel) goal
            case inferred of
                Left failure -> return (Left failure)
                Right (typed, variables) -> withSessionFactsWithLimit (limitBytes limits) Native (kernelFresh kernel) (kernelReady kernel) (diagnosticFacts kernel facts) variables typed (runtimeConfig kernel printed) (firstAnswer kernel limits)

-- A ground run on the cached engine, which holds the kernel and the facts of
-- the environment `source`. `facts` are all the facts of that environment: they
-- are read only when the engine holds another environment and is built again.
-- An engine that cannot leave the run is dropped.
loadedRun :: Kernel -> Limits -> Maybe Stamp -> [TermNode] -> TermNode -> [LogicVar] -> IO Verdict
loadedRun kernel limits source facts goal outputs = hostVerdict limits (engineRun (kernelCache kernel) kernel limits source facts goal outputs)

-- The same on the engine that the oracle asks.
asideRun :: Kernel -> Limits -> Maybe Stamp -> [TermNode] -> TermNode -> [LogicVar] -> IO Verdict
asideRun kernel = engineRun (kernelAside kernel) kernel

engineRun :: MVar (Maybe Loaded) -> Kernel -> Limits -> Maybe Stamp -> [TermNode] -> TermNode -> [LogicVar] -> IO Verdict
engineRun cache kernel limits source facts goal outputs
    | not (Set.isSubsetOf (getLVars goal) (Set.fromList outputs)) = return (Undecided "the query has a logic variable that is not an output")
    | otherwise = withCache cache $ \acquire cached -> do
        synced <- sync acquire cached
        case synced of
            Left message -> return (Nothing, Undecided (describeFailure message))
            Right loaded -> do
                when (cache == kernelCache kernel) (prepareAside loaded)
                printed <- newIORef []
                limited <- Full.setEngineMemoryLimit (loadedEngine loaded) (limitBytes limits)
                outcome <- timeout (limitMicros limits) (try (run loaded printed limited))
                reports <- readIORef printed
                usable <- Full.leaveEngine (loadedEngine loaded)
                kept <- either (\_ -> Nothing <$ Full.closeEngine (loadedEngine loaded)) (\() -> return (Just loaded)) usable
                return (kept, verdictOf outputs reports (fmap (fmap (either (Left . describeFailure) id)) outcome))
    where
        run loaded printed limited = case limited of
            Left failure -> return (Left failure)
            Right () -> do
                inferred <- inferGoalTypes (kernelFresh kernel) (kernelReady kernel) goal
                case inferred of
                    Left failure -> return (Left failure)
                    Right (typed, variables) -> Full.withQuery (kernelFresh kernel) (runtimeConfig kernel printed) (loadedEngine loaded) variables typed (firstAnswer kernel limits)
        sync acquire cached = case cached of
            Just loaded@Loaded {}
                | loadedSource loaded == source -> return (Right loaded)
            _ -> do
                mapM_ (Full.closeEngine . loadedEngine) cached
                created <- acquire (Full.createEngineWithLimit (limitBytes limits) (kernelReady kernel))
                case created of
                    Left message -> return (Left message)
                    Right engine -> do
                        extended <- extendAll engine (diagnosticFacts kernel facts)
                        either (\message -> Left message <$ Full.closeEngine engine) (\() -> return (Right (Loaded engine source))) extended
        -- Prepare the independent oracle machine before borrowing the main
        -- engine for a query. Never wait for another dialogue's aside cache.
        prepareAside loaded = mask $ \restore -> do
            taken <- tryTakeMVar (kernelAside kernel)
            case taken of
                Nothing -> return ()
                Just current -> do
                    owned <- newIORef (map loadedEngine (maybe [] (: []) current))
                    let acquire = acquireOwnedEngine owned
                    let build = case current of
                            Just aside
                                | loadedSource aside == loadedSource loaded -> return current
                            _ -> do
                                mapM_ (Full.closeEngine . loadedEngine) current
                                forked <- acquire (Full.forkEngine (loadedEngine loaded))
                                return (either (const Nothing) (\engine -> Just (Loaded engine (loadedSource loaded))) forked)
                    next <- restore build `onException` (closeOwnedEngines owned `finally` putMVar (kernelAside kernel) Nothing)
                    putMVar (kernelAside kernel) next
        -- An environment is loaded in pieces, so that no fragment is large.
        extendAll engine remaining = case splitAt 512 remaining of
            ([], _) -> return (Right ())
            (piece, rest) -> Full.extendEngine engine piece >>= either (return . Left) (\() -> extendAll engine rest)

-- A long-lived proof never holds kernelCache while waiting for input. It
-- forks an idle program synchronized with the immutable declaration Env.
forkLoadedEngine :: Kernel -> Limits -> Maybe Stamp -> [TermNode] -> IO (Either Failure Full.Engine)
forkLoadedEngine kernel limits source = forkWithNames kernel limits source Nothing

-- Ground callers and proof callers share the cache lock and its ownership
-- rules. A proof entry carries the namespace for which its name facts hold.
forkWithNames :: Kernel -> Limits -> Maybe Stamp -> Maybe (Set.Set String) -> [TermNode] -> IO (Either Failure Full.Engine)
forkWithNames kernel limits source names facts = withCache (kernelCache kernel) $ \acquire cached -> do
    synchronized <- case cached of
        Just loaded
            | loadedSource loaded == source && namespace loaded == names -> return (Right loaded)
        _ -> do
            mapM_ (Full.closeEngine . loadedEngine) cached
            made <- acquire (Full.createEngineWithLimit (limitBytes limits) (kernelReady kernel))
            case made of
                Left failure -> return (Left failure)
                Right engine -> do
                    extended <- add engine (diagnosticFacts kernel facts) `onException` voidClose engine
                    either (\failure -> Left failure <$ Full.closeEngine engine) (\() -> return (Right (maybe (Loaded engine source) (PreparedProof engine source) names))) extended
    case synchronized of
        Left failure -> return (Nothing, Left failure)
        Right loaded -> do
            limited <- Full.setEngineMemoryLimit (loadedEngine loaded) (limitBytes limits)
            forked <- either (return . Left) (const (acquire (Full.forkEngine (loadedEngine loaded)))) limited
            return (Just loaded, forked)
    where
        namespace Loaded {} = Nothing
        namespace PreparedProof { loadedNames = visible } = Just visible
        voidClose engine = Full.closeEngine engine >> return ()
        add engine remaining = case splitAt 512 remaining of
            ([], _) -> return (Right ())
            (piece, rest) -> Full.extendEngine engine piece >>= either (return . Left) (\() -> add engine rest)

-- Qed adds a single immutable declaration. If another document has since
-- used this cache, its engine is left alone. A failed extension is discarded.
extendProofCache :: Kernel -> Maybe Stamp -> Stamp -> Set.Set String -> Set.Set String -> [TermNode] -> IO ()
extendProofCache kernel source next before after facts = withCache (kernelCache kernel) $ \_ cached -> case cached of
    Just loaded@PreparedProof {}
        | loadedSource loaded == source && loadedNames loaded == before && before `Set.isSubsetOf` after -> do
            result <- Full.extendEngine (loadedEngine loaded) facts
            case result of
                Right () -> return (Just loaded { loadedSource = Just next, loadedNames = after }, ())
                Left _ -> Full.closeEngine (loadedEngine loaded) >> return (Nothing, ())
    _ -> return (cached, ())

-- The environment `next` is `source` with the declaration that has `facts`:
-- an engine that holds `source` takes the facts and holds `next`.
loadedExtend :: Kernel -> Maybe Stamp -> Stamp -> [TermNode] -> IO ()
loadedExtend kernel source next facts = do
    mapM_ extend [kernelCache kernel, kernelAside kernel]
    mapM_ (\proposal -> loadedExtend proposal source next facts) (kernelElaborator kernel)
    where
        extend cache = withCache cache $ \_ cached -> case cached of
            Just loaded@Loaded {}
                | loadedSource loaded == source -> do
                    extended <- Full.extendEngine (loadedEngine loaded) facts
                    kept <- either (\_ -> Nothing <$ Full.closeEngine (loadedEngine loaded)) (\() -> return (Just loaded { loadedSource = Just next })) extended
                    return (kept, ())
            _ -> return (cached, ())

-- Track every engine acquired before publication, including a newly built
-- cache entry and a fork returned to the caller. The long action is unmasked;
-- acquiring and registering a resource is one masked operation.
acquireOwnedEngine :: IORef [Full.Engine] -> IO (Either Failure Full.Engine) -> IO (Either Failure Full.Engine)
acquireOwnedEngine owned action = mask_ $ do
    result <- action
    case result of
        Left _ -> return ()
        Right engine -> modifyIORef' owned (engine :)
    return result

closeOwnedEngines :: IORef [Full.Engine] -> IO ()
closeOwnedEngines owned = readIORef owned >>= close where
    close [] = return ()
    close (engine : rest) = void (Full.closeEngine engine) `finally` close rest

-- One caller at a time. An exception closes old and newly acquired engines.
withCache :: MVar (Maybe Loaded) -> ((IO (Either Failure Full.Engine) -> IO (Either Failure Full.Engine)) -> Maybe Loaded -> IO (Maybe Loaded, a)) -> IO a
withCache cache action = mask $ \restore -> do
    cached <- takeMVar cache
    owned <- newIORef (map loadedEngine (maybe [] (: []) cached))
    (next, result) <- restore (action (acquireOwnedEngine owned) cached) `onException` (closeOwnedEngines owned `finally` putMVar cache Nothing)
    putMVar cache next
    return result

-- The first answer is the answer.
firstAnswer :: Kernel -> Limits -> Full.Session -> IO (Either String (Maybe Context))
firstAnswer kernel limits session = do
    memory <- Full.setMemoryLimit session (limitBytes limits)
    work <- maybe (return (Right ())) (Full.setWorkLimit session) (limitVisits limits)
    let limited = memory >> work
    case limited of
        Left message -> return (Left (describeFailure message))
        Right () -> do
            answer <- Full.nextSolution session
            return $ case answer of
                Left failure -> Left (describeFailure failure)
                Right (Answer context) -> Right (Just context)
                Right NoAnswer -> Right Nothing
                Right (StepFailure _) -> Left "unexpected proof step in a ground query"

-- A run that did not end has no verdict, whatever it printed before: the
-- time limit, an exception and a failure of the engine come first. Of a run
-- that ended: the elaborator says where an implicit argument needs a
-- universe of its own (E-Refresh, elab.hol). Such a run counts as none,
-- with or without an answer: its verdict is the nodes that it named, and
-- the host reads the declaration again with a universe for each.
verdictOf :: [LogicVar] -> [TermNode] -> Maybe (Either IOException (Either String (Maybe Context))) -> Verdict
verdictOf outputs reports outcome = case outcome of
    Nothing -> Undecided "the time limit was reached"
    Just (Left exception) -> Undecided (show exception)
    Just (Right (Left message)) -> Undecided message
    Just (Right (Right _))
        | not (null refreshed) -> Rejected (Just (Report "E-Refresh" (concatMap reportArgs refreshed) (concatMap reportCore refreshed)))
    Just (Right (Right Nothing)) -> Rejected (listToMaybe (mapMaybe (either (const Nothing) Just . recoverReport) (reverse reports)))
    Just (Right (Right (Just ctx)))
        | not (null (_LeftConstraints ctx)) -> Undecided "the answer has a residual constraint"
        | otherwise -> either Undecided Admitted (outputsOf ctx outputs)
    where
        refreshed = [report | Right report <- map recoverReport (reverse reports), reportRule report == "E-Refresh"]

outputsOf :: Context -> [LogicVar] -> Either String [TermNode]
outputsOf _ [] = Right []
outputsOf ctx outputs = mapM outputValue (bindVars (_TotalVarBinding ctx) (map mkLVar outputs))

-- An output that still contains a logic variable does not admit.
outputOf :: Context -> LogicVar -> Either String TermNode
outputOf ctx output = outputValue (bindVars (_TotalVarBinding ctx) (mkLVar output))

outputValue :: TermNode -> Either String TermNode
outputValue term
    | Set.null (getLVars value) = Right value
    | otherwise = Left "the answer has a logic variable"
    where
        value = rewrite NF term

runtimeConfig :: Kernel -> IORef [TermNode] -> HostConfig
runtimeConfig kernel printed = defaultHostConfig
    { hostPrint = \_ ctx term -> do
        value <- evaluate (rewrite NF (bindVars (_TotalVarBinding ctx) term))
        modifyIORef' printed (value :)
    , hostOracle = \_ ctx question -> maybe (ioError (userError "the LoL oracle callback is not installed")) (\answer -> answer ctx question) (kernelAsked kernel)
    }

-- Release caches owned by a retired document/program. withOracle copies share
-- these cells, so the caller must first release all workers using that Kernel.
-- Program values themselves are ordinary Haskell data and live until GC.
closeKernel :: Kernel -> IO (Either Failure ())
closeKernel kernel = do
    results <- mapM close [kernelCache kernel, kernelAside kernel]
    elaborator <- maybe (return (Right ())) closeKernel (kernelElaborator kernel)
    return (sequence_ results >> elaborator)
    where
        close cache = withCache cache $ \_ current -> do
            outcomes <- mapM (Full.closeEngine . loadedEngine) current
            return (Nothing, sequence_ outcomes)
