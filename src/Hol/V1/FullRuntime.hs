module Hol.V1.FullRuntime where

import qualified Calc.Presburger.Internal as P
import Control.Concurrent.MVar
import Control.Exception (IOException, bracket, bracketOnError, evaluate, mask_, throwIO, try)
import Control.Monad
import Control.Monad.IO.Class
import Control.Monad.Trans.Class
import Control.Monad.Trans.Except
import Control.Monad.Trans.Reader (runReaderT)
import Control.Monad.Trans.State.Strict
import Data.Char (chr, ord)
import Data.Int
import Data.IORef
import Data.Maybe (isJust, mapMaybe)
import qualified Data.IntMap.Strict as IntMap
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.Word
import Hol.BETA.Arith (ArithStore)
import Hol.BETA.Constant
import Hol.BETA.Debugger
import Hol.BETA.Header
import Hol.BETA.HOPU
import Hol.BETA.Runtime hiding (Snapshot, snapshot, restore, beginStep, endStep)
import Hol.BETA.TermNode
import Hol.V1.FullBytecode
import Hol.V1.FullCompiler
import qualified Hol.V1.Services as Services
import qualified Hol.V2.Constraints as Constraints
import qualified X.HigherMachine as Native
import System.Mem.StableName (eqStableName, makeStableName)
import Z.Utils

-- A session is used sequentially. Native snapshots retain immutable host-state
-- tokens. Native identities use compact reversible allocation ranges; custom
-- allocators without ranges retain the per-identity fallback caches.
data Session
    = Session
        { sessionMachine       :: Native.Machine
        , sessionProgram       :: FullProgram
        , sessionEnvironment   :: RuntimeEnv
        , sessionDebugging     :: IORef Bool
        , sessionBridge        :: IORef Bridge
        , sessionConstraints   :: IORef (Map.Map Word64 [Constraint])
        , sessionPremises      :: IORef (Map.Map Word64 ArithStore)
        , sessionNextToken     :: IORef Word64
        , sessionStopped       :: IORef Bool
        , sessionRestored      :: IORef (Maybe VarBinding)
        , sessionRestoredView  :: IORef (Maybe Stack)
        , sessionWaiting       :: IORef Waiting
        , sessionStep          :: IORef (Maybe DebugEvent)
        , sessionDebugLabel    :: IORef (Maybe TermNode)
        , sessionLease         :: RuntimeLease
        , sessionClosed        :: IORef Bool
        , sessionOwnsMachine   :: Bool
        , sessionScopedView    :: IORef Bool
        , sessionCollections   :: IORef Word64
        , sessionUniqueFloor   :: Int
        , sessionInitialLabels :: Labeling
        , sessionViews         :: IORef (Map.Map Word64 HostView)
        , sessionCurrentView   :: IORef (Maybe HostView)
        , sessionStores        :: IORef (Map.Map Word64 Constraints.Store)
        , sessionPreparedStore :: IORef (Maybe (Word64, Constraints.Store))
        }
    deriving ()

-- What the machine waits for while a callback of the host runs. A machine
-- that waits for the reply of print, read or oracle is not replaced by a
-- snapshot, and what an oracle callback assigns are the edits of that call.
data Waiting
    = WaitingForNothing
    | WaitingForService
    | WaitingForOracle
    deriving (Eq)

data Bridge
    = Bridge
        { bridgeVariables      :: !(Map.Map Word64 LogicVar)
        , bridgeVariableWires  :: !(Map.Map LogicVar [Int64])
        , bridgeConstants      :: !(Map.Map Word64 Constant)
        , bridgeConstantWires  :: !(Map.Map Constant [Int64])
        , bridgeSymbols        :: !(IntMap.IntMap FullSymbol)
        , bridgeSymbolIndices  :: !(Map.Map String Int)
        , bridgeLabeling       :: !Labeling
        , bridgeTypeBinders    :: !(Map.Map MetaTVar MetaTVar)
        , bridgeIdentities     :: !(Map.Map Word64 Unique)
        , bridgeIdentityBlocks :: !(Map.Map Word64 UniqueBlock)
        , bridgeIdentityRanges :: !(IntMap.IntMap (Word64, Int))
        , bridgeNextIdentity   :: !Word64
        , bridgeQuerySlots     :: !Word64
        , bridgeUncertain      :: !Bool
        , bridgeMetadata       :: !(IntMap.IntMap NodeMetadata)
        , bridgeMetadataKeys   :: !(Map.Map (Maybe String, Maybe StoredType, Maybe ((Int, Int), (Int, Int))) Int)
        , bridgeTransientTypes :: !(Map.Map LogicVar Word64)
        }
    deriving ()

-- Values are already normalized substitutions. A reverse index names only
-- entries affected when a watched variable acquires a new value.
data HostView
    = HostView
        { hostViewBinding    :: !VarBinding
        , hostViewLabeling   :: !Labeling
        , hostViewDependents :: !(Map.Map LogicVar (Set.Set LogicVar))
        , hostViewChanged    :: !(Set.Set LogicVar)
        , hostViewRoots      :: !(Set.Set LogicVar)
        , hostViewTokens     :: !(Word64, Word64)
        }
    deriving ()

-- IORefs retain these records across services. Force their finite map roots
-- so a new cached label cannot keep the whole preceding Bridge alive.
strictLabeling :: Labeling -> Labeling
strictLabeling labeling = _ConLabel labeling `seq` _VarLabel labeling `seq` _ConTypes labeling `seq` _VarTypes labeling `seq` _NamedTypes labeling `seq` _TyVarKeys labeling `seq` _TypeEnv labeling `seq` _QueryOrder labeling `seq` _PreserveQueryWitnesses labeling `seq` labeling

makeHostView :: VarBinding -> Labeling -> HostView
makeHostView binding labeling = HostView binding (strictLabeling labeling) (Map.foldlWithKey' add Map.empty (unVarBinding binding)) (Map.keysSet (unVarBinding binding)) Set.empty (0, 0) where
    add known variable value = Set.foldl' (\index dependency -> Map.insertWith Set.union dependency (Set.singleton variable) index) known (getLVars value)

updateHostView :: VarBinding -> HostView -> HostView
updateHostView changed before
    | Map.null additions = before { hostViewChanged = Set.empty }
    | otherwise = before { hostViewBinding = VarBinding values, hostViewDependents = dependencies, hostViewChanged = affected }
    where
        additions = unVarBinding changed
        original = unVarBinding (hostViewBinding before)
        reverse = hostViewDependents before
        affected = Map.foldlWithKey' (\keys variable _ -> Set.union keys (Map.findWithDefault Set.empty variable reverse)) (Map.keysSet additions) additions
        replacements = Map.union additions (Map.map (bindVarsUnchecked changed) (Map.restrictKeys original affected))
        values = Map.union replacements original
        remove variable known
            | Set.null remaining = Nothing
            | otherwise = Just remaining
            where
                remaining = Set.delete variable known
        detached = Map.foldlWithKey' (\index variable value -> Set.foldl' (\current dependency -> Map.update (remove variable) dependency current) index (getLVars value)) reverse (Map.restrictKeys original affected)
        dependencies = Map.foldlWithKey' (\index variable value -> Set.foldl' (\current dependency -> Map.insertWith Set.union dependency (Set.singleton variable) current) index (getLVars value)) detached replacements

-- Event-local bindings are needed for this service, but need not become the
-- next immutable base. Native terms carry them to later events themselves.
retainHostView :: Bool -> (Word64, Word64) -> Set.Set LogicVar -> HostView -> HostView
retainHostView growing tokens roots view = view
    { hostViewBinding = VarBinding (Map.withoutKeys binding removed)
    , hostViewDependents = dependencies
    , hostViewChanged = Set.empty
    , hostViewRoots = roots
    , hostViewTokens = tokens
    }
    where
        binding = unVarBinding (hostViewBinding view)
        candidates = Set.union (hostViewChanged view) (if growing || tokens == hostViewTokens view then Set.empty else Set.difference (hostViewRoots view) roots)
        temporary variable = case variable of
            LV_ty_var _ -> False
            _ -> variable `Set.notMember` roots
        removed = Set.filter temporary candidates
        remove variable known
            | Set.null remaining = Nothing
            | otherwise = Just remaining
            where
                remaining = Set.delete variable known
        dependencies = Map.foldlWithKey' (\index variable value -> Set.foldl' (\current dependency -> Map.update (remove variable) dependency current) index (getLVars value)) (hostViewDependents view) (Map.restrictKeys binding removed)

data Snapshot
    = Snapshot
        { nativeSnapshot      :: Native.Snapshot
        , snapshotPending     :: VarBinding
        , snapshotNames       :: NameCache
        , snapshotStopped     :: Bool
        , snapshotStep        :: Maybe DebugEvent
        , snapshotDebugLabel  :: Maybe TermNode
        , snapshotView        :: Stack
        , snapshotConstraints :: Map.Map Word64 [Constraint]
        , snapshotPremises    :: Map.Map Word64 ArithStore
        , snapshotViews       :: Map.Map Word64 HostView
        , snapshotStores      :: Map.Map Word64 Constraints.Store
        }
    deriving ()

createSession :: RuntimeEnv -> IORef Bool -> FullProgram -> IO Session
createSession env debugging original = withRuntimeAccess env $ do
    let program = typedQueryProgram env original
    first <- either (ioError . userError) return (validateFullBytecode program >> fullUniqueFloor program)
    bracketOnError (claimRuntime env) (releaseRuntime env) $ \lease ->
        bracketOnError (Native.createMachine (fullWords program)) Native.closeMachine $ \machine -> do
            let slots = case fullSections (fullWords program) of
                    Right (_, rows, _, _, _, _) -> rows
                    Left _ -> []
                indices = Map.fromList [(symbolIdentity symbol, index) | (index, symbol) <- IntMap.toList (fullSymbols program)]
            openSession env debugging machine program slots indices 0 lease True first

createSessionWithLimit :: Word64 -> RuntimeEnv -> IORef Bool -> FullProgram -> IO (Either (Native.ErrorCode, String) Session)
createSessionWithLimit limit env debugging original = withRuntimeAccess env $ case validateFullBytecode program >> fullUniqueFloor program of
    Left message -> return (Left (Native.UsageError, message))
    Right first -> bracketOnError (claimRuntime env) (releaseRuntime env) $ \lease -> do
        created <- Native.createMachineWithLimit limit (fullWords program)
        case created of
            Left failure -> releaseRuntime env lease >> return (Left failure)
            Right machine -> bracketOnError (return machine) Native.closeMachine $ \owned -> do
                let slots = case fullSections (fullWords program) of
                        Right (_, rows, _, _, _, _) -> rows
                        Left _ -> []
                    indices = Map.fromList [(symbolIdentity symbol, index) | (index, symbol) <- IntMap.toList (fullSymbols program)]
                Right <$> openSession env debugging owned program slots indices 0 lease True first
    where
        program = typedQueryProgram env original

typedQueryProgram :: RuntimeEnv -> FullProgram -> FullProgram
typedQueryProgram env program
    | take 2 (fullWords program) == [0x484f4c31, 4] || not (Map.null extra) = withRuntimeMetadata (fullKindEnv program) (fullTypeEnv program) (fullQueryTypes program `Map.union` extra) program
    | otherwise = program
    where
        extra = Map.restrictKeys (_TypeInfo env) (Set.fromList (fullVariables program)) `Map.difference` fullQueryTypes program

-- The machine runs the query of `program`. Its query variables have the
-- identities from `base` on, and `indices` finds a symbol by its identity.
openSession :: RuntimeEnv -> IORef Bool -> Native.Machine -> FullProgram -> [[Int64]] -> Map.Map String Int -> Word64 -> RuntimeLease -> Bool -> Int -> IO Session
openSession env debugging machine program slots indices = openSessionWithMetadata env debugging machine program slots indices (Map.fromList [(storeMetadata info, index) | (index, info) <- IntMap.toList (fullMetadata program)])

openSessionWithMetadata :: RuntimeEnv -> IORef Bool -> Native.Machine -> FullProgram -> [[Int64]] -> Map.Map String Int -> Map.Map (Maybe String, Maybe StoredType, Maybe ((Int, Int), (Int, Int))) Int -> Word64 -> RuntimeLease -> Bool -> Int -> IO Session
openSessionWithMetadata env debugging machine program slots indices metadataIndices base lease owned first = do
    startRun env
    waiting <- newIORef WaitingForNothing
    let typedEnv = env { _TypeInfo = fullQueryTypes program `Map.union` _TypeInfo env }
        labeling = Labeling IntMap.empty IntMap.empty IntMap.empty IntMap.empty (Map.fromList [(name, ty) | (LV_Named name, ty) <- Map.toList (_TypeInfo typedEnv)]) IntMap.empty (_ProgramTypeEnv env) (Map.fromList (zip (fullVariables program) [0 ..])) False
        initial = strictLabeling (labelingWithRuntimeTypes typedEnv labeling)
        variables = Map.fromList (zip [base ..] (fullVariables program))
        wires = Map.fromList [(variable, [0, fromIntegral uid, 0, isType, meta]) | (uid, (variable, isType : meta : _)) <- zip [base ..] (zip (fullVariables program) slots)]
        frontier = base + fromIntegral (length (fullVariables program))
        bridge = Bridge variables wires Map.empty Map.empty (fullSymbols program) indices initial Map.empty Map.empty Map.empty IntMap.empty frontier frontier False (fullMetadata program) metadataIndices Map.empty
        serving kind action = bracket (readIORef waiting <* writeIORef waiting kind) (writeIORef waiting) (const action)
        protected = typedEnv
            { _PrintPrimitive = \ctx term -> serving WaitingForService (_PrintPrimitive env ctx term)
            , _ReadPrimitive = \ctx term -> serving WaitingForService (_ReadPrimitive env ctx term)
            , _OraclePrimitive = \ctx question -> serving WaitingForOracle (_OraclePrimitive env ctx question >>= evaluate)
            }
    Session machine program protected debugging <$> newIORef bridge <*> newIORef (Map.singleton 0 []) <*> newIORef (Map.singleton 0 emptyArithStore) <*> newIORef 1 <*> newIORef False <*> newIORef Nothing <*> newIORef Nothing <*> pure waiting <*> newIORef Nothing <*> newIORef Nothing <*> pure lease <*> newIORef False <*> pure owned <*> newIORef False <*> newIORef 0 <*> pure first <*> pure initial <*> newIORef (Map.singleton 0 (makeHostView mempty (bridgeLabeling bridge))) <*> newIORef Nothing <*> newIORef (Map.singleton 0 Constraints.empty) <*> newIORef Nothing

-- A machine that keeps its program: the facts given to it stay loaded, and
-- every query runs on them. It is used by one caller at a time.
data Engine
    = Engine
        { engineMachine :: Native.Machine
        , engineProgram :: IORef LoadedTables
        , engineAccess  :: MVar ()
        }
    deriving ()

createEngine :: PreparedProgram -> IO (Either String Engine)
createEngine prepared = case loadPreparedProgram prepared of
    Left message -> return (Left message)
    Right (program, tables) -> bracketOnError (Native.createMachine (fullWords program)) Native.closeMachine $ \machine -> do
        ready <- Native.leaveRun machine
        case ready of
            Left message -> Native.closeMachine machine >> return (Left message)
            Right () -> Right <$> (Engine machine <$> newIORef tables <*> newMVar ())

createEngineWithLimit :: Word64 -> PreparedProgram -> IO (Either (Native.ErrorCode, String) Engine)
createEngineWithLimit limit prepared = case loadPreparedProgram prepared of
    Left message -> return (Left (Native.UsageError, message))
    Right (program, tables) -> do
        created <- Native.createMachineWithLimit limit (fullWords program)
        case created of
            Left failure -> return (Left failure)
            Right machine -> do
                ready <- Native.leaveRun machine
                case ready of
                    Left message -> do
                        code <- Native.getErrorCode machine
                        Native.closeMachine machine
                        return (Left (either (const Native.InternalError) id code, message))
                    Right () -> Right <$> (Engine machine <$> newIORef tables <*> newMVar ())

-- A fresh idle machine shares the immutable program, not the active query.
forkEngine :: Engine -> IO (Either String Engine)
forkEngine engine = withEngine engine $ do
    tables <- readIORef (engineProgram engine)
    forked <- Native.forkMachine (engineMachine engine)
    case forked of
        Left message -> return (Left message)
        Right machine -> Right <$> (Engine machine <$> newIORef tables <*> newMVar ())

data ProgramMark
    = ProgramMark
        { markNative :: Native.ProgramMark
        , markTables :: LoadedTables
        }
    deriving ()

markProgram :: Engine -> IO (Either String ProgramMark)
markProgram engine = withEngine engine $ do
    tables <- readIORef (engineProgram engine)
    fmap (fmap (\native -> ProgramMark native tables)) (Native.markProgram (engineMachine engine))

truncateProgram :: Engine -> ProgramMark -> IO (Either String ())
truncateProgram engine saved = withEngine engine $ mask_ $ do
    result <- Native.truncateProgram (engineMachine engine) (markNative saved)
    case result of
        Left message -> return (Left message)
        Right () -> Right () <$ writeIORef (engineProgram engine) (markTables saved)

closeProgramMark :: ProgramMark -> IO ()
closeProgramMark = Native.closeProgramMark . markNative

closeEngine :: Engine -> IO ()
closeEngine engine = withEngine engine (Right <$> Native.closeMachine (engineMachine engine)) >>= either (ioError . userError) return

-- Reject overlapping engine operations; waiting here would deadlock a
-- callback that tried to start a second query on its own engine.
withEngine :: Engine -> IO (Either String a) -> IO (Either String a)
withEngine engine action = bracket (tryTakeMVar (engineAccess engine)) (mapM_ (putMVar (engineAccess engine))) $ \acquired -> case acquired of
    Nothing -> return (Left "Hol V1 engine is already in use")
    Just () -> action

-- The facts have no logic variable. A failure of the machine leaves the engine
-- unusable; a fact that does not compile leaves it as it was.
extendEngine :: Engine -> [TermNode] -> IO (Either String ())
extendEngine engine facts = withEngine engine $ mask_ $ do
    tables <- readIORef (engineProgram engine)
    case extendLoadedProgram tables facts >>= \extended -> validateLoadedFragment tables (fst extended) >> return extended of
        Left message -> return (Left message)
        Right (program, next) -> do
            loaded <- Native.extendProgram (engineMachine engine) (fullWords program)
            either (return . Left) (\() -> Right () <$ writeIORef (engineProgram engine) next) loaded

extendEngineEnvironment :: Engine -> KindEnv -> TypeEnv -> [TermNode] -> IO (Either String ())
extendEngineEnvironment engine kinds types facts = withEngine engine $ mask_ $ do
    tables <- readIORef (engineProgram engine)
    case extendLoadedEnvironment tables kinds types facts >>= \extended -> validateLoadedFragment tables (fst extended) >> return extended of
        Left message -> return (Left message)
        Right (program, next) -> do
            loaded <- Native.extendProgram (engineMachine engine) (fullWords program)
            case loaded of
                Left message -> return (Left message)
                Right () -> Right () <$ writeIORef (engineProgram engine) next

-- Runs a query on the program of the engine. The session is valid inside the
-- action only. Returning or unwinding expires the session, not the engine.
withQuery :: RuntimeEnv -> IORef Bool -> Engine -> Map.Map LogicVar (MonoType Int) -> TermNode -> (Session -> IO a) -> IO (Either String a)
withQuery = withQueryM

withQueryM :: MonadRuntime m => RuntimeEnv -> IORef Bool -> Engine -> Map.Map LogicVar (MonoType Int) -> TermNode -> (Session -> m a) -> m (Either String a)
withQueryM env debugging engine queryTypes query action = runtimeBracket (tryTakeMVar (engineAccess engine)) (mapM_ (putMVar (engineAccess engine))) $ \acquired -> case acquired of
    Nothing -> return (Left "Hol V1 engine is already in use")
    Just () -> withRuntimeAccess env run
    where
        run = do
            tables <- liftIO (readIORef (engineProgram engine))
            case queryLoadedProgram tables queryTypes query >>= \program -> validateLoadedFragment tables program >> ((,) program <$> loadedFragmentUniqueFloor tables program) of
                Left message -> return (Left message)
                Right (program, first) -> runtimeBracket (withRuntimeAccess env (bracketOnError (claimRuntime env) (releaseRuntime env) (start tables program first))) (either (const (return ())) expireSession) (either (return . Left) (fmap Right . action))
        machine = engineMachine engine
        start tables program first lease = do
            started <- Native.startQuery machine (fullWords program)
            frontier <- Native.uidFrontier machine
            case started >> frontier of
                Left message -> releaseRuntime env lease >> return (Left message)
                Right next -> do
                    let count = length (fullVariables program)
                        width = if take 1 (drop 1 (fullWords program)) >= [5] then 3 else 2
                        slots = take count (rows width (drop 8 (fullWords program)))
                    Right <$> openSessionWithMetadata env debugging machine program slots (fragmentIndices tables program) (fragmentMetadataIndices tables program) (next - fromIntegral count) lease False first
        rows width values = case splitAt width values of
            ([], _) -> []
            (row, rest) -> row : rows width rest

-- Ends the run of the last query and releases what it allocated. A failure
-- means that the engine is unusable.
leaveEngine :: Engine -> IO (Either String ())
leaveEngine engine = withEngine engine (Native.leaveRun (engineMachine engine))

closeSession :: Session -> IO ()
closeSession session = withRuntimeAccess (sessionEnvironment session) $ mask_ $ do
    closed <- readIORef (sessionClosed session)
    unless closed $ do
        phase <- runtimePhase <$> readIORef (_RuntimeControl (sessionEnvironment session))
        case phase of
            RuntimeHost -> do
                when (sessionOwnsMachine session) (Native.closeMachine (sessionMachine session))
                expireSession session
            _ -> ioError (userError "a session can be closed only between execution calls")

enableScopedExports :: Session -> IO (Either String ())
enableScopedExports session = do
    configured <- Native.setScopedExports (sessionMachine session) True
    case configured of
        Left message -> return (Left message)
        Right () -> writeIORef (sessionScopedView session) True >> return (Right ())

-- The debugger views of this session keep the current goal and, of its
-- hypotheses, those of these predicates. Nothing asks for complete views.
setDebugFocus :: Session -> Maybe [Constant] -> IO (Either String ())
setDebugFocus session focus = do
    interned <- runExceptT (mapM (internSymbol session . ConstantSymbol) (maybe [] id focus))
    case interned of
        Left _ -> return (Left "a predicate of the debugger focus could not be registered")
        Right symbols -> Native.setDebugFocus (sessionMachine session) (map fromIntegral symbols <$ focus)

enableTerminalAliases :: Session -> IO (Either String Session)
enableTerminalAliases session = do
    let slots = [index | (index, LV_Named _) <- zip [0 ..] (fullVariables (sessionProgram session))]
        preserve labeling = labeling { _PreserveQueryWitnesses = True }
        preserveView view = view { hostViewLabeling = preserve (hostViewLabeling view) }
    configured <- Native.setQueryWitnesses (sessionMachine session) slots
    case configured of
        Left message -> return (Left message)
        Right () -> do
            modifyIORef' (sessionBridge session) (\bridge -> bridge { bridgeLabeling = preserve (bridgeLabeling bridge) })
            modifyIORef' (sessionViews session) (Map.map preserveView)
            modifyIORef' (sessionCurrentView session) (fmap preserveView)
            return (Right (session { sessionInitialLabels = preserve (sessionInitialLabels session) }))

expireSession :: Session -> IO ()
expireSession session = mask_ $ do
    writeIORef (sessionClosed session) True
    let env = sessionEnvironment session
    lease <- runtimeLease <$> readIORef (_RuntimeControl env)
    when (lease == Just (sessionLease session)) $ do
        writeIORef (_StackRef env) []
        writeIORef (_PendingSubst env) mempty
        releaseRuntime env (sessionLease session)

sessionAccess :: Session -> IO (Either String a) -> IO (Either String a)
sessionAccess session action = do
    result <- try (withRuntimeAccess (sessionEnvironment session) (mask_ guarded))
    return (either (Left . show . (id :: IOException -> IOException)) id result)
    where
        guarded = do
            closed <- readIORef (sessionClosed session)
            if closed then return (Left "Hol V1 session is closed") else action

withSession :: RuntimeEnv -> IORef Bool -> FullProgram -> (Session -> IO a) -> IO a
withSession env debugging program action = withRuntimeAccess env (bracket (createSession env debugging program) closeSession action)

setWorkLimit :: Session -> Word64 -> IO (Either String ())
setWorkLimit session limit = sessionAccess session (Native.setWorkLimit (sessionMachine session) limit)

setMemoryLimit :: Session -> Word64 -> IO (Either String ())
setMemoryLimit session limit = sessionAccess session (Native.setMemoryLimit (sessionMachine session) limit)

getMemoryLimit :: Session -> IO (Either String Word64)
getMemoryLimit session = sessionAccess session (Native.getMemoryLimit (sessionMachine session))

getWorkLimit :: Session -> IO (Either String Word64)
getWorkLimit session = sessionAccess session (Native.getWorkLimit (sessionMachine session))

-- A host starts a proof step at an exposed state. Its failure identifies that
-- state, not the transient branch that the native search has already rejected.
beginStep :: Session -> IO (Either String StepId)
beginStep session = sessionAccess session $ do
    let env = sessionEnvironment session
    allowed <- (>>) <$> runtimeCanControl env <*> runtimeCanResume env
    phase <- runtimePhase <$> readIORef (_RuntimeControl env)
    saved <- readIORef (sessionStep session)
    stack <- exposedView session
    case (allowed, phase, saved, stack) of
        (Left message, _, _, _) -> return (Left message)
        (_, RuntimeStepFailure, _, _) -> return (Left "a failed proof state must be restored before starting a step")
        (_, _, Just _, _) -> return (Left "a proof step is already active")
        (_, _, _, []) -> return (Left "a proof step requires an exposed state")
        (_, _, _, (ctx, cells) : alternatives) -> do
            fresh <- nextStepId env
            case fresh of
                Left message -> return (Left message)
                Right step@(StepId identity) -> do
                    started <- Native.beginStep (sessionMachine session) identity
                    case started of
                        Left message -> return (Left message)
                        Right () -> do
                            verbose <- readIORef (_VerboseTyping env)
                            pending <- readIORef (_PendingSubst env)
                            let viewed = map (\(context, goals) -> (zonkLVar pending context, map (zonkLVar pending) goals)) stack
                                shown = zonkLVar pending ctx
                                free = Set.fromList (fullVariables (sessionProgram session))
                                text = showsCurrentState (_NotationDB env) (_ProgramKindEnv env) verbose free (_TypeInfo env) shown (map (zonkLVar pending) cells) alternatives ""
                            writeIORef (sessionStep session) (Just (DebugEvent (StepFailed step) shown viewed text))
                            return (Right step)

-- Ending a failed step is the explicit permission to try the older search.
endStep :: Session -> StepId -> IO (Either String ())
endStep session step@(StepId identity) = sessionAccess session $ do
    let env = sessionEnvironment session
    allowed <- (>>) <$> runtimeCanControl env <*> runtimeCanResume env
    quit <- runtimeQuit <$> readIORef (_RuntimeControl env)
    saved <- readIORef (sessionStep session)
    case (allowed, fmap debugReason saved) of
        (Left message, _) -> return (Left message)
        _
            | quit -> fmap (>> Left "proof-step identity does not match the active step") (abandonStep session)
        (_, Just (StepFailed active))
            | active == step -> do
                ended <- Native.endStep (sessionMachine session) identity
                case ended of
                    Left message -> return (Left message)
                    Right () -> do
                        writeIORef (sessionStep session) Nothing
                        writeIORef (sessionStopped session) False
                        modifyIORef' (_RuntimeControl env) (\control -> control { runtimeStep = Nothing })
                        return (Right ())
        _ -> return (Left "proof-step identity does not match the active step")

-- Quitting cancels the run. Clearing its fence must not also resume the
-- alternatives that fence protected; only a saved snapshot can revive it.
abandonStep :: Session -> IO (Either String ())
abandonStep session = sessionAccess session $ do
    allowed <- runtimeCanControl (sessionEnvironment session)
    case allowed of
        Left message -> return (Left message)
        Right () -> abandonStepActive session

abandonStepActive :: Session -> IO (Either String ())
abandonStepActive session = mask_ $ do
    saved <- readIORef (sessionStep session)
    ended <- case fmap debugReason saved of
        Just (StepFailed (StepId identity)) -> Native.endStep (sessionMachine session) identity
        _ -> return (Right ())
    case ended of
        Left message -> return (Left message)
        Right () -> do
            writeIORef (sessionStep session) Nothing
            writeIORef (sessionDebugLabel session) Nothing
            writeIORef (sessionStopped session) True
            writeIORef (sessionRestored session) Nothing
            let env = sessionEnvironment session
            writeIORef (_StackRef env) []
            writeIORef (_PendingSubst env) mempty
            modifyIORef' (_RuntimeControl env) (\control -> control { runtimeQuit = True, runtimeStep = Nothing })
            return (Right ())

takeSnapshot :: Session -> IO (Either String Snapshot)
takeSnapshot session = sessionAccess session $ do
    allowed <- runtimeCanSnapshot (sessionEnvironment session)
    case allowed of
        Left message -> return (Left message)
        Right () -> captureSnapshot session

captureSnapshot :: Session -> IO (Either String Snapshot)
captureSnapshot session = mask_ $ do
    quit <- runtimeQuit <$> readIORef (_RuntimeControl (sessionEnvironment session))
    -- A snapshot taken by the callback after cmdQuit already records the
    -- cancellation, even though the callback has not returned yet.
    cancelled <- if quit then abandonStep session else return (Right ())
    case cancelled of
        Left message -> return (Left message)
        Right () -> do
            pruned <- pruneHostTokens session True
            captured <- case pruned of
                Left message -> return (Left message)
                Right () -> Native.takeSnapshot (sessionMachine session)
            waiting <- readIORef (sessionWaiting session)
            -- Oracle edits belong to its reply, not the execution snapshot.
            pending <- if waiting == WaitingForOracle then return mempty else readIORef (_PendingSubst (sessionEnvironment session))
            names <- readIORef (_NameCacheRef (sessionEnvironment session))
            stopped <- readIORef (sessionStopped session)
            step <- readIORef (sessionStep session)
            label <- readIORef (sessionDebugLabel session)
            view <- exposedView session
            constraints <- readIORef (sessionConstraints session)
            premises <- readIORef (sessionPremises session)
            views <- readIORef (sessionViews session)
            stores <- readIORef (sessionStores session)
            return ((\native -> Snapshot native pending names stopped step label view constraints premises views stores) <$> captured)

-- The machine is the one of the snapshot afterwards. What the host saw of
-- the machine that is gone is no state of this one: the stack reference is
-- emptied, and the stop inside whose callback the snapshot was restored
-- gets no reply (`replaced`). A snapshot has the event that was pending
-- when it was taken: the next `nextSolution` reports it again. Inside the
-- callback of print, read or oracle the machine waits for the reply of that
-- callback, and is not replaced.
restoreSnapshot :: Session -> Snapshot -> IO (Either String ())
restoreSnapshot = restoreSnapshotUsing Native.restoreSnapshot

-- On success the native snapshot capability is consumed. Its immutable host
-- payload is installed before the masked operation returns; failed validation
-- or native preflight leaves the snapshot and current session unchanged.
restoreSnapshotConsuming :: Session -> Snapshot -> IO (Either String ())
restoreSnapshotConsuming = restoreSnapshotUsing Native.restoreSnapshotConsuming

restoreSnapshotUsing :: (Native.Machine -> Native.Snapshot -> IO (Either String ())) -> Session -> Snapshot -> IO (Either String ())
restoreSnapshotUsing restoreNative session saved = sessionAccess session $ mask_ $ do
    waiting <- readIORef (sessionWaiting session)
    allowed <- runtimeCanControl (sessionEnvironment session)
    restored <- case allowed of
        Left message -> return (Left message)
        Right () -> if waiting == WaitingForNothing then restoreNative (sessionMachine session) (nativeSnapshot saved) else return (Left "a snapshot cannot be restored inside the callback of print, read or oracle: the machine waits for its reply")
    case restored of
        Left message -> return (Left message)
        Right () -> do
            let env = sessionEnvironment session
            modifyIORef' (sessionBridge session) releaseImportedTypes
            writeIORef (_PendingSubst env) (snapshotPending saved)
            modifyIORef' (_NameCacheRef env) (mergeKeepingNewEntries (snapshotNames saved))
            writeIORef (sessionConstraints session) (snapshotConstraints saved)
            writeIORef (sessionPremises session) (snapshotPremises saved)
            writeIORef (sessionViews session) (snapshotViews saved)
            writeIORef (sessionStores session) (snapshotStores saved)
            writeIORef (sessionPreparedStore session) Nothing
            writeIORef (sessionStopped session) (snapshotStopped saved)
            writeIORef (sessionStep session) (snapshotStep saved)
            writeIORef (sessionDebugLabel session) (snapshotDebugLabel saved)
            writeIORef (_StackRef env) []
            writeIORef (sessionRestoredView session) (Just (snapshotView saved))
            writeIORef (sessionRestored session) (Just (snapshotPending saved))
            modifyIORef' (_RuntimeControl env) $ \control -> control
                { runtimeQuit = False
                , runtimeInterrupted = False
                , runtimeStep = failureBoundary (snapshotStopped saved) (snapshotStep saved)
                , runtimeRestores = runtimeRestores control + 1
                , runtimePhase = case runtimePhase control of
                    RuntimeStepFailure -> RuntimeDebugger
                    phase -> phase
                }
            return (Right ())

-- Native collection drops abandoned branches. Host tokens follow the same
-- live choice/frame roots; each saved snapshot owns its persistent maps.
-- The arena scan is performed only after collection or before capture.
pruneHostTokens :: Session -> Bool -> IO (Either String ())
pruneHostTokens session force = do
    modifyIORef' (sessionBridge session) releaseImportedTypes
    next <- readIORef (sessionNextToken session)
    scoped <- readIORef (sessionScopedView session)
    if next == 1 && not scoped && not force then return (Right ()) else pruneIssuedTokens session force

-- A legacy session has only the permanent token zero until its first host
-- obligation. Scoped sessions also prune variable identities at collections.
pruneIssuedTokens :: Session -> Bool -> IO (Either String ())
pruneIssuedTokens session force = do
    retired <- Native.drainRetiredTokens (sessionMachine session)
    case retired of
        Left message -> return (Left message)
        Right (states, views) -> do
            modifyIORef' (sessionConstraints session) (\values -> foldr Map.delete values states)
            modifyIORef' (sessionStores session) (\values -> foldr Map.delete values states)
            modifyIORef' (sessionViews session) (\values -> foldr Map.delete values views)
            pruneCollectedTokens session force

-- A fresh host type variable has the same reversible identity range as a
-- native variable. Its raw wire is needed only until the reply imports it;
-- subsequent encoding consults the live native identity and rejects expiry.
releaseImportedTypes :: Bridge -> Bridge
releaseImportedTypes bridge = bridge
    { bridgeVariables = Map.foldl' (flip Map.delete) (bridgeVariables bridge) (bridgeTransientTypes bridge)
    , bridgeVariableWires = Map.withoutKeys (bridgeVariableWires bridge) (Map.keysSet (bridgeTransientTypes bridge))
    , bridgeTransientTypes = Map.empty
    }

pruneCollectedTokens :: Session -> Bool -> IO (Either String ())
pruneCollectedTokens session force = do
    generation <- Native.collections (sessionMachine session)
    previous <- readIORef (sessionCollections session)
    case generation of
        Left message -> return (Left message)
        Right current
            | not force && current == previous -> return (Right ())
            | otherwise -> do
                roots <- Native.liveTokens (sessionMachine session)
                case roots of
                    Left message -> return (Left message)
                    Right (states, premises) -> do
                        scoped <- readIORef (sessionScopedView session)
                        views <- if scoped then Native.liveViewTokens (sessionMachine session) else return (Right [])
                        identities <- if scoped && current /= previous then Native.getLiveIdentities (sessionMachine session) else return (Right [])
                        case (views, identities) of
                            (Left message, _) -> return (Left message)
                            (_, Left message) -> return (Left message)
                            (Right liveViews, Right liveIdentities) -> do
                                modifyIORef' (sessionConstraints session) (\values -> Map.restrictKeys values (Set.fromList (0 : states)))
                                modifyIORef' (sessionStores session) (\values -> Map.restrictKeys values (Set.fromList (0 : states)))
                                modifyIORef' (sessionPremises session) (\values -> Map.restrictKeys values (Set.fromList (0 : premises)))
                                when scoped $ do
                                    bridge <- readIORef (sessionBridge session)
                                    let retained = Set.fromList liveIdentities
                                        keep variable = maybe True (`Set.member` retained) (hostIdentity bridge variable)
                                        keepKey key = maybe True (`Set.member` retained) (nativeIdentity bridge (Unique key))
                                        labels labeling = labeling
                                            { _ConLabel = IntMap.filterWithKey (\key _ -> keepKey key) (_ConLabel labeling)
                                            , _VarLabel = IntMap.filterWithKey (\key _ -> keepKey key) (_VarLabel labeling)
                                            , _ConTypes = IntMap.filterWithKey (\key _ -> keepKey key) (_ConTypes labeling)
                                            , _VarTypes = IntMap.filterWithKey (\key _ -> keepKey key) (_VarTypes labeling)
                                            , _TyVarKeys = IntMap.filterWithKey (\key _ -> keepKey key) (_TyVarKeys labeling)
                                            }
                                        trim view = (makeHostView (VarBinding (Map.filterWithKey (\variable _ -> keep variable) (unVarBinding (hostViewBinding view)))) (labels (hostViewLabeling view))) { hostViewRoots = hostViewRoots view, hostViewTokens = hostViewTokens view }
                                    modifyIORef' (sessionViews session) (\values -> (if current /= previous then Map.map trim else id) (Map.restrictKeys values (Set.fromList (0 : liveViews))))
                                writeIORef (sessionCollections session) current
                                return (Right ())

-- A restored presentation is visible to V2 inspection and step setup before
-- the native event is reported again. The V1 raw stack remains empty, keeping
-- stale legacy assignments from acting on the callback that was replaced.
exposedView :: Session -> IO Stack
exposedView session = readIORef (sessionRestoredView session) >>= maybe (fst <$> runtimeView (sessionEnvironment session)) return

-- Proof presentation omits unrelated query outputs. Assignment is an explicit
-- request to inspect a variable, so validate it against the complete active
-- Context even when that variable is not in the displayed goals. Exact native
-- declarations can supply the same evidence without decoding discarded frame
-- terms. Binder-dependent or missing evidence keeps the complete legacy view.
debugAssignmentView :: UniqueM m => Session -> LogicVar -> ExceptT KernelErr m (Maybe Stack)
debugAssignmentView session target = do
    frames <- liftIO (exposedView session)
    pending <- liftIO (readIORef (_PendingSubst (sessionEnvironment session)))
    case frames of
        [] -> return (Just [])
        (context, cells) : _
            | not (assignmentTargetIsKnown (sessionEnvironment session) context cells pending target) -> return Nothing
        (context, cells) : rest -> do
            extra <- hostRootIdentities session (concatMap constraintTerms (_LeftConstraints context))
            bridge <- liftIO (readIORef (sessionBridge session))
            let targeted = maybe extra (: extra) (hostIdentity bridge target)
            selected <- fetched session (\machine -> Native.fetchAssignmentViewWith machine targeted)
            view <- maybe (fetched session (\machine -> Native.fetchViewWith machine targeted)) return selected
            (binding, disagreements) <- decodeState session (Native.viewState view)
            void (decodeRoots session (Native.viewDeclarations view))
            void (decodeFrames session (Native.viewFrames view))
            void (decodeHypotheses session (Native.viewHypotheses view))
            labeling <- liftIO (bridgeLabeling <$> readIORef (sessionBridge session))
            let otherConstraints =
                    [ constraint
                    | constraint <- _LeftConstraints context
                    , case constraint of
                        DisagreementConstraint _ -> False
                        _ -> True
                    ]
                complete = context
                    { _TotalVarBinding = binding
                    , _CurrentLabeling = refineBindingTypes (sessionEnvironment session) binding labeling
                    , _LeftConstraints = map DisagreementConstraint disagreements ++ otherConstraints
                    }
            return (Just ((complete, cells) : rest))

-- The reference interpreter's read-only failure view is also used by native
-- sessions. The native choice-point fence itself remains in the C machine.
failureBoundary :: Bool -> Maybe DebugEvent -> Maybe StepBoundary
failureBoundary failed event = case event of
    Just saved
        | failed, StepFailed key <- debugReason saved -> Just (StepBoundary key 0 saved mempty True True True)
    _ -> Nothing

-- Whether the callback of a stop restored a snapshot. The stop belonged to
-- the machine that is gone, so it gets no reply: the host state and the
-- premises of that event are not those of the machine that is there now.
-- Its pending assignments are those of the snapshot, whatever the callback
-- left.
replaced :: MonadIO m => Session -> m Bool
replaced session = liftIO $ do
    restored <- readIORef (sessionRestored session)
    case restored of
        Nothing -> return False
        Just pending -> do
            writeIORef (_PendingSubst (sessionEnvironment session)) pending
            writeIORef (sessionRestored session) Nothing
            return True

closeSnapshot :: Snapshot -> IO ()
closeSnapshot = Native.closeSnapshot . nativeSnapshot

runFullProgram :: UniqueM m => RuntimeEnv -> IORef Bool -> FullProgram -> ExceptT KernelErr m Satisfied
runFullProgram = runFullProgramWithLimit 0

runFullProgramWithLimit :: UniqueM m => Word64 -> RuntimeEnv -> IORef Bool -> FullProgram -> ExceptT KernelErr m Satisfied
runFullProgramWithLimit = runProgramWithPolicy False

runTerminalProgramWithLimit :: UniqueM m => Word64 -> RuntimeEnv -> IORef Bool -> FullProgram -> ExceptT KernelErr m Satisfied
runTerminalProgramWithLimit = runProgramWithPolicy True

runProgramWithPolicy :: UniqueM m => Bool -> Word64 -> RuntimeEnv -> IORef Bool -> FullProgram -> ExceptT KernelErr m Satisfied
runProgramWithPolicy terminal limit env debugging program = withRuntimeAccess env $ runtimeBracket acquire (either (const (return ())) closeSession) $ \opened -> do
    session <- either (throwE . BackendError . message) return opened
    runtimeBracketOutcome (return ()) (\_ finished -> unless finished (markRuntimeInterrupted env)) (const (loop session))
    where
        acquire = do
            result <- try (createSessionWithLimit limit env debugging program) :: IO (Either IOException (Either (Native.ErrorCode, String) Session))
            case either (Left . (\exception -> (Native.InternalError, show exception))) id result of
                Right session
                    | terminal -> do
                        configured <- enableTerminalAliases session
                        case configured of
                            Left failure -> closeSession session >> return (Left (Native.InternalError, failure))
                            Right ready -> return (Right ready)
                opened -> return opened
        message (code, text) = case code of
            Native.MemoryLimitError -> "Native memory limit exceeded"
            Native.WorkLimitError -> "Native term work limit exceeded"
            _ -> text
        loop session = do
            answer <- nextSolution session
            case answer of
                Nothing -> return False
                Just ctx -> do
                    more <- liftIO (withRuntimePhase env RuntimeService (_Answer env ctx))
                    if more then loop session else return True

nativeResult :: Monad m => Either String a -> ExceptT KernelErr m a
nativeResult = either (throwE . BackendError) return

nextSolution :: UniqueM m => Session -> ExceptT KernelErr m (Maybe Context)
nextSolution session = do
    closed <- liftIO (readIORef (sessionClosed session))
    when closed (throwE (BackendError "Hol V1 session is closed"))
    withRuntimeExecution env (Just (sessionLease session)) $ do
        liftIO (runtimeCanResume env) >>= nativeResult
        outcome <- lift (runExceptT (nextSolutionReady session))
        case outcome of
            Left failure -> liftIO (interruptSession session) >> throwE failure
            Right answer -> return answer
    where
        env = sessionEnvironment session

interruptSession :: Session -> IO ()
interruptSession = markRuntimeInterrupted . sessionEnvironment

nextSolutionReady :: UniqueM m => Session -> ExceptT KernelErr m (Maybe Context)
nextSolutionReady session = do
    quit <- liftIO (runtimeQuit <$> readIORef (_RuntimeControl (sessionEnvironment session)))
    when quit (liftIO (abandonStepActive session) >>= nativeResult)
    stopped <- liftIO (readIORef (sessionStopped session))
    if stopped then return Nothing else nextSolutionActive session

nextSolutionActive :: UniqueM m => Session -> ExceptT KernelErr m (Maybe Context)
nextSolutionActive session = do
    liftIO (writeIORef (sessionRestored session) Nothing)
    liftIO (writeIORef (sessionRestoredView session) Nothing)
    liftIO (writeIORef (sessionCurrentView session) Nothing)
    liftIO (writeIORef (sessionPreparedStore session) Nothing)
    applyPending session
    debugging <- liftIO (readIORef (sessionDebugging session))
    event <- liftIO (Native.nextEventWithDebugging machine debugging)
    result <- case event of
        Right step -> return step
        Left message -> do
            code <- liftIO (Native.getErrorCode machine) >>= nativeResult
            case code of
                Native.InvalidGoalError -> logicalFailure BadGoalGiven
                Native.InvalidFactError -> logicalFailure BadFactGiven
                _ -> throwE (BackendError message)
    liftIO (pruneHostTokens session False) >>= nativeResult
    case result of
        Native.Exhausted -> do
            liftIO (writeIORef (_StackRef env) [])
            return Nothing
        Native.Answer token _ _ -> do
            reserveIdentities session
            pending <- fetched session Native.pendingCount
            scoped <- liftIO (readIORef (sessionScopedView session))
            (binding, disagreements) <- if scoped then do
                constraints <- lookupToken "host state" (sessionConstraints session) token
                extra <- hostRootIdentities session (concatMap constraintTerms constraints)
                view <- fetched session (\native -> Native.fetchViewWith native extra)
                decoded <- decodeState session (Native.viewState view)
                void (decodeRoots session (Native.viewDeclarations view))
                return decoded
            else if debugging || token /= 0 || pending /= 0 then completeState session else do
                reduced <- rootState session True (return ())
                maybe (completeState session) (return . fst) reduced
            ctx <- currentContext session token 0 binding disagreements
            liftIO (writeIORef (_StackRef env) [(ctx, [])])
            return (Just ctx)
        Native.Request request
            | Native.requestKind request == 6 -> do
                saved <- liftIO (readIORef (sessionStep session))
                event <- case saved of
                    Just stopped
                        | StepFailed (StepId identity) <- debugReason stopped
                        , identity == fromIntegral (Native.requestAuxiliary request) -> return stopped
                    _ -> throwE (BackendError "native proof-step failure has no matching host boundary")
                liftIO $ do
                    writeIORef (_StackRef env) (debugStack event)
                    modifyIORef' (_RuntimeControl env) (\control -> control { runtimeStep = failureBoundary True (Just event) })
                    withRuntimePhase env RuntimeStepFailure (_Debugger env env event)
                cancelled <- liftIO (runtimeQuit <$> readIORef (_RuntimeControl env))
                restored <- if cancelled then return False else replaced session
                active <- liftIO (readIORef (sessionStep session))
                quit <- liftIO (null <$> readIORef (_StackRef env))
                if cancelled || not restored && quit then do
                    liftIO (abandonStepActive session) >>= nativeResult
                    return Nothing
                else if restored || maybe True (const False) active then nextSolutionReady session else do
                    liftIO (writeIORef (_StackRef env) [])
                    liftIO (writeIORef (sessionStopped session) True)
                    return Nothing
            | Native.requestKind request == 4 -> do
                reserveIdentities session
                (binding, disagreements, _, cells) <- completeRequest session request
                ctx <- currentContext session (Native.requestHostState request) (Native.requestCallId request) binding disagreements
                continue <- debugInteraction session ctx cells
                cancelled <- liftIO (runtimeQuit <$> readIORef (_RuntimeControl env))
                restored <- if cancelled then return False else replaced session
                if cancelled then do
                    liftIO (abandonStepActive session) >>= nativeResult
                    return Nothing
                else if restored then
                    nextSolutionReady session
                else if continue then do
                    applyPending session
                    liftIO (Native.resume machine 1 (Native.requestHostState request) (Native.requestPremises request) [0]) >>= nativeResult
                    nextSolutionReady session
                else do
                    liftIO (Native.resume machine 0 (Native.requestHostState request) (Native.requestPremises request) [0]) >>= nativeResult
                    liftIO (abandonStepActive session) >>= nativeResult
                    return Nothing
            | otherwise -> do
                reserveIdentities session
                (binding, disagreements, roots) <- requestState debugging request
                ctx <- currentContext session (Native.requestHostState request) (Native.requestCallId request) binding disagreements
                premises <- lookupToken "arithmetic premise" (sessionPremises session) (Native.requestPremises request)
                reply <- dispatch request roots premises ctx (null disagreements)
                installReply session request ctx reply
                nextSolutionReady session
    where
        logicalFailure constructor = do
            reserveIdentities session
            roots <- fetched session Native.fetchFailure >>= decodeRoots session
            case roots of
                [term] -> throwE (constructor term)
                _ -> throwE (BackendError "native logical failure has no offending term")
        machine = sessionMachine session
        env = sessionEnvironment session
        -- An antecedent contributes premises from its own term, and an
        -- equality that mentions no arithmetic is left to the native search:
        -- neither reply consults a binding, a label or a disagreement.
        requestState debugging request = do
            scoped <- liftIO (readIORef (sessionScopedView session))
            if scoped then do
                symbols <- liftIO (bridgeSymbols <$> readIORef (sessionBridge session))
                if requestNeedsCallbackContext symbols (Native.requestTerms request) then do
                    liftIO (writeIORef (sessionCurrentView session) Nothing)
                    completeRequest session request >>= \(binding, disagreements, terms, _) -> return (binding, disagreements, terms)
                else serviceDelta session request
            else legacyState debugging request
        legacyState debugging request = case Native.requestKind request of
            1 -> stateWithRoots
            3 -> termsOnly
            5 -> do
                (_, _, roots) <- termsOnly
                case roots of
                    [goal]
                        | not (Services.equalityUsesArithmetic (snd (unfoldlNApp goal))) -> return (mempty, [], roots)
                    _ -> stateWithRoots
            _ -> stateWithRoots
            where
                reducible = not debugging && Native.requestHostState request == 0 && Native.requestPremises request == 0
                termsOnly = do
                    resetLabeling session
                    roots <- decodeRoots session (Native.requestTerms request)
                    return (mempty, [], roots)
                stateWithRoots = if reducible then rootState session False (decodeRoots session (Native.requestTerms request)) >>= maybe complete acceptReduced else complete
                acceptReduced ((binding, disagreements), roots)
                    | Native.requestKind request == 1 && any callsUserCallback roots = complete
                    | otherwise = return (binding, disagreements, roots)
                complete = (\(binding, disagreements, roots, _) -> (binding, disagreements, roots)) <$> completeRequest session request
        -- `read` and `print` give their callbacks the complete Context. The
        -- callback of `oracle` gets a question, which is made of what the
        -- stop decodes: the term, the hypotheses and the disagreements. So
        -- the complete state, whose size grows with the whole run, is not
        -- decoded for it.
        callsUserCallback goal = case fst (unfoldlNApp goal) of
            NCon constant _ -> callsUserCallbackConstant constant
            _ -> False
        dispatch request roots premises ctx clear = case (Native.requestKind request, roots) of
            (2, []) -> incrementalService session request clear premises ctx Services.Settle
            (3, [fact]) -> Services.runService env premises ctx (Services.AssumePremises fact)
            (5, [goal]) -> do
                let args = snd (unfoldlNApp goal)
                defined <- Services.runService env premises ctx (Services.EqualityDefinitions args)
                case defined of
                    Services.ServiceContinue next active -> Services.runService env active next (Services.EqualityDecision args)
                    Services.ServiceFailure -> return Services.ServiceReject
                    other -> return other
            (1, [goal]) -> case unfoldlNApp goal of
                (NCon (DC (DC_LO LO_is)) _, [lhs, rhs]) -> incrementalService session request clear premises ctx (Services.Evaluate lhs rhs)
                (NCon (DC (DC_LO LO_debug)) _, [label]) -> Services.runService env premises ctx (Services.Debug label)
                (NCon (DC (DC_Named "print")) _, args) -> Services.runService env premises ctx (Services.Print args)
                (NCon (DC (DC_Named "read")) _, args) -> Services.runService env premises ctx (Services.Read args)
                (NCon (DC (DC_Named "oracle")) _, args) -> do
                    (level, hyps) <- fetched session Native.fetchHypotheses >>= decodeHypotheses session
                    bridge <- liftIO (readIORef (sessionBridge session))
                    Services.runService env premises ctx { _CurrentLabeling = refineBindingTypes env (_TotalVarBinding ctx) (bridgeLabeling bridge) } (Services.Oracle args level hyps (inspectOracle request premises) (interruptSession session))
                (NCon predicate _, args) -> withExceptT (goalLocation ctx goal) (incrementalService session request clear premises ctx (Services.Compare predicate args))
                (NPresburgerCheck rep freeOf _, []) -> Services.runService env premises ctx (Services.Presburger rep freeOf)
                _ -> throwE (BadGoalGiven goal)
            _ -> throwE (BackendError "invalid native service request")
        inspectOracle request premises = do
            -- Native identities were reserved before the callback. Anonymous
            -- lexical type binders use the retained host supply separately.
            exhausted <- newIORef maxBound
            inspected <- runReaderT (runUniqueT (runExceptT inspect)) exhausted
            either (\failure -> ioError (userError (failureMessage failure))) return inspected
            where
                failureMessage failure = case failure of
                    BackendError message -> message
                    _ -> "invalid oracle inspection"
                inspect = do
                    scoped <- liftIO (readIORef (sessionScopedView session))
                    (binding, disagreements, roots) <- if scoped then do
                        (binding, disagreements, roots, _) <- completeRequest session request
                        return (binding, disagreements, roots)
                    else do
                        (binding, disagreements) <- completeState session
                        roots <- decodeRoots session (Native.requestTerms request)
                        return (binding, disagreements, roots)
                    cells <- fetched session Native.fetchFrames >>= decodeFrames session
                    (level, hyps) <- fetched session Native.fetchHypotheses >>= decodeHypotheses session
                    context <- currentContext session (Native.requestHostState request) (Native.requestCallId request) binding disagreements
                    when scoped (liftIO (writeIORef (sessionCurrentView session) (Just (makeHostView binding (_CurrentLabeling context)))))
                    case roots of
                        [goal] -> return [(context, mkCell Map.empty hyps premises level goal (_ContextThreadId context) : cells)]
                        _ -> throwE (BackendError "invalid oracle inspection roots")
        goalLocation ctx goal failure
            | _QueryCallId env == Just (_ContextThreadId ctx)
            , Just location <- getNodeSLoc goal
            , UnsupportedArithmeticConstraint (NApp function argument _) <- failure
            = UnsupportedArithmeticConstraint (NApp function argument (Just location))
            | otherwise = failure

callsUserCallbackConstant :: Constant -> Bool
callsUserCallbackConstant (DC (DC_Named name)) = name `elem` ["read", "print"]
callsUserCallbackConstant _ = False

-- This only selects the state view. It is not a wire validator: the chosen
-- path must still decode the complete buffer, including every type edge.
-- Unknown heads conservatively receive the complete callback Context.
requestNeedsCallbackContext :: IntMap.IntMap FullSymbol -> [Int64] -> Bool
requestNeedsCallbackContext _ [0] = False
requestNeedsCallbackContext symbols (1 : words) = head words where
    head (2 : _ : rest) = head rest
    head (1 : symbol : _ : _)
        | symbol >= 0 && toInteger symbol <= toInteger (maxBound :: Int) = case IntMap.lookup (fromIntegral symbol) symbols of
            Just (ConstantSymbol constant) -> callsUserCallbackConstant constant
            Just PresburgerSymbol {} -> False
            _ -> True
    head _ = True
requestNeedsCallbackContext _ _ = True

-- The certificate is only a fast SAT witness for one immutable conjunction.
-- An affected dependency or unsupported row returns to the complete service,
-- including definedness, joint quantifier closure and evaluation settlement.
-- No variable is assigned the witness, and no obligation is removed by it.
incrementalService :: UniqueM m => Session -> Native.NativeRequest -> Bool -> ArithStore -> Context -> Services.ServiceRequest -> ExceptT KernelErr m Services.ServiceResult
incrementalService session request clear premises before action = do
    scoped <- liftIO (readIORef (sessionScopedView session))
    cached <- liftIO (readIORef (sessionCurrentView session))
    stores <- liftIO (readIORef (sessionStores session))
    case (scoped && clear, cached, Map.lookup token stores) of
        (True, Just view, Just prior)
            | Constraints.zeroWitness prior && not (Constraints.affected (hostViewChanged view) prior) -> case action of
                Services.Settle -> return (Services.ServiceContinue before premises)
                _ -> do
                    small <- Services.runService env premises before { _LeftConstraints = [] } action
                    case small of
                        Services.ServiceContinue next active -> do
                            let changes = Map.keysSet (Map.differenceWith (\new old -> if new == old then Nothing else Just new) (unVarBinding (_TotalVarBinding next)) (unVarBinding (_TotalVarBinding before)))
                                additions = _LeftConstraints next
                                store = Constraints.prepend (_CurrentLabeling next) (_TotalVarBinding next) additions prior
                            if Constraints.affected changes prior || not (Constraints.zeroWitness store) then complete else do
                                liftIO (writeIORef (sessionPreparedStore session) (Just (token, store)))
                                return (Services.ServiceContinue next { _LeftConstraints = if null additions then _LeftConstraints before else Constraints.constraints store } active)
                        _ -> complete
        _ -> complete
    where
        token = Native.requestHostState request
        env = sessionEnvironment session
        complete = Services.runService env premises before action

fetched :: MonadIO m => Session -> (Native.Machine -> IO (Either String a)) -> ExceptT KernelErr m a
fetched session fetch = liftIO (fetch (sessionMachine session)) >>= nativeResult

-- The complete state includes every native variable and its value. Callback
-- metadata comes from shared frames or the original ordered declarations.
completeState :: UniqueM m => Session -> ExceptT KernelErr m (VarBinding, [Disagreement])
completeState session = fetched session Native.fetchState >>= decodeState session

completeRequest :: UniqueM m => Session -> Native.NativeRequest -> ExceptT KernelErr m (VarBinding, [Disagreement], [TermNode], [Cell])
completeRequest session request = do
    let debug = Native.requestKind request == 4
    scoped <- liftIO (readIORef (sessionScopedView session))
    (state, frames, declarations) <- if scoped then do
        constraints <- lookupToken "host state" (sessionConstraints session) (Native.requestHostState request)
        premises <- lookupToken "arithmetic premise" (sessionPremises session) (Native.requestPremises request)
        extra <- hostRootIdentities session (concatMap constraintTerms constraints ++ arithStoreTerms premises)
        view <- fetched session (\machine -> (if debug then Native.fetchProofViewWith else Native.fetchContextViewWith) machine extra)
        -- Shared frames carry closed, exact declarations. Decode them once
        -- for callback metadata as well; the legacy path keeps its original
        -- declaration order and lexical type-binder freshening.
        let shared = case Native.viewFrames view of
                -2 : _ -> True
                _ -> False
        return (Native.viewState view, if debug || shared then Native.viewFrames view else [0], Native.viewDeclarations view)
    else (,,) <$> fetched session Native.fetchState <*> (if debug then fetched session Native.fetchFrames else return [0]) <*> (if debug then return [0] else fetched session Native.fetchDeclarations)
    (binding, disagreements) <- decodeState session state
    roots <- decodeRoots session (Native.requestTerms request)
    cells <- decodeFrames session frames
    void (decodeRoots session declarations)
    return (binding, disagreements, roots, if debug then cells else [])

-- A view token names the immutable pre-reply binding/type environment. The
-- VM restores its matching trail watermark on backtracking and snapshot Undo.
serviceDelta :: UniqueM m => Session -> Native.NativeRequest -> ExceptT KernelErr m (VarBinding, [Disagreement], [TermNode])
serviceDelta session request = do
    delta <- fetched session Native.fetchServiceDelta
    before <- lookupToken "service view" (sessionViews session) (Native.deltaViewToken delta)
    liftIO (modifyIORef' (sessionBridge session) (\bridge -> bridge { bridgeLabeling = hostViewLabeling before, bridgeTypeBinders = Map.empty, bridgeUncertain = False }))
    (changed, disagreements) <- decodeStateBuffer session (Native.deltaState delta)
    roots <- decodeRoots session (Native.requestTerms request)
    labels <- liftIO (bridgeLabeling <$> readIORef (sessionBridge session))
    let current = (updateHostView changed before) { hostViewLabeling = strictLabeling labels }
    liftIO (writeIORef (sessionCurrentView session) (Just current))
    return (hostViewBinding current, disagreements, roots)

hostIdentity :: Bridge -> LogicVar -> Maybe Word64
hostIdentity bridge variable = case Map.lookup variable (bridgeVariableWires bridge) of
    Just (_ : uid : _) -> Just (fromIntegral uid)
    _ -> case variable of
        LV_Unique unique _ -> nativeIdentity bridge unique
        LV_ty_var unique -> nativeIdentity bridge unique
        _ -> Nothing

hostRootIdentities :: MonadIO m => Session -> [TermNode] -> ExceptT KernelErr m [Word64]
hostRootIdentities session terms = do
    bridge <- liftIO (readIORef (sessionBridge session))
    let variables = Set.toList (getLVars terms)
        identity = hostIdentity bridge
        nominal constant = case Map.lookup constant (bridgeConstantWires bridge) of
            Just (_ : uid : _) -> Just (fromIntegral uid)
            _ -> case constant of
                DC (DC_Unique unique _) -> nativeIdentity bridge unique
                _ -> Nothing
        constants = mapMaybe nominal (fst (occurrences terms))
    ids <- mapM (maybe (throwE (BackendError "host constraint has no native identity")) return . identity) variables
    return (ids ++ constants)

-- The state a stop can consult while the host holds no constraint and no
-- premise: the query variables of an answer, the disagreements, and whatever
-- the given action decodes. Nothing is returned when a decoded variable has a
-- type that the complete state could decide differently.
rootState :: UniqueM m => Session -> Bool -> ExceptT KernelErr m a -> ExceptT KernelErr m (Maybe ((VarBinding, [Disagreement]), a))
rootState session query decodeMore = do
    state <- fetched session (\machine -> Native.fetchRootState machine query)
    decoded <- decodeState session state
    more <- decodeMore
    bridge <- liftIO (readIORef (sessionBridge session))
    return (if bridgeUncertain bridge then Nothing else Just (decoded, more))

-- Native identities are numbered in creation order at every stop, whether or
-- not the stop decodes them, before the host allocates identities of its own.
reserveIdentities :: UniqueM m => Session -> ExceptT KernelErr m ()
reserveIdentities session = do
    frontier <- fetched session Native.uidFrontier
    bridge <- liftIO (readIORef (sessionBridge session))
    let start = bridgeNextIdentity bridge
        count = toInteger frontier - toInteger start
    when (count > 0) $ do
        when (count > toInteger (maxBound :: Int)) (liftIO (throwIO UniqueExhausted))
        reserved <- getUniqueBlock (fromInteger count)
        block <- maybe (liftIO (throwIO UniqueExhausted)) return reserved
        liftIO (modifyIORef' (sessionBridge session) (reserveIdentityBlock start frontier block))

reserveIdentityBlock :: Word64 -> Word64 -> UniqueBlock -> Bridge -> Bridge
reserveIdentityBlock start frontier block bridge = case block of
    UniqueRange first count -> case Map.lookupMax (bridgeIdentityBlocks bridge) of
        Just (previous, UniqueRange initial size)
            | previous + fromIntegral size == start && initial + size == first -> store previous initial (size + count)
        _ -> store start first count
    _ -> bridge { bridgeIdentityBlocks = Map.insert start block (bridgeIdentityBlocks bridge), bridgeNextIdentity = frontier }
    where
        store uid first count = bridge
            { bridgeIdentityBlocks = Map.insert uid (UniqueRange first count) (bridgeIdentityBlocks bridge)
            , bridgeIdentityRanges = IntMap.insert first (uid, count) (bridgeIdentityRanges bridge)
            , bridgeNextIdentity = frontier
            }

nativeIdentity :: Bridge -> Unique -> Maybe Word64
nativeIdentity bridge (Unique unique) = case IntMap.lookupLE unique (bridgeIdentityRanges bridge) of
    Just (first, (uid, count))
        | unique - first < count -> Just (uid + fromIntegral (unique - first))
    _ -> Nothing

compactIdentity :: Bridge -> Word64 -> Bool
compactIdentity bridge uid = case Map.lookupLE uid (bridgeIdentityBlocks bridge) of
    Just (start, UniqueRange _ count) -> uid - start < fromIntegral count
    _ -> False

resetLabeling :: MonadIO m => Session -> m ()
resetLabeling session = liftIO (modifyIORef' (sessionBridge session) (\bridge -> bridge { bridgeLabeling = initialLabeling session, bridgeTypeBinders = Map.empty, bridgeUncertain = False }))

initialLabeling :: Session -> Labeling
initialLabeling = sessionInitialLabels

closedType :: MonoType Int -> Bool
closedType typ = case typ of
    TyCon _ -> True
    TyApp left right -> closedType left && closedType right
    _ -> False

lookupToken :: MonadIO m => String -> IORef (Map.Map Word64 a) -> Word64 -> ExceptT KernelErr m a
lookupToken name table token = do
    values <- liftIO (readIORef table)
    maybe (throwE (BackendError ("unknown native " ++ name ++ " token"))) return (Map.lookup token values)

freshToken :: MonadIO m => Session -> ExceptT KernelErr m Word64
freshToken session = do
    next <- liftIO (readIORef (sessionNextToken session))
    when (next >= fromIntegral (maxBound :: Int64)) (throwE (BackendError "native host-state identifier overflow"))
    liftIO (writeIORef (sessionNextToken session) (next + 1))
    return next

installReply :: UniqueM m => Session -> Native.NativeRequest -> Context -> Services.ServiceResult -> ExceptT KernelErr m ()
installReply session request before reply = case reply of
    Services.ServiceReject -> send 0 (Native.requestHostState request) (Native.requestPremises request) []
    Services.ServiceFailure -> send 0 (Native.requestHostState request) (Native.requestPremises request) []
    Services.ServiceResume -> send 1 (Native.requestHostState request) (Native.requestPremises request) []
    Services.ServiceDebug label -> do
        liftIO (writeIORef (sessionDebugLabel session) (Just label))
        liftIO (writeIORef (sessionDebugging session) True)
        send 1 (Native.requestHostState request) (Native.requestPremises request) []
    Services.ServiceContinue next premises -> accept (if equality then 2 else 1) next premises []
    Services.ServiceUndecided next premises -> accept 4 next premises []
    Services.ServiceUnify next premises left right -> accept 1 next premises [(left, right)]
    Services.ServiceEquality decision next premises -> accept (equalityStatus decision) next premises []
    where
        equality = Native.requestKind request == 5
        equalityStatus decision = case decision of
            Just True -> 2
            Just False -> 3
            Nothing -> 4
        send status state premises pairs = do
            words <- encodeTermPairs session pairs
            scoped <- liftIO (readIORef (sessionScopedView session))
            if not scoped then liftIO (Native.resume (sessionMachine session) status state premises words) >>= nativeResult else do
                view <- freshToken session
                cached <- liftIO (readIORef (sessionCurrentView session))
                let current = maybe (makeHostView (_TotalVarBinding before) (_CurrentLabeling before)) id cached
                    tokens = (state, premises)
                roots <- if tokens == hostViewTokens current && isJust cached then return (hostViewRoots current) else do
                    store <- lookupToken "constraint index" (sessionStores session) state
                    active <- lookupToken "premise" (sessionPremises session) premises
                    return (Set.union (Constraints.roots store) (getLVars (arithStoreTerms active)))
                prepared <- liftIO (readIORef (sessionPreparedStore session))
                let growing = case prepared of
                        Just (parent, _) -> state /= 0 && (parent, premises) == hostViewTokens current
                        Nothing -> False
                    -- With no retained host obligation, the next service
                    -- needs no historical substitution, including type
                    -- substitutions. Its event exports current exact types.
                    -- Complete callback/answer views are fetched separately.
                    base
                        | Set.null roots = (makeHostView mempty (initialLabeling session)) { hostViewTokens = tokens }
                        | otherwise = retainHostView growing tokens roots current
                liftIO (modifyIORef' (sessionViews session) (Map.insert view base))
                constraintDelta <- if state == 0 || state == Native.requestHostState request then return Nothing else do
                    case prepared of
                        Just (parent, store) -> do
                            additions <- hostRootIdentities session (map mkLVar (Set.toList (Constraints.addedRoots store)))
                            return (Just (Native.RootDelta state parent additions []))
                        Nothing -> do
                            constraints <- lookupToken "constraint" (sessionConstraints session) state
                            additions <- hostRootIdentities session (concatMap constraintTerms constraints)
                            return (Just (Native.RootDelta state 0 additions []))
                premiseDelta <- if premises == 0 || premises == Native.requestPremises request then return Nothing else do
                    active <- lookupToken "premise" (sessionPremises session) premises
                    additions <- hostRootIdentities session (arithStoreTerms active)
                    return (Just (Native.RootDelta premises 0 additions []))
                let subscription = if Set.null roots then Just (Native.RootDelta view 0 [] []) else Nothing
                liftIO (Native.resumeWithSubscriptions (sessionMachine session) status state premises view words constraintDelta premiseDelta subscription) >>= nativeResult
        accept status next premises pairs = do
            sameConstraints <- liftIO (sameObject (_LeftConstraints before) (_LeftConstraints next))
            sameBindings <- liftIO (sameObject (_TotalVarBinding before) (_TotalVarBinding next))
            prepared <- liftIO (readIORef (sessionPreparedStore session))
            scoped <- liftIO (readIORef (sessionScopedView session))
            let constraints = maybe [constraint | constraint <- _LeftConstraints next, not (disagreement constraint)] (Constraints.constraints . snd) prepared
                changed = if sameBindings then [] else [(mkLVar variable, value) | (variable, value) <- Map.toList (unVarBinding (_TotalVarBinding next)), Map.lookup variable (unVarBinding (_TotalVarBinding before)) /= Just value]
            state <- if sameConstraints then return (Native.requestHostState request) else if null constraints then return 0 else do
                token <- freshToken session
                liftIO (modifyIORef' (sessionConstraints session) (Map.insert token constraints))
                when scoped $ do
                    let store = maybe (Constraints.fromConstraints (_CurrentLabeling next) (_TotalVarBinding next) constraints) snd prepared
                    liftIO (modifyIORef' (sessionStores session) (Map.insert token store))
                return token
            premise <- if Native.requestKind request /= 3 then return (Native.requestPremises request) else if nullArithStore premises then return 0 else do
                token <- freshToken session
                liftIO (modifyIORef' (sessionPremises session) (Map.insert token premises))
                return token
            send status state premise (changed ++ pairs)
        disagreement DisagreementConstraint {} = True
        disagreement _ = False

-- Sharing is only a fast positive answer: distinct objects still take the
-- ordinary structural/difference path. No identity decides logical equality.
sameObject :: a -> a -> IO Bool
sameObject left right = do
    leftName <- evaluate left >>= makeStableName
    rightName <- evaluate right >>= makeStableName
    return (eqStableName leftName rightName)

currentContext :: MonadIO m => Session -> Word64 -> Word64 -> VarBinding -> [Disagreement] -> ExceptT KernelErr m Context
currentContext session token callId binding disagreements = do
    constraints <- lookupToken "constraint" (sessionConstraints session) token
    bridge <- liftIO (readIORef (sessionBridge session))
    cached <- liftIO (readIORef (sessionCurrentView session))
    when (toInteger callId > toInteger (maxBound :: Int)) (throwE (BackendError "native call identifier overflow"))
    let labeling = case cached of
            Just _
                | not (bridgeUncertain bridge) -> bridgeLabeling bridge
            _ -> refineBindingTypes (sessionEnvironment session) binding (bridgeLabeling bridge)
    liftIO (writeIORef (sessionCurrentView session) (fmap (\view -> view { hostViewLabeling = strictLabeling labeling }) cached))
    return (Context binding labeling (map DisagreementConstraint disagreements ++ constraints) (Unique (fromIntegral callId)) (sessionDebugging session))

debugInteraction :: MonadIO m => Session -> Context -> [Cell] -> ExceptT KernelErr m Bool
debugInteraction session ctx cells = do
    let env = sessionEnvironment session
        free = Set.fromList (fullVariables (sessionProgram session))
    active <- liftIO (evaluate [(ctx, cells)])
    shown <- liftIO (makeStableName active)
    liftIO $ do
        writeIORef (_StackRef env) active
        modifyIORef' (_NameCacheRef env) (recordVisibleLVarHints active)
        verbose <- readIORef (_VerboseTyping env)
        label <- readIORef (sessionDebugLabel session)
        let reason = maybe DebugTrace DebugGoal label
            event = DebugEvent reason ctx active (showsCurrentState (_NotationDB env) (_ProgramKindEnv env) verbose free (_TypeInfo env) ctx cells [] "")
        withRuntimePhase env RuntimeDebugger (_Debugger env env event)
    updated <- liftIO (readIORef (_StackRef env) >>= evaluate)
    left <- liftIO (makeStableName updated)
    restored <- liftIO (readIORef (sessionRestored session))
    when (maybe True (const False) restored) (liftIO (writeIORef (sessionDebugLabel session) Nothing))
    -- The stack reference shows the stop to the host; the machine does not
    -- read it back. An empty one leaves the stop (`cmdQuit`). Another stack,
    -- such as the one that `restore` of Hol.BETA.Runtime puts there from an
    -- earlier stop, would be ignored: it is refused instead.
    when (not (null updated) && not (eqStableName shown left) && maybe True (const False) restored) (throwE (BackendError "the debugger stack of a V1 session cannot be replaced: use restoreSnapshot"))
    assertStack updated `seq` return (not (null updated))

type Decode m = StateT [Int64] (ExceptT KernelErr m)

data Decoded
    = Term TermNode
    | Formula P.MyPresburgerFormulaRep [P.MyVar] [TermNode] (Maybe SLoc)
    deriving ()

type TermDictionary = IORef (IntMap.IntMap Decoded, Set.Set Int)

word :: Monad m => Decode m Int64
word = do
    words <- get
    case words of
        [] -> lift (throwE (BackendError "truncated native term buffer"))
        value : rest -> put rest >> return value

naturalWord :: Monad m => Decode m Int64
naturalWord = do
    value <- word
    when (value < 0) (lift (throwE (BackendError "negative native term field")))
    return value

countWord :: Monad m => Decode m Int
countWord = do
    value <- naturalWord
    when (toInteger value > toInteger (maxBound :: Int)) (lift (throwE (BackendError "native count exceeds host range")))
    return (fromIntegral value)

runDecode :: Monad m => Decode m a -> [Int64] -> ExceptT KernelErr m a
runDecode parser words = do
    (result, remaining) <- runStateT parser words
    unless (null remaining) (throwE (BackendError "trailing native term buffer words"))
    return result

metadata :: MonadIO m => Session -> Int64 -> m NodeMetadata
metadata session index = liftIO $ do
    bridge <- readIORef (sessionBridge session)
    -- Variable display hints may remain unevaluated for the whole run. Force
    -- the lookup now so such a hint cannot retain a historical Bridge.
    evaluate (IntMap.findWithDefault (NodeMetadata Nothing noLamType Nothing) (fromIntegral index) (bridgeMetadata bridge))

-- Host-created annotations are session identities. Do not reuse their indices
-- on Undo: another live snapshot can still contain that annotation.
internRuntimeMetadata :: MonadIO m => Session -> NodeMetadata -> m Int64
internRuntimeMetadata session info = liftIO $ atomicModifyIORef' (sessionBridge session) $ \bridge ->
    case Map.lookup (storeMetadata info) (bridgeMetadataKeys bridge) of
        Just index -> (bridge, fromIntegral index)
        Nothing ->
            let index = IntMap.size (bridgeMetadata bridge)
            in (bridge { bridgeMetadata = IntMap.insert index info (bridgeMetadata bridge), bridgeMetadataKeys = Map.insert (storeMetadata info) index (bridgeMetadataKeys bridge) }, fromIntegral index)

decodeTerm :: UniqueM m => Session -> Decode m TermNode
decodeTerm session = decodeSharedTerm session Nothing

-- The transient frame producer shares only complete views without lexical
-- type binders or context-dependent annotations. Replaying a decoded subtree
-- therefore skips only identical type/scope enrollment. Keep partial formula
-- applications too; their enclosing application still supplies the arguments.
decodeSharedTerm :: UniqueM m => Session -> Maybe TermDictionary -> Decode m TermNode
decodeSharedTerm session dictionary = term [] False where
    finish (Term value) = return value
    finish Formula {} = lift (throwE (BackendError "incomplete native Presburger application"))
    term bound typeBinder = decoded bound typeBinder >>= finish
    decoded bound typeBinder = do
        tag <- word
        case tag of
            11 -> do
                entries <- dictionaryRef
                identity <- countWord
                (known, pending) <- liftIO (readIORef entries)
                when (IntMap.member identity known || Set.member identity pending) (invalid "duplicate native term dictionary entry")
                liftIO (writeIORef entries (known, Set.insert identity pending))
                value <- decoded bound typeBinder
                liftIO (modifyIORef' entries (\(values, active) -> (IntMap.insert identity value values, Set.delete identity active)))
                return value
            12 -> do
                entries <- dictionaryRef
                identity <- countWord
                known <- liftIO (fst <$> readIORef entries)
                maybe (invalid "unknown or forward native term dictionary reference") return (IntMap.lookup identity known)
            0 -> variable bound False
            9 -> variable bound True
            1 -> do
                symbol <- countWord
                meta <- word
                info <- metadata session meta
                table <- liftIO (bridgeSymbols <$> readIORef (sessionBridge session))
                case IntMap.lookup symbol table of
                    Just (ConstantSymbol (DC (DC_NatL number)))
                        | number < 0 -> lift (throwE (BackendError "negative native natural symbol"))
                    Just (ConstantSymbol constant) -> return (Term (mkNConLoc (nodeLocation info) constant))
                    Just (PresburgerSymbol rep [] loc) -> return (Term (NPresburgerCheck rep Map.empty loc))
                    Just (PresburgerSymbol rep vars loc) -> return (Formula rep vars [] loc)
                    Nothing -> lift (throwE (BackendError "unknown native constant symbol"))
            2 -> do
                meta <- word
                info <- metadata session meta
                function <- decoded bound False
                argument <- term bound $ case function of
                    Term (NCon (DC (DC_LO LO_ty_pi)) _) -> True
                    _ -> False
                case function of
                    -- Every child was decoded and its leaves checked above.
                    -- Rechecking each completed subtree makes a spine quadratic.
                    Term value -> return (Term (mkNAppLocUnchecked (nodeLocation info) value argument))
                    Formula rep names arguments loc
                        | length arguments + 1 == length names -> return (Term (NPresburgerCheck rep (Map.fromList (zip names (arguments ++ [argument]))) loc))
                        | otherwise -> return (Formula rep names (arguments ++ [argument]) loc)
            3 -> Term . mkNIdx <$> countWord
            4 -> lambda bound typeBinder False
            8 -> lambda bound typeBinder True
            5 -> nominal bound False
            10 -> nominal bound True
            6 -> do
                count <- countWord
                digits <- replicateM count word
                when (null digits || any (\digit -> digit < 48 || digit > 57) digits) (lift (throwE (BackendError "invalid native natural literal")))
                return (Term (mkNCon (DC_NatL (foldl (\value digit -> value * 10 + toInteger (digit - 48)) 0 digits))))
            7 -> return (Term (mkNCon DC_wc))
            _ -> lift (throwE (BackendError "invalid native term tag"))
    dictionaryRef = maybe (invalid "native term dictionary reference outside a shared view") return dictionary
    invalid message = lift (throwE (BackendError message))
    annotation bound = term bound False >>= lift . decodeTypeTerm session bound
    variable bound typed = do
        uid <- naturalWord
        scope <- countWord
        isType <- naturalWord
        meta <- word
        when (isType > 1 || (typed && isType /= 0)) (lift (throwE (BackendError "invalid native variable kind")))
        typ <- if typed then Just <$> annotation bound else return Nothing
        value <- lift (decodeTypedVariable session (fromIntegral uid) scope (isType == 1) meta typ)
        return (Term (mkLVar value))
    nominal bound typed = do
        uid <- naturalWord
        scope <- countWord
        meta <- word
        typ <- if typed then Just <$> annotation bound else return Nothing
        constant <- lift (decodeTypedNominal session (fromIntegral uid) scope meta typ)
        info <- metadata session meta
        return (Term (mkNConLoc (nodeLocation info) constant))
    lambda bound typeBinder typed = do
        meta <- word
        info <- metadata session meta
        marker <- if not typeBinder then return Nothing else case unLamType (nodeType info) >>= runtimeTypeVariable of
            Just variable -> return (Just variable)
            Nothing -> do
                supply <- liftIO (runtimeTypeSupply <$> readIORef (_RuntimeControl (sessionEnvironment session)))
                fresh <- maybe (lift (throwE (BackendError "a host type binder requires an active unique allocator"))) liftIO supply
                maybe (liftIO (throwIO UniqueExhausted)) (return . Just) fresh
        typ <- if typed then mkLamType <$> annotation bound else return (maybe (nodeType info) (mkLamType . TyMTV) marker)
        body <- term (marker : bound) False
        return (Term (NLam (nodeHint info) typ body (nodeLocation info)))

-- A type in an uninstantiated local clause may name its enclosing type binder.
-- This decodes the Hol type wire; it performs no LoL typing or conversion.
decodeTypeTerm :: Monad m => Session -> [Maybe MetaTVar] -> TermNode -> ExceptT KernelErr m (MonoType Int)
decodeTypeTerm session bound value = do
    closed <- replace value
    maybe (throwE (BackendError "invalid native type annotation")) return (primitiveTypeArgumentWithKinds (_ProgramKindEnv (sessionEnvironment session)) closed)
    where
        replace term = case term of
            NIdx index | index < 0 -> throwE (BackendError "negative native type annotation index")
            NIdx index -> case drop index bound of
                Just variable : _ -> return (mkLVar (LV_ty_var variable))
                _ -> throwE (BackendError "unbound native type annotation")
            NApp function argument location -> mkNAppLoc location <$> replace function <*> replace argument
            _ -> return term

decodeVariable :: UniqueM m => Session -> Word64 -> Int -> Bool -> Int64 -> ExceptT KernelErr m LogicVar
decodeVariable session uid scope isType meta = decodeTypedVariable session uid scope isType meta Nothing

decodeTypedVariable :: UniqueM m => Session -> Word64 -> Int -> Bool -> Int64 -> Maybe (MonoType Int) -> ExceptT KernelErr m LogicVar
decodeTypedVariable session uid scope isType meta exact = do
    info <- metadata session meta
    bridge <- liftIO (readIORef (sessionBridge session))
    variable <- case Map.lookup uid (bridgeVariables bridge) of
        Just known -> return known
        Nothing -> do
            unique <- identityFor session uid
            return (if isType then LV_ty_var unique else LV_Unique unique (mkHint (nodeHint info)))
    bridge <- liftIO (readIORef (sessionBridge session))
    let encoded = [0, fromIntegral uid, fromIntegral scope, if isType then 1 else 0, meta]
        binders = case (variable, unLamType (nodeType info)) of
            (LV_ty_var unique, Just (TyMTV original)) -> Map.insert original unique (bridgeTypeBinders bridge)
            _ -> bridgeTypeBinders bridge
        label
            | isType && uid < bridgeQuerySlots bridge = bridgeLabeling bridge
            | otherwise = enrollLabel variable scope (bridgeLabeling bridge)
        withType = case (variable, exact `mplus` fmap (instantiateMetadataType binders) (unLamType (nodeType info))) of
            (LV_Named name, Just typ)
                | isJust exact -> label { _NamedTypes = Map.insert name typ (_NamedTypes label) }
            (LV_Named _, _) -> label
            (_, Just typ) -> label { _VarTypes = IntMap.insertWith (\found old -> if isJust exact || guessedType old then found else old) (lvKey variable) typ (_VarTypes label) }
            _ -> label
        typed = if isType then withType { _TyVarKeys = IntMap.insert (lvKey variable) () (_TyVarKeys withType) } else withType
        uncertain = case variable of
            LV_Named _ -> isType
            _ -> isType || maybe True (not . closedType) (exact `mplus` unLamType (nodeType info))
        keep = not (compactIdentity bridge uid) || Map.member uid (bridgeVariables bridge)
    liftIO (writeIORef (sessionBridge session) bridge { bridgeVariables = if keep then Map.insert uid variable (bridgeVariables bridge) else bridgeVariables bridge, bridgeVariableWires = if keep then Map.insert variable encoded (bridgeVariableWires bridge) else bridgeVariableWires bridge, bridgeLabeling = strictLabeling typed, bridgeTypeBinders = binders, bridgeUncertain = bridgeUncertain bridge || uncertain })
    return variable

decodeNominal :: UniqueM m => Session -> Word64 -> Int -> Int64 -> ExceptT KernelErr m Constant
decodeNominal session uid scope meta = decodeTypedNominal session uid scope meta Nothing

decodeTypedNominal :: UniqueM m => Session -> Word64 -> Int -> Int64 -> Maybe (MonoType Int) -> ExceptT KernelErr m Constant
decodeTypedNominal session uid scope meta exact = do
    info <- metadata session meta
    bridge <- liftIO (readIORef (sessionBridge session))
    constant <- case Map.lookup uid (bridgeConstants bridge) of
        Just known -> return known
        Nothing -> do
            unique <- identityFor session uid
            return (DC (DC_Unique unique (mkHint (nodeHint info))))
    bridge <- liftIO (readIORef (sessionBridge session))
    let encoded = [5, fromIntegral uid, fromIntegral scope, meta]
        labeling = enrollLabel constant scope (bridgeLabeling bridge)
        typed = case (constant, exact `mplus` fmap (instantiateMetadataType (bridgeTypeBinders bridge)) (unLamType (nodeType info))) of
            (DC (DC_Unique unique _), Just typ) -> labeling { _ConTypes = IntMap.insertWith (\found old -> if isJust exact || guessedType old then found else old) (unUnique unique) typ (_ConTypes labeling) }
            _ -> labeling
        uncertain = maybe False (not . closedType) (exact `mplus` unLamType (nodeType info))
        keep = not (compactIdentity bridge uid) || Map.member uid (bridgeConstants bridge)
    liftIO (writeIORef (sessionBridge session) bridge { bridgeConstants = if keep then Map.insert uid constant (bridgeConstants bridge) else bridgeConstants bridge, bridgeConstantWires = if keep then Map.insert constant encoded (bridgeConstantWires bridge) else bridgeConstantWires bridge, bridgeLabeling = strictLabeling typed, bridgeUncertain = bridgeUncertain bridge || uncertain })
    return constant

decodeState :: UniqueM m => Session -> [Int64] -> ExceptT KernelErr m (VarBinding, [Disagreement])
decodeState session words = resetLabeling session >> decodeStateBuffer session words

decodeStateBuffer :: UniqueM m => Session -> [Int64] -> ExceptT KernelErr m (VarBinding, [Disagreement])
decodeStateBuffer session words = runDecode parser words
    where
        parser = do
            count <- countWord
            pairs <- replicateM count $ do
                variable <- decodeTerm session
                value <- decodeTerm session
                case variable of
                    LVar name -> return (name, value)
                    _ -> lift (throwE (BackendError "native state does not begin with a variable"))
            remaining <- countWord
            disagreements <- replicateM remaining ((:=?=:) <$> decodeTerm session <*> decodeTerm session)
            return (VarBinding (Map.fromList [(variable, value) | (variable, value) <- pairs, value /= mkLVar variable]), disagreements)

decodeRoots :: UniqueM m => Session -> [Int64] -> ExceptT KernelErr m [TermNode]
decodeRoots session = runDecode (countWord >>= \count -> replicateM count (decodeTerm session))

-- The scope of the goal of an event and its hypotheses, the latest first.
decodeHypotheses :: UniqueM m => Session -> [Int64] -> ExceptT KernelErr m (ScopeLevel, [TermNode])
decodeHypotheses session = runDecode ((,) <$> countWord <*> (countWord >>= \count -> replicateM count (decodeTerm session)))

decodeFrames :: UniqueM m => Session -> [Int64] -> ExceptT KernelErr m [Cell]
decodeFrames session = runDecode $ do
    marker <- word
    dictionary <- if marker == -2 then Just <$> liftIO (newIORef (IntMap.empty, Set.empty)) else return Nothing
    let decoder = decodeSharedTerm session dictionary
    if marker == -1 || marker == -2 then do
        count <- countWord
        evalStateT (replicateM count (sharedFrame decoder)) IntMap.empty
    else if marker < 0 || toInteger marker > toInteger (maxBound :: Int) then
        lift (throwE (BackendError "invalid native frame count"))
    else replicateM (fromIntegral marker) frame
    where
        frame = do
            scope <- countWord
            callId <- countWord
            hypotheses <- countWord >>= \count -> replicateM count (decodeTerm session)
            goal <- decodeTerm session
            return (mkCell Map.empty hypotheses emptyArithStore scope goal (Unique callId))
        sharedFrame decoder = do
            scope <- lift countWord
            callId <- lift countWord
            hypotheses <- chain decoder Set.empty []
            goal <- lift decoder
            return (mkCell Map.empty hypotheses emptyArithStore scope goal (Unique callId))
        -- Facts are decoded in their original forward order. Registering each
        -- suffix afterwards shares the persistent list without re-decoding its
        -- exact types. Native eligibility excludes type-binder freshening.
        chain decoder pending reversed = do
            tag <- lift word
            case tag of
                0 -> finish reversed []
                1 -> do
                    identity <- lift countWord
                    entries <- get
                    when (Set.member identity pending || IntMap.member identity entries) (invalid "duplicate native hypothesis dictionary entry")
                    fact <- lift decoder
                    chain decoder (Set.insert identity pending) ((identity, fact) : reversed)
                2 -> do
                    identity <- lift countWord
                    entries <- get
                    maybe (invalid "unknown native hypothesis dictionary suffix") (finish reversed) (IntMap.lookup identity entries)
                _ -> invalid "invalid native hypothesis chain tag"
        finish reversed suffix = foldM add suffix reversed
        add suffix (identity, fact) = do
            let result = fact : suffix
            modify' (IntMap.insert identity result)
            return result
        invalid message = lift (lift (throwE (BackendError message)))

encodePairs :: UniqueM m => Session -> [(LogicVar, TermNode)] -> ExceptT KernelErr m [Int64]
encodePairs session = encodeTermPairs session . map (\(variable, value) -> (mkLVar variable, value))

encodeTermPairs :: UniqueM m => Session -> [(TermNode, TermNode)] -> ExceptT KernelErr m [Int64]
encodeTermPairs session pairs = do
    encoded <- mapM (\(left, right) -> (++) <$> encodeTerm session left <*> encodeTerm session right) pairs
    return (fromIntegral (length pairs) : concat encoded)

encodeTerm :: UniqueM m => Session -> TermNode -> ExceptT KernelErr m [Int64]
encodeTerm session input = go 0 Map.empty (rewrite NF input) where
    go depth binders (LVar variable) = do
        bridge <- liftIO (readIORef (sessionBridge session))
        case Map.lookup variable (bridgeVariableWires bridge) of
            Just encoded -> return encoded
            Nothing -> do
                let uid = case variable of
                        LV_Unique unique _ -> nativeIdentity bridge unique
                        LV_ty_var unique -> nativeIdentity bridge unique
                        _ -> Nothing
                case uid of
                    Just known -> fetched session (\machine -> Native.lookupIdentity machine known)
                    Nothing -> do
                        reserveIdentities session
                        bridge <- liftIO (readIORef (sessionBridge session))
                        fresh <- liftIO (Native.reserveUid (sessionMachine session)) >>= nativeResult
                        let isType = case variable of
                                LV_ty_var _ -> 1
                                _ -> 0
                            -- Fresh type variables introduced by a host value
                            -- range over global types, never pi term constants.
                            scope = case variable of
                                LV_ty_var _ -> 0
                                _ -> lookupLabel variable (bridgeLabeling bridge)
                            encoded = [0, fromIntegral fresh, fromIntegral scope, isType, -1]
                            registered = case variable of
                                LV_ty_var (Unique unique) -> (reserveIdentityBlock fresh (fresh + 1) (UniqueRange unique 1) bridge) { bridgeTransientTypes = Map.insert variable fresh (bridgeTransientTypes bridge) }
                                _ -> bridge
                        liftIO (writeIORef (sessionBridge session) registered { bridgeVariables = Map.insert fresh variable (bridgeVariables registered), bridgeVariableWires = Map.insert variable encoded (bridgeVariableWires registered) })
                        return encoded
    go depth binders (NCon (DC (DC_NatL value)) _)
        | value >= 0 = return (6 : fromIntegral (length digits) : map (fromIntegral . ord) digits)
        | otherwise = throwE (BackendError "negative natural in a native binding")
        where
            digits = show value
    go depth binders (NCon (DC DC_wc) _) = return [7]
    go depth binders (NCon constant _) = do
        bridge <- liftIO (readIORef (sessionBridge session))
        case Map.lookup constant (bridgeConstantWires bridge) of
            Just nominal -> return nominal
            Nothing -> case constant of
                DC (DC_Unique unique _)
                    | Just uid <- nativeIdentity bridge unique -> fetched session (\machine -> Native.lookupIdentity machine uid)
                _ -> do
                    symbol <- internSymbol session (ConstantSymbol constant)
                    return [1, fromIntegral symbol, -1]
    go depth binders (NIdx index)
        | index >= 0 = return [3, fromIntegral index]
        | otherwise = throwE (BackendError "negative de Bruijn index in a native binding")
    go depth binders (NApp function@(NCon (DC (DC_LO LO_ty_pi)) _) (NLam hint typ body location) _) = do
        variable <- maybe (throwE (BackendError "missing native type binder identity")) return (unLamType typ >>= runtimeTypeVariable)
        function' <- go depth binders function
        body' <- go (depth + 1) (Map.insert variable depth binders) body
        marker <- internRuntimeMetadata session (NodeMetadata hint typ location)
        return ([2, -1] ++ function' ++ [4, marker] ++ body')
    go depth binders (NApp function argument _) = do
        lhs <- go depth binders function
        rhs <- go depth binders argument
        return ([2, -1] ++ lhs ++ rhs)
    go depth binders (NLam hint typ body location) = do
        marker <- internRuntimeMetadata session (NodeMetadata hint typ location)
        encodedBody <- go (depth + 1) binders body
        case unLamType typ of
            Nothing -> return ([4, marker] ++ encodedBody)
            Just domain -> do
                nativeType <- encodeType depth binders domain
                encodedType <- go depth binders nativeType
                return ([8, marker] ++ encodedType ++ encodedBody)
    go depth binders (NPresburgerCheck rep freeOf loc) = do
        symbol <- internSymbol session (PresburgerSymbol rep (Map.keys freeOf) loc)
        foldM (\function argument -> do value <- go depth binders argument; return ([2, -1] ++ function ++ value)) [1, fromIntegral symbol, -1] (Map.elems freeOf)
    go depth binders suspended@Susp {} = go depth binders (rewrite NF suspended)

    encodeType depth binders typ = case typ of
        TyMTV variable -> return (variableType variable)
        TyCon (TCon (TC_Unique variable) _) -> return (variableType variable)
        TyCon (TCon constructor _) -> return (mkNCon constructor)
        TyApp function argument -> mkNApp <$> encodeType depth binders function <*> encodeType depth binders argument
        TyVar _ -> throwE (BackendError "generalized type index in a native value")
        where
            variableType variable = case Map.lookup variable binders of
                Just level -> mkNIdx (depth - level - 1)
                Nothing -> mkLVar (LV_ty_var variable)

internSymbol :: MonadIO m => Session -> FullSymbol -> ExceptT KernelErr m Int
internSymbol session symbol = do
    bridge <- liftIO (readIORef (sessionBridge session))
    case Map.lookup key (bridgeSymbolIndices bridge) of
        Just index -> return index
        Nothing -> do
            let index = IntMap.size (bridgeSymbols bridge)
            liftIO (Native.ensureSymbol (sessionMachine session) index (symbolRole symbol)) >>= nativeResult
            liftIO (writeIORef (sessionBridge session) bridge { bridgeSymbols = IntMap.insert index symbol (bridgeSymbols bridge), bridgeSymbolIndices = Map.insert key index (bridgeSymbolIndices bridge) })
            return index
    where
        key = symbolIdentity symbol

-- The type of a binder with the type variables of the instance that was
-- decoded last. That is the instance of a variable that a clause made on
-- entry, and a guess for one that `sigma` or `pi` made later in a body: the
-- type variable is recorded as one of no run (foreignTypeVariable), so that
-- it is shown and decides nothing. `refineBindingTypes` gives a variable the
-- type that its place in a value of a typed variable has.
instantiateMetadataType :: Map.Map MetaTVar MetaTVar -> MonoType Int -> MonoType Int
instantiateMetadataType binders typ = case typ of
    TyMTV original -> TyMTV (foreignTypeVariable (Map.findWithDefault original original binders))
    TyApp left right -> TyApp (instantiateMetadataType binders left) (instantiateMetadataType binders right)
    _ -> typ


applyPending :: UniqueM m => Session -> ExceptT KernelErr m ()
applyPending session = do
    let pendingRef = _PendingSubst (sessionEnvironment session)
    pending <- liftIO (readIORef pendingRef)
    unless (Map.null (unVarBinding pending)) $ do
        words <- encodePairs session (Map.toList (unVarBinding pending))
        liftIO (Native.assign (sessionMachine session) words) >>= nativeResult
        liftIO (writeIORef pendingRef mempty)

-- Arithmetic quantifier order follows creation order, including unseen UID gaps.
identityFor :: UniqueM m => Session -> Word64 -> ExceptT KernelErr m Unique
identityFor session uid = do
    bridge <- liftIO (readIORef (sessionBridge session))
    case Map.lookup uid (bridgeIdentities bridge) of
        Just unique -> return unique
        Nothing
            | uid < bridgeQuerySlots bridge -> throwE (BackendError "native identity collides with a query slot")
            | uid < bridgeNextIdentity bridge -> case Map.lookupLE uid (bridgeIdentityBlocks bridge) of
                Just (start, block) -> uniqueAt (uid - start) block >>= remember
                Nothing -> throwE (BackendError "missing native identity reservation")
            | otherwise -> do
                let start = bridgeNextIdentity bridge
                    count = toInteger uid - toInteger start + 1
                when (count > toInteger (maxBound :: Int)) (liftIO (throwIO UniqueExhausted))
                reserved <- getUniqueBlock (fromInteger count)
                block <- maybe (liftIO (throwIO UniqueExhausted)) return reserved
                unique <- uniqueAt (uid - start) block
                liftIO (modifyIORef' (sessionBridge session) (reserveIdentityBlock start (uid + 1) block))
                remember unique
    where
        uniqueAt offset block
            | toInteger offset > toInteger (maxBound :: Int) = liftIO (throwIO UniqueExhausted)
            | otherwise = maybe (throwE (BackendError "invalid native identity reservation")) return (lookupUniqueBlock (fromIntegral offset) block)
        remember unique = do
            liftIO (modifyIORef' (sessionBridge session) (\bridge -> if compactIdentity bridge uid then bridge else bridge { bridgeIdentities = Map.insert uid unique (bridgeIdentities bridge) }))
            return unique
