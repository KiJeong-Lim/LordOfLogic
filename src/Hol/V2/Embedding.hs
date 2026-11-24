-- The supported embedding boundary. Runtime references and search stacks are
-- private; a host receives terms and checked capabilities instead.
module Hol.V2.Embedding
    ( module Terms, module Constants, module Types, Unique (..)
    , Context, Question, OracleCheckpoint
    , _QuestionName, _QuestionType, _QuestionTerm, _QuestionHyps, _QuestionNest, _QuestionCons, _QuestionVars, _QuestionLeft, renderQuestion
    , Constraint (..), Disagreement (..), VarBinding (..), bindVars, getLVars
    , ConstraintView (..), PremisesView (..), FormulaView (..), constraintView
    , PresburgerFormula (..), PresburgerTermRep (..)
    , _TotalVarBinding, _LeftConstraints, DebugReason (..), StepId (..)
    , DiagnosticMode (..), diagnosticWithModule, initialCache, prettyTerm, initial
    , Backend (..), Supply, newSupply, Program, programKinds, programTypes, programFacts, programWarnings
    , emptyProgram, prepareProgram, inferGoalTypes, loadProgram, loadProgramCached, readPreparedFile, writePreparedFile, Engine, createEngine, createEngineWithLimit, forkEngine, extendEngine, extendModule, loadModuleIntoEngine
    , leaveEngine, closeEngine, withQuery, ProgramMark, markProgram, truncateProgram, closeProgramMark, Session, openSession, openSessionWithLimit, closeSession
    , withSession, withSessionFacts, withSessionFactsWithLimit, HostConfig (..), defaultHostConfig, Outcome (..)
    , Failure (..), UsageError (..), ExecutionError (..), AssignmentReason (..), AssignmentFailure (..), Operation (..), Phase (..)
    , GoalView (..), NominalView (..), VariableView (..), ProofState (..)
    , nextSolution, inspect, assign, tryInstantiate, captureOracleCheckpoint, restoreOracleCheckpoint, beginStep, endStep, Snapshot
    , takeSnapshot, restoreSnapshot, restoreSnapshotConsuming, closeSnapshot, abandon, setTracing
    , setWorkLimit, setEngineMemoryLimit, setMemoryLimit, getMemoryLimit, NativeStats (..), sessionStats
    , setCounting, setLegacyCopy, setCollectionStep, describeFailure
    ) where

import Calc.Presburger.Internal (PresburgerFormula (..), PresburgerTermRep (..))
import Control.Concurrent (ThreadId, myThreadId)
import Control.Concurrent.MVar
import Control.Exception (Exception, IOException, bracket, catch, finally, mask, mask_, onException, throwIO, try)
import Control.Monad (unless, void, when)
import Control.Monad.Trans.Except (runExceptT)
import Control.Monad.Trans.Reader (runReaderT)
import Data.IORef
import qualified Data.IntMap.Strict as IntMap
import Data.List (nub, sortOn)
import qualified Data.Map.Strict as Map
import Data.Maybe (fromMaybe)
import qualified Data.Set as Set
import Data.Word (Word64)
import qualified Hol.BETA.Answer as Answer
import Hol.BETA.Constant as Constants
import Hol.BETA.Debugger (initialCache, prettyTerm)
import Hol.BETA.Diagnostic (DiagnosticMode (..), diagnosticWithModule)
import Hol.BETA.Header as Types hiding (Program, TermExpr (..))
import Hol.BETA.HOPU (Disagreement (..), Labeling (..), VarBinding (..), bindVars, getLVars, zonkLVar, lookupConType, lookupLabel)
import qualified Hol.BETA.Main as BETA
import qualified Hol.BETA.ModuleLoader as Loader
import Hol.BETA.Notation (initial)
import qualified Hol.BETA.Runtime as Runtime
import Hol.BETA.Runtime (AssignmentReason (..), AssignmentFailure (..), Context, Constraint (..), DebugReason (..), StepId (..), _TotalVarBinding, _LeftConstraints)
import Hol.BETA.TermNode as Terms
import qualified Hol.V1.FullCompiler as Compiler
import qualified Hol.V1.FullBytecode as Bytecode
import Hol.V1.Checked (CheckedProgram, checkedProgram)
import qualified Hol.V1.FullRuntime as Full
import qualified Hol.V2.Cache as Cache
import qualified Hol.V2.Typing as Typing
import System.Environment (lookupEnv)
import qualified X.HigherMachine as Machine
import X.HigherMachine (NativeStats (..))
import Z.Utils (Unique (..), UniqueExhausted (..), UniqueT, getUnique, runUniqueT)

-- A structural view of residual obligations. This preserves the stored
-- terms, formula binders and captured premises; it does not solve, simplify
-- or infer any type. ProofState already applies its current substitution.
data ConstraintView
    = DisagreementView TermNode TermNode
    | EvaluationView TermNode TermNode
    | ArithmeticView PremisesView TermNode
    | PresburgerView PremisesView FormulaView
    deriving ()

data PremisesView
    = PremisesView
        { premiseComparisons :: [TermNode]
        , premiseFormulas    :: [FormulaView]
        }
    deriving ()

data FormulaView
    = FormulaView
        { formulaSyntax    :: PresburgerFormula PresburgerTermRep
        , formulaFreeTerms :: Map.Map Integer TermNode
        }
    deriving ()

constraintView :: Constraint -> ConstraintView
constraintView constraint = case constraint of
    DisagreementConstraint (left :=?=: right) -> DisagreementView left right
    EvalutionConstraint left right -> EvaluationView left right
    ArithmeticConstraint premises term -> ArithmeticView (viewPremises premises) term
    PresburgerConstraint premises formula free -> PresburgerView (viewPremises premises) (FormulaView formula free)
    where
        viewPremises (comparisons, formulas) = PremisesView comparisons [FormulaView formula free | (formula, free) <- formulas]

-- Question data remains readable after a callback. Its editing capabilities
-- belong to exactly one live session and are only used by checked functions.
data Question = Question (IORef Bool) Runtime.Question deriving ()
data OracleCheckpoint = OracleCheckpoint (IORef Bool) ThreadId Runtime.OracleCheckpoint deriving ()

_QuestionName :: Question -> String
_QuestionName (Question _ question) = Runtime._QuestionName question

_QuestionType :: Question -> TermNode
_QuestionType (Question _ question) = Runtime._QuestionType question

_QuestionTerm :: Question -> TermNode
_QuestionTerm (Question _ question) = Runtime._QuestionTerm question

_QuestionHyps :: Question -> [TermNode]
_QuestionHyps (Question _ question) = Runtime._QuestionHyps question

_QuestionNest :: Question -> Int
_QuestionNest (Question _ question) = Runtime._QuestionNest question

_QuestionCons :: Question -> [(Constant, Int)]
_QuestionCons (Question _ question) = Runtime._QuestionCons question

_QuestionVars :: Question -> [(LogicVar, Int)]
_QuestionVars (Question _ question) = Runtime._QuestionVars question

_QuestionLeft :: Question -> [Constraint]
_QuestionLeft (Question _ question) = orderedConstraints (Runtime._QuestionLeft question)

renderQuestion :: Question -> ([String], String)
renderQuestion (Question _ question) = Answer.renderQuestionWithNames initial initialCache names question where
    names = Answer.extendQuestionNames initialCache (const True) [] question

data Backend = Interpreter | Native deriving (Eq, Show)
data Supply = Supply (IORef Int) (MVar (Maybe String)) deriving ()

newSupply :: IO Supply
newSupply = Supply <$> newIORef 0 <*> newMVar Nothing

runSupply :: Supply -> UniqueT IO a -> IO a
runSupply (Supply counter _) action = runReaderT (runUniqueT action) counter

cacheCompiler :: Supply -> IO String
cacheCompiler (Supply _ cell) = modifyMVar cell $ \known -> case known of
    Just compiler -> return (known, compiler)
    Nothing -> do
        compiler <- Cache.compilerIdentity
        return (Just compiler, compiler)

data Program
    = Program
        { storedKinds     :: KindEnv
        , storedTypes     :: TypeEnv
        , storedFacts     :: [TermNode]
        , programReady    :: Compiler.PreparedProgram
        , programManifest :: Maybe Cache.Manifest
        }
    deriving ()

programKinds :: Program -> KindEnv
programKinds = storedKinds

programTypes :: Program -> TypeEnv
programTypes = storedTypes

programFacts :: Program -> [TermNode]
programFacts = storedFacts

programWarnings :: Program -> [String]
programWarnings = maybe [] Cache.manifestWarnings . programManifest

emptyProgram :: Either Failure Program
emptyProgram = prepareProgram BETA.theInitialKindDecls BETA.theInitialTypeDecls BETA.theInitialFactDecls

prepareProgram :: KindEnv -> TypeEnv -> [TermNode] -> Either Failure Program
prepareProgram kinds types facts = do
    validateInputTerms facts
    either (Left . Usage . InvalidInput) (\ready -> Right (Program kinds types facts ready Nothing)) (Compiler.prepareFullProgram kinds types facts)

inferGoalTypes :: Supply -> Program -> TermNode -> IO (Either Failure (TermNode, Map.Map LogicVar (MonoType Int)))
inferGoalTypes supply program goal = identityFailure $ withInputTerms [goal] $ do
    reserved <- either (return . Left . Usage . InvalidInput) (reserveSupplyFloor supply) (Compiler.preparedUniqueFloor (programReady program))
    case reserved of
        Left failure -> return (Left failure)
        Right () -> do
            result <- runSupply supply (runExceptT (Typing.inferGoal (programKinds program) (programTypes program) goal))
            return (either (Left . Usage . InvalidInput) Right result)

-- Raw constructors are public, while the legacy term algorithms assume their
-- representation invariants. Reject malformed input before those partial
-- algorithms inspect it. This checks structure, not Hol or LoL typing.
validateInputTerms :: [TermNode] -> Either Failure ()
validateInputTerms = loop where
    invalid = Left . Usage . InvalidInput
    loop [] = Right ()
    loop (value : rest) = case value of
        NCon (DC (DC_NatL number)) _
            | number < 0 -> invalid "negative natural literal"
        NIdx index
            | index < 0 -> invalid "negative de Bruijn index"
        NApp function argument _ -> loop (function : argument : rest)
        NLam _ _ body _ -> loop (body : rest)
        Susp body old new environment
            | old < 0 || new < 0 || length environment /= old -> invalid "invalid suspension levels or environment length"
            | otherwise -> items new environment (body : rest)
        NPresburgerCheck formula free _ -> do
            either invalid (const (Right ())) (Bytecode.restoreFormula (Bytecode.storeFormula formula))
            if any (<= 0) (Map.keys free) then invalid "nonpositive Presburger variable" else loop (Map.elems free ++ rest)
        _ -> loop rest
    items _ [] rest = loop rest
    items new (entry : remaining) rest = case entry of
        Dummy level
            | level >= 0 && level <= new -> items new remaining rest
        Binds body level
            | level >= 0 && level <= new -> items new remaining (body : rest)
        _ -> invalid "invalid suspension environment entry"

withInputTerms :: [TermNode] -> IO (Either Failure a) -> IO (Either Failure a)
withInputTerms values action = either (return . Left) (const action) (validateInputTerms values)

loadProgram :: Supply -> FilePath -> IO (Either Failure Program)
loadProgram supply path = identityFailure $ do
    loaded <- runSupply supply (Loader.loadMainWithDiagnostic DiagnosticTest BETA.theInitialKindDecls BETA.theInitialTypeDecls BETA.theInitialFactDecls path)
    case loaded of
        Left message -> return (Left (Usage (InvalidInput message)))
        Right module' -> do
            manifest <- Cache.manifestFor module'
            let env = Loader.loadedMain module'
            return $ do
                program <- prepareProgram (Loader.moduleEnvKinds env) (Loader.moduleEnvTypes env) (Loader.moduleEnvFacts env)
                return program { programManifest = Just manifest }

-- Cache failure is never a source-program verdict. Loading invalidates stale
-- source/import/compiler metadata, then rebuilds through the ordinary loader.
loadProgramCached :: Supply -> FilePath -> IO (Either Failure Program)
loadProgramCached supply path = do
    disabled <- lookupEnv "LOL_HOL_CACHE"
    if disabled == Just "off" then loadProgram supply path else do
        location <- try (do { compiler <- cacheCompiler supply; storage <- Cache.cachePathWith compiler path; return (compiler, storage) }) :: IO (Either IOException (String, FilePath))
        case location of
            Left _ -> loadProgram supply path
            Right (compiler, storage) -> do
                cached <- restorePrepared <$> Cache.readCacheWith compiler storage path
                case cached of
                    Right program -> return (Right program)
                    Left _ -> do
                        loaded <- loadProgram supply path
                        case loaded of
                            Left failure -> return (Left failure)
                            Right program -> do
                                _ <- writePreparedWith (Cache.writeCacheWith compiler) storage program
                                Cache.pruneCache storage
                                return (Right program)

readPreparedFile :: FilePath -> FilePath -> IO (Either Failure Program)
readPreparedFile storage source = restorePrepared <$> Cache.readCache storage source

restorePrepared :: Either String (Cache.Manifest, CheckedProgram) -> Either Failure Program
restorePrepared read = do
    (manifest, checked) <- either (Left . Usage . InvalidInput) Right read
    (ready, facts) <- either (Left . Usage . InvalidInput) Right (Compiler.restoreCheckedProgram checked)
    let stored = checkedProgram checked
    return (Program (Bytecode.fullKindEnv stored) (Bytecode.fullTypeEnv stored) facts ready (Just manifest))

writePreparedFile :: FilePath -> Program -> IO (Either Failure ())
writePreparedFile = writePreparedWith Cache.writeCache

writePreparedWith :: (FilePath -> Cache.Manifest -> Bytecode.FullProgram -> IO (Either String ())) -> FilePath -> Program -> IO (Either Failure ())
writePreparedWith write storage program = case programManifest program of
    Nothing -> return (Left (Usage (InvalidInput "a prepared file requires source provenance from loadProgram")))
    Just manifest -> case Compiler.loadPreparedProgram (programReady program) of
        Left message -> return (Left (Usage (InvalidInput message)))
        Right (stored, _) -> fmap (either (Left . Usage . InvalidInput) Right) (write storage manifest stored)

-- A loaded module remains the version that the engine admitted. Re-importing
-- it is idempotent; changed source/import resolution requires a new engine.
-- Compilation and all name checks precede the native transaction.
loadModuleIntoEngine :: Supply -> Engine -> FilePath -> IO (Either Failure ())
loadModuleIntoEngine supply engine path = engineAccess engine $ do
    before <- readIORef (engineProgram engine)
    tables <- readIORef (Full.engineProgram (engineRuntime engine))
    reserved <- reserveSupplyFloor supply (Compiler.loadedUniqueFloor tables)
    loaded <- case reserved of
        Left failure -> return (Left failure)
        Right () -> fmap (either (Left . Usage . InvalidInput) Right) (runSupply supply (Loader.loadMainWithDiagnostic DiagnosticTest BETA.theInitialKindDecls BETA.theInitialTypeDecls [] path))
    case loaded of
        Left failure -> return (Left failure)
        Right module' -> do
            manifest <- Cache.manifestFor module'
            let known = Map.fromList [(source, (digest, imports)) | (source, digest, imports) <- maybe [] Cache.manifestSources (programManifest before)]
                changed = [source | (source, digest, imports) <- Cache.manifestSources manifest, Just old <- [Map.lookup source known], old /= (digest, imports)]
                additions = [env | source <- Loader.moduleEnvClosure (Loader.loadedMain module'), Map.notMember source known, Just env <- [Map.lookup source (Loader.loadedAll module')]]
                kinds = Map.unions (map Loader.moduleEnvOwnKinds additions)
                types = Map.unions (map Loader.moduleEnvOwnTypes additions)
                facts = concatMap Loader.moduleEnvOwnFacts additions
            case changed of
                source : _ -> return (Left (Usage (InvalidInput ("an already loaded module or its imports changed; reload the engine: " ++ source))))
                [] -> do
                    let original = fromMaybe manifest (programManifest before)
                        rows = maybe [] Cache.manifestSources (programManifest before) ++ [row | row@(source, _, _) <- Cache.manifestSources manifest, Map.notMember source known]
                        combined = original { Cache.manifestSources = rows }
                    -- Facts and their provenance commit together, including cancellation.
                    mask_ $ do
                        result <- if null additions then return (Right ()) else extendModuleLocked engine kinds types facts
                        case result of
                            Left failure -> return (Left failure)
                            Right () -> do
                                modifyIORef' (engineProgram engine) (\program -> program { programManifest = Just combined })
                                return (Right ())

data Operation = Inspect | Assign | Begin | End | Capture | Restore | Abandon | Continue | Configure | ResourceLimit | Trace | Instantiate | Close deriving (Eq, Show)
data Phase = BetweenCalls | DebuggerStop | StepFailureStop | ServiceStop | OracleStop | AnswerStop | Interrupted | Closed deriving (Eq, Show)

data UsageError
    = WrongThread
    | ClosedSession
    | BusyEngine
    | InterruptedSession
    | WrongPhase Operation Phase
    | ActiveStep
    | StaleStep
    | NoActiveGoal
    | WrongSnapshot
    | ClosedSnapshot
    | StaleProgramMark
    | InvalidInput String
    | AssignmentRejected AssignmentFailure
    | StaleOracle
    | UnsupportedBackend Operation
    deriving (Eq, Show)

data ExecutionError
    = WorkLimitExceeded
    | MemoryLimitExceeded
    | IdentityLimitExceeded
    | EngineFault String
    | InvalidGoal TermNode
    | InvalidFact TermNode
    | UnsupportedArithmetic TermNode
    deriving (Eq, Show)

data Failure = Usage UsageError | Execution ExecutionError deriving (Eq, Show)

-- Malformed host values and interrupted checked callbacks use this internal
-- exception. Other user exceptions and cancellation keep their identities.
newtype HostInputError = HostInputError Failure deriving (Show)
instance Exception HostInputError

describeFailure :: Failure -> String
describeFailure failure = case failure of
    Usage (InvalidInput message) -> message
    Usage (AssignmentRejected failure) -> assignmentMessage failure
    Execution (EngineFault message) -> message
    Execution WorkLimitExceeded -> "Native term work limit exceeded"
    Execution MemoryLimitExceeded -> "Native memory limit exceeded"
    Execution IdentityLimitExceeded -> "Host variable identity limit exceeded"
    _ -> show failure

identityFailure :: IO (Either Failure a) -> IO (Either Failure a)
identityFailure action = action `catch` \UniqueExhausted -> return (Left (Execution IdentityLimitExceeded))

data GoalView
    = GoalView
        { goalTerm       :: TermNode
        , goalHypotheses :: [TermNode]
        , goalScope      :: Int
        }
    deriving (Eq, Show)

data NominalView
    = NominalView
        { nominalConstant :: Constant
        , nominalType     :: Maybe (MonoType Int)
        , nominalName     :: Maybe String
        , nominalScope    :: Int
        }
    deriving ()

data VariableView
    = VariableView
        { variableIdentity :: LogicVar
        , variableType     :: Maybe (MonoType Int)
        , variableScope    :: Int
        }
    deriving ()

data ProofState
    = ProofState
        { proofReason      :: DebugReason
        , proofGoals       :: [GoalView]
        , proofNominals    :: [NominalView]
        , proofVariables   :: [VariableView]
        , proofConstraints :: [Constraint]
        }
    deriving ()

-- Callbacks borrow their session on the calling thread. Holding the Session
-- value is harmless; every operation checks its lifetime and current phase.
-- A host that reads only some hypotheses of the current goal names their
-- predicates in hostFocus. Its ProofState then has that goal alone and, of
-- its hypotheses, the facts and clauses of those predicates; the variables
-- and nominals are those of what is left and of the constraints. An engine
-- need not prepare the rest of a continuation for such a host.
data HostConfig
    = HostConfig
        { hostDebug   :: Session -> ProofState -> IO ()
        , hostPrint   :: Session -> Context -> TermNode -> IO ()
        , hostRead    :: Session -> Context -> TermNode -> IO (Maybe TermNode)
        , hostOracle  :: Session -> Context -> Question -> IO Bool
        , hostAnswer  :: Session -> Context -> IO ()
        , hostTracing :: Bool
        , hostFocus   :: Maybe [Constant]
        }
    deriving ()

defaultHostConfig :: HostConfig
defaultHostConfig = HostConfig (\_ _ -> return ()) (\_ _ _ -> return ()) (\_ _ _ -> return Nothing) (\_ _ _ -> return False) (\_ _ -> return ()) False Nothing

data Running = Reference (IORef (Maybe Context)) | Compiled Full.Session deriving ()

data Session
    = Session
        { sessionRuntime   :: Runtime.RuntimeEnv
        , sessionRunning   :: Running
        , sessionSupply    :: Supply
        , sessionClosed    :: IORef Bool
        , sessionCallback  :: IORef (Maybe Phase)
        , sessionStep      :: IORef (Maybe StepId)
        , sessionFailure   :: IORef (Maybe StepId)
        , sessionConfig    :: HostConfig
        , sessionStarted   :: IORef Bool
        , sessionAnswer    :: IORef (Maybe Context)
        , sessionInterrupt :: IORef (Maybe Failure)
        }
    deriving ()

data Outcome = Answer Context | NoAnswer | StepFailure StepId deriving ()

data Engine
    = Engine
        { engineRuntime :: Full.Engine
        , engineProgram :: IORef Program
        , engineBusy    :: IORef Bool
        , engineClosed  :: IORef Bool
        }
    deriving ()

createEngine :: Program -> IO (Either Failure Engine)
createEngine program = do
    created <- Full.createEngine (programReady program)
    case created of
        Left message -> return (Left (Execution (EngineFault message)))
        Right engine -> Right <$> (Engine engine <$> newIORef program <*> newIORef False <*> newIORef False)

nativeFailure :: (Machine.ErrorCode, String) -> Failure
nativeFailure (code, message) = case code of
    Machine.UsageError -> Usage (InvalidInput message)
    Machine.WorkLimitError -> Execution WorkLimitExceeded
    Machine.MemoryLimitError -> Execution MemoryLimitExceeded
    _ -> Execution (EngineFault message)

createEngineWithLimit :: Word64 -> Program -> IO (Either Failure Engine)
createEngineWithLimit limit program = do
    created <- Full.createEngineWithLimit limit (programReady program)
    case created of
        Left failure -> return (Left (nativeFailure failure))
        Right engine -> Right <$> (Engine engine <$> newIORef program <*> newIORef False <*> newIORef False)

forkEngine :: Engine -> IO (Either Failure Engine)
forkEngine engine = engineAccess engine $ do
    forked <- Full.forkEngine (engineRuntime engine)
    case forked of
        Left message -> return (Left (Execution (EngineFault message)))
        Right native -> do
            program <- readIORef (engineProgram engine)
            Right <$> (Engine native <$> newIORef program <*> newIORef False <*> newIORef False)

engineAccess :: Engine -> IO (Either Failure a) -> IO (Either Failure a)
engineAccess engine action = identityFailure $ mask $ \restore -> do
    closed <- readIORef (engineClosed engine)
    taken <- if closed then return False else atomicModifyIORef' (engineBusy engine) (\busy -> (True, not busy))
    if closed then return (Left (Usage ClosedSession)) else if not taken then return (Left (Usage BusyEngine)) else restore action `finally` writeIORef (engineBusy engine) False

engineResult :: IO (Either String a) -> IO (Either Failure a)
engineResult action = fmap (either (Left . Execution . EngineFault) Right) action

extendEngine :: Engine -> [TermNode] -> IO (Either Failure ())
extendEngine engine facts = extendModule engine Map.empty Map.empty facts

-- The declarations and facts have been checked by the Hol frontend. A failed
-- stage publishes neither native code nor the host's new type environment.
extendModule :: Engine -> KindEnv -> TypeEnv -> [TermNode] -> IO (Either Failure ())
extendModule engine kinds types facts = engineAccess engine (withInputTerms facts (extendModuleLocked engine kinds types facts))

extendModuleLocked :: Engine -> KindEnv -> TypeEnv -> [TermNode] -> IO (Either Failure ())
extendModuleLocked engine kinds types facts = mask_ $ do
    result <- Full.extendEngineEnvironment (engineRuntime engine) kinds types facts
    case result of
        Left message -> do
            code <- Machine.getErrorCode (Full.engineMachine (engineRuntime engine))
            return $ Left $ case code of
                Right Machine.MemoryLimitError -> Execution MemoryLimitExceeded
                Right Machine.WorkLimitError -> Execution WorkLimitExceeded
                _ -> Usage (InvalidInput message)
        Right () -> do
            modifyIORef' (engineProgram engine) (\program -> program { storedKinds = Map.union kinds (programKinds program), storedTypes = Map.union types (programTypes program), storedFacts = programFacts program ++ facts })
            return (Right ())

leaveEngine :: Engine -> IO (Either Failure ())
leaveEngine engine = engineAccess engine (engineResult (Full.leaveEngine (engineRuntime engine)))

closeEngine :: Engine -> IO (Either Failure ())
closeEngine engine = engineAccess engine $ do
    Full.closeEngine (engineRuntime engine)
    writeIORef (engineClosed engine) True
    return (Right ())

data ProgramMark
    = ProgramMark
        { programMarkOwner :: IORef Bool
        , programMarkValue :: MVar (Maybe (Full.ProgramMark, Program))
        }
    deriving ()

markProgram :: Engine -> IO (Either Failure ProgramMark)
markProgram engine = engineAccess engine $ do
    saved <- Full.markProgram (engineRuntime engine)
    case saved of
        Left message -> return (Left (Execution (EngineFault message)))
        Right native -> do
            program <- readIORef (engineProgram engine)
            Right . ProgramMark (engineClosed engine) <$> newMVar (Just (native, program))

truncateProgram :: Engine -> ProgramMark -> IO (Either Failure ())
truncateProgram engine saved = engineAccess engine $ mask_ $
    if programMarkOwner saved /= engineClosed engine then return (Left (Usage StaleProgramMark)) else withMVar (programMarkValue saved) $ \captured -> case captured of
        Nothing -> return (Left (Usage StaleProgramMark))
        Just (native, program) -> do
            result <- Full.truncateProgram (engineRuntime engine) native
            case result of
                Right () -> Right () <$ writeIORef (engineProgram engine) program
                Left message -> do
                    code <- Machine.getErrorCode (Full.engineMachine (engineRuntime engine))
                    return $ Left $ case code of
                        Right Machine.UsageError -> Usage StaleProgramMark
                        Right actual -> nativeFailure (actual, message)
                        _ -> Execution (EngineFault message)

closeProgramMark :: ProgramMark -> IO ()
closeProgramMark saved = modifyMVar_ (programMarkValue saved) $ \captured -> do
    mapM_ (Full.closeProgramMark . fst) captured
    return Nothing

makeRuntime :: Program -> Map.Map LogicVar (MonoType Int) -> HostConfig -> IO (Runtime.RuntimeEnv, IORef (Maybe Session), IORef (Maybe Context), IORef (Maybe Phase))
makeRuntime program queryTypes config = do
    holder <- newIORef Nothing
    answer <- newIORef Nothing
    phase <- newIORef Nothing
    pending <- newIORef mempty
    debugging <- newIORef (hostTracing config)
    verbose <- newIORef False
    stack <- newIORef []
    names <- newIORef initialCache
    control <- Runtime.newRuntimeControl
    let callback where' action = bracket (readIORef phase <* writeIORef phase (Just where')) (writeIORef phase) $ \_ -> do
            session <- readIORef holder >>= maybe (ioError (userError "uninitialized embedding callback")) return
            writeIORef (sessionStarted session) True
            writeIORef (sessionAnswer session) Nothing
            checkedCallback session (action session)
        debuggerPhase event = case Runtime.debugReason event of
            StepFailed _ -> StepFailureStop
            _ -> DebuggerStop
        env = Runtime.RuntimeEnv
            { Runtime._Debugger = \_ event -> callback (debuggerPhase event) $ \session -> do
                case Runtime.debugReason event of
                    StepFailed identity -> writeIORef (sessionFailure session) (Just identity)
                    _ -> return ()
                waiting <- readIORef pending
                let context = Runtime.debugContext event
                    normalize = rewrite NF . bindVars (_TotalVarBinding context)
                    terms = case (sessionRunning session, Runtime.debugReason event) of
                        (Compiled _, StepFailed _) -> normalize
                        (Compiled _, _)
                            | Map.null (unVarBinding waiting)
                            , Map.null (unVarBinding (_TotalVarBinding context)) -> id
                        _ -> normalize
                -- FullRuntime calls this native branch only after applying
                -- pending edits and exporting every frame in native NF. Keep
                -- that view's exact sharing, hints, types and locations when
                -- no substitution remains. A nonempty host substitution can
                -- also change display metadata, even on unaffected terms.
                -- Failure replay, interpreter stops and inspect still bind
                -- and normalize their stored host terms below.
                hostDebug config session (proofStateWithTerms (hostFocus config) terms env (Runtime.debugReason event) context (Runtime.debugStack event))
            , Runtime._RuntimeControl = control
            , Runtime._Answer = \context -> do
                writeIORef answer (Just context)
                modifyIORef' stack (drop 1)
                return False
            , Runtime._PrintPrimitive = \context term -> callback ServiceStop (\session -> hostPrint config session (publicContext context) term)
            , Runtime._ReadPrimitive = \context term -> callback ServiceStop $ \session -> do
                value <- hostRead config session (publicContext context) term
                case value of
                    Nothing -> return Nothing
                    Just result -> either (throwIO . HostInputError) (const (return value)) (validateInputTerms [result])
            , Runtime._OraclePrimitive = \context question -> callback OracleStop (\session -> hostOracle config session (publicContext context) (Question (sessionClosed session) question))
            , Runtime._TypeInfo = queryTypes
            , Runtime._PendingSubst = pending
            , Runtime._ProgramKindEnv = programKinds program
            , Runtime._ProgramTypeEnv = programTypes program
            , Runtime._VerboseTyping = verbose
            , Runtime._StackRef = stack
            , Runtime._NameCacheRef = names
            , Runtime._DebuggingRef = debugging
            , Runtime._NotationDB = initial
            , Runtime._ModuleName = "embedding"
            , Runtime._QueryCallId = Nothing
            }
    return (env, holder, answer, phase)

-- A focus is a set of predicates: the native engine is given each one once
-- and keeps as many as there are. What it refuses is a failure of this call,
-- as for the interpreter, and no exception.
assembleSession :: Supply -> HostConfig -> Runtime.RuntimeEnv -> Running -> IORef (Maybe Phase) -> IORef (Maybe Session) -> IO (Either Failure Session)
assembleSession supply config env running phase holder = do
    session <- Session env running supply <$> newIORef False <*> pure phase <*> newIORef Nothing <*> newIORef Nothing <*> pure config <*> newIORef False <*> newIORef Nothing <*> newIORef Nothing
    configured <- case running of
        Compiled native -> do
            scoped <- Full.enableScopedExports native
            focused <- either (return . Left) (const (Full.setDebugFocus native (nub <$> hostFocus config))) scoped
            either (fmap Left . machineFailure (Full.sessionMachine native)) (return . Right) focused
        Reference _ -> return (Right ())
    case configured of
        Left failure -> return (Left failure)
        Right () -> do
            writeIORef holder (Just session)
            return (Right session)

openSession :: Backend -> Supply -> Program -> Map.Map LogicVar (MonoType Int) -> TermNode -> HostConfig -> IO (Either Failure Session)
openSession backend supply program queryTypes query config = openSessionWithFacts backend supply program [] queryTypes query config

openSessionWithFacts :: Backend -> Supply -> Program -> [TermNode] -> Map.Map LogicVar (MonoType Int) -> TermNode -> HostConfig -> IO (Either Failure Session)
openSessionWithFacts backend supply program additional queryTypes query config = openSessionWithFactsLimit 0 backend supply program additional queryTypes query config

openSessionWithLimit :: Word64 -> Backend -> Supply -> Program -> Map.Map LogicVar (MonoType Int) -> TermNode -> HostConfig -> IO (Either Failure Session)
openSessionWithLimit limit backend supply program = openSessionWithFactsLimit limit backend supply program []

reserveSupply :: Supply -> Bytecode.FullProgram -> IO (Either Failure ())
reserveSupply supply program = either (return . Left . Usage . InvalidInput) (reserveSupplyFloor supply) (Bytecode.fullUniqueFloor program)

reserveSupplyFloor :: Supply -> Int -> IO (Either Failure ())
reserveSupplyFloor (Supply counter _) first
    | first == maxBound = return (Left (Execution IdentityLimitExceeded))
    | otherwise = Right () <$ atomicModifyIORef' counter (\next -> (max first next, ()))

openSessionWithFactsLimit :: Word64 -> Backend -> Supply -> Program -> [TermNode] -> Map.Map LogicVar (MonoType Int) -> TermNode -> HostConfig -> IO (Either Failure Session)
openSessionWithFactsLimit limit backend supply program additional queryTypes query config = identityFailure (openSessionWithFactsLimitActive limit backend supply program additional queryTypes query config)

openSessionWithFactsLimitActive :: Word64 -> Backend -> Supply -> Program -> [TermNode] -> Map.Map LogicVar (MonoType Int) -> TermNode -> HostConfig -> IO (Either Failure Session)
openSessionWithFactsLimitActive limit backend supply program additional queryTypes query config
    | Left invalid <- validateInputTerms (query : additional) = return (Left invalid)
openSessionWithFactsLimitActive limit backend supply program additional queryTypes query config
    | Left invalid <- Loader.validateGoalTerm query = return (Left (Usage (InvalidInput ("invalid query goal: " ++ show invalid))))
openSessionWithFactsLimitActive limit backend supply program additional queryTypes query config = case Compiler.compilePreparedProgram (programReady program) (Map.restrictKeys queryTypes (getLVars query)) additional query of
    Left message -> return (Left (Usage (InvalidInput message)))
    Right code -> do
        reserved <- reserveSupply supply code
        case reserved of
            Left failure -> return (Left failure)
            Right () -> do
                (env, holder, answer, phase) <- makeRuntime program (Map.restrictKeys queryTypes (getLVars query)) config
                case backend of
                    Native -> do
                        created <- Full.createSessionWithLimit limit env (Runtime._DebuggingRef env) code
                        case created of
                            Left failure -> return (Left (nativeFailure failure))
                            Right native -> do
                                assembled <- assembleSession supply config (Full.sessionEnvironment native) (Compiled native) phase holder
                                case assembled of
                                    Left failure -> Full.closeSession native >> return (Left failure)
                                    Right session -> return (Right session)
                    Interpreter
                        | limit /= 0 -> return (Left (Usage (UnsupportedBackend Configure)))
                        | otherwise -> case BETA.addIndex (programFacts program ++ additional) of
                            Left error' -> return (Left (kernelFailure error'))
                            Right facts -> do
                                identity <- runSupply supply getUnique
                                let labels = Runtime.initialQueryLabeling env query (Labeling IntMap.empty IntMap.empty IntMap.empty IntMap.empty Map.empty IntMap.empty (programTypes program) Map.empty False)
                                    context = Runtime.Context mempty labels [] identity (Runtime._DebuggingRef env)
                                    cell = Runtime.mkCell facts [] Runtime.emptyArithStore 0 query identity
                                writeIORef (Runtime._StackRef env) [(context, [cell])]
                                assembleSession supply config env (Reference answer) phase holder

withSession :: Backend -> Supply -> Program -> Map.Map LogicVar (MonoType Int) -> TermNode -> HostConfig -> (Session -> IO a) -> IO (Either Failure a)
withSession backend supply program = withSessionFacts backend supply program []

withSessionFacts :: Backend -> Supply -> Program -> [TermNode] -> Map.Map LogicVar (MonoType Int) -> TermNode -> HostConfig -> (Session -> IO a) -> IO (Either Failure a)
withSessionFacts = withSessionFactsWithLimit 0

withSessionFactsWithLimit :: Word64 -> Backend -> Supply -> Program -> [TermNode] -> Map.Map LogicVar (MonoType Int) -> TermNode -> HostConfig -> (Session -> IO a) -> IO (Either Failure a)
withSessionFactsWithLimit limit backend supply program facts queryTypes query config action = mask $ \restore -> do
    opened <- openSessionWithFactsLimit limit backend supply program facts queryTypes query config
    case opened of
        Left failure -> return (Left failure)
        Right session -> Right <$> (restore (action session) `finally` void (closeSession session))

withQuery :: Supply -> HostConfig -> Engine -> Map.Map LogicVar (MonoType Int) -> TermNode -> (Session -> IO a) -> IO (Either Failure a)
withQuery supply config engine queryTypes query action = engineAccess engine $ withInputTerms [query] $ case Loader.validateGoalTerm query of
    Left invalid -> return (Left (Usage (InvalidInput ("invalid query goal: " ++ show invalid))))
    Right () -> do
        program <- readIORef (engineProgram engine)
        let actualTypes = Map.restrictKeys queryTypes (getLVars query)
        (env, holder, _, phase) <- makeRuntime program actualTypes config
        result <- Full.withQuery env (Runtime._DebuggingRef env) (engineRuntime engine) actualTypes query $ \native -> do
            reserved <- reserveSupplyFloor supply (Full.sessionUniqueFloor native)
            case reserved of
                Left failure -> return (Left failure)
                Right () -> do
                    assembled <- assembleSession supply config (Full.sessionEnvironment native) (Compiled native) phase holder
                    case assembled of
                        Left failure -> return (Left failure)
                        Right session -> Right <$> (action session `finally` writeIORef (sessionClosed session) True)
        case result of
            Right value -> return value
            Left message -> Left <$> machineFailure (Full.engineMachine (engineRuntime engine)) message

phaseOf :: Session -> Runtime.RuntimeControl -> IO Phase
phaseOf session control
    | Runtime.runtimeInterrupted control = return Interrupted
    | otherwise = do
        callback <- readIORef (sessionCallback session)
        return (fromMaybe BetweenCalls callback)

permitted :: Operation -> Phase -> Bool
permitted operation phase = case phase of
    Closed -> False
    Interrupted -> operation `elem` [Restore, Close, ResourceLimit]
    BetweenCalls -> operation /= Instantiate
    DebuggerStop -> operation `notElem` [Continue, Close, Instantiate]
    StepFailureStop -> operation `elem` [Inspect, End, Capture, Restore, Abandon, Configure, ResourceLimit, Trace]
    ServiceStop -> operation `elem` [Inspect, Capture]
    OracleStop -> operation `elem` [Inspect, Capture, Instantiate]
    AnswerStop -> operation `elem` [Inspect, Capture]

-- Claim before checking the phase. Another thread cannot slip between the
-- permission check and the legacy operation, including on an idle session.
access :: Session -> Operation -> IO (Either Failure a) -> IO (Either Failure a)
access session operation action = mask $ \restore -> do
    caller <- myThreadId
    let controlRef = Runtime._RuntimeControl (sessionRuntime session)
    closed <- readIORef (sessionClosed session)
    claimed <- if closed then return (Left ClosedSession) else atomicModifyIORef' controlRef $ \control ->
        if maybe False (/= caller) (Runtime.runtimeOwner control) then (control, Left WrongThread) else (control { Runtime.runtimeOwner = Just caller }, Right (Runtime.runtimeOwner control))
    case claimed of
        Left problem -> return (Left (Usage problem))
        Right previous -> flip finally (modifyIORef' controlRef (\control -> control { Runtime.runtimeOwner = previous })) $ do
            control <- readIORef controlRef
            phase <- phaseOf session control
            if not (permitted operation phase) then return (Left (Usage (if phase == Interrupted then InterruptedSession else WrongPhase operation phase))) else (restore action >>= remember) `catch` exhausted
    where
        remember result = do
            interrupted <- Runtime.runtimeInterrupted <$> readIORef (Runtime._RuntimeControl (sessionRuntime session))
            case result of
                Left failure
                    | interrupted && failure /= Usage InterruptedSession -> modifyIORef' (sessionInterrupt session) (Just . fromMaybe failure)
                _ -> return ()
            return result
        exhausted UniqueExhausted = do
            Runtime.markRuntimeInterrupted (sessionRuntime session)
            remember (Left (Execution IdentityLimitExceeded))

-- A callback cannot turn an interrupted nested operation into successful
-- engine continuation by ignoring its typed result. Restore may clear the
-- interrupted state before the callback returns.
checkedCallback :: Session -> IO a -> IO a
checkedCallback session action = do
    value <- action
    interrupted <- Runtime.runtimeInterrupted <$> readIORef (Runtime._RuntimeControl (sessionRuntime session))
    when interrupted $ do
        failure <- fromMaybe (Usage InterruptedSession) <$> readIORef (sessionInterrupt session)
        throwIO (HostInputError failure)
    return value

kernelFailure :: Runtime.KernelErr -> Failure
kernelFailure failure = Execution $ case failure of
    Runtime.BackendError message -> EngineFault message
    Runtime.BadGoalGiven term -> InvalidGoal term
    Runtime.BadFactGiven term -> InvalidFact term
    Runtime.UnsupportedArithmeticConstraint term -> UnsupportedArithmetic term

nextSolution :: Session -> IO (Either Failure Outcome)
nextSolution session = access session Continue $ mask $ \restore -> do
    writeIORef (sessionStarted session) True
    writeIORef (sessionAnswer session) Nothing
    let env = sessionRuntime session
        run = case sessionRunning session of
            Compiled native -> do
                outcome <- runSupply (sessionSupply session) (runExceptT (Full.nextSolution native))
                case outcome of
                    Right value -> return (Right value)
                    Left failure -> do
                        code <- Machine.getErrorCode (Full.sessionMachine native)
                        return $ Left $ case code of
                            Right Machine.WorkLimitError -> Execution WorkLimitExceeded
                            Right Machine.MemoryLimitError -> Execution MemoryLimitExceeded
                            _ -> kernelFailure failure
            Reference answer -> do
                writeIORef answer Nothing
                stack <- readIORef (Runtime._StackRef env)
                result <- runSupply (sessionSupply session) (runExceptT (Runtime.runTransition env (Map.keysSet (Runtime._TypeInfo env)) stack))
                case result of
                    Left failure -> return (Left (kernelFailure failure))
                    Right _ -> Right <$> readIORef answer
        completed = do
            result <- run
            case result of
                Left failure -> return (Left failure)
                Right (Just original) -> do
                    let context = publicContext original
                    writeIORef (sessionAnswer session) (Just context)
                    bracket (readIORef (sessionCallback session) <* writeIORef (sessionCallback session) (Just AnswerStop)) (writeIORef (sessionCallback session)) (\_ -> Runtime.withRuntimePhase env Runtime.RuntimeService (checkedCallback session (hostAnswer (sessionConfig session) session context)))
                    return (Right (Answer context))
                Right Nothing -> maybe (Right NoAnswer) (Right . StepFailure) <$> readIORef (sessionFailure session)
        invalidHostInput (HostInputError failure) = Runtime.markRuntimeInterrupted env >> return (Left failure)
    (restore completed `catch` invalidHostInput) `onException` Runtime.markRuntimeInterrupted env

closeSession :: Session -> IO (Either Failure ())
closeSession session = access session Close $ do
    case sessionRunning session of
        Compiled native -> Full.closeSession native
        Reference _ -> Runtime.runRuntime Runtime.cmdQuit (sessionRuntime session)
    writeIORef (sessionClosed session) True
    return (Right ())

-- Residual constraints form a conjunction. The public boundary fixes their
-- kind order without changing either engine's legacy Context representation.
publicContext :: Context -> Context
publicContext context = context { _LeftConstraints = orderedConstraints (_LeftConstraints context) }

orderedConstraints :: [Constraint] -> [Constraint]
orderedConstraints = sortOn rank where
    rank constraint = case constraint of
        DisagreementConstraint _ -> 0 :: Int
        EvalutionConstraint _ _ -> 1
        ArithmeticConstraint _ _ -> 2
        PresburgerConstraint _ _ _ -> 3

proofState :: Maybe [Constant] -> Runtime.RuntimeEnv -> DebugReason -> Context -> Runtime.Stack -> ProofState
proofState focus env reason context = proofStateWithTerms focus (rewrite NF . bindVars (_TotalVarBinding context)) env reason context

-- The predicate of a hypothesis: that of an atomic fact, and that of the
-- conclusion of a clause under its quantifiers and conditions.
factPredicate :: TermNode -> Maybe Constant
factPredicate fact = case unfoldlNApp (rewrite HNF fact) of
    (NCon (DC (DC_LO LO_pi)) _, [NLam _ _ body _]) -> factPredicate body
    (NCon (DC (DC_LO LO_ty_pi)) _, [NLam _ _ body _]) -> factPredicate body
    (NCon (DC (DC_LO LO_if)) _, [conclusion, _]) -> factPredicate conclusion
    (NCon constant _, _) -> Just constant
    _ -> Nothing

-- The goal of a focused state as a cell: its hypotheses of the named predicates.
focusedCell :: [Constant] -> VarBinding -> Runtime.Cell -> Runtime.Cell
focusedCell predicates binding cell = cell { Runtime._GivenHypos = filter (maybe False (`elem` predicates) . factPredicate . rewrite NF . bindVars binding) (Runtime._GivenHypos cell) }

proofStateWithTerms :: Maybe [Constant] -> (TermNode -> TermNode) -> Runtime.RuntimeEnv -> DebugReason -> Context -> Runtime.Stack -> ProofState
proofStateWithTerms focus term env reason context frames = ProofState reason goals nominals variables constraints where
    active = case frames of
        (_, found) : _ -> found
        [] -> []
    cells = maybe active (const (take 1 active)) focus
    kept = case focus of
        Nothing -> const True
        Just predicates -> \fact -> maybe False (`elem` predicates) (factPredicate fact)
    binding = _TotalVarBinding context
    constraints = orderedConstraints (map (zonkLVar binding) (_LeftConstraints context))
    goals = [GoalView (term (Runtime._WantedGoal cell)) (filter kept (map term (reverse (Runtime._GivenHypos cell)))) (Runtime._ScopeLevel cell) | cell <- cells]
    roots = concat [[goalTerm goal] ++ goalHypotheses goal | goal <- goals]
    labels = Runtime._CurrentLabeling context
    visible = Set.unions (map getLVars (roots ++ concatMap Runtime.constraintTerms constraints))
    variables = [VariableView variable (Runtime.variableType env context variable) (lookupLabel variable labels) | variable <- Set.toAscList visible]
    constants = fst (Runtime.occurrences (roots ++ concatMap Runtime.constraintTerms constraints))
    nominals = sortOn nominalScope [NominalView constant (Runtime.specializeType (Runtime._ProgramKindEnv env) binding <$> lookupConType constant labels) (unDispHint hint) (lookupLabel constant labels) | constant@(DC (DC_Unique unique hint)) <- constants, IntMap.member (unUnique unique) (_ConLabel labels)]

inspect :: Session -> IO (Either Failure ProofState)
inspect session = access session Inspect $ do
    callback <- readIORef (sessionCallback session)
    started <- readIORef (sessionStarted session)
    answer <- readIORef (sessionAnswer session)
    let env = sessionRuntime session
        focus = hostFocus (sessionConfig session)
    if not started || callback `elem` [Just ServiceStop, Just OracleStop] then return (Left (Usage NoActiveGoal)) else case answer of
        Just context -> return (Right (proofState focus env DebugTrace context []))
        Nothing -> do
            (rawFrames, pending) <- Runtime.runtimeView env
            frames <- case sessionRunning session of
                Reference _ -> return rawFrames
                Compiled native -> Full.exposedView native
            control <- readIORef (Runtime._RuntimeControl env)
            case frames of
                [] -> return (Left (Usage NoActiveGoal))
                (context, _) : _ -> do
                    failed <- readIORef (sessionFailure session)
                    label <- case sessionRunning session of
                        Reference _ -> return (Runtime.runtimeLabel control)
                        Compiled native -> readIORef (Full.sessionDebugLabel native)
                    let reason = maybe (maybe DebugTrace DebugGoal label) StepFailed failed
                        viewed = map (\(ctx, goals) -> (zonkLVar pending ctx, map (zonkLVar pending) goals)) frames
                    return (Right (proofState focus env reason (zonkLVar pending context) viewed))

assign :: Session -> LogicVar -> TermNode -> IO (Either Failure ())
assign session variable term = access session Assign $ withInputTerms [term] $ do
    started <- readIORef (sessionStarted session)
    answered <- maybe False (const True) <$> readIORef (sessionAnswer session)
    failed <- readIORef (sessionFailure session)
    if not started || answered then return (Left (Usage NoActiveGoal)) else if maybe False (const True) failed then return (Left (Usage (WrongPhase Assign StepFailureStop))) else do
        let checked = do
                result <- Runtime.runRuntime (Runtime.cmdAssignVarChecked variable term) (sessionRuntime session)
                return (either (Left . Usage . AssignmentRejected) Right result)
            stack = Runtime._StackRef (sessionRuntime session)
            unknown = Left (Usage (AssignmentRejected (AssignmentFailure AssignmentUnknownVariable "unknown or inactive variable")))
        -- Under a focus the right to a target is settled first, by the
        -- projected state alone and for both backends alike; the checks of
        -- the value then use the whole context of each.
        permitted <- maybe (return True) (const (focusedTarget session variable)) (hostFocus (sessionConfig session))
        if not permitted then return unknown else case sessionRunning session of
            Reference _ -> checked
            Compiled native -> do
                viewed <- runSupply (sessionSupply session) (runExceptT (Full.debugAssignmentView native variable))
                case viewed of
                    Left failure -> do
                        Runtime.markRuntimeInterrupted (sessionRuntime session)
                        case failure of
                            Runtime.BackendError message -> Left <$> machineFailure (Full.sessionMachine native) message
                            _ -> return (Left (kernelFailure failure))
                    Right Nothing -> return unknown
                    Right (Just frames) -> bracket (readIORef stack <* writeIORef stack frames) (writeIORef stack) (const checked)

-- The target of an assignment under a focus is a variable of the projected
-- state, the one that inspect shows, or a named variable of the query. A
-- variable that only a hidden hypothesis or a binding outside that state
-- still has is not one, in either backend.
focusedTarget :: Session -> LogicVar -> IO Bool
focusedTarget session variable = do
    let env = sessionRuntime session
    (rawFrames, pending) <- Runtime.runtimeView env
    frames <- case sessionRunning session of
        Reference _ -> return rawFrames
        Compiled native -> Full.exposedView native
    return $ case frames of
        [] -> True
        (context, _) : _ -> Runtime.namedQueryVariable env context variable || variable `elem` map variableIdentity (proofVariables shown) where
            shown = proofState (hostFocus (sessionConfig session)) env DebugTrace (zonkLVar pending context) viewed
            viewed = map (\(ctx, goals) -> (zonkLVar pending ctx, map (zonkLVar pending) goals)) frames

-- An oracle edit is a tentative branch value, distinct from a debugger
-- assignment. Only the question's live capability can enter that mode.
tryInstantiate :: Session -> Question -> LogicVar -> TermNode -> IO (Either Failure ())
tryInstantiate session (Question owner question) variable value = access session Instantiate $
    if owner /= sessionClosed session then return (Left (Usage StaleOracle)) else withInputTerms [value] $ case Runtime._QuestionEdit question of
        Nothing -> return (Left (Usage StaleOracle))
        Just enter -> do
            entered <- try enter
            case entered of
                Left exception -> oracleCapabilityFailure session exception
                Right _ -> do
                    result <- Runtime.runRuntime (Runtime.cmdAssignVarChecked variable value) (sessionRuntime session)
                    return (either (Left . Usage . AssignmentRejected) Right result)

captureOracleCheckpoint :: Session -> Question -> IO (Either Failure OracleCheckpoint)
captureOracleCheckpoint session (Question owner question) = access session Instantiate $
    if owner /= sessionClosed session then return (Left (Usage StaleOracle)) else case Runtime._QuestionCheckpoint question of
        Nothing -> return (Left (Usage StaleOracle))
        Just capture -> do
            captured <- try capture
            case captured of
                Left exception -> oracleCapabilityFailure session exception
                Right saved -> do
                    thread <- myThreadId
                    return (Right (OracleCheckpoint owner thread saved))

oracleCapabilityFailure :: Session -> IOException -> IO (Either Failure a)
oracleCapabilityFailure session _ = case sessionRunning session of
    Reference _ -> return (Left (Usage StaleOracle))
    Compiled native -> do
        code <- Machine.getErrorCode (Full.sessionMachine native)
        return (Left (case code of
            Right Machine.WorkLimitError -> Execution WorkLimitExceeded
            Right Machine.MemoryLimitError -> Execution MemoryLimitExceeded
            _ -> Usage StaleOracle))

restoreOracleCheckpoint :: OracleCheckpoint -> IO (Either Failure ())
restoreOracleCheckpoint (OracleCheckpoint owner thread saved) = do
    closed <- readIORef owner
    caller <- myThreadId
    if closed then return (Left (Usage ClosedSession)) else if caller /= thread then return (Left (Usage WrongThread)) else fmap (either (const (Left (Usage StaleOracle))) Right) (Runtime.restoreOracleCheckpoint saved)

beginStep :: Session -> IO (Either Failure StepId)
beginStep session = access session Begin $ do
    started <- readIORef (sessionStarted session)
    answered <- maybe False (const True) <$> readIORef (sessionAnswer session)
    active <- readIORef (sessionStep session)
    frames <- case sessionRunning session of
        Reference _ -> readIORef (Runtime._StackRef (sessionRuntime session))
        Compiled native -> Full.exposedView native
    if not started || answered then return (Left (Usage NoActiveGoal)) else if maybe False (const True) active then return (Left (Usage ActiveStep)) else if null frames then return (Left (Usage NoActiveGoal)) else do
        result <- case sessionRunning session of
            Reference _ -> Runtime.runRuntime Runtime.beginStep (sessionRuntime session)
            Compiled native -> Full.beginStep native
        case result of
            Left message -> return (Left (Execution (EngineFault message)))
            Right identity -> do
                writeIORef (sessionStep session) (Just identity)
                return (Right identity)

endStep :: Session -> StepId -> IO (Either Failure ())
endStep session identity = access session End $ do
    active <- readIORef (sessionStep session)
    if active /= Just identity then return (Left (Usage StaleStep)) else do
        result <- case sessionRunning session of
            Reference _ -> Runtime.runRuntime (Runtime.endStep identity) (sessionRuntime session)
            Compiled native -> Full.endStep native identity
        case result of
            Left message -> return (Left (Execution (EngineFault message)))
            Right () -> do
                writeIORef (sessionStep session) Nothing
                writeIORef (sessionFailure session) Nothing
                return (Right ())

data Saved = ReferenceSnapshot Runtime.Snapshot | CompiledSnapshot Full.Snapshot deriving ()

data Snapshot
    = Snapshot
        { snapshotOwner :: IORef Bool
        , snapshotValue :: MVar (Maybe Captured)
        }
    deriving ()

data Captured
    = Captured
        { snapshotState   :: Saved
        , snapshotStep    :: Maybe StepId
        , snapshotFailure :: Maybe StepId
        , snapshotStarted :: Bool
        , snapshotAnswer  :: Maybe Context
        }
    deriving ()

takeSnapshot :: Session -> IO (Either Failure Snapshot)
takeSnapshot session = access session Capture $ do
    captured <- case sessionRunning session of
        Reference _ -> Right . ReferenceSnapshot <$> Runtime.runRuntime Runtime.snapshot (sessionRuntime session)
        Compiled native -> do
            result <- Full.takeSnapshot native
            case result of
                Left message -> Left <$> machineFailure (Full.sessionMachine native) message
                Right value -> return (Right (CompiledSnapshot value))
    case captured of
        Left failure -> return (Left failure)
        Right saved -> do
            value <- Captured saved <$> readIORef (sessionStep session) <*> readIORef (sessionFailure session) <*> readIORef (sessionStarted session) <*> readIORef (sessionAnswer session)
            Right . Snapshot (sessionClosed session) <$> newMVar (Just value)

restoreSnapshot :: Session -> Snapshot -> IO (Either Failure ())
restoreSnapshot = restoreSnapshotUsing False

-- Transfer a saved execution state instead of allocating a replacement copy.
-- Success closes this snapshot; rejected owner/lifetime/phase checks and a
-- failed native preflight preserve it. The ordinary restore remains reusable.
restoreSnapshotConsuming :: Session -> Snapshot -> IO (Either Failure ())
restoreSnapshotConsuming = restoreSnapshotUsing True

restoreSnapshotUsing :: Bool -> Session -> Snapshot -> IO (Either Failure ())
restoreSnapshotUsing consume session snapshot = access session Restore $
    if snapshotOwner snapshot /= sessionClosed session then return (Left (Usage WrongSnapshot)) else mask_ $ modifyMVar (snapshotValue snapshot) $ \captured -> case captured of
        Nothing -> return (Nothing, Left (Usage ClosedSnapshot))
        Just saved -> do
            result <- case (sessionRunning session, snapshotState saved) of
                (Reference _, ReferenceSnapshot state) -> do
                    restored <- Runtime.runRuntime (Runtime.restore state) (sessionRuntime session)
                    return (either (Left . Execution . EngineFault) Right restored)
                (Compiled native, CompiledSnapshot state) -> do
                    restored <- (if consume then Full.restoreSnapshotConsuming else Full.restoreSnapshot) native state
                    case restored of
                        Left message -> Left <$> machineFailure (Full.sessionMachine native) message
                        Right () -> return (Right ())
                _ -> return (Left (Usage WrongSnapshot))
            case result of
                Left failure -> return (captured, Left failure)
                Right () -> do
                    writeIORef (sessionStep session) (snapshotStep saved)
                    writeIORef (sessionFailure session) (snapshotFailure saved)
                    writeIORef (sessionStarted session) (snapshotStarted saved)
                    writeIORef (sessionAnswer session) (snapshotAnswer saved)
                    writeIORef (sessionInterrupt session) Nothing
                    return (if consume then Nothing else captured, Right ())

-- Closing releases the host maps and views too. The payload lock makes close
-- racing with restore either a completed restore or a typed ClosedSnapshot.
closeSnapshot :: Snapshot -> IO ()
closeSnapshot saved = modifyMVar_ (snapshotValue saved) $ \captured -> do
    case fmap snapshotState captured of
        Just (CompiledSnapshot state) -> Full.closeSnapshot state
        _ -> return ()
    return Nothing

abandon :: Session -> IO (Either Failure ())
abandon session = access session Abandon $ do
    Runtime.runRuntime Runtime.cmdQuit (sessionRuntime session)
    result <- case sessionRunning session of
        Reference _ -> return (Right ())
        Compiled native -> Full.abandonStep native
    writeIORef (sessionStep session) Nothing
    writeIORef (sessionFailure session) Nothing
    return (either (Left . Execution . EngineFault) Right result)

setTracing :: Session -> Bool -> IO (Either Failure ())
setTracing session enabled = access session Trace $ do
    writeIORef (Runtime._DebuggingRef (sessionRuntime session)) enabled
    return (Right ())

setWorkLimit :: Session -> Word64 -> IO (Either Failure ())
setWorkLimit session limit = access session ResourceLimit $
    if limit == 0 then return (Left (Usage (InvalidInput "the work limit must be positive"))) else nativeOperation session (\native -> Full.setWorkLimit native limit)

setEngineMemoryLimit :: Engine -> Word64 -> IO (Either Failure ())
setEngineMemoryLimit engine limit = engineAccess engine $ do
    result <- Machine.setMemoryLimit (Full.engineMachine (engineRuntime engine)) limit
    case result of
        Right () -> return (Right ())
        Left message -> do
            code <- Machine.getErrorCode (Full.engineMachine (engineRuntime engine))
            return (Left (nativeFailure (either (const Machine.InternalError) id code, message)))

setMemoryLimit :: Session -> Word64 -> IO (Either Failure ())
setMemoryLimit session limit = access session ResourceLimit $ nativeOperation session (\native -> Full.setMemoryLimit native limit)

getMemoryLimit :: Session -> IO (Either Failure Word64)
getMemoryLimit session = access session ResourceLimit $ nativeOperation session Full.getMemoryLimit

sessionStats :: Session -> IO (Either Failure NativeStats)
sessionStats session = access session ResourceLimit $ nativeOperation session (Machine.getStats . Full.sessionMachine)

setCounting :: Session -> Bool -> IO (Either Failure ())
setCounting session enabled = access session Configure $ nativeOperation session (\native -> Machine.setCounting (Full.sessionMachine native) enabled)

setLegacyCopy :: Session -> Bool -> IO (Either Failure ())
setLegacyCopy session enabled = access session Configure $ nativeOperation session (\native -> Machine.setLegacyCopy (Full.sessionMachine native) enabled)

setCollectionStep :: Session -> Word64 -> IO (Either Failure ())
setCollectionStep session interval = access session Configure $ nativeOperation session (\native -> Machine.setCollectionStep (Full.sessionMachine native) interval)

nativeOperation :: Session -> (Full.Session -> IO (Either String a)) -> IO (Either Failure a)
nativeOperation session action = case sessionRunning session of
    Reference _ -> return (Left (Usage (UnsupportedBackend Configure)))
    Compiled native -> do
        result <- action native
        case result of
            Right value -> return (Right value)
            Left message -> Left <$> machineFailure (Full.sessionMachine native) message

machineFailure :: Machine.Machine -> String -> IO Failure
machineFailure machine message = do
    code <- Machine.getErrorCode machine
    return (nativeFailure (either (const Machine.InternalError) id code, message))
