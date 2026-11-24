{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ScopedTypeVariables #-}

-- A proof is one suspended Hol query on one owner thread. This module only
-- transports raw syntax and controls that query; Qed admission belongs to the
-- document layer and its independent ground kernel.
module LoL.Proof.Session
    ( ProofSession, RequestId, StateId, GoalId (..), ProofView (..)
    , LocalBinding (..), ProofFailure (..), ProofReply (ProofAdvanced, ProofRestored, ProofAborted), restoredCode
    , startProof, startProofWithUniverses, startProofWithStatement, startSectionProof, submitProof, restoreProof, pruneProofHistory, configureProofHistory, cancelProof, closeProof
    , extendAfterAdmission, completedProposal, completedTheorem, describeUnsettled, describeRefusedStep, describeProofFailure, distinct, inspectTerm
    ) where

import Control.Concurrent
import Control.Exception
import Control.Monad (foldM, forM_, unless, void, when)
import qualified Control.Monad.Trans.Class as Trans
import qualified Control.Monad.Trans.State.Strict as State
import qualified Data.Graph as Graph
import Data.IORef
import Data.List (elemIndex, find, sortOn)
import qualified Data.Map.Strict as Map
import Data.Maybe (listToMaybe)
import Data.Ord (Down (..))
import Data.Word (Word64)
import qualified Data.Set as Set
import qualified Hol.V2.Embedding as Hol
import qualified LoL.Core as Core
import qualified LoL.Diagnostic as Diagnostic
import qualified LoL.Env as Env
import qualified LoL.Front.ArgumentScopes as ArgScopes
import qualified LoL.Front.Fixity as Fixity
import qualified LoL.Front.Syntax as Front
import qualified LoL.Hol.Elab as Elab
import qualified LoL.Hol.Embed as Embed
import LoL.Hol.Embed (Info (..), Report (..), binderHint, binderOf, embedList, embedTerm, embedUniverseConstraints, kindOf, named, natural, recoverList, recoverOpenList, recoverReport, recoverString, recoverTerm, recoverUniverseConstraints, reifyUniverseSlots, scopedUniverseSlots, termType, universePool)
import qualified LoL.Hol.Session as Kernel
import qualified LoL.Proof.Command as Command
import System.IO.Error (ioeGetErrorString, isUserError)

-- These are internal monotone identifiers; the document revision is separate.
type RequestId = Integer
type StateId = Integer

-- This identifies the focused debugger pause, not an equivalence class of
-- logical obligations. A restored snapshot restores it; a successful tactic
-- may create a new pause even when it leaves the same expected type/context.
newtype GoalId = GoalId Hol.LogicVar deriving (Eq, Ord, Show)

data LocalBinding
    = LocalBinding
        { localName  :: String
        , localHint  :: String
        , localValue :: Hol.TermNode
        , localType  :: Maybe Hol.TermNode
        , localBody  :: Maybe Hol.TermNode
        }
    deriving ()

data ProofView
    = ProofView
        { proofStateId            :: !StateId
        , proofRetained           :: ![(StateId, Maybe StateId)]
        , proofGoalId             :: !(Maybe GoalId)
        , proofFocusPosition      :: !(Maybe Integer)
        , proofRegions            :: ![Hol.TermNode]
        , proofExpected           :: !Hol.TermNode
        , proofLocals             :: ![LocalBinding]
        , proofMachine            :: !(Maybe Hol.ProofState)
        , proofPositions          :: !(Map.Map Integer Front.Span)
        , proofProposal           :: !(Maybe Core.Term)
        , proofReports            :: ![Hol.TermNode]
        , proofNativeBytes        :: !Word64
        , proofPeakNative         :: !Word64
        , proofUniverses          :: !Core.UniverseContext
        , proofUniverseParameters :: ![Hol.TermNode]
        , proofUniversePool       :: !(Maybe Hol.Unique)
        , proofRecorded           :: !(Maybe [Core.UniverseConstraint])
        , proofTheorem            :: !(Maybe (Either [String] (Core.UniverseContext, Core.Term, [Core.Level])))
        }
    deriving ()

-- Recover the same proof-local indices and universe slots for the goal
-- display and for read-only searches in this debugger view.
inspectTerm :: ProofView -> Hol.TermNode -> Either String Core.Term
inspectTerm view value = do
    slots <- scopedUniverseSlots (proofUniversePool view) (proofUniverseParameters view)
    reified <- reifyUniverseSlots slots value
    Embed.recoverWith (\term -> elemIndex term (map localValue (proofLocals view))) [] reified

-- proofUniverses names the universes that a view shows: those of the
-- statement, and then the universes of the proof that are still open, `_0`,
-- `_1`, ... in the order in which they were made (a level that is left out
-- is written `_`). proofUniverseParameters
-- are their runtime levels in that order. proofRecorded is what the kernel
-- has recorded of those universes while the proof went on, under the same
-- names and in the order of the record (Rocq: Show Universes), or nothing
-- when the record has no such reading. A proof that has no goal left has
-- proofTheorem: the universes and the statement that its end settled (with
-- the term in proofProposal) and the level at which each universe marker of
-- the written statement ended, or the rules by which they could not be
-- settled. Such a proof stands, and its Qed is refused (as Rocq refuses the
-- Qed of a proof whose constraints are not the declared ones).

data ProofFailure
    = ClosedProof
    | StaleProofState StateId StateId
    | ReusedRequest RequestId
    | ExpiredProofState StateId
    | InvalidProofCommand String
    | ProofDiagnostic Diagnostic.Diagnostic
    | ProofBudgetExceeded Word64 Word64
    | ProofRuntimeFailure String
    | ProofResourceFailure String
    deriving (Eq, Show)

instance Exception ProofFailure

describeProofFailure :: ProofFailure -> String
describeProofFailure failure = case failure of
    ClosedProof -> "The proof session is closed."
    StaleProofState expected actual -> "The proof state is stale: expected " ++ show expected ++ ", current " ++ show actual ++ "."
    ReusedRequest _ -> "The proof request ID was already used."
    ExpiredProofState _ -> "The requested proof state is no longer retained."
    InvalidProofCommand message -> message
    ProofDiagnostic diagnostic -> Diagnostic.diagnosticText diagnostic
    ProofBudgetExceeded limit used -> "The native proof budget was exceeded (" ++ show used ++ " of " ++ show limit ++ " bytes)."
    ProofRuntimeFailure message -> message
    ProofResourceFailure message -> message

data ProofReply
    = ProofAdvanced ProofView
    | Recovered ProofView Recovery
    | ProofAborted
    deriving ()

data Recovery = Recovery String String

pattern ProofRestored :: ProofView -> String -> ProofReply
pattern ProofRestored view message <- Recovered view (Recovery _ message) where
    ProofRestored view message = Recovered view (refusal message)

{-# COMPLETE ProofAdvanced, ProofRestored, ProofAborted #-}

restoredCode :: ProofReply -> String
restoredCode (Recovered _ (Recovery code _)) = code
restoredCode _ = "P-Internal"

refusal :: String -> Recovery
refusal = Recovery "P-StepFailed"

limited :: String -> Recovery
limited = Recovery "R5"

engineRecovery :: Hol.Failure -> Recovery
engineRecovery failure = case failure of
    Hol.Execution Hol.MemoryLimitExceeded -> limited message
    Hol.Execution Hol.WorkLimitExceeded -> limited message
    Hol.Execution Hol.IdentityLimitExceeded -> limited message
    _ -> refusal message
    where
        message = Hol.describeFailure failure

data Activity = Starting | Waiting | Executing RequestId | Cancelling RequestId | Restoring | Stopped deriving (Eq)

data Control
    = Control
        { controlActivity :: Activity
        , controlLast     :: RequestId
        , controlReply    :: Maybe (MVar (Either ProofFailure ProofReply))
        , controlClosing  :: Bool
        }
    deriving ()

data Input = CommandInput Command.Command | RestoreInput StateId | PruneInput (Set.Set StateId) (Maybe Word64) | CloseInput deriving ()

data Request
    = Request
        { requestId       :: RequestId
        , requestExpected :: Maybe StateId
        , requestInput    :: Input
        , requestReply    :: MVar (Either ProofFailure ProofReply)
        }
    deriving ()

data ProofSession
    = ProofSession
        { proofInbox   :: Chan Request
        , proofControl :: MVar Control
        , proofGate    :: MVar ()
        , proofThread  :: MVar ThreadId
        , proofDone    :: MVar ()
        }
    deriving ()

data Focus
    = Focus
        { focusPosition           :: Integer
        , focusExpected           :: Hol.TermNode
        , focusCommand            :: Hol.LogicVar
        , focusLocals             :: [LocalBinding]
        , focusAliases            :: [(String, Hol.TermNode)]
        , focusRegions            :: [Hol.TermNode]
        , focusUniverseParameters :: [Hol.TermNode]
        , focusUniversePool       :: Maybe Hol.Unique
        , focusUniverses          :: Core.UniverseContext
        , focusRecorded           :: Maybe [Core.UniverseConstraint]
        }
    deriving ()

-- How a proof starts: from a statement that is elaborated, under a context
-- that is all that the theorem has (p_universe_start), or from the statement
-- as it is written (p_universe_statement).
data Start
    = StartClosed Core.UniverseContext Core.Term
    | StartStatement Elab.Statement [String] [Core.ConstId]
    deriving ()

-- What the end of a proof gave.
data Finished
    = Settled Core.UniverseContext Core.Term Core.Term [Core.Level]
    | Unsettled [String]
    deriving ()

data Saved
    = Saved
        { savedView     :: ProofView
        , savedParent   :: Maybe StateId
        , savedOrigin   :: StateId
        , savedSnapshot :: Hol.Snapshot
        }
    deriving ()

data Pending
    = Pending
        { pendingRequest :: Request
        , pendingBefore  :: StateId
        , pendingStep    :: Hol.StepId
        , pendingTimer   :: Maybe ThreadId
        }
    deriving ()

data Replay
    = Replay
        { replayRequest  :: Request
        , replayTarget   :: StateId
        , replayReason   :: Recovery
        , replayConsumed :: Bool
        }
    deriving ()

data Worker
    = Worker
        { workerCurrent   :: Maybe StateId
        , workerStates    :: Map.Map StateId Saved
        , workerNextState :: StateId
        , workerNextPos   :: Integer
        , workerPositions :: Map.Map Integer Front.Span
        , workerPending   :: Maybe Pending
        , workerReplay    :: Maybe Replay
        , workerClosing   :: Maybe Request
        , workerHandling  :: Maybe Request
        , workerReports   :: [Hol.TermNode]
        , workerUniverses :: Core.UniverseContext
        , workerRoot      :: Maybe (Hol.TermNode, [Hol.TermNode], Maybe Hol.Unique, Core.UniverseContext)
        , workerStatement :: Maybe Core.Term
        }
    deriving ()

-- workerUniverses are the universes that the statement names, with their
-- constraints: a term of a command may name them. workerRoot is the first
-- goal with the levels of the universes of its statement and all its
-- universe levels, which a proof that could not be settled shows again. workerStatement is the statement of a proof that started
-- with p_start: a proof program answers that entry with a term alone.

-- Only these typed, private signals have control meaning. Other exceptions
-- close the worker and remain failures; an oracle exception is never Undo.
data ControlSignal = Rewind Request StateId Recovery | StopProof Request | CancelStep RequestId Recovery deriving ()
instance Show ControlSignal where
    show _ = "proof worker control signal"
instance Exception ControlSignal

completedProposal :: ProofView -> Either String (Maybe (Core.Term, Core.Term))
completedProposal view = case (proofTheorem view, proofProposal view) of
    (Just (Right (_, typ, _)), Just body) -> Right (Just (body, typ))
    (Just (Left rules), _) -> Left (describeUnsettled rules)
    _ -> Right Nothing

-- The theorem that a proof without a goal gives: its universes, its
-- statement, its term and the levels of the markers of its statement.
completedTheorem :: ProofView -> Either [String] (Maybe (Core.UniverseContext, Core.Term, Core.Term, [Core.Level]))
completedTheorem view = case (proofTheorem view, proofProposal view) of
    (Just (Right (universes, typ, marks)), Just body) -> Right (Just (universes, typ, body, marks))
    (Just (Left rules), _) -> Left rules
    _ -> Right Nothing

-- Why the universes of a proof could not be settled, by the first rule that
-- the proof program reported.
describeUnsettled :: [String] -> String
describeUnsettled rules = case rules of
    "E-Declared" : _ -> "The proof needs a universe constraint that the theorem does not declare: write it in the constraints of the theorem (Rocq: Universe constraints are not implied by the ones declared)."
    "E-Set" : _ -> "The proof puts a universe of the theorem below Set: no such universe is made (Rocq: Cannot enforce u <= Set)."
    "E-Algebraic" : _ -> "The proof needs a level below a maximum or a successor, and the constraints do not put it there (Rocq: cannot handle algebraic on the right)."
    "E-Universes" : _ -> "The universe constraints of the proof have no model (Rocq: universe inconsistency)."
    rule : _ -> "The universes of the proof could not be settled [" ++ rule ++ "]."
    [] -> "The universes of the proof could not be settled."

-- Why a command was refused for its universes, when the proof program
-- reported that: the state that the proof returned to has the reports of
-- the command.
describeRefusedStep :: ProofView -> Maybe String
describeRefusedStep view = case [text | Right (Report rule _ _) <- map recoverReport (proofReports view), Just text <- [explain rule]] of
    text : _ -> Just text
    [] -> Nothing
    where
        explain rule = case rule of
            "E-Universes" -> Just "The proof step failed: the universe constraints of the proof would have no model (Rocq: universe inconsistency)."
            "E-Set" -> Just "The proof step failed: it puts a universe that is not flexible below Set (Rocq: Cannot enforce u <= Set)."
            "E-Algebraic" -> Just "The proof step failed: it needs a level below a maximum or a successor, and the constraints do not put it there (Rocq: cannot handle algebraic on the right)."
            "P-NameUsed" -> Just "The proof step failed: a name that it gives is the name of a hypothesis already, or is given twice (Rocq: H is already used)."
            "P-ContextCycle" -> Just "The proof step failed: the proposed type would make the local context cyclic."
            "P-Used" -> Just "The proof step failed: the hypothesis that it would replace is used in another hypothesis or in the goal (Rocq: Cannot change H, it is used in ...)."
            "P-NothingToInject" -> Just "The proof step failed: the two sides are not applications of one constructor (Rocq: Nothing to inject)."
            "P-InjectionFamily" -> Just "Dependent injection needs a compatible dependent-pair family in scope. Import lol.theories.Sigma or give one family the visible name sigT."
            "P-SimplOccurrence" -> Just "The simpl occurrence number exceeds the number of matching applications."
            "P-SimplOverlap" -> Just "Two selected simpl occurrences overlap."
            "P-NoInjection" -> Just "The proof step failed: the two sides differ at no position that injection can use (Rocq: No information can be deduced from this equality)."
            _ -> Nothing

startProof :: Kernel.Kernel -> Kernel.Kernel -> Kernel.Limits -> Env.Env -> Core.Term -> IO (Either ProofFailure (ProofSession, ProofView))
startProof base program limits environment = startProofWithUniverses base program limits environment Core.emptyUniverses

startProofWithUniverses :: Kernel.Kernel -> Kernel.Kernel -> Kernel.Limits -> Env.Env -> Core.UniverseContext -> Core.Term -> IO (Either ProofFailure (ProofSession, ProofView))
startProofWithUniverses base program limits environment universes expected
    | not (Env.validUniverses universes && Core.wellScopedUniverses (length (Core.universeNames universes)) 0 expected) = return (Left (InvalidProofCommand "The proof type or universe context is not closed."))
    | otherwise = startWith base program limits environment universes (StartClosed universes expected)

-- The statement of a theorem as it is written. The names of its universes
-- are those that a term of a command may use; a statement that names none
-- has none.
-- `introduced` are the names of the binders of the header: they are in the
-- context of the first goal, as in Rocq.
startProofWithStatement :: Kernel.Kernel -> Kernel.Kernel -> Kernel.Limits -> Env.Env -> Core.UniverseContext -> Elab.Statement -> [String] -> IO (Either ProofFailure (ProofSession, ProofView))
startProofWithStatement base program limits environment universes statement introduced = startSectionProof base program limits environment universes statement introduced []

startSectionProof :: Kernel.Kernel -> Kernel.Kernel -> Kernel.Limits -> Env.Env -> Core.UniverseContext -> Elab.Statement -> [String] -> [Core.ConstId] -> IO (Either ProofFailure (ProofSession, ProofView))
startSectionProof base program limits environment universes statement introduced section = startWith base program limits environment universes (StartStatement statement introduced section)

startWith :: Kernel.Kernel -> Kernel.Kernel -> Kernel.Limits -> Env.Env -> Core.UniverseContext -> Start -> IO (Either ProofFailure (ProofSession, ProofView))
startWith base program limits environment universes begin = mask $ \restore -> do
    handle <- ProofSession <$> newChan <*> newMVar (Control Starting (-1) Nothing False) <*> newMVar () <*> newEmptyMVar <*> newEmptyMVar
    first <- newEmptyMVar
    void $ forkIO $ do
        owner <- myThreadId
        putMVar (proofThread handle) owner
        worker <- newIORef $ Worker Nothing Map.empty 0 1 Map.empty Nothing Nothing Nothing Nothing [] universes Nothing $ case begin of
            StartClosed context expected
                | context == Core.emptyUniverses -> Just expected
            _ -> Nothing
        let startupTimeout = do
                threadDelay (Kernel.limitMicros limits)
                modifyMVar_ (proofControl handle) $ \control -> case controlActivity control of
                    Starting -> do
                        throwTo owner (ProofResourceFailure "The initial proof state time limit was reached.")
                        return control { controlActivity = Cancelling (-1) }
                    _ -> return control
        startupTimer <- if Kernel.limitMicros limits <= 0 then return Nothing else Just <$> forkIO startupTimeout
        let failed :: SomeException -> IO ()
            failed exception = do
                Kernel.disableHostBudget
                let problem = maybe (ProofRuntimeFailure (describeWorkerException exception)) id (fromException exception)
                void (tryPutMVar first (Left problem))
                current <- readIORef worker
                mapM_ (replyLeft problem . pendingRequest) (workerPending current)
                mapM_ (replyLeft problem . replayRequest) (workerReplay current)
                mapM_ (replyLeft problem) (workerClosing current)
                mapM_ (replyLeft problem) (workerHandling current)
            finish = do
                Kernel.disableHostBudget
                mapM_ killThread startupTimer
                outstanding <- modifyMVar (proofControl handle) (\control -> return (control { controlActivity = Stopped }, controlReply control))
                mapM_ (\response -> void (tryPutMVar response (Left ClosedProof))) outstanding
                current <- readIORef worker
                mapM_ (replyLeft ClosedProof . pendingRequest) (workerPending current)
                mapM_ (replyLeft ClosedProof) (workerHandling current)
                mapM_ stopTimer (workerPending current)
                mapM_ (Hol.closeSnapshot . savedSnapshot) (Map.elems (workerStates current))
                void (tryPutMVar first (Left ClosedProof))
                void (tryPutMVar (proofDone handle) ())
        restore (Kernel.resetHostBudget limits >> runWorker handle worker first base program limits environment begin) `catch` failed `finally` finish
    result <- restore (takeMVar first) `onException` closeProof handle
    case result of
        Left _ -> restore (readMVar (proofDone handle))
        Right _ -> return ()
    return ((\view -> (handle, view)) <$> result)

-- What a user reads when a worker ends: the sentence of a failure that this
-- module raised, and a sentence for the allocation limit, not their Haskell
-- display.
describeWorkerException :: SomeException -> String
describeWorkerException exception = case (fromException exception, fromException exception) of
    (Just AllocationLimitExceeded, _) -> "The Haskell allocation limit was reached before the proof had a state to return to (--host-allocation-mib=N; 0 removes it)."
    (_, Just failure)
        | isUserError failure -> ioeGetErrorString failure
    _ -> displayException exception

submitProof :: ProofSession -> RequestId -> StateId -> Command.Command -> IO (Either ProofFailure ProofReply)
submitProof handle identity state command = sendRequest handle identity (Just state) (CommandInput command)

restoreProof :: ProofSession -> RequestId -> StateId -> StateId -> IO (Either ProofFailure ProofReply)
restoreProof handle identity current target = sendRequest handle identity (Just current) (RestoreInput target)

pruneProofHistory :: ProofSession -> RequestId -> StateId -> [StateId] -> IO (Either ProofFailure ProofReply)
pruneProofHistory handle identity current retained = configureProofHistory handle identity current retained Nothing

configureProofHistory :: ProofSession -> RequestId -> StateId -> [StateId] -> Maybe Word64 -> IO (Either ProofFailure ProofReply)
configureProofHistory handle identity current retained budget = sendRequest handle identity (Just current) (PruneInput (Set.fromList retained) budget)

sendRequest :: ProofSession -> RequestId -> Maybe StateId -> Input -> IO (Either ProofFailure ProofReply)
sendRequest handle identity expected input = withMVar (proofGate handle) $ \() -> mask $ \restore -> do
    response <- newEmptyMVar
    accepted <- modifyMVar (proofControl handle) $ \control -> case controlActivity control of
        Stopped -> return (control, Left ClosedProof)
        _
            | controlClosing control -> return (control, Left ClosedProof)
            | identity <= controlLast control -> return (control, Left (ReusedRequest identity))
            | otherwise -> do
                writeChan (proofInbox handle) (Request identity expected input response)
                return (control { controlLast = identity, controlReply = Just response }, Right ())
    case accepted of
        Left failure -> return (Left failure)
        Right () -> do
            result <- restore (takeMVar response)
            case result of
                Right ProofAborted -> readMVar (proofDone handle)
                _ -> return ()
            return result

-- Holding this short phase lock through synchronous delivery prevents an old
-- cancellation from arriving in a later request. Waiting itself is not killed.
cancelProof :: ProofSession -> RequestId -> IO Bool
cancelProof handle identity = cancelWith handle identity (refusal "The proof command was cancelled.")

cancelWith :: ProofSession -> RequestId -> Recovery -> IO Bool
cancelWith handle identity reason = modifyMVar (proofControl handle) $ \control -> case controlActivity control of
    Executing active
        | active == identity -> do
            owner <- readMVar (proofThread handle)
            throwTo owner (CancelStep identity reason)
            return (control { controlActivity = Cancelling identity }, True)
    _ -> return (control, False)

closeProof :: ProofSession -> IO ()
closeProof handle = mask $ \restore -> do
    response <- newEmptyMVar
    sent <- modifyMVar (proofControl handle) $ \control ->
        if controlActivity control == Stopped || controlClosing control then return (control, False) else do
            let request = Request (controlLast control + 1) Nothing CloseInput response
                closing = control { controlLast = controlLast control + 1, controlReply = Just response, controlClosing = True }
            writeChan (proofInbox handle) request
            case controlActivity control of
                Executing _ -> readMVar (proofThread handle) >>= (\owner -> throwTo owner (StopProof request))
                Starting -> readMVar (proofThread handle) >>= killThread
                _ -> return ()
            return (closing, True)
    when sent (restore (void (takeMVar response)))
    restore (readMVar (proofDone handle))

runWorker :: ProofSession -> IORef Worker -> MVar (Either ProofFailure ProofView) -> Kernel.Kernel -> Kernel.Kernel -> Kernel.Limits -> Env.Env -> Start -> IO ()
runWorker handle cell first base program limits environment begin = do
    constructorBound <- evaluate (maximum (0 : [toInteger (length (Env.familyCons family)) | entry <- Map.elems (Env.envDecls environment), Env.Inductive _ families <- [Env.entryDecl entry], family <- families]))
    case begin of
        StartClosed universeContext expected
            | universeContext /= Core.emptyUniverses -> do
                checkedType <- Env.typeOfTermWithUniverses base limits environment universeContext expected
                either (throwIO . userError . show) (const (return ())) checkedType
        _ -> return ()
    let visible = reservedProofNames environment
        initialFacts = Env.allFacts environment ++ namingFacts program visible (Map.toList (Env.envDecls environment))
        acquire = Kernel.forkWithNames program limits (Env.envStamp environment) (Just visible) initialFacts >>= either (throwIO . userError . Hol.describeFailure) return
    bracket acquire (void . Hol.closeEngine) $ \engine -> Env.withProofOracle base limits environment $ \oracle -> do
        when (Map.member (Hol.DC_Named "p_root_names") (Kernel.kernelTypes program)) $ do
            let hints = case begin of
                    StartClosed _ typ -> Elab.coreHints typ
                    StartStatement statement _ _ -> Elab.statementHints statement
                fact = Hol.mkNApp (named "p_root_names") hints
            checked (Hol.extendEngine engine [fact])
        case begin of
            StartStatement statement _ _
                | Kernel.kernelBundled program
                , Just typ <- Elab.statementCore statement
                , let raw = Hol.TyCon (Hol.TCon (Hol.TC_Named "raw") Hol.Star)
                , let expected = Hol.Forall [] (Hol.mkTyArrow raw (Hol.mkTyArrow termType Hol.mkTyO))
                , Map.lookup (Hol.DC_Named "p_checked_header") (Kernel.kernelTypes program) == Just expected ->
                    checked (Hol.extendEngine engine [Hol.foldlNApp (named "p_checked_header") [Elab.statementRaw statement, embedTerm typ]])
            _ -> return ()
        when (Map.member (Hol.DC_Named "ps_mutual") (Kernel.kernelTypes program)) $ do
            let facts = mutualFacts environment
            unless (null facts) (checked (Hol.extendEngine engine facts))
        when (Map.member (Hol.DC_Named "ps_never") (Kernel.kernelTypes program)) $ do
            let never = [Hol.mkNApp (named "ps_never") (natural i) | Core.GlobalCst i <- Set.toList (Env.syntaxNever (Env.envSyntax environment))]
            unless (null never) (checked (Hol.extendEngine engine never))
        when (Map.member (Hol.DC_Named "ps_never_field") (Kernel.kernelTypes program)) $ do
            let fields = [Hol.foldlNApp (named "ps_never_field") [natural block, natural (toInteger field)] | Core.GlobalProj block field <- Set.toList (Env.syntaxNever (Env.envSyntax environment))]
            unless (null fields) (checked (Hol.extendEngine engine fields))
        -- p_start is the entry that a proof program must have. One that
        -- knows universes has the other two (proof.hol).
        let outputs = case begin of
                StartClosed universeContext _
                    | universeContext == Core.emptyUniverses -> [Hol.LV_Named "ProofResult"]
                StartClosed _ _ -> map Hol.LV_Named ["ProofStatus", "ProofUniverseCount", "ProofUniverseConstraints", "ProofStatement", "ProofResult"]
                StartStatement _ _ _ -> map Hol.LV_Named ["ProofStatus", "ProofUniverseCount", "ProofUniverseConstraints", "ProofStatement", "ProofResult", "ProofMarks"]
            goal = case begin of
                StartClosed universeContext expected
                    | universeContext == Core.emptyUniverses -> Hol.foldlNApp (named "p_start") (embedTerm expected : map Hol.mkLVar outputs)
                StartClosed universeContext expected -> Hol.foldlNApp (named "p_universe_start")
                    ([natural (toInteger (length (Core.universeNames universeContext))), embedUniverseConstraints (Core.universeConstraints universeContext), embedTerm expected] ++ map Hol.mkLVar outputs)
                StartStatement statement introduced section -> withSection section $ Hol.foldlNApp (named "p_universe_statement") (Elab.statementPrefix statement ++ [Elab.statementRaw statement, embedList (kindOf "ptac") [Hol.foldlNApp (named "p_universe_command") [embedList (kindOf "nat") [], Hol.mkNApp (named "p_intros") (embedList (Hol.mkNApp (kindOf "list") (kindOf "char")) (map (embedList (kindOf "char") . map (Hol.mkNCon . Hol.DC_ChrL)) introduced))] | not (null introduced)]] ++ map Hol.mkLVar outputs)
            withSection section query = foldr assume query facts where
                facts = concat [[Hol.foldlNApp (named "p_name") [nameTerm (Env.entryName entry), value], Hol.foldlNApp (named "p_name_type") [value, embedTerm typ]] | c <- section, Just entry <- [Map.lookup c (Env.envDecls environment)], Env.Axiom typ <- [Env.entryDecl entry], let value = embedTerm (Core.Cst c [])]
                assume fact body = Hol.foldlNApp (Hol.mkNCon Hol.LO_imply) [fact, body]
            config = Hol.defaultHostConfig
                { Hol.hostDebug = paused handle cell first program environment constructorBound limits
                , Hol.hostOracle = \_ context question -> oracle context question
                , Hol.hostPrint = \_ _ term -> modifyIORef' cell (\worker -> worker { workerReports = take 32 (term : workerReports worker) })
                , Hol.hostFocus = Just (map (Hol.DC . Hol.DC_Named) focusPredicates)
                }
        inferred <- Hol.inferGoalTypes (Kernel.kernelFresh program) (Kernel.kernelReady program) (Env.universeGoal program environment goal)
        (typed, types) <- either (throwIO . userError . Hol.describeFailure) return inferred
        result <- Hol.withQuery (Kernel.kernelFresh program) config engine types typed $ \session -> do
            mapM_ (\limit -> checked (Hol.setWorkLimit session limit)) (Kernel.limitVisits limits)
            drive handle cell first environment outputs session
        either (throwIO . userError . Hol.describeFailure) return result

-- Only spellings are offered to the proof program. They never participate in
-- conversion or typing. The field names belong to the admitted constructor.
nameTerm :: String -> Hol.TermNode
nameTerm = embedList (kindOf "char") . map (Hol.mkNCon . Hol.DC_ChrL)

fieldHintsTerm :: [(String, String)] -> Hol.TermNode
fieldHintsTerm = embedList (kindOf "pfhint") . map field where
    field (binder, headName) = Hol.foldlNApp (named "p_field_hint") [nameTerm binder, nameTerm headName]

reservedProofNames :: Env.Env -> Set.Set String
reservedProofNames environment = Map.keysSet (Env.envNames environment) `Set.union` Env.envAmbiguous environment `Set.union` Env.notationWords (Env.envSyntax environment)

extendAfterAdmission :: Kernel.Kernel -> Env.Env -> Env.Env -> IO ()
extendAfterAdmission program before after = case (Env.envStamp after, Env.appendedFacts before after) of
    (Just next, Just (number, entry, added)) -> Kernel.extendProofCache program (Env.envStamp before) next oldNames newNames (added ++ namingFacts program (Set.difference newNames oldNames) [(number, entry)])
    _ -> return ()
    where
        oldNames = reservedProofNames before
        newNames = reservedProofNames after

namingFacts :: Kernel.Kernel -> Set.Set String -> [(Core.ConstId, Env.Entry)] -> [Hol.TermNode]
namingFacts program visible entries = concat [reserved ++ definitions ++ heads ++ concat families | supports "p_root_names"] ++ concat [premiseNameFacts entries | supports "p_signature_names"] ++ concat [projectionNameFacts entries | supports "p_projection_names"] where
    supports tag = Map.member (Hol.DC_Named tag) (Kernel.kernelTypes program)
    reserved = [Hol.mkNApp (named "p_global_name") (nameTerm label) | label <- Set.toList visible, '.' `notElem` label]
    heads = [Hol.foldlNApp (named "p_head_spelling") [embedTerm (Core.fromGlobal ref), nameTerm (shortName label)] | (number, entry) <- entries, (label, ref) <- Env.declGlobals number (Env.entryName entry) (Env.entryDecl entry), needsHead ref]
    needsHead Core.GlobalInd {} = False
    needsHead _ = True
    shortName = reverse . takeWhile (/= '.') . reverse
    definitions = concat [offered number 0 body | (number, entry) <- entries, Env.Definition _ body <- [Env.entryDecl entry]]
    offered number count (Core.Lam _ _ body) = offered number (count + 1) body
    offered number count body = case alias 0 body of
        Just (target, arity) -> [Hol.foldlNApp (named "p_definition_alias") (map natural [number, count, target, arity])]
        Nothing -> [Hol.foldlNApp (named "p_definition_names") [natural number, natural count, hints] | hints /= Elab.emptyHints]
        where
            hints = Elab.coreHints body
    alias count (Core.App fun _) = alias (count + 1) fun
    alias count (Core.Cast body _) = alias count body
    alias count (Core.Cst target _) = Just (target, count)
    alias _ _ = Nothing
    families = [describe block index count family | (block, entry) <- entries, Env.Inductive count entries <- [Env.entryDecl entry], (index, family) <- zip [0 ..] entries]
    describe block index count family = stem ++ parameterHints ++ fields where
        fact predicate tail_ = Hol.foldlNApp (named predicate) (natural block : natural index : tail_)
        stem = [fact "p_family_stem" [nameTerm (shortName (Env.familyName family))]]
        parameterHints = [fact "p_parameter_names" [embedList (Hol.mkNApp (kindOf "list") (kindOf "char")) (map nameTerm names)] | any (not . null) names]
        names = take count (map fst (fieldStems False [] (Env.familyType family)))
        fields = concat [describeFields number typ | (number, (_, typ)) <- zip [0 ..] (Env.familyCons family)]
        describeFields number typ = namedFields ++ schemeFields where
            namedFields = [fact "p_field_names" [natural number, fieldHintsTerm hints] | any (/= ("", "")) hints]
            schemeFields = [fact "p_ind_field_names" [natural number, fieldHintsTerm schemes] | schemes /= hints]
            hints = drop count (fieldStems False [] typ)
            schemes = drop count (fieldStems True [] typ)
        -- Constructor binders are explicit hints. The head of an anonymous
        -- field can be a named inline fix, or a parameter of the original
        -- induction scheme. Preserve those spellings before embedding in Hol.
        fieldStems scheme scope (Core.Pi name domain rest) = (name, headName) : fieldStems scheme (name : scope) rest where
            headName = if null name then sourceHead scheme scope 0 domain else ""
        fieldStems _ _ _ = []
        sourceHead scheme scope depth term = case term of
            Core.Fix index functions -> concatMap Core.functionName (take 1 (drop index functions))
            Core.Var index
                | scheme && index >= depth -> concat (take 1 (drop (index - depth) scope))
            Core.App fun _ -> sourceHead scheme scope depth fun
            Core.Cast body _ -> sourceHead scheme scope depth body
            Core.Pi _ _ body -> sourceHead scheme scope (depth + 1) body
            Core.Lam _ _ body -> sourceHead scheme scope (depth + 1) body
            Core.Let _ _ _ body -> sourceHead scheme scope (depth + 1) body
            _ -> ""

-- Suggestions for the premises generated by apply or constructor. Record
-- the mentioned field only when it has a telescope with a written name.
premiseNameFacts :: [(Core.ConstId, Env.Entry)] -> [Hol.TermNode]
premiseNameFacts entries = [fact key hints | (number, entry) <- entries, (key, typ) <- sources number (Env.entryDecl entry), let hints = argumentHints typ, hints /= Elab.emptyHints] where
    fact key hints = Hol.foldlNApp (named "p_signature_names") [embedTerm key, hints]
    sources n (Env.Inductive _ families) = concat [family n index item | (index, item) <- zip [0 ..] families]
    sources n decl = [(Core.Cst n [], typ) | typ <- Env.declTypes decl]
    family n i item = (Core.Ind n i [], Env.familyType item) : [(Core.Con n i j [], typ) | (j, (_, typ)) <- zip [0 ..] (Env.familyCons item)]

-- The prefix form takes the record parameters and receiver first. A dotted
-- projection has consumed both; its first argument belongs to the field.
projectionNameFacts :: [(Core.ConstId, Env.Entry)] -> [Hol.TermNode]
projectionNameFacts entries = concat [fields block count family | (block, entry) <- entries, Env.Inductive count families <- [Env.entryDecl entry], family <- families, Just _ <- [Env.familyRecord family]] where
    fields block count family = case Env.familyCons family of
        [(_, constructor)] -> [fact index field full | (index, domain) <- zip [0 ..] args, let field = argumentHints domain, let full = prefix field, full /= Elab.emptyHints]
            where
                (parameters, args) = splitAt count (domains constructor)
                prefix field = foldr (Elab.hintNode "" . Elab.coreHints) (Elab.hintNode "" Elab.emptyHints field) parameters
                fact index field full = Hol.foldlNApp (named "p_projection_names") [natural block, natural index, full, field]
        _ -> []
    domains (Core.Pi _ typ rest) = typ : domains rest
    domains _ = []

-- Only products take arguments. A let in the signature can introduce a
-- binder name for display but occupies no position in an application.
argumentHints :: Core.Term -> Hol.TermNode
argumentHints (Core.Pi _ typ body) = Elab.hintNode "" (Elab.coreHints typ) (argumentHints body)
argumentHints (Core.Let _ _ _ body) = argumentHints body
argumentHints (Core.Cast body _) = argumentHints body
argumentHints _ = Elab.emptyHints

-- Vernac admits the projections of a mutual Fixpoint consecutively, in
-- declaration order. Stored modules preserve these names and this order.
-- Send only their identities to the proof engine. Hol checks the selected
-- body at the actual universe instance before using its name.
mutualFacts :: Env.Env -> [Hol.TermNode]
mutualFacts environment = concat [members base functions | (base, entry) <- Map.toList entries, Env.Definition _ (Core.Fix 0 functions@(_ : _ : _)) <- [Env.entryDecl entry]] where
    entries = Env.envDecls environment
    members base functions
        | and (zipWith (member base) [0 ..] functions) = [Hol.foldlNApp (named "ps_mutual") [natural (base + index), natural base] | index <- [0 .. toInteger (length functions) - 1]]
        | otherwise = []
    member base index function = case Map.lookup (base + toInteger index) entries of
        Just entry
            | Env.entryName entry == Core.functionName function
            , Env.Definition _ (Core.Fix selected _) <- Env.entryDecl entry -> selected == index
        _ -> False

checked :: IO (Either Hol.Failure a) -> IO a
checked action = action >>= either (throwIO . userError . Hol.describeFailure) return

replyLeft :: ProofFailure -> Request -> IO ()
replyLeft problem request = void (tryPutMVar (requestReply request) (Left problem))

stopTimer :: Pending -> IO ()
stopTimer pending = mapM_ killThread (pendingTimer pending)

-- The worker's outer run loop is the only place that restores after a private
-- control interruption. Completed snapshots do not resume search.
drive :: ProofSession -> IORef Worker -> MVar (Either ProofFailure ProofView) -> Env.Env -> [Hol.LogicVar] -> Hol.Session -> IO ()
drive handle cell first environment outputs session = loop where
    loop = ((next `catch` allocationFailure) `catch` dispatch) >>= \again -> when again loop
    dispatch signal = control signal `catch` dispatch
    allocationFailure AllocationLimitExceeded = do
        Kernel.disableHostBudget
        worker <- readIORef cell
        case workerPending worker of
            Just pending -> restore (pendingRequest pending) (pendingBefore pending) (limited "The Haskell allocation limit of a proof command was reached (--host-allocation-mib=N; 0 removes it).")
            Nothing -> throwIO (ProofResourceFailure "The Haskell allocation limit was reached before the proof had a state to return to (--host-allocation-mib=N; 0 removes it).")
    next = do
        worker <- readIORef cell
        let proposed = workerCurrent worker >>= (`Map.lookup` workerStates worker) >>= proofTheorem . savedView
        case (proposed, workerPending worker, workerReplay worker) of
            (Just _, Nothing, Nothing) -> waitCompleted
            _ -> advance
    advance = do
        outcome <- Hol.nextSolution session
        case outcome of
            Left failure -> recover (engineRecovery failure)
            Right Hol.NoAnswer -> do
                worker <- readIORef cell
                if noInitialState worker
                    then throwIO (userError (unwords ("The kernel did not accept the statement of the theorem as a type." : ["[" ++ label ++ "]" | Right (Report label _ _) <- map recoverReport (reverse (workerReports worker))])))
                    else failed "The proof command failed."
            Right (Hol.StepFailure _) -> failed "The proof step failed."
            Right (Hol.Answer context) -> case mapM (Kernel.outputOf context) outputs of
                Left message -> failed message
                Right values
                    | not (null (Hol._LeftConstraints context)) -> failed "The proof has a residual constraint."
                    | otherwise -> do
                        worker <- readIORef cell
                        case finishedProof worker values of
                            -- An answer that cannot be read says so itself, also before the proof has a state.
                            Left message
                                | Nothing <- workerPending worker, Nothing <- workerClosing worker -> throwIO (userError message)
                                | otherwise -> failed message
                            Right finished -> do
                                committed cell (commit handle cell first session Nothing (Just finished))
                                return True
    waitCompleted = do
        request <- awaitRequest handle cell
        accepted <- validState cell request
        if not accepted then waitCompleted else case requestInput request of
            CloseInput -> throwIO (StopProof request)
            RestoreInput target -> rewind request target
            PruneInput retained budget -> pruneHistory cell session request retained budget >> waitCompleted
            CommandInput command -> case command of
                Command.ShowProof _ -> currentReply request >> waitCompleted
                Command.ShowUniverses _ -> currentReply request >> waitCompleted
                Command.UndoProof _ -> undo request
                Command.AbortProof _ -> throwIO (StopProof request)
                _ -> replyLeft (InvalidProofCommand "No proof goals remain; use Qed, Undo, or Abort.") request >> waitCompleted
    currentReply request = do
        state <- currentSaved cell
        void (tryPutMVar (requestReply request) (Right (ProofAdvanced (savedView state))))
    undo request = do
        state <- currentSaved cell
        case savedParent state of
            Nothing -> replyLeft (InvalidProofCommand "There is no earlier proof state.") request >> waitCompleted
            Just target -> rewind request target
    rewind request target = do
        exists <- Map.member target . workerStates <$> readIORef cell
        if exists then throwIO (Rewind request target (refusal "")) else replyLeft (ExpiredProofState target) request >> waitCompleted
    failed = recover . refusal
    recover reason@(Recovery code message) = do
        worker <- readIORef cell
        case workerPending worker of
            Just pending -> throwIO (Rewind (pendingRequest pending) (pendingBefore pending) reason)
            Nothing -> do
                closing <- workerClosing <$> readIORef cell
                case closing of
                    Just request -> void (tryPutMVar (requestReply request) (Right ProofAborted)) >> return False
                    Nothing
                        | code == "R5" -> throwIO (ProofResourceFailure message)
                        | otherwise -> throwIO (userError message)
    noInitialState worker = case (workerCurrent worker, workerPending worker, workerClosing worker) of
        (Nothing, Nothing, Nothing) -> True
        _ -> False
    control signal = case signal of
        StopProof request -> do
            modifyIORef' cell (\worker -> worker { workerClosing = Just request })
            void (Hol.closeSession session)
            void (tryPutMVar (requestReply request) (Right ProofAborted))
            return False
        CancelStep identity reason -> do
            worker <- readIORef cell
            case workerPending worker of
                Just pending
                    | requestId (pendingRequest pending) == identity -> restore (pendingRequest pending) (pendingBefore pending) reason
                _ -> throwIO (userError "A stale proof cancellation reached the worker.")
        Rewind request target reason -> restore request target reason
    -- The phase lock serializes rollback with a cancel already delivering to
    -- this command. Once restoring, its snapshot and debugger replay belong
    -- to the worker until it publishes a state; a later cancel has no target.
    claimRestore request reason = claim `catch` delivered where
        claim = modifyMVar_ (proofControl handle) (\state -> return state { controlActivity = Restoring }) >> return reason
        delivered (CancelStep identity message)
            | identity == requestId request = claimRestore request message
        delivered signal = throwIO signal
    restore request target original = mask_ $ do
        Kernel.disableHostBudget
        reason <- claimRestore request original
        worker <- readIORef cell
        case Map.lookup target (workerStates worker) of
            Nothing -> do
                modifyMVar_ (proofControl handle) (\state -> return state { controlActivity = Waiting })
                replyLeft (ExpiredProofState target) request
                return True
            Just saved -> do
                mapM_ stopTimer (workerPending worker)
                restored <- Hol.restoreSnapshot session (savedSnapshot saved)
                consumed <- case restored of
                    Right () -> return False
                    Left (Hol.Execution Hol.MemoryLimitExceeded) -> do
                        checked (Hol.restoreSnapshotConsuming session (savedSnapshot saved))
                        return True
                    Left failure -> throwIO (userError (Hol.describeFailure failure))
                writeIORef cell worker
                    { workerPending = Nothing
                    , workerReplay = Just (Replay request target reason consumed)
                    , workerPositions = proofPositions (savedView saved)
                    }
                case (proofTheorem (savedView saved), proofProposal (savedView saved)) of
                    (Just (Right (universes, typ, marks)), Just body) -> do
                        commit handle cell first session Nothing (Just (Settled universes typ body marks))
                        return True
                    (Just (Left rules), _) -> do
                        commit handle cell first session Nothing (Just (Unsettled rules))
                        return True
                    _ -> return True

-- What the answer of the proof program says: its status, and for a proof
-- that is settled the universes, the statement and the term of the theorem,
-- and for a statement that was given as it is written the level at which
-- each of its markers ended. The universes that the statement does not name
-- are u0, u1, ... Each of them is the level of a marker, so their number is
-- bounded by what the answer wrote before any name is made.
finishedProof :: Worker -> [Hol.TermNode] -> Either String Finished
finishedProof worker values = case values of
    [result]
        | Just statement <- workerStatement worker -> (\body -> Settled Core.emptyUniverses statement body []) <$> recoverTerm result
    Hol.NCon (Hol.DC (Hol.DC_NatL 0)) _ : Hol.NCon (Hol.DC (Hol.DC_NatL count)) _ : constraints : statement : result : marked
        | count >= toInteger (length declared) && length marked < 2 -> do
            marks <- case map recoverTerm marked of
                [] -> Right []
                [Right (Core.Cst 0 levels)] -> Right levels
                _ -> Left "The proof program did not say where the universes of the statement ended."
            obligations <- recoverUniverseConstraints constraints
            typ <- recoverTerm statement
            body <- recoverTerm result
            -- A universe is one that the statement names, one that the answer mentions or at most one more for each marker (Qed judges those).
            if count > toInteger (length declared + length marks + Set.size (Set.unions (map Core.levelParameters marks ++ map Core.termParameters [typ, body]))) then Left "The proof program returned more universes than its statement has." else Right ()
            let universes = Core.UniverseContext (declared ++ take (fromInteger count - length declared) [name | index <- [0 :: Integer ..], let name = "u" ++ show index, name `notElem` declared]) obligations
            if Env.validUniverses universes && all (Core.wellScopedUniverses (fromInteger count) 0) [typ, body] then Right (Settled universes typ body marks) else Left "The proof program returned a theorem outside its universe context."
    Hol.NCon (Hol.DC (Hol.DC_NatL status)) _ : _
        | status /= 0 -> Right (Unsettled [label | Right (Report label _ _) <- map recoverReport (reverse (workerReports worker))])
    _ -> Left "The proof program returned no theorem."
    where
        declared = Core.universeNames (workerUniverses worker)

awaitRequest :: ProofSession -> IORef Worker -> IO Request
awaitRequest handle cell = do
    request <- readChan (proofInbox handle)
    closing <- controlClosing <$> readMVar (proofControl handle)
    case requestInput request of
        CloseInput -> accepted request
        _
            | closing -> replyLeft ClosedProof request >> awaitRequest handle cell
            | otherwise -> accepted request
    where
        accepted request = modifyIORef' cell (\worker -> worker { workerHandling = Just request }) >> return request

currentSaved :: IORef Worker -> IO Saved
currentSaved cell = do
    worker <- readIORef cell
    maybe (throwIO (userError "The proof has no current state.")) return (workerCurrent worker >>= (`Map.lookup` workerStates worker))

validState :: IORef Worker -> Request -> IO Bool
validState cell request = do
    current <- workerCurrent <$> readIORef cell
    case (requestExpected request, current) of
        (Just expected, Just actual)
            | expected /= actual -> False <$ replyLeft (StaleProofState expected actual) request
        _ -> return True

descends :: Worker -> StateId -> StateId -> Bool
descends worker target identity = case Map.lookup identity (workerStates worker) >>= savedParent of
    Nothing -> False
    Just parent -> parent == target || maybe False ((== target) . savedOrigin) (Map.lookup parent (workerStates worker)) || descends worker target parent

paused :: ProofSession -> IORef Worker -> MVar (Either ProofFailure ProofView) -> Kernel.Kernel -> Env.Env -> Integer -> Kernel.Limits -> Hol.Session -> Hol.ProofState -> IO ()
paused handle cell first program environment constructorBound limits session state = case Hol.proofReason state of
    Hol.StepFailed _ -> do
        worker <- readIORef cell
        case workerPending worker of
            Just pending -> throwIO (Rewind (pendingRequest pending) (pendingBefore pending) (refusal "The proof step failed."))
            Nothing -> throwIO (userError "Unexpected proof step failure.")
    _ -> do
        checked (Hol.setTracing session False)
        declared <- workerUniverses <$> readIORef cell
        focus <- either (throwIO . userError) return (decodeFocus environment declared state)
        committed cell (commit handle cell first session (Just (state, focus)) Nothing)
        wait focus
    where
        wait focus = do
            request <- awaitRequest handle cell
            accepted <- validState cell request
            if not accepted then wait focus else case requestInput request of
                CloseInput -> throwIO (StopProof request)
                RestoreInput target -> rewind request focus target
                PruneInput retained budget -> pruneHistory cell session request retained budget >> wait focus
                CommandInput command -> case command of
                    Command.ShowProof _ -> shown request focus
                    Command.ShowUniverses _ -> shown request focus
                    Command.UndoProof _ -> do
                        current <- currentSaved cell
                        case savedParent current of
                            Nothing -> replyLeft (InvalidProofCommand "There is no earlier proof state.") request >> wait focus
                            Just target -> rewind request focus target
                    Command.AbortProof _ -> throwIO (StopProof request)
                    Command.RunTactic _ tactic -> execute request focus tactic
                    _ -> replyLeft (InvalidProofCommand "This command is not a proof step.") request >> wait focus
        shown request focus = do
            current <- currentSaved cell
            void (tryPutMVar (requestReply request) (Right (ProofAdvanced (savedView current))))
            wait focus
        rewind request focus target = do
            exists <- Map.member target . workerStates <$> readIORef cell
            if exists then throwIO (Rewind request target (refusal "")) else replyLeft (ExpiredProofState target) request >> wait focus
        execute request focus tactic = mask $ \restoreAction -> do
            worker <- readIORef cell
            current <- currentSaved cell
            step <- checked (Hol.beginStep session)
            let before = proofStateId (savedView current)
            writeIORef cell worker
                { workerPending = Just (Pending request before step Nothing)
                , workerReports = []
                }
            permitted <- modifyMVar (proofControl handle) $ \control ->
                if controlClosing control then return (control, False) else return (control { controlActivity = Executing (requestId request) }, True)
            unless permitted (throwIO (StopProof request))
            timer <- if Kernel.limitMicros limits <= 0 then return Nothing else Just <$> forkIO (threadDelay (Kernel.limitMicros limits) >> void (cancelWith handle (requestId request) (limited "The proof command time limit was reached.")))
            modifyIORef' cell (\active -> active { workerPending = fmap (\pending -> pending { pendingTimer = timer }) (workerPending active) })
            let reject failure = do
                    Kernel.disableHostBudget
                    active <- readIORef cell
                    mapM_ stopTimer (workerPending active)
                    checked (Hol.endStep session step)
                    modifyMVar_ (proofControl handle) $ \control -> do
                        modifyIORef' cell (\latest -> latest { workerPending = Nothing })
                        return control { controlActivity = Waiting }
                    replyLeft failure request
                    wait focus
            Kernel.resetHostBudget limits
            restoreAction $ case encodeTactic environment constructorBound (workerUniverses worker) (not (null (focusUniverseParameters focus))) (workerNextPos worker) (focusLocals focus) (focusAliases focus) tactic of
                Left message -> reject message
                Right (raw, positions) -> do
                    annotated <- annotateTactic program raw
                    case annotated of
                        Left message -> reject (InvalidProofCommand message)
                        Right command -> do
                            modifyIORef' cell (\active -> active
                                { workerNextPos = maybe (workerNextPos worker) ((+ 1) . fst) (Map.lookupMax positions)
                                , workerPositions = Map.union positions (workerPositions worker)
                                })
                            result <- Hol.assign session (focusCommand focus) command
                            either (\failure -> throwIO (Rewind request before (engineRecovery failure))) (const (return ())) result

-- The allocation limit can run out while a state is being published. Its
-- exception then arrives when commit unmasks: the step is over and its state
-- stands, so there is nothing to return to. One that arrives before commit
-- published is passed on: a pending step is undone, and a proof that has no
-- state yet answers its start with the failure. commit alone gives a state
-- its number, so the next number tells whether this call published.
committed :: IORef Worker -> IO () -> IO ()
committed cell = Kernel.afterPublication (workerNextState <$> readIORef cell)

-- Publication and rollback are outside the allocation limit of a command:
-- the limit covers execution and decoding, and is switched off before the
-- snapshot so that it cannot run out between the snapshot and the reply.
commit :: ProofSession -> IORef Worker -> MVar (Either ProofFailure ProofView) -> Hol.Session -> Maybe (Hol.ProofState, Focus) -> Maybe Finished -> IO ()
commit handle cell first session focus finished = mask_ $ do
    Kernel.disableHostBudget
    seen <- readIORef cell
    -- The first goal is the statement as the proof reads it.
    let presentation shown = (focusExpected shown, focusUniverseParameters shown, focusUniversePool shown, focusUniverses shown)
        worker = case (workerRoot seen, focus) of
            (Nothing, Just (_, shown)) -> seen { workerRoot = Just (presentation shown) }
            _ -> seen
        root = maybe (embedTerm Core.Prop, [], Nothing, workerUniverses worker) id (workerRoot worker)
        written = case (finished, focus) of
            (Nothing, Just (_, shown)) -> focusRecorded shown
            _ -> Just []
        ((expected, levels, pool, shownUniverses), proposal, theorem) = case (finished, focus) of
            (Just (Settled universes typ body marks), _) -> ((embedTerm typ, [], Nothing, universes), Just body, Just (Right (universes, typ, marks)))
            (Just (Unsettled rules), _) -> (root, Nothing, Just (Left rules))
            (Nothing, Just (_, shown)) -> (presentation shown, Nothing, Nothing)
            (Nothing, Nothing) -> (root, Nothing, Nothing)
    mapM_ (\pending -> stopTimer pending >> checked (Hol.endStep session (pendingStep pending))) (workerPending worker)
    unpublished <- newIORef True
    captured <- Hol.takeSnapshot session
    saved <- case captured of
        Right snapshot -> return snapshot
        Left failure -> case workerPending worker of
            Just pending -> throwIO (Rewind (pendingRequest pending) (pendingBefore pending) (engineRecovery failure))
            Nothing -> throwIO (userError (Hol.describeFailure failure))
    let abandon = readIORef unpublished >>= \owned -> when owned (Hol.closeSnapshot saved)
        publish = do
            let identity = workerNextState worker
                parent = case workerReplay worker of
                    Just replay -> Map.lookup (replayTarget replay) (workerStates worker) >>= savedParent
                    Nothing -> workerCurrent worker
                initialView = ProofView identity retained (GoalId . focusCommand . snd <$> focus) (focusPosition . snd <$> focus) (maybe [] (focusRegions . snd) focus) expected (maybe [] (focusLocals . snd) focus) (fst <$> focus) (workerPositions worker) proposal (reverse (workerReports worker)) 0 0 shownUniverses levels pool written theorem
                origin = case workerReplay worker >>= (\replay -> Map.lookup (replayTarget replay) (workerStates worker)) of
                    Just restored -> savedOrigin restored
                    Nothing -> identity
                branch = workerPending worker >>= (\pending -> savedOrigin <$> Map.lookup (pendingBefore pending) (workerStates worker))
                discarded = maybe Map.empty (\ancestor -> Map.filterWithKey (\number _ -> descends worker ancestor number) (workerStates worker)) branch
                reusable = case workerReplay worker of
                    Just replay
                        | replayConsumed replay -> Map.delete (replayTarget replay) (workerStates worker)
                    _ -> workerStates worker
                states = Map.insert identity (Saved initialView parent origin saved) (Map.difference reusable discarded)
                excess = max 0 (Map.size states - 16)
                expired = take excess (Map.toAscList states)
                kept = foldr (Map.delete . fst) states expired
                retained = [(number, savedParent entry) | (number, entry) <- Map.toAscList kept]
            forM_ retained (\(number, parentId) -> evaluate number >> evaluate (maybe (-1) id parentId))
            -- Cancellation delivers while holding proofControl. Acquire that lock before
            -- closing any old snapshot, so a cancelled publication leaves its history
            -- intact. The fresh snapshot remains locally owned until the IORef write.
            modifyMVar_ (proofControl handle) $ \control -> do
                -- Publish ownership before retirement. No reply escapes until the
                -- updated resource counters are installed below. If cleanup itself
                -- throws, the worker finalizer owns exactly the kept snapshots.
                let prepared = worker { workerCurrent = Just identity, workerStates = kept, workerNextState = identity + 1, workerPending = Nothing, workerReplay = Nothing }
                writeIORef cell prepared
                writeIORef unpublished False
                mapM_ (Hol.closeSnapshot . savedSnapshot) (Map.elems discarded)
                mapM_ (Hol.closeSnapshot . savedSnapshot . snd) expired
                statistics <- checked (Hol.sessionStats session)
                let view = initialView { proofNativeBytes = Hol.allocatedBytes statistics, proofPeakNative = Hol.peakBytes statistics }
                    finalStates = Map.adjust (\entry -> entry { savedView = view }) identity kept
                writeIORef cell prepared { workerStates = finalStates }
                void (tryPutMVar first (Right view))
                mapM_ (\pending -> void (tryPutMVar (requestReply (pendingRequest pending)) (Right (ProofAdvanced view)))) (workerPending worker)
                let replyReplay replay = void (tryPutMVar (requestReply (replayRequest replay)) (Right (Recovered view (replayReason replay))))
                mapM_ replyReplay (workerReplay worker)
                return control { controlActivity = Waiting }
    publish `onException` abandon

-- This is bookkeeping, so it preserves the semantic state ID. A document
-- can prune every retained worker to its own referenced timeline checkpoints.
pruneHistory :: IORef Worker -> Hol.Session -> Request -> Set.Set StateId -> Maybe Word64 -> IO ()
pruneHistory cell session request retained budget = mask_ $ do
    worker <- readIORef cell
    current <- currentSaved cell
    let identity = proofStateId (savedView current)
        keep = Set.insert identity retained
        (remaining, discarded) = Map.partitionWithKey (\number _ -> Set.member number keep) (workerStates worker)
        summary = [(number, savedParent entry) | (number, entry) <- Map.toAscList remaining]
    forM_ summary (\(number, parent) -> evaluate number >> evaluate (maybe (-1) id parent))
    mapM_ (Hol.closeSnapshot . savedSnapshot) (Map.elems discarded)
    statistics <- checked (Hol.sessionStats session)
    let view = (savedView current) { proofRetained = summary, proofNativeBytes = Hol.allocatedBytes statistics, proofPeakNative = Hol.peakBytes statistics }
        states = Map.adjust (\entry -> entry { savedView = view }) identity remaining
    writeIORef cell worker { workerStates = states }
    case budget of
        Just bytes
            | bytes > 0 && bytes < proofNativeBytes view -> replyLeft (ProofBudgetExceeded bytes (proofNativeBytes view)) request
        _ -> do
            configured <- maybe (return (Right ())) (Hol.setMemoryLimit session) budget
            case configured of
                Left failure -> replyLeft (ProofRuntimeFailure (Hol.describeFailure failure)) request
                Right () -> void (tryPutMVar (requestReply request) (Right (ProofAdvanced view)))

-- What decodeFocus reads of a debugger state. The rest of a suspended proof
-- (its continuation, requests and earlier holes) grows with every step and
-- is not prepared for this host.
focusPredicates :: [String]
focusPredicates = ["p_focus", "p_display_names", "p_domain_names", "p_focus_constraints", "u_parameters", "e_u_cells", "p_u_pool", "u_stream", "p_name", "p_name_type", "p_name_view", "p_name_body", "p_automatic", "p_cleared", "p_placed", "var_type", "var_body", "p_region"]

decodeFocus :: Env.Env -> Core.UniverseContext -> Hol.ProofState -> Either String Focus
decodeFocus environment declared state = case [(goal, facts, latest, position, expected, command) | goal <- Hol.proofGoals state, let facts = namedFacts goal, let latest = reverse facts, ("p_focus", [Hol.NCon (Hol.DC (Hol.DC_NatL position)) _, expected, _, Hol.LVar command]) <- latest] of
    (goal, facts, latest, position, expected, command) : _ -> do
        parameters <- case [value | ("u_parameters", [value]) <- latest] of
            value : _ -> recoverList value
            [] -> Right []
        -- The cells of the proof: every e_u_cells ends in the one registry,
        -- and the registry itself is the hypothesis without a prefix.
        registries <- mapM recoverOpenList [value | ("e_u_cells", [value]) <- facts]
        let cells = if null registries then [] else foldr1 (\one other -> if length one <= length other then one else other) registries
            levels = parameters ++ cells
        pool <- universePool (Hol.goalHypotheses goal)
        settled <- length <$> scopedUniverseSlots pool parameters
        slots <- scopedUniverseSlots pool levels
        let names = Core.universeNames declared
            fixed = take settled (names ++ ["u" ++ show index | index <- [length names ..]])
            opened = ["_" ++ show index | index <- [0 .. length slots - settled - 1]]
            universes = Core.UniverseContext (fixed ++ opened) (Core.universeConstraints declared)
            -- What the kernel has recorded (u_stream): the leaves of its chunks, in the order of the record.
            streams = [recorded (Hol.rewrite Hol.NF queue) | ("u_stream", [queue]) <- latest]
            visible = [cs | ("p_focus_constraints", [cs]) <- latest]
            written = do
                let constraints = case visible of
                        cs : _ -> cs
                        [] -> embedList (kindOf "uconstraint") (concat (take 1 streams))
                reifyUniverseSlots slots constraints >>= recoverUniverseConstraints
        bindings <- locals facts latest
        let hints = listToMaybe [tree | ("p_display_names", [tree]) <- latest]
            actual = localAliases False environment bindings
            oldNames = Map.fromList [(x, name) | ("p_automatic", [x, label]) <- facts, Right name <- [recoverString (Hol.rewrite Hol.NF label)]]
            originals = [binding { localName = old, localHint = old } | binding <- bindings, let old = Map.findWithDefault (localHint binding) (localValue binding) oldNames]
            primary = Set.fromList (map localName actual)
            legacy = [(label, localValue binding) | binding <- localAliases True environment bindings ++ localAliases True environment originals, let label = localName binding, Set.notMember label primary, Set.notMember label (reservedProofNames environment)]
        Right (Focus position (maybe expected (flip withHints expected) hints) command actual legacy [region | ("p_region", [region]) <- latest] levels pool universes (either (const Nothing) (Just . distinct) written))
    _ -> Left "The debugger stop has no well-formed proof focus."
    where
        namedFacts goal = [(name, args) | hypothesis <- Hol.goalHypotheses goal, (Hol.NCon (Hol.DC (Hol.DC_Named name)) _, args) <- [Hol.unfoldlNApp (Hol.rewrite Hol.WHNF hypothesis)]]
        -- The C machine erases lambda spellings. Decorate its exported copy
        -- for display; an eta-short HOAS binder is opened as in recoverTerm.
        withHints tree value
            | Just [label, domain, rest] <- application "p_binding" tree
            , Right hint <- recoverString label
            = case value of
                Hol.NApp (Hol.NApp hd@(Hol.NCon (Hol.DC (Hol.DC_Named "prod")) _) typ at) scope location -> Hol.NApp (Hol.NApp hd (withHints domain typ) at) (decorate hint rest scope) location
                Hol.NApp (Hol.NApp hd@(Hol.NApp (Hol.NCon (Hol.DC (Hol.DC_Named "letin")) _) _ _) typ at) scope location -> Hol.NApp (Hol.NApp hd (withHints domain typ) at) (decorate hint rest scope) location
                _ -> value
            | otherwise = value
        decorate hint rest scope = case scope of
            Hol.NLam old typ body at -> Hol.NLam (if null hint then old else binderHint hint) typ (withHints rest body) at
            _ -> Hol.NLam (binderHint hint) Hol.noLamType (withHints rest (snd (binderOf scope))) Nothing
        -- The named variables that the rest of the proof has, the latest first. One that a tactic cleared is left out
        -- (lol/hol/proof.hol, pn_clear). One that replaces another is shown where that one stood (pn_place), or after
        -- the last variable that its type mentions, as Rocq places it.
        locals facts latest = do
            places <- foldM place Map.empty (Graph.stronglyConnComp (map node entries))
            return (sortOn (\binding -> Down (Map.findWithDefault [] (localValue binding) places)) [binding | (_, binding) <- entries, Set.notMember (localValue binding) cleared])
            where
                entries = [(index, LocalBinding name name value (shownType value) (factOf ["p_name_body"] value)) | (index, (name, value)) <- zip (reverse [0 :: Int .. length named - 1]) named]
                shownType value = case factOf ["p_domain_names"] value of
                    Just hints -> withHints hints <$> actualType
                    Nothing -> actualType
                    where
                        actualType = factOf ["p_name_view", "p_name_type", "var_type"] value
                named = [(name, value) | ("p_name", [label, value]) <- latest, Right name <- [recoverString (Hol.rewrite Hol.NF label)]]
                cleared = Set.fromList [x | ("p_cleared", [x]) <- latest]
                -- Last asserted fact wins, also when two predicates supply
                -- alternative views of the same type after a tactic.
                byLocal = Map.fromListWith (++) [(local, [(tag, term)]) | (tag, [local, term]) <- facts, tag `elem` ["p_placed", "p_name_view", "p_name_type", "var_type", "var_body", "p_name_body", "p_domain_names"]]
                factOf predicates local = listToMaybe [term | (tag, term) <- Map.findWithDefault [] local byLocal, tag `elem` predicates]
                node (index, binding) = ((value, index, replaced, dependencies), value, maybe id (:) replaced dependencies) where
                    value = localValue binding
                    replaced = factOf ["p_placed"] value
                    dependencies = concatMap nominals [term | predicates <- [["p_name_type", "var_type"], ["var_body"]], Just term <- [factOf predicates value]]
                place _ (Graph.CyclicSCC _) = Left "The debugger returned a cyclic local context."
                place places (Graph.AcyclicSCC (value, index, replaced, dependencies)) = Right (Map.insert value (maximum (base : moved)) places) where
                    base = maybe [] (\old -> Map.findWithDefault [] old places) replaced ++ [index]
                    moved = [key ++ [index] | other <- dependencies, Just key <- [Map.lookup other places], key > base]
        nominals term = case term of
            Hol.NCon (Hol.DC (Hol.DC_Unique _ _)) _ -> [term]
            Hol.NApp function argument _ -> nominals function ++ nominals argument
            Hol.NLam _ _ body _ -> nominals body
            _ -> []
        recorded queue = case application "u_chunk" queue of
            Just [_, tree, _, rest] -> leaves tree ++ recorded rest
            _ -> []
        leaves tree = case (application "u_leaf" tree, application "u_branch" tree) of
            (Just [constraint], _) -> [constraint]
            (_, Just [left, _, right, _]) -> leaves left ++ leaves right
            _ -> []

-- The items of a list without their repetitions, in the order of the first
-- of each. The record of a proof repeats a constraint with every reading of
-- the term that owes it, and a proof state is decoded at every command.
distinct :: Ord a => [a] -> [a]
distinct = go Set.empty where
    go _ [] = []
    go seen (item : rest)
        | Set.member item seen = go seen rest
        | otherwise = item : go (Set.insert item seen) rest

-- Local aliases are part of the input namespace, not just presentation. Keep
-- the nearest original spelling, and reserve every real/global name before
-- freshening older shadowed hints. Undo recomputes the same aliases from its
-- restored ordered hypotheses.
localAliases :: Bool -> Env.Env -> [LocalBinding] -> [LocalBinding]
localAliases legacy environment locals = go Set.empty reserved locals where
    reserved = reservedProofNames environment `Set.union` Set.fromList (map localHint locals)
    go _ _ [] = []
    go seen used (local : rest)
        | not (null hint) && not (Set.member hint seen) = local : go (Set.insert hint seen) used rest
        | otherwise = local { localName = fresh } : go (Set.insert hint seen) (Set.insert fresh used) rest
        where
            hint = localHint local
            stem = if null hint then "x" else hint
            fresh = head (filter (\candidate -> Set.notMember candidate used) candidates)
            candidates
                | legacy = [stem ++ "_" ++ show index | index <- [0 :: Integer ..]]
                | otherwise = tail (iterate nextSpelling stem)
    nextSpelling name = case span (\digit -> digit >= '0' && digit <= '9') (reverse name) of
        ([], _) -> name ++ "0"
        (digits, prefix) -> reverse prefix ++ reverse (increment digits)
    increment [] = "1"
    increment ('9' : digits) = '0' : increment digits
    increment (digit : digits) = succ digit : digits

application :: String -> Hol.TermNode -> Maybe [Hol.TermNode]
application name term = case Hol.unfoldlNApp (Hol.rewrite Hol.WHNF term) of
    (Hol.NCon (Hol.DC (Hol.DC_Named actual)) _, arguments)
        | actual == name -> Just arguments
    _ -> Nothing

-- A command that leaves a level out, or one of a proof that has a universe
-- already (`involved`), is run as a universe command: its levels become
-- universes of the proof, and what it adds to the constraints is judged
-- (p_universe_command of proof.hol). Any other command is run as it is, so
-- that a proof program that knows no universe runs it too.
encodeTactic :: Env.Env -> Integer -> Core.UniverseContext -> Bool -> Integer -> [LocalBinding] -> [(String, Hol.TermNode)] -> Command.Tactic -> Either ProofFailure (Hol.TermNode, Map.Map Integer Front.Span)
encodeTactic environment constructorBound universes involved origin locals legacy tactic = do
    case tactic of
        Command.All _ inner -> withoutAll inner
        _ -> withoutAll tactic
    ((value, positions), (_, kinds)) <- State.runStateT (go False origin tactic) (0, [])
    return (if involved || not (null kinds) then Hol.foldlNApp (named "p_universe_command") [embedList (kindOf "nat") (map natural kinds), value] else value, positions)
    where
        withoutAll value = case value of
            Command.All {} -> Left (InvalidProofCommand "The all: selector is allowed only at the outermost tactic position.")
            Command.Then _ left right -> withoutAll left >> withoutAll right
            Command.Try _ inner -> withoutAll inner
            Command.Repeat _ inner -> withoutAll inner
            Command.First _ alternatives -> mapM_ withoutAll alternatives
            Command.Bullet _ _ _ inner -> withoutAll inner
            _ -> Right ()
        aliases = Set.fromList (map fst legacy ++ [localName local | local <- locals, localName local /= localHint local])
        references = [(localName local, localValue local) | local <- locals] ++ legacy
        string = embedList (kindOf "char") . map (Hol.mkNCon . Hol.DC_ChrL)
        following start positions = maybe start ((+ 1) . fst) (Map.lookupMax positions)
        encode deferred start term = do
            (frontier, earlier) <- State.get
            rewritten <- Trans.lift (either (Left . ProofDiagnostic) Right (Fixity.rewrite (ArgScopes.withoutNames environment [Front.Name (Front.termSpan term) n | (n,_) <- references]) term))
            let mode = if deferred then Elab.DeferredProof (length references) aliases else Elab.EagerProof
                context = if universes /= Core.emptyUniverses || Elab.needsUniverses environment rewritten then Just universes else Nothing
            (encoded, next, kinds) <- Trans.lift (either (Left . ProofDiagnostic) Right (Elab.encodeProofWithUniverses mode environment start references context frontier rewritten))
            unless (null (Elab.encodedHoles encoded)) (Trans.lift (Left (InvalidProofCommand "A proof template unexpectedly contains allocated holes.")))
            State.put (next, earlier ++ kinds)
            return (Elab.encodedTerm encoded, Elab.encodedSpans encoded)
        go deferred start tactic = case tactic of
            Command.Then _ left right -> do
                (first, before) <- go True start left
                (second, after) <- go True (following start before) right
                return (Hol.foldlNApp (named "p_then") [first, second], Map.union before after)
            Command.Try _ inner -> unary "p_try" inner
            Command.Repeat _ inner -> unary "p_repeat" inner
            Command.All _ inner -> do
                (value, positions) <- go True start inner
                return (Hol.mkNApp (named "p_all") value, positions)
            Command.First _ alternatives -> do
                (values, positions) <- manyTactics start alternatives
                return (Hol.mkNApp (named "p_first") (embedList (kindOf "ptac") values), positions)
            Command.Primitive _ primitive -> case primitive of
                Command.RefineProof term -> termCommand "p_refine" term
                Command.ExactProof term -> termCommand "p_exact" term
                Command.ApplyProof term -> termCommand "p_apply" term
                Command.IntroProof [] -> return (Hol.mkNApp (named "p_intro") (string ""), Map.empty)
                Command.IntroProof [name] -> return (Hol.mkNApp (named "p_intro") (string (Front.nameText name)), Map.empty)
                Command.IntrosProof [] -> plain "p_intros_auto"
                Command.IntrosProof names -> return (Hol.mkNApp (named "p_intros") (embedList (Hol.mkNApp (kindOf "list") (kindOf "char")) (map (string . Front.nameText) names)), Map.empty)
                Command.AssumptionProof -> plain "p_assumption"
                Command.ReflexivityProof -> plain "p_reflexivity"
                Command.SymmetryProof -> plain "p_symmetry"
                Command.ExfalsoProof -> plain "p_exfalso"
                Command.SpecializeProof term -> termCommand "p_specialize" term
                Command.AssertProof name term -> do
                    (value, positions) <- encode deferred start term
                    return (Hol.foldlNApp (named "p_assert_hinted") [string (Front.nameText name), value, Elab.surfaceHints term], positions)
                Command.InjectionProof term target -> do
                    (command, positions) <- targetedTermCommand "p_injection" term target
                    return (Hol.foldlNApp (named "pe_using_families") [embedList (kindOf "pe_family") pairFamilies, command], positions)
                Command.DiscriminateProof term target -> do
                    (evidence, before) <- case term of
                        Nothing -> return (named "pe_search", Map.empty)
                        Just written -> do
                            (value, positions) <- encode deferred start written
                            return (Hol.mkNApp (named "pe_given") value, positions)
                    (destination, after) <- targetTerm (following start before) target
                    return (Hol.foldlNApp (named "p_discriminate") [evidence, destination], Map.union before after)
                Command.TransitivityProof term -> termCommand "p_transitivity" term
                Command.DestructProof term names -> namedTermCommand "p_destruct" term names
                Command.InductionProof term names -> namedTermCommand "p_induction" term names
                Command.RewriteProof direction term target -> do
                    (value, before) <- encode deferred start term
                    (destination, after) <- targetTerm (following start before) target
                    return (Hol.foldlNApp (named "p_rewrite") [named (if direction == Command.Forward then "pe_forward" else "pe_backward"), value, destination], Map.union before after)
                Command.ChangeProof term target -> do
                    (command, positions) <- targetedTermCommand "p_change_hinted" term target
                    return (Hol.mkNApp command (Elab.surfaceHints term), positions)
                Command.SimplProof target -> do
                    (destination, positions) <- targetTerm start target
                    return (Hol.mkNApp (named "p_simpl") destination, positions)
                Command.SimplAtProof name include sites target -> do
                    (function, before) <- encode deferred start (Front.Term (Front.nameSpan name) (Front.SExplicit name))
                    (destination, after) <- targetTerm (following start before) target
                    let selection = case sites of
                            [] -> named "ps_all"
                            _ -> Hol.foldlNApp (named (if include then "ps_only" else "ps_except")) [embedList (kindOf "nat") (map natural sites), natural (maximum sites)]
                    return (Hol.foldlNApp (named "p_simpl_at") [function, selection, destination], Map.union before after)
                Command.UnfoldProof names target -> do
                    (values, before) <- manyTerms start [Front.Term (Front.nameSpan name) (Front.SExplicit name) | name <- names]
                    (destination, after) <- targetTerm (following start before) target
                    return (Hol.foldlNApp (named "p_unfold") [embedList (kindOf "raw") values, destination], Map.union before after)
                Command.SplitProof -> plain "p_split"
                Command.LeftProof -> plain "p_left"
                Command.RightProof -> plain "p_right"
                Command.ConstructorProof Nothing -> plain "p_constructor_auto"
                Command.ConstructorProof (Just index)
                    -- No family can contain this index. Keep this a logical
                    -- tactic failure so first/try retain their normal behavior.
                    | index > constructorBound -> return (Hol.mkNApp (named "p_first") (embedList (kindOf "ptac") []), Map.empty)
                    | index > 0 -> return (Hol.mkNApp (named "p_constructor") (Hol.mkNCon (Hol.DC_NatL index)), Map.empty)
                    | otherwise -> Trans.lift (Left (InvalidProofCommand "Constructor numbers start at one."))
                Command.ExistsProof terms -> do
                    (values, positions) <- manyTerms start terms
                    return (Hol.mkNApp (named "p_exists") (embedList (kindOf "raw") values), positions)
                Command.UserProof name terms -> do
                    (values, positions) <- manyTerms start terms
                    return (Hol.foldlNApp (named "p_user") [string (Front.nameText name), embedList (kindOf "raw") values], positions)
                _ -> Trans.lift (Left (InvalidProofCommand "This proof primitive is not implemented by this bridge yet."))
            _ -> Trans.lift (Left (InvalidProofCommand "This tactical is not implemented by this bridge yet."))
            where
                plain command = return (named command, Map.empty)
                unary command inner = do
                    (value, positions) <- go True start inner
                    return (Hol.mkNApp (named command) value, positions)
                termCommand command term = do
                    (value, positions) <- encode deferred start term
                    return (Hol.mkNApp (named command) value, positions)
                namedTermCommand command term names = do
                    (value, positions) <- encode deferred start term
                    return (Hol.foldlNApp (named command) [value, embedList (Hol.mkNApp (kindOf "list") (kindOf "char")) (map (string . Front.nameText) names)], positions)
                targetedTermCommand command term target = do
                    (value, before) <- encode deferred start term
                    (destination, after) <- targetTerm (following start before) target
                    return (Hol.foldlNApp (named command) [value, destination], Map.union before after)
                targetTerm _ Command.GoalTarget = return (named "pe_goal", Map.empty)
                targetTerm next (Command.HypothesisTarget name) = do
                    (value, positions) <- encode deferred next (Front.Term (Front.nameSpan name) (Front.SName name))
                    return (Hol.foldlNApp (named "pe_hyp") [string (Front.nameText name), value], positions)
                manyTerms _ [] = return ([], Map.empty)
                manyTerms next (term : rest) = do
                    (value, before) <- encode deferred next term
                    (values, after) <- manyTerms (following next before) rest
                    return (value : values, Map.union before after)
        -- The admitted packet supplies only identifiers, universe arity and
        -- field counts. Hol verifies the dependent constructor telescope.
        pairFamilies =
            [ Hol.foldlNApp (named "pe_family") (map natural [priority global, block, index, toInteger (length (Core.universeNames (Env.entryUniverses entry)))])
            | (block, entry) <- Map.toAscList (Env.envDecls environment)
            , (index, Info 2 True [[False, False]]) <- zip [0 ..] (Env.entryInfo entry)
            , let global = Core.GlobalInd block (fromInteger index), Set.member global visible
            ]
        visible = Set.fromList (Map.elems (Env.envNames environment))
        priority global
            | Map.lookup "lol.theories.Sigma.sigT" (Env.envNames environment) == Just global = 0
            | Map.lookup "sigT" (Env.envNames environment) == Just global = 1
            | otherwise = 2
        manyTactics _ [] = return ([], Map.empty)
        manyTactics start (tactic : rest) = do
            (value, before) <- go True start tactic
            (values, after) <- manyTactics (following start before) rest
            return (value : values, Map.union before after)

-- This annotates Hol transport lambdas using the existing Hol typechecker.
-- The equality is never executed. Active nominal/scope evidence is checked
-- again by assign; no LoL term is typed or reduced here.
annotateTactic :: Kernel.Kernel -> Hol.TermNode -> IO (Either String Hol.TermNode)
annotateTactic program command = do
    let goal = Hol.foldlNApp (Hol.mkNCon Hol.DC_eq) [kindOf "ptac", command, command]
    result <- Hol.inferGoalTypes (Kernel.kernelFresh program) (Kernel.kernelReady program) goal
    return $ case result of
        Left failure -> Left (Hol.describeFailure failure)
        Right (typed, _) -> case Hol.unfoldlNApp typed of
            (_, [_, annotated, _]) -> Right annotated
            _ -> Left "The Hol command typing adapter returned an invalid shape."
