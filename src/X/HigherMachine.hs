{-# LANGUAGE CApiFFI #-}
module X.HigherMachine
    ( Machine
    , Snapshot
    , ProgramMark
    , markProgram
    , truncateProgram
    , closeProgramMark
    , NativeStep (..)
    , NativeRequest (..)
    , createMachine
    , createMachineWithLimit
    , liveTokens
    , liveViewTokens
    , getLiveIdentities
    , drainRetiredTokens
    , ServiceDelta (..)
    , fetchServiceDelta
    , registerHostRoots
    , forkMachine
    , setLegacyCopy
    , setScopedExports
    , setQueryWitnesses
    , setDebugFocus
    , closeMachine
    , withMachine
    , extendProgram
    , startQuery
    , leaveRun
    , nextStep
    , nextStepForHost
    , nextEvent, nextEventWithDebugging
    , beginStep
    , endStep
    , fetchState
    , fetchRootState
    , fetchFrames
    , fetchDeclarations
    , fetchHypotheses
    , pendingCount
    , uidFrontier
    , lookupIdentity
    , heapCount
    , collections
    , setCollectionStep
    , resume
    , resumeWithView
    , RootDelta (..)
    , resumeWithRootDeltas
    , resumeWithSubscriptions
    , setDebugging
    , ensureSymbol
    , reserveUid
    , assign
    , takeSnapshot
    , restoreSnapshot
    , restoreSnapshotConsuming
    , closeSnapshot
    , setWorkLimit
    , getWorkLimit
    , ErrorCode (..)
    , NativeStats (..)
    , NativeView (..)
    , fetchView
    , fetchViewWith
    , fetchContextViewWith
    , fetchProofViewWith
    , fetchAssignmentViewWith
    , nextStepScoped
    , getErrorCode
    , fetchFailure
    , setMemoryLimit
    , getMemoryLimit
    , setCounting
    , getStats
    ) where

import Control.Concurrent (yield)
import Control.Concurrent.MVar
import Control.Exception (allowInterrupt, bracket, mask_, onException)
import Data.Int
import Data.IORef
import Data.Word
import Foreign.C.String (peekCString)
import Foreign.C.Types
import Foreign.ForeignPtr
import Foreign.Marshal.Alloc (alloca, free)
import Foreign.Marshal.Array
import Foreign.Ptr
import Foreign.Storable (peek, sizeOf)

data CMachine
    deriving ()

data Machine
    = Machine (IORef ()) (MVar (Maybe (ForeignPtr CMachine)))
    deriving ()

data Snapshot
    = Snapshot (IORef ()) (MVar (Maybe (ForeignPtr CMachine)))
    deriving ()

data ErrorCode
    = NoError
    | UsageError
    | WorkLimitError
    | MemoryLimitError
    | AllocationError
    | InternalError
    | InvalidGoalError
    | InvalidFactError
    deriving (Eq, Show)

data NativeView
    = NativeView
        { viewState        :: [Int64]
        , viewFrames       :: [Int64]
        , viewDeclarations :: [Int64]
        , viewHypotheses   :: [Int64]
        }
    deriving (Eq, Show)

data NativeStats
    = NativeStats
        { allocatedBytes    :: Word64
        , peakBytes         :: Word64
        , heapNodes         :: Word64
        , sealedNodes       :: Word64
        , collectionCount   :: Word64
        , workVisits        :: Word64
        , normalizeVisits   :: Word64
        , bindingVisits     :: Word64
        , scopeVisits       :: Word64
        , createdNodes      :: Word64
        , copiedNodes       :: Word64
        , exportedNodes     :: Word64
        , collectedVisits   :: Word64
        , copiedProgramRows :: Word64
        }
    deriving (Eq, Show)

data ServiceDelta
    = ServiceDelta
        { deltaViewToken :: Word64
        , deltaState     :: [Int64]
        }
    deriving (Eq, Show)

data RootDelta
    = RootDelta
        { rootToken   :: Word64
        , rootParent  :: Word64
        , rootAdded   :: [Word64]
        , rootRemoved :: [Word64]
        }
    deriving (Eq, Show)

data ProgramMark
    = ProgramMark (IORef ()) (MVar (Maybe (ForeignPtr CMachine)))
    deriving ()

data NativeRequest
    = NativeRequest
        { requestKind :: Int
        , requestHostState :: Word64
        , requestPremises :: Word64
        , requestScope :: Int
        , requestCallId :: Word64
        , requestAuxiliary :: Int64
        , requestTerms :: [Int64]
        , requestState :: [Int64]
        , requestFrames :: [Int64]
        , requestDeclarations :: [Int64]
        }
    deriving (Eq, Show)

data NativeStep
    = Exhausted
    | Answer Word64 [Int64] [Int64]
    | Request NativeRequest
    deriving (Eq, Show)

foreign import ccall safe "hol_v2_create" c_create :: Ptr Int64 -> CSize -> IO (Ptr CMachine)
foreign import ccall safe "hol_v2_create_limited" c_createLimited :: Ptr Int64 -> CSize -> Word64 -> Ptr CInt -> IO (Ptr CMachine)
foreign import ccall safe "hol_v2_destroy" c_destroyNow :: Ptr CMachine -> IO ()
foreign import ccall "&hol_v2_destroy" c_destroy :: FinalizerPtr CMachine
foreign import ccall safe "hol_v2_extend" c_extend :: Ptr CMachine -> Ptr Int64 -> CSize -> IO CInt
foreign import ccall safe "hol_v2_query" c_query :: Ptr CMachine -> Ptr Int64 -> CSize -> IO CInt
foreign import ccall safe "hol_v2_idle" c_idle :: Ptr CMachine -> IO CInt
foreign import ccall safe "hol_v2_error" c_error :: Ptr CMachine -> IO (Ptr CChar)
foreign import ccall safe "hol_v2_next_event" c_nextEvent :: Ptr CMachine -> CInt -> Ptr Int64 -> CSize -> IO CInt
foreign import ccall safe "hol_v2_next" c_next :: Ptr CMachine -> IO CInt
foreign import ccall safe "hol_v2_begin_step" c_beginStep :: Ptr CMachine -> Word64 -> IO CInt
foreign import ccall safe "hol_v2_end_step" c_endStep :: Ptr CMachine -> Word64 -> IO CInt
foreign import ccall safe "hol_v2_answer_size" c_answerSize :: Ptr CMachine -> IO CSize
foreign import ccall safe "hol_v2_answer" c_answer :: Ptr CMachine -> Ptr Int64 -> CSize -> IO CInt
foreign import ccall safe "hol_v2_view_state_size_with" c_viewStateSizeWith :: Ptr CMachine -> Ptr Word64 -> CSize -> IO CSize
foreign import ccall safe "hol_v2_proof_state_size_with" c_proofStateSizeWith :: Ptr CMachine -> Ptr Word64 -> CSize -> IO CSize
foreign import ccall safe "hol_v2_assignment_declarations_size_with" c_assignmentDeclarationsSizeWith :: Ptr CMachine -> Ptr Word64 -> CSize -> IO CSize
foreign import ccall safe "hol_v2_view_state_size" c_viewStateSize :: Ptr CMachine -> IO CSize
foreign import ccall safe "hol_v2_live_tokens_size" c_liveTokensSize :: Ptr CMachine -> IO CSize
foreign import ccall safe "hol_v2_live_views_size" c_liveViewsSize :: Ptr CMachine -> IO CSize
foreign import ccall safe "hol_v2_live_identities_size" c_liveIdentitiesSize :: Ptr CMachine -> IO CSize
foreign import ccall safe "hol_v2_retired_tokens_size" c_retiredTokensSize :: Ptr CMachine -> IO CSize
foreign import ccall safe "hol_v2_service_delta_size" c_serviceDeltaSize :: Ptr CMachine -> IO CSize
foreign import ccall safe "hol_v2_register_host_roots" c_registerHostRoots :: Ptr CMachine -> CInt -> Word64 -> Ptr Word64 -> CSize -> IO CInt
foreign import ccall safe "hol_v2_state_size" c_stateSize :: Ptr CMachine -> IO CSize
foreign import ccall safe "hol_v2_state" c_state :: Ptr CMachine -> Ptr Int64 -> CSize -> IO CInt
foreign import ccall safe "hol_v2_root_state_size" c_rootStateSize :: Ptr CMachine -> CInt -> IO CSize
foreign import ccall safe "hol_v2_pending_count" c_pendingCount :: Ptr CMachine -> IO CSize
foreign import ccall safe "hol_v2_uid_frontier" c_uidFrontier :: Ptr CMachine -> IO Word64
foreign import ccall safe "hol_v2_identity" c_identity :: Ptr CMachine -> Word64 -> Ptr Int64 -> CSize -> IO CInt
foreign import ccall safe "hol_v2_heap_count" c_heapCount :: Ptr CMachine -> IO CSize
foreign import ccall safe "hol_v2_collections" c_collections :: Ptr CMachine -> IO CSize
foreign import ccall safe "hol_v2_set_collection_step" c_setCollectionStep :: Ptr CMachine -> CSize -> IO ()
foreign import ccall safe "hol_v2_event_size" c_eventSize :: Ptr CMachine -> IO CSize
foreign import ccall safe "hol_v2_event" c_event :: Ptr CMachine -> Ptr Int64 -> CSize -> IO CInt
foreign import ccall safe "hol_v2_event_info" c_eventInfo :: Ptr CMachine -> Ptr Int64 -> CSize -> IO CInt
foreign import ccall safe "hol_v2_compact_frames_size" c_compactFramesSize :: Ptr CMachine -> IO CSize
foreign import ccall safe "hol_v2_proof_frames_size" c_proofFramesSize :: Ptr CMachine -> IO CSize
foreign import ccall safe "hol_v2_frames" c_frames :: Ptr CMachine -> Ptr Int64 -> CSize -> IO CInt
foreign import ccall safe "hol_v2_declarations_size" c_declarationsSize :: Ptr CMachine -> IO CSize
foreign import ccall safe "hol_v2_declarations" c_declarations :: Ptr CMachine -> Ptr Int64 -> CSize -> IO CInt
foreign import ccall safe "hol_v2_hypotheses_size" c_hypothesesSize :: Ptr CMachine -> IO CSize
foreign import ccall safe "hol_v2_hypotheses" c_hypotheses :: Ptr CMachine -> Ptr Int64 -> CSize -> IO CInt
foreign import ccall safe "hol_v2_host_state" c_hostState :: Ptr CMachine -> IO Word64
foreign import ccall safe "hol_v2_resume" c_resume :: Ptr CMachine -> CInt -> Word64 -> Word64 -> Ptr Int64 -> CSize -> IO CInt
foreign import ccall safe "hol_v2_resume_with_view" c_resumeWithView :: Ptr CMachine -> CInt -> Word64 -> Word64 -> Word64 -> Ptr Int64 -> CSize -> IO CInt
foreign import ccall safe "hol_v2_resume_with_root_deltas" c_resumeWithRootDeltas :: Ptr CMachine -> CInt -> Word64 -> Word64 -> Word64 -> Ptr Int64 -> CSize -> Ptr Word64 -> CSize -> IO CInt
foreign import ccall safe "hol_v2_assign" c_assign :: Ptr CMachine -> Ptr Int64 -> CSize -> IO CInt
foreign import ccall safe "hol_v2_set_debugging" c_debug :: Ptr CMachine -> CInt -> IO ()
foreign import ccall safe "hol_v2_ensure_symbol" c_ensureSymbol :: Ptr CMachine -> CSize -> CInt -> IO CInt
foreign import ccall safe "hol_v2_reserve_uid" c_reserveUid :: Ptr CMachine -> IO Word64
foreign import ccall safe "hol_v2_program_mark" c_programMark :: Ptr CMachine -> IO (Ptr CMachine)
foreign import ccall safe "hol_v2_program_truncate" c_programTruncate :: Ptr CMachine -> Ptr CMachine -> IO CInt
foreign import ccall safe "hol_v2_fork" c_fork :: Ptr CMachine -> IO (Ptr CMachine)
foreign import ccall safe "hol_v2_set_legacy_copy" c_legacyCopy :: Ptr CMachine -> CInt -> IO ()
foreign import ccall safe "hol_v2_set_scoped_exports" c_scopedExports :: Ptr CMachine -> CInt -> IO ()
foreign import ccall safe "hol_v2_set_query_witnesses" c_queryWitnesses :: Ptr CMachine -> Ptr Word64 -> CSize -> IO CInt
foreign import ccall safe "hol_v2_set_debug_focus" c_debugFocus :: Ptr CMachine -> Ptr Word64 -> CSize -> CInt -> IO CInt
foreign import ccall safe "hol_v2_clone" c_clone :: Ptr CMachine -> IO (Ptr CMachine)
foreign import ccall safe "hol_v2_snapshot" c_snapshot :: Ptr CMachine -> IO (Ptr CMachine)
foreign import ccall safe "hol_v2_restore_consuming" c_restoreConsuming :: Ptr CMachine -> Ptr CMachine -> IO CInt
foreign import ccall safe "hol_v2_restore" c_restore :: Ptr CMachine -> Ptr CMachine -> IO CInt
foreign import ccall safe "hol_v2_set_work_limit" c_setWorkLimit :: Ptr CMachine -> Word64 -> IO CInt
foreign import ccall safe "hol_v2_work_limit" c_getWorkLimit :: Ptr CMachine -> IO Word64

foreign import ccall safe "hol_v2_error_code" c_errorCode :: Ptr CMachine -> IO CInt
foreign import ccall safe "hol_v2_failure_size" c_failureSize :: Ptr CMachine -> IO CSize
foreign import ccall safe "hol_v2_failure" c_failure :: Ptr CMachine -> Ptr Int64 -> CSize -> IO CInt
foreign import ccall safe "hol_v2_set_memory_limit" c_setMemoryLimit :: Ptr CMachine -> Word64 -> IO CInt
foreign import ccall safe "hol_v2_memory_limit" c_memoryLimit :: Ptr CMachine -> IO Word64
foreign import ccall safe "hol_v2_set_counting" c_counting :: Ptr CMachine -> CInt -> IO ()
foreign import ccall safe "hol_v2_stats" c_stats :: Ptr CMachine -> Ptr Word64 -> CSize -> IO CInt

createMachine :: [Int64] -> IO Machine
createMachine code = mask_ $ withArrayLen code $ \count words -> do
    pointer <- c_create words (fromIntegral count)
    if pointer == nullPtr then ioError (userError "Hol V1 native machine allocation failed") else do
        owner <- newForeignPtr c_destroy pointer `onException` c_destroyNow pointer
        identity <- newIORef ()
        Machine identity <$> newMVar (Just owner)

createMachineWithLimit :: Word64 -> [Int64] -> IO (Either (ErrorCode, String) Machine)
createMachineWithLimit limit code = mask_ $ withArrayLen code $ \count words -> alloca $ \failure -> do
    pointer <- c_createLimited words (fromIntegral count) limit failure
    status <- peek failure
    if pointer == nullPtr then return (Left (decodeErrorCode status, "Hol V2 native machine allocation failed")) else do
        owner <- newForeignPtr c_destroy pointer `onException` c_destroyNow pointer
        identity <- newIORef ()
        machine <- Machine identity <$> newMVar (Just owner)
        if status == 0 then return (Right machine) else do
            message <- readError pointer
            closeMachine machine
            return (Left (decodeErrorCode status, message))

closeState :: MVar (Maybe (ForeignPtr CMachine)) -> IO ()
closeState state = modifyMVar_ state $ \current -> do
    maybe (return ()) finalizeForeignPtr current
    return Nothing

closeMachine :: Machine -> IO ()
closeMachine (Machine _ state) = closeState state

withMachine :: [Int64] -> (Machine -> IO a) -> IO a
withMachine code = bracket (createMachine code) closeMachine

-- A machine keeps its program across runs. `extendProgram` adds the symbols and
-- clauses of a fragment to it, `startQuery` starts a run of a fragment's query,
-- and `leaveRun` ends the run and releases what it allocated. The first two
-- leave the current run first. Extension stages the complete change and leaves
-- the old machine usable on failure; a malformed query leaves an execution error.
extendProgram :: Machine -> [Int64] -> IO (Either String ())
extendProgram = loadFragment c_extend

startQuery :: Machine -> [Int64] -> IO (Either String ())
startQuery = loadFragment c_query

loadFragment :: (Ptr CMachine -> Ptr Int64 -> CSize -> IO CInt) -> Machine -> [Int64] -> IO (Either String ())
loadFragment load (Machine _ state) code = withPointer state $ \pointer ->
    withArrayLen code $ \count words -> do
        status <- load pointer words (fromIntegral count)
        if status < 0 then Left <$> readError pointer else return (Right ())

leaveRun :: Machine -> IO (Either String ())
leaveRun (Machine _ state) = withPointer state $ \pointer -> do
    status <- c_idle pointer
    if status < 0 then Left <$> readError pointer else return (Right ())

beginStep :: Machine -> Word64 -> IO (Either String ())
beginStep (Machine _ state) step = withPointer state $ \pointer -> do
    status <- c_beginStep pointer step
    if status < 0 then Left <$> readError pointer else return (Right ())

endStep :: Machine -> Word64 -> IO (Either String ())
endStep (Machine _ state) step = withPointer state $ \pointer -> do
    status <- c_endStep pointer step
    if status < 0 then Left <$> readError pointer else return (Right ())

withPointer :: MVar (Maybe (ForeignPtr CMachine)) -> (Ptr CMachine -> IO (Either String a)) -> IO (Either String a)
withPointer state action = withMVar state $ \current -> case current of
    Nothing -> return (Left "Hol V1 native machine is closed")
    Just owner -> withForeignPtr owner action

readError :: Ptr CMachine -> IO String
readError pointer = c_error pointer >>= peekCString

setWorkLimit :: Machine -> Word64 -> IO (Either String ())
setWorkLimit (Machine _ state) visits = withPointer state $ \pointer -> do
    result <- c_setWorkLimit pointer visits
    if result < 0 then Left <$> readError pointer else return (Right ())

getWorkLimit :: Machine -> IO (Either String Word64)
getWorkLimit (Machine _ state) = withPointer state (fmap Right . c_getWorkLimit)

lookupIdentity :: Machine -> Word64 -> IO (Either String [Int64])
lookupIdentity (Machine _ state) uid = withPointer state $ \pointer -> allocaArray 5 $ \output -> do
    count <- c_identity pointer uid output 5
    if count < 0 then Left <$> readError pointer else Right <$> peekArray (fromIntegral count) output

copyBuffer :: Ptr CMachine -> (Ptr CMachine -> IO CSize) -> (Ptr CMachine -> Ptr Int64 -> CSize -> IO CInt) -> IO (Either String [Int64])
copyBuffer pointer size copy = do
    count <- size pointer
    if toInteger count > toInteger ((maxBound :: Int) `div` sizeOf (0 :: Int64)) then
        return (Left "Hol V1 native buffer exceeds the host array size")
    else bracket (mallocArray (fromIntegral count)) free $ \output -> do
        status <- copy pointer output count
        if status < 0 then Left <$> readError pointer else Right <$> peekArray (fromIntegral count) output

nextStep :: Machine -> IO (Either String NativeStep)
nextStep = nextStepWith False False

nextStepForHost :: Machine -> IO (Either String NativeStep)
nextStepForHost = nextStepWith True False

nextStepScoped :: Machine -> IO (Either String NativeStep)
nextStepScoped = nextStepWith True True

nextStepWith :: Bool -> Bool -> Machine -> IO (Either String NativeStep)
nextStepWith compact scoped (Machine _ state) = withPointer state $ \pointer -> do
    status <- nextStatus pointer
    case status of
        -1 -> Left <$> readError pointer
        0 -> return (Right Exhausted)
        1 -> do
            answer <- if compact then return (Right []) else copyBuffer pointer c_answerSize c_answer
            current <- copyBuffer pointer c_stateSize c_state
            token <- c_hostState pointer
            return (Answer token <$> answer <*> current)
        3 -> do
            info <- copyBuffer pointer (const (return 6)) c_eventInfo
            terms <- copyBuffer pointer c_eventSize c_event
            let failed = case info of
                    Right (6 : _) -> True
                    _ -> False
            let debugState = case info of
                    Right (4 : _) -> scoped
                    _ -> False
            current <- if failed then return (Right []) else copyBuffer pointer (if debugState then c_viewStateSize else c_stateSize) c_state
            let debug = case info of
                    Right (4 : _) -> True
                    _ -> False
            frames <- if failed || compact && not debug then return (Right [0]) else copyBuffer pointer c_compactFramesSize c_frames
            declarations <- if not failed && compact && not debug then copyBuffer pointer c_declarationsSize c_declarations else return (Right [0])
            return $ do
                fields <- info
                roots <- terms
                bindings <- current
                remaining <- frames
                metadata <- declarations
                case fields of
                    [kind, host, premises, scope, callId, auxiliary]
                        | all (>= 0) [kind, host, premises, scope, callId]
                        , toInteger scope <= toInteger (maxBound :: Int) ->
                            Right (Request (NativeRequest (fromIntegral kind) (fromIntegral host) (fromIntegral premises) (fromIntegral scope) (fromIntegral callId) auxiliary roots bindings remaining metadata))
                    _ -> Left "Hol V1 native machine returned invalid event metadata"
        _ -> return (Left "Hol V1 native machine returned an invalid status")
    where
        nextStatus pointer = do
            status <- c_next pointer
            -- Let signal and timeout threads run even when this loop allocates nothing.
            if status == 2 then yield >> allowInterrupt >> nextStatus pointer else return status

-- The state, frames and declarations of the returned step are left empty: a
-- host that needs one of them fetches it before the next mutating call.
nextEvent :: Machine -> IO (Either String NativeStep)
nextEvent = nextEventWith (-1)

nextEventWithDebugging :: Machine -> Bool -> IO (Either String NativeStep)
nextEventWithDebugging machine enabled = nextEventWith (if enabled then 1 else 0) machine

nextEventWith :: CInt -> Machine -> IO (Either String NativeStep)
nextEventWith debugging (Machine _ state) = withPointer state $ \pointer -> allocaArray capacity $ \buffer -> do
    status <- nextStatus pointer buffer
    case status of
        -1 -> Left <$> readError pointer
        0 -> return (Right Exhausted)
        1 -> do
            token <- peek buffer
            return (Right (Answer (fromIntegral token) [] []))
        3 -> do
            fields <- peekArray 7 buffer
            case fields of
                [kind, host, premises, scope, callId, auxiliary, count]
                    | all (>= 0) [kind, host, premises, scope, callId]
                    , toInteger scope <= toInteger (maxBound :: Int)
                    , count > 0
                    , toInteger count <= toInteger (maxBound :: CSize) -> do
                        terms <- if count <= fromIntegral (capacity - 7)
                            then Right <$> peekArray (fromIntegral count) (advancePtr buffer 7)
                            else copyBuffer pointer (const (return (fromIntegral count))) c_event
                        return $ do
                            roots <- terms
                            return (Request (NativeRequest (fromIntegral kind) (fromIntegral host) (fromIntegral premises) (fromIntegral scope) (fromIntegral callId) auxiliary roots [] [] []))
                _ -> return (Left "Hol V1 native machine returned invalid event metadata")
        _ -> return (Left "Hol V1 native machine returned an invalid status")
    where
        capacity = 64
        nextStatus pointer buffer = do
            status <- c_nextEvent pointer debugging buffer (fromIntegral capacity)
            if status == 2 then yield >> allowInterrupt >> nextStatus pointer buffer else return status

fetchFailure :: Machine -> IO (Either String [Int64])
fetchFailure (Machine _ state) = withPointer state $ \pointer -> copyBuffer pointer c_failureSize c_failure

fetchState :: Machine -> IO (Either String [Int64])
fetchState (Machine _ state) = withPointer state $ \pointer -> copyBuffer pointer c_stateSize c_state

fetchRootState :: Machine -> Bool -> IO (Either String [Int64])
fetchRootState (Machine _ state) query = withPointer state $ \pointer -> copyBuffer pointer (\machine -> c_rootStateSize machine (if query then 1 else 0)) c_state

fetchFrames :: Machine -> IO (Either String [Int64])
fetchFrames (Machine _ state) = withPointer state $ \pointer -> copyBuffer pointer c_compactFramesSize c_frames

fetchDeclarations :: Machine -> IO (Either String [Int64])
fetchDeclarations (Machine _ state) = withPointer state $ \pointer -> copyBuffer pointer c_declarationsSize c_declarations

-- The scope of the goal of the event and its hypotheses, the latest first.
fetchHypotheses :: Machine -> IO (Either String [Int64])
fetchHypotheses (Machine _ state) = withPointer state $ \pointer -> copyBuffer pointer c_hypothesesSize c_hypotheses

pendingCount :: Machine -> IO (Either String Int)
pendingCount (Machine _ state) = withPointer state $ \pointer -> do
    count <- c_pendingCount pointer
    return (if toInteger count > toInteger (maxBound :: Int) then Left "Hol V1 native disagreement count exceeds the host range" else Right (fromIntegral count))

uidFrontier :: Machine -> IO (Either String Word64)
uidFrontier (Machine _ state) = withPointer state (fmap Right . c_uidFrontier)

-- Term nodes now on the native heap, and compactions run so far.
heapCount :: Machine -> IO (Either String Word64)
heapCount (Machine _ state) = withPointer state (fmap (Right . fromIntegral) . c_heapCount)

collections :: Machine -> IO (Either String Word64)
collections (Machine _ state) = withPointer state (fmap (Right . fromIntegral) . c_collections)

-- Minimum heap growth, in term nodes, between two compactions.
setCollectionStep :: Machine -> Word64 -> IO (Either String ())
setCollectionStep (Machine _ state) nodes = withPointer state $ \pointer -> do
    c_setCollectionStep pointer (fromIntegral nodes)
    return (Right ())

resume :: Machine -> Int -> Word64 -> Word64 -> [Int64] -> IO (Either String ())
resume (Machine _ state) result host premises bindings = withPointer state $ \pointer ->
    withArrayLen bindings $ \count words -> do
        status <- c_resume pointer (fromIntegral result) host premises words (fromIntegral count)
        if status < 0 then Left <$> readError pointer else return (Right ())

setDebugging :: Machine -> Bool -> IO (Either String ())
setDebugging (Machine _ state) enabled = withPointer state $ \pointer -> do
    c_debug pointer (if enabled then 1 else 0)
    return (Right ())

takeSnapshot :: Machine -> IO (Either String Snapshot)
takeSnapshot (Machine identity state) = withPointer state $ \pointer -> mask_ $ do
    duplicate <- c_snapshot pointer
    if duplicate == nullPtr then
        Left <$> readError pointer
    else do
        owner <- newForeignPtr c_destroy duplicate `onException` c_destroyNow duplicate
        Right . Snapshot identity <$> newMVar (Just owner)

restoreSnapshot :: Machine -> Snapshot -> IO (Either String ())
restoreSnapshot (Machine identity state) (Snapshot source snapshot)
    | identity /= source = return (Left "snapshot belongs to a different runtime")
    | otherwise = withPointer state $ \pointer -> withPointer snapshot $ \saved -> do
        status <- c_restore pointer saved
        if status < 0 then Left <$> readError pointer else return (Right ())

restoreSnapshotConsuming :: Machine -> Snapshot -> IO (Either String ())
restoreSnapshotConsuming (Machine identity state) (Snapshot source snapshot)
    | identity /= source = return (Left "snapshot belongs to a different runtime")
    | otherwise = withPointer state $ \pointer -> mask_ $ modifyMVar snapshot $ \current -> case current of
        Nothing -> return (Nothing, Left "Hol V1 native snapshot is closed")
        Just owner -> withForeignPtr owner $ \saved -> do
            status <- c_restoreConsuming pointer saved
            if status < 0 then do
                message <- readError pointer
                return (current, Left message)
            else do
                finalizeForeignPtr owner
                return (Nothing, Right ())

closeSnapshot :: Snapshot -> IO ()
closeSnapshot (Snapshot _ state) = closeState state

ensureSymbol :: Machine -> Int -> Int -> IO (Either String ())
ensureSymbol (Machine _ state) symbol role = withPointer state $ \pointer -> do
    status <- c_ensureSymbol pointer (fromIntegral symbol) (fromIntegral role)
    if status < 0 then Left <$> readError pointer else return (Right ())

reserveUid :: Machine -> IO (Either String Word64)
reserveUid (Machine _ state) = withPointer state $ \pointer -> do
    uid <- c_reserveUid pointer
    if uid == maxBound then Left <$> readError pointer else return (Right uid)

assign :: Machine -> [Int64] -> IO (Either String ())
assign (Machine _ state) bindings = withPointer state $ \pointer ->
    withArrayLen bindings $ \count words -> do
        status <- c_assign pointer words (fromIntegral count)
        if status < 0 then Left <$> readError pointer else return (Right ())

decodeErrorCode :: CInt -> ErrorCode
decodeErrorCode code = case code of
    0 -> NoError
    1 -> UsageError
    2 -> WorkLimitError
    3 -> MemoryLimitError
    4 -> AllocationError
    6 -> InvalidGoalError
    7 -> InvalidFactError
    _ -> InternalError

getErrorCode :: Machine -> IO (Either String ErrorCode)
getErrorCode (Machine _ state) = withPointer state $ \pointer -> Right . decodeErrorCode <$> c_errorCode pointer

setMemoryLimit :: Machine -> Word64 -> IO (Either String ())
setMemoryLimit (Machine _ state) bytes = withPointer state $ \pointer -> do
    status <- c_setMemoryLimit pointer bytes
    if status < 0 then Left <$> readError pointer else return (Right ())

getMemoryLimit :: Machine -> IO (Either String Word64)
getMemoryLimit (Machine _ state) = withPointer state (fmap Right . c_memoryLimit)

setCounting :: Machine -> Bool -> IO (Either String ())
setCounting (Machine _ state) enabled = withPointer state $ \pointer -> do
    c_counting pointer (if enabled then 1 else 0)
    return (Right ())

getStats :: Machine -> IO (Either String NativeStats)
getStats (Machine _ state) = withPointer state $ \pointer -> allocaArray 14 $ \output -> do
    status <- c_stats pointer output 14
    if status < 0 then Left <$> readError pointer else do
        values <- peekArray 14 output
        case values of
            [a, b, c, d, e, f, g, h, i, j, k, l, m, n] -> return (Right (NativeStats a b c d e f g h i j k l m n))
            _ -> return (Left "Hol V2 native statistics size mismatch")

forkMachine :: Machine -> IO (Either String Machine)
forkMachine (Machine _ state) = withPointer state $ \pointer -> mask_ $ do
    duplicate <- c_fork pointer
    if duplicate == nullPtr then return (Left "Hol V2 native fork allocation failed") else do
        owner <- newForeignPtr c_destroy duplicate `onException` c_destroyNow duplicate
        identity <- newIORef ()
        Right . Machine identity <$> newMVar (Just owner)

setLegacyCopy :: Machine -> Bool -> IO (Either String ())
setLegacyCopy (Machine _ state) enabled = withPointer state $ \pointer -> do
    c_legacyCopy pointer (if enabled then 1 else 0)
    return (Right ())

setScopedExports :: Machine -> Bool -> IO (Either String ())
setScopedExports (Machine _ state) enabled = withPointer state $ \pointer -> do
    c_scopedExports pointer (if enabled then 1 else 0)
    return (Right ())

setQueryWitnesses :: Machine -> [Word64] -> IO (Either String ())
setQueryWitnesses (Machine _ state) slots = withPointer state $ \pointer -> withArrayLen slots $ \count values -> do
    status <- c_queryWitnesses pointer values (fromIntegral count)
    if status < 0 then Left <$> readError pointer else return (Right ())

-- The predicates whose hypotheses the debugger views of this machine keep;
-- Nothing asks for complete views again.
setDebugFocus :: Machine -> Maybe [Word64] -> IO (Either String ())
setDebugFocus (Machine _ state) focus = withPointer state $ \pointer -> withArrayLen (maybe [] id focus) $ \count values -> do
    status <- c_debugFocus pointer values (fromIntegral count) (maybe 0 (const 1) focus)
    if status < 0 then Left <$> readError pointer else return (Right ())

fetchView :: Machine -> IO (Either String NativeView)
fetchView machine = fetchViewWith machine []

fetchViewWith :: Machine -> [Word64] -> IO (Either String NativeView)
fetchViewWith = fetchSelectedView False True c_viewStateSizeWith c_compactFramesSize

fetchContextViewWith :: Machine -> [Word64] -> IO (Either String NativeView)
fetchContextViewWith = fetchSelectedView True False c_viewStateSizeWith c_compactFramesSize

fetchProofViewWith :: Machine -> [Word64] -> IO (Either String NativeView)
fetchProofViewWith = fetchSelectedView True False c_proofStateSizeWith c_proofFramesSize

fetchAssignmentViewWith :: Machine -> [Word64] -> IO (Either String (Maybe NativeView))
fetchAssignmentViewWith (Machine _ state) uids = withPointer state $ \pointer -> withArrayLen uids $ \count roots -> do
    declarations <- copyBuffer pointer (\native -> c_assignmentDeclarationsSizeWith native roots (fromIntegral count)) c_state
    case declarations of
        Left message -> return (Left message)
        Right [0] -> return (Right Nothing)
        Right (1 : rows) -> do
            current <- copyBuffer pointer (\native -> c_viewStateSizeWith native roots (fromIntegral count)) c_state
            return (fmap (\values -> Just (NativeView values [0] rows [0, 0])) current)
        _ -> return (Left "Invalid native assignment declarations")

-- The hypotheses of the current goal are a part of an assignment view alone:
-- the callers of the other two views do not read them.
fetchSelectedView :: Bool -> Bool -> (Ptr CMachine -> Ptr Word64 -> CSize -> IO CSize) -> (Ptr CMachine -> IO CSize) -> Machine -> [Word64] -> IO (Either String NativeView)
fetchSelectedView declarationsInFrames withHypotheses select framesSize (Machine _ state) uids = withPointer state $ \pointer -> withArrayLen uids $ \count roots -> do
    current <- copyBuffer pointer (\native -> select native roots (fromIntegral count)) c_state
    frames <- copyBuffer pointer framesSize c_frames
    -- These callers decode every shared frame. A shared view certifies exact,
    -- closed types and no type-binder writes, so replaying its declarations
    -- would enroll only the same identities again. Other callers need them.
    declarations <- case frames of
        Right (-2 : _)
            | declarationsInFrames -> return (Right [0])
        _ -> copyBuffer pointer c_declarationsSize c_declarations
    hypotheses <- if withHypotheses then copyBuffer pointer c_hypothesesSize c_hypotheses else return (Right [0, 0])
    return (NativeView <$> current <*> frames <*> declarations <*> hypotheses)

markProgram :: Machine -> IO (Either String ProgramMark)
markProgram (Machine identity state) = withPointer state $ \pointer -> mask_ $ do
    saved <- c_programMark pointer
    if saved == nullPtr then Left <$> readError pointer else do
        owner <- newForeignPtr c_destroy saved `onException` c_destroyNow saved
        Right . ProgramMark identity <$> newMVar (Just owner)

truncateProgram :: Machine -> ProgramMark -> IO (Either String ())
truncateProgram (Machine identity state) (ProgramMark source saved)
    | identity /= source = return (Left "program mark belongs to a different engine")
    | otherwise = withPointer state $ \pointer -> withPointer saved $ \mark -> do
        status <- c_programTruncate pointer mark
        if status < 0 then Left <$> readError pointer else return (Right ())

closeProgramMark :: ProgramMark -> IO ()
closeProgramMark (ProgramMark _ state) = closeState state

liveTokens :: Machine -> IO (Either String ([Word64], [Word64]))
liveTokens (Machine _ state) = withPointer state $ \pointer -> do
    copied <- copyBuffer pointer c_liveTokensSize c_state
    return $ copied >>= \words -> case words of
        count : rest
            | count >= 0 && toInteger count <= toInteger (length rest) -> case splitAt (fromIntegral count) rest of
                (hosts, premiseCount : premises)
                    | premiseCount >= 0 && toInteger premiseCount == toInteger (length premises) -> Right (map fromIntegral hosts, map fromIntegral premises)
                _ -> Left "Invalid Hol V2 live token buffer"
        _ -> Left "Invalid Hol V2 live token buffer"

fetchServiceDelta :: Machine -> IO (Either String ServiceDelta)
fetchServiceDelta (Machine _ state) = withPointer state $ \pointer -> do
    copied <- copyBuffer pointer c_serviceDeltaSize c_state
    return $ copied >>= \words -> case words of
        token : rest
            | token >= 0 -> Right (ServiceDelta (fromIntegral token) rest)
        _ -> Left "Invalid Hol V2 service delta buffer"

resumeWithView :: Machine -> Int -> Word64 -> Word64 -> Word64 -> [Int64] -> IO (Either String ())
resumeWithView (Machine _ state) result host premises view bindings = withPointer state $ \pointer ->
    withArrayLen bindings $ \count words -> do
        status <- c_resumeWithView pointer (fromIntegral result) host premises view words (fromIntegral count)
        if status < 0 then Left <$> readError pointer else return (Right ())

resumeWithRootDeltas :: Machine -> Int -> Word64 -> Word64 -> Word64 -> [Int64] -> Maybe RootDelta -> Maybe RootDelta -> IO (Either String ())
resumeWithRootDeltas machine result host premises view bindings constraints hypotheses = resumeWithSubscriptions machine result host premises view bindings constraints hypotheses Nothing

-- An absent subscription keeps the conservative historic-watch behavior. An
-- explicit empty set exports only event/disagreement roots. A nonempty set
-- names the retained host binding roots and every variable they depend on.
resumeWithSubscriptions :: Machine -> Int -> Word64 -> Word64 -> Word64 -> [Int64] -> Maybe RootDelta -> Maybe RootDelta -> Maybe RootDelta -> IO (Either String ())
resumeWithSubscriptions (Machine _ state) result host premises view bindings constraints hypotheses subscriptions = withPointer state $ \pointer ->
    withArrayLen bindings $ \count words ->
        withArrayLen roots $ \rootCount rootWords -> do
            status <- c_resumeWithRootDeltas pointer (fromIntegral result) host premises view words (fromIntegral count) rootWords (fromIntegral rootCount)
            if status < 0 then Left <$> readError pointer else return (Right ())
    where
        roots = fromIntegral (length entries) : concat entries
        entries = concat [encode 0 constraints, encode 1 hypotheses, encode 4 subscriptions]
        encode _ Nothing = []
        encode kind (Just delta) = [concat [[kind, rootToken delta, rootParent delta, fromIntegral (length (rootAdded delta))], rootAdded delta, [fromIntegral (length (rootRemoved delta))], rootRemoved delta]]

registerHostRoots :: Machine -> Int -> Word64 -> [Word64] -> IO (Either String ())
registerHostRoots (Machine _ state) kind token uids = withPointer state $ \pointer ->
    withArrayLen uids $ \count roots -> do
        status <- c_registerHostRoots pointer (fromIntegral kind) token roots (fromIntegral count)
        if status < 0 then Left <$> readError pointer else return (Right ())

liveViewTokens :: Machine -> IO (Either String [Word64])
liveViewTokens machine = countedIdentities machine c_liveViewsSize

getLiveIdentities :: Machine -> IO (Either String [Word64])
getLiveIdentities machine = countedIdentities machine c_liveIdentitiesSize

countedIdentities :: Machine -> (Ptr CMachine -> IO CSize) -> IO (Either String [Word64])
countedIdentities (Machine _ state) size = withPointer state $ \pointer -> do
    copied <- copyBuffer pointer size c_state
    return $ copied >>= \words -> case words of
        count : values
            | count >= 0 && toInteger count == toInteger (length values) && all (>= 0) values -> Right (map fromIntegral values)
        _ -> Left "Invalid Hol V2 identity list"

drainRetiredTokens :: Machine -> IO (Either String ([Word64], [Word64]))
drainRetiredTokens (Machine _ state) = withPointer state $ \pointer -> do
    copied <- copyBuffer pointer c_retiredTokensSize c_state
    return $ copied >>= \words -> case words of
        count : values
            | count >= 0 && 2 * toInteger count == toInteger (length values) -> groups values [] []
        _ -> Left "Invalid Hol V2 retired token buffer"
    where
        groups [] hosts views = Right (reverse hosts, reverse views)
        groups (kind : token : rest) hosts views
            | token > 0 && kind == 0 = groups rest (fromIntegral token : hosts) views
            | token > 0 && kind == 1 = groups rest hosts (fromIntegral token : views)
        groups _ _ _ = Left "Invalid Hol V2 retired token kind"
