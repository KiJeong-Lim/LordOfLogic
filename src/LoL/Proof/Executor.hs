{-# LANGUAGE ScopedTypeVariables #-}
module LoL.Proof.Executor where

import Control.Concurrent
import Control.Exception
import Control.Monad (unless, void)
import Data.IORef
import qualified Data.Map.Strict as Map
import qualified LoL.Proof.Command as Command
import qualified LoL.Proof.Document as Document
import qualified LoL.Proof.Protocol as Protocol
import qualified LoL.Proof.Session as Proof
import qualified LoL.Front.Parse as Front
import LoL.Hol.Session (Kernel, Limits, closeKernel)
import System.FilePath ((</>), isAbsolute, normalise, takeExtension)

data OpenDocument
    = OpenDocument
        { openIdentity    :: String
        , openIncarnation :: Integer
        , openRevision    :: Integer
        , openDocument    :: Document.Document
        }
    deriving ()

data Result
    = Result
        { resultDocument :: Maybe OpenDocument
        , resultReply    :: Maybe Document.Reply
        , resultError    :: Maybe (String, String)
        , resultInput    :: Maybe String
        }
    deriving ()

data Operation = ProtocolOperation Protocol.Request | TerminalOperation Integer String deriving ()

-- A restoration is one atomic operation. Tactic cancellation goes to the
-- proof owner; cancelling its waiting caller would abandon the result.
data Cancellation = Interruptible | Native Proof.ProofSession Integer | Atomic deriving ()

data Running
    = Running
        { runningRequest :: Integer
        , runningThread  :: ThreadId
        , runningCancel  :: Cancellation
        , runningWanted  :: Bool
        }
    deriving ()

data State
    = State
        { stateDocument :: Maybe OpenDocument
        , stateRunning  :: Maybe Running
        , stateLatest   :: Integer
        , stateClosed   :: Bool
        }
    deriving ()

data Executor
    = Executor
        { executorState   :: MVar State
        , executorBase    :: Kernel
        , executorProgram :: Kernel
        , executorLimits  :: Limits
        , executorRoot    :: FilePath
        }
    deriving ()

newtype Cancelled = Cancelled Integer deriving (Show)
instance Exception Cancelled

newExecutor :: Kernel -> Kernel -> Limits -> FilePath -> IO Executor
newExecutor base program limits root = Executor <$> newMVar (State Nothing Nothing 0 False) <*> pure base <*> pure program <*> pure limits <*> pure root

currentDocument :: Executor -> IO (Maybe OpenDocument)
currentDocument executor = stateDocument <$> readMVar (executorState executor)

identityOf :: Operation -> Integer
identityOf operation = case operation of
    ProtocolOperation request -> Protocol.requestId request
    TerminalOperation identity _ -> identity

failure :: Maybe OpenDocument -> String -> String -> Result
failure current code message = Result current Nothing (Just (code, message)) Nothing

execute :: Executor -> Operation -> IO Result
execute executor operation = mask $ \restore -> do
    owner <- myThreadId
    accepted <- modifyMVar control $ \state -> case stateRunning state of
        Just _ -> return (state, Left (failure (stateDocument state) "busy" "Another request is running."))
        Nothing
            | stateClosed state -> return (state, Left (failure Nothing "closed" "The session is closed."))
            | identity <= stateLatest state -> return (state, Left (failure (stateDocument state) "reused-request" "Request IDs must increase within a session."))
            | otherwise -> return (state { stateLatest = identity, stateRunning = Just (Running identity owner Interruptible False) }, Right (stateDocument state))
    case accepted of
        Left refused -> return refused
        Right before -> do
            proposed <- newIORef Nothing
            let finish result = do
                    -- Publication ends cancellation, but the next command
                    -- cannot start until obsolete workers have been closed.
                    modifyMVar_ control $ \state -> return state { stateDocument = resultDocument result, stateRunning = fmap (\active -> active { runningCancel = Atomic }) (stateRunning state) }
                    cleaned <- traverse retire (resultDocument result)
                    modifyMVar_ control $ \state -> return state { stateDocument = cleaned, stateRunning = Nothing }
                    let refreshed = case cleaned of
                            Nothing -> resultReply result
                            Just opened -> fmap (\reply -> reply { Document.replyDocument = openDocument opened }) (resultReply result)
                    return result { resultDocument = cleaned, resultReply = refreshed }
                retire opened = do
                    cleaned <- Document.disposeRetired (openDocument opened)
                    return opened { openDocument = cleaned }
                cancelled (Cancelled target)
                    | target == identity = do
                        readIORef proposed >>= mapM_ (discardNew before)
                        finish (failure before "cancelled" "The command was cancelled; the previous document state is retained.")
                    | otherwise = throwIO (Cancelled target)
                failed (exception :: SomeException) = do
                    readIORef proposed >>= mapM_ (discardNew before)
                    modifyMVar_ control $ \state -> return state { stateRunning = Nothing, stateClosed = True, stateDocument = Nothing }
                    mapM_ (Document.closeDocument . openDocument) before
                    throwIO exception
                run = do
                    result <- restore (dispatch executor operation before)
                    writeIORef proposed (Just result)
                    finish result
            (run `catch` cancelled) `catch` failed
    where
        control = executorState executor
        identity = identityOf operation

-- Only newly created workers are disposable before publication. Existing
-- workers and snapshots still belong to the previous visible document.
discardNew :: Maybe OpenDocument -> Result -> IO ()
discardNew before result = case resultDocument result of
    Nothing -> return ()
    Just opened -> do
        mapM_ (Proof.closeProof . Document.handleSession) fresh
        mapM_ closeKernel (Map.elems freshPrograms)
        where
            old = maybe [] (map Document.handleIdentity . handles . openDocument) before
            fresh = filter ((`notElem` old) . Document.handleIdentity) (handles (openDocument opened))
            handles document = Map.elems (Document.documentHandles document) ++ Document.documentRetired document
            oldPrograms = maybe Map.empty (Document.documentPrograms . openDocument) before
            freshPrograms = Map.difference (Document.documentPrograms (openDocument opened)) oldPrograms

setCancellation :: Executor -> Integer -> Cancellation -> IO ()
setCancellation executor identity cancellation = modifyMVar_ (executorState executor) $ \state -> case stateRunning state of
    Just active
        | runningRequest active == identity -> return state { stateRunning = Just active { runningCancel = cancellation } }
    _ -> ioError (userError "The command lost its execution ownership.")

cancel :: Executor -> Integer -> IO Bool
cancel executor target = mask_ $ modifyMVar (executorState executor) $ \state -> case stateRunning state of
    Just active
        | runningRequest active == target, not (runningWanted active) -> case runningCancel active of
            Atomic -> return (state, False)
            Interruptible -> do
                throwTo (runningThread active) (Cancelled target)
                return (state { stateRunning = Just active { runningWanted = True } }, True)
            Native _ _ -> do
                void (forkIO (cancelNative executor target))
                return (state { stateRunning = Just active { runningWanted = True } }, True)
    _ -> return (state, False)

-- The request can be registered before the proof worker has received it.
-- Retry while that exact request is active; the proof API also checks its ID.
cancelNative :: Executor -> Integer -> IO ()
cancelNative executor target = do
    active <- stateRunning <$> readMVar (executorState executor)
    case active of
        Just running
            | runningRequest running == target -> case runningCancel running of
                Native session internal -> do
                    delivered <- Proof.cancelProof session internal
                    unless delivered (threadDelay 1000 >> cancelNative executor target)
                _ -> return ()
        _ -> return ()

closeExecutor :: Executor -> IO ()
closeExecutor executor = mask $ \restore -> do
    active <- modifyMVar (executorState executor) $ \state -> return (state { stateClosed = True }, stateRunning state)
    case active of
        Just running -> do
            void (cancel executor (runningRequest running))
            restore wait
        Nothing -> return ()
    previous <- modifyMVar (executorState executor) $ \state -> return (state { stateClosed = True, stateDocument = Nothing }, stateDocument state)
    mapM_ (Document.closeDocument . openDocument) previous
    where
        wait = do
            active <- stateRunning <$> readMVar (executorState executor)
            case active of
                Nothing -> return ()
                Just _ -> threadDelay 1000 >> wait

dispatch :: Executor -> Operation -> Maybe OpenDocument -> IO Result
dispatch executor operation before = case operation of
    TerminalOperation identity source -> withDocument $ \opened -> do
        prepare identity source opened
        let document = openDocument opened
        response <- Document.submitText base limits identity source document
        let next = if Document.replyFailure response == Nothing then opened { openRevision = openRevision opened + 1 } else opened
        return (fromReply next response) { resultInput = Just (Document.documentSource document ++ Document.terminalChunk document source) }
    ProtocolOperation request -> case Protocol.requestBody request of
        Protocol.Open name revision path source -> case before of
            Just _ -> return (bad "document-open" "Close the current document before opening another one.")
            Nothing
                | takeExtension path /= ".lol" -> return (bad "document-path" "A source document must have the .lol extension.")
                | length source > Front.inputLimit -> return (bad "document-limit" ("The document exceeds " ++ show Front.inputLimit ++ " characters."))
                | otherwise -> do
                    setCancellation executor identity Atomic
                    let absolute = normalise (if isAbsolute path then path else executorRoot executor </> path)
                        document = Document.newDocument (executorProgram executor) (executorRoot executor) absolute source
                    return (Result (Just (OpenDocument name identity revision document)) Nothing Nothing Nothing)
        Protocol.Append reference revision source -> edit reference revision (Document.appendSource source)
        Protocol.Replace reference revision source -> edit reference revision (Document.replaceRemaining source)
        Protocol.Next reference -> withReference reference $ \opened -> do
            let document = openDocument opened
            prepare identity (Document.documentRemaining document) opened
            fromReply opened <$> Document.advanceDocument base limits identity document
        Protocol.Show reference -> withReference reference $ \opened -> return (Result (Just opened) Nothing Nothing Nothing)
        Protocol.Undo reference target -> withReference reference $ \opened -> do
            setCancellation executor identity Atomic
            fromReply opened <$> Document.rewindDocument identity target (openDocument opened)
        Protocol.Close reference -> withReference reference $ \opened -> do
            setCancellation executor identity Atomic
            Document.closeDocument (openDocument opened)
            return (Result Nothing Nothing Nothing Nothing)
        Protocol.Cancel _ -> return (bad "cancellation-route" "Cancellation must use the reader's cancellation channel.")
        Protocol.Shutdown -> return (bad "shutdown-route" "Shutdown must use the reader's shutdown channel.")
        where
            identity = Protocol.requestId request
    where
        base = executorBase executor
        limits = executorLimits executor
        bad = failure before
        withDocument action = maybe (return (bad "no-document" "Open a document before sending this request.")) action before
        withReference reference action = withDocument $ \opened ->
            if openIdentity opened /= Protocol.referenceDocument reference then return (bad "wrong-document" "The request names a different document.") else
                if openIncarnation opened /= Protocol.referenceIncarnation reference then return (bad "stale-incarnation" "The document was closed and reopened; use the current incarnation.") else
                    if openRevision opened /= Protocol.referenceRevision reference then return (bad "stale-revision" "The document revision has changed.") else
                        if Document.documentState (openDocument opened) /= Protocol.referenceState reference then return (bad "stale-state" "The document state has changed.") else action opened
        edit reference revision change = withReference reference $ \opened ->
            if revision <= openRevision opened then return (bad "stale-revision" "The new document revision must increase.") else case change (openDocument opened) of
                Left (code, message) -> return (bad code message)
                Right document -> return (Result (Just opened { openRevision = revision, openDocument = document }) Nothing Nothing Nothing)
        fromReply opened response = Result (Just opened { openDocument = Document.replyDocument response }) (Just response) Nothing Nothing
        prepare identity source opened = case Front.commandChunks source of
            (_, first) : _ -> case Document.parseNext (openDocument opened) first of
                Right (Just (Command.RunTactic {})) -> case Document.documentProof (openDocument opened) of
                    Just pending -> setCancellation executor identity (Native (Document.handleSession (Document.pendingHandle pending)) (Document.proofRequest identity))
                    Nothing -> return ()
                Right (Just (Command.UndoProof _)) -> setCancellation executor identity Atomic
                _ -> return ()
            _ -> return ()
