{-# LANGUAGE ScopedTypeVariables #-}
module LoL.Proof.Main where

import Control.Concurrent
import Control.Exception
import Control.Monad (unless, void, when)
import Data.Char (isSpace)
import Data.IORef
import Data.List (dropWhileEnd, stripPrefix)
import LoL.Diagnostic (renderDiagnostic)
import qualified LoL.Front.Parse as Front
import qualified LoL.Front.Syntax as Front
import qualified LoL.Hol.Session as Kernel
import qualified LoL.Module as Module
import qualified LoL.Proof.Document as Document
import qualified LoL.Proof.Executor as Executor
import qualified LoL.Proof.Json as Json
import qualified LoL.Proof.Protocol as Protocol
import qualified LoL.Proof.Server as Server
import qualified LoL.Proof.Session as Proof
import qualified LoL.Proof.View as View
import System.Directory (canonicalizePath, doesDirectoryExist, getCurrentDirectory)
import System.FilePath (takeDirectory)
import System.Exit (exitFailure)
import System.IO
import System.IO.Error (doesNotExistErrorType, ioeGetErrorString, mkIOError)
import X.Machine (withTerminalInterrupts)

withExecutor :: Kernel.Limits -> (Executor.Executor -> IO a) -> IO a
withExecutor limits action = do
    base <- Kernel.loadSurfaceKernel >>= either startupFailure return
    flip finally (Kernel.closeKernel base) $ do
        program <- Kernel.loadProofProgram >>= either startupFailure return
        flip finally (Kernel.closeKernel program) $ do
            root <- getCurrentDirectory
            bracket (Executor.newExecutor base program limits root) Executor.closeExecutor action
    where
        startupFailure problem = hPutStrLn stderr ("LoL: could not load the Hol programs from the project root: " ++ problem) >> exitFailure

loadSource :: Kernel.Kernel -> Kernel.Limits -> FilePath -> FilePath -> ([String] -> IO ()) -> IO (Either Module.Failure Module.Loaded)
loadSource base limits project original emit = do
    paths <- try ((,) <$> canonicalizePath project <*> canonicalizePath original) :: IO (Either IOException (FilePath, FilePath))
    case paths of
        Left problem -> return (Left (Module.inputFailure original problem))
        Right (root, path) -> do
            input <- Module.readSource path
            case input of
                Left problem -> return (Left (Module.inputFailure original problem))
                Right source -> do
                    result <- Document.runDocument base limits (Document.newBatchDocument root path source) emit
                    return $ case result of
                        Left failure
                            | Module.failurePath failure == path -> Left failure { Module.failurePath = original }
                        _ -> result

server :: Kernel.Limits -> IO ()
server limits = withExecutor limits $ \executor -> Server.serve stdin stdout stderr (handlers executor)

handlers :: Executor.Executor -> Server.Handlers
handlers executor = Server.Handlers run cancel (Executor.closeExecutor executor) where
    run request = View.resultJson (Protocol.requestId request) <$> Executor.execute executor (Executor.ProtocolOperation request)
    cancel request target = do
        accepted <- Executor.cancel executor target
        return $ if accepted then Protocol.reply (Just (Protocol.requestId request)) "ok" [("target", Json.Integer target), ("message", Json.String "Cancellation was requested. The target request's final response determines its outcome.")] else Protocol.failure (Just (Protocol.requestId request)) "not-cancellable" "The target request is not running or is completing an atomic operation."

-- A terminal command runs on a worker just like a server command. Ctrl-C
-- targets it and then waits for its final, restored-or-failed response.
awaitOperation :: Executor.Executor -> Executor.Operation -> IO Executor.Result
awaitOperation executor operation = mask $ \restore -> do
    response <- newEmptyMVar
    void $ forkIO $ try (restore (Executor.execute executor operation)) >>= putMVar response
    let wait = restore (readMVar response) `catch` \exception -> case exception of
            UserInterrupt -> cancelSafely >> wait
            _ -> throwIO (exception :: AsyncException)
        cancelSafely = requestCancellation `catch` \exception -> case exception of
            UserInterrupt -> cancelSafely
            _ -> throwIO (exception :: AsyncException)
        requestCancellation = do
            finished <- not <$> isEmptyMVar response
            unless finished $ do
                accepted <- Executor.cancel executor (Executor.identityOf operation)
                unless accepted (threadDelay 1000 >> requestCancellation)
    result <- wait
    either (throwIO :: SomeException -> IO Executor.Result) return result

interactive :: Kernel.Limits -> Maybe FilePath -> IO ()
interactive limits path = withTerminalInterrupts $ withExecutor limits $ \executor -> do
    mapM_ (\handle -> hSetEncoding handle utf8) [stdin, stdout, stderr]
    hSetBuffering stdout NoBuffering
    source <- maybe (return "") readSource path
    let actualPath = maybe "Interactive.lol" id path
    initial <- awaitOperation executor (Executor.ProtocolOperation (Protocol.Request 1 (Protocol.Open "terminal" 0 actualPath source)))
    case Executor.resultError initial of
        Just (_, message) -> hPutStrLn stderr ("LoL: " ++ message) >> exitFailure
        Nothing -> do
            next <- newIORef 2
            putStrLn "LoL V1. End commands with a period. Use :next, :run, :discard, :save PATH, or :quit."
            when (path /= Nothing) (putStrLn "The source is open at its first command; use :next or :run.")
            loop executor next ""
    where
        readSource file = Module.readSource file >>= either reject return where
            reject problem = do
                hPutStrLn stderr (renderDiagnostic file "" (Module.failureDiagnostic (Module.inputFailure file problem)))
                exitFailure

loop :: Executor.Executor -> IORef Integer -> String -> IO ()
loop executor counter buffered = do
    following <- iteration `catch` \exception -> case exception of
        UserInterrupt -> putStrLn "\nInput cancelled." >> return (Just "")
        _ -> throwIO (exception :: AsyncException)
    maybe (return ()) (loop executor counter) following
    where
    iteration = do
        current <- Executor.currentDocument executor
        putStr (if null buffered then prompt current else "...> ")
        input <- Json.readFrame stdin `catch` \problem -> do
            hPutStrLn stderr ("LoL: could not read UTF-8 terminal input: " ++ ioeGetErrorString problem)
            exitFailure
        let control = dropWhileEnd isSpace . dropWhile isSpace
        case input of
            Left message -> hPutStrLn stderr ("LoL: " ++ message) >> exitFailure
            Right Nothing
                | null buffered -> putStrLn "" >> return Nothing
                | otherwise -> do
                    identity <- fresh counter
                    result <- awaitOperation executor (Executor.TerminalOperation identity buffered)
                    hPutStr stderr (View.terminal result)
                    hPutStrLn stderr "LoL: unexpected end of input in an unfinished command."
                    exitFailure
            Right (Just line)
                | null buffered, control line == ":quit" -> return Nothing
                | null buffered, control line == ":next" -> next executor counter >>= present >> return (Just "")
                | null buffered, control line == ":run" -> runRemaining executor counter >> return (Just "")
                | null buffered, control line == ":discard" -> do
                    identity <- fresh counter
                    case current of
                        Nothing -> putStrLn "No document is open."
                        Just opened -> do
                            let reference = Protocol.Reference (Executor.openIdentity opened) (Executor.openIncarnation opened) (Executor.openRevision opened) (Document.documentState (Executor.openDocument opened))
                            result <- awaitOperation executor (Executor.ProtocolOperation (Protocol.Request identity (Protocol.Replace reference (Executor.openRevision opened + 1) "")))
                            present result
                            when (Executor.resultError result == Nothing) (putStrLn "The unexecuted source was discarded.")
                    return (Just "")
                | null buffered, Just target <- stripPrefix ":save " (dropWhile isSpace line), not (null target) -> do
                    case current of
                        Nothing -> putStrLn "No document is open."
                        Just opened -> do
                            saved <- try (saveTranscript target (Document.documentSource (Executor.openDocument opened))) :: IO (Either IOException ())
                            either (hPutStrLn stderr . ("Could not save the transcript: " ++) . show) (const (putStrLn ("The transcript was saved to " ++ target ++ "."))) saved
                    return (Just "")
                | null buffered, ':' : _ <- control line -> do
                    putStrLn "Unknown terminal command. Use :next, :run, :discard, :save PATH, or :quit."
                    return (Just "")
                | null buffered, all Front.sourceSpace line -> return (Just "")
                | otherwise -> do
                    let source = buffered ++ line ++ "\n"
                    if length source > Json.messageBytes then do
                        putStrLn "The command exceeds 1048576 characters; input was discarded."
                        return (Just "")
                    else submit (map snd (Front.commandChunks source))
        where
            -- Keep whitespace between pasted commands in the transcript.
            submit [] = return (Just "")
            submit (source : more) = case more of
                later : rest -> do
                    let (gap, remaining) = span Front.sourceSpace later
                    run (source ++ gap) (if null remaining then rest else remaining : rest)
                [] -> run source []
            run source rest
                | complete source = do
                    identity <- fresh counter
                    result <- awaitOperation executor (Executor.TerminalOperation identity source)
                    present result
                    case (Executor.resultError result, Executor.resultReply result) of
                        (Nothing, Just reply)
                            | Document.replyFailure reply == Nothing -> submit rest
                        _ -> return (Just "")
                | otherwise = return (Just source)

-- :save follows the file the user selected, including a final symlink.
-- The parent directory must already exist, as for an ordinary file save.
saveTranscript :: FilePath -> String -> IO ()
saveTranscript target source = do
    path <- canonicalizePath target
    let parent = takeDirectory path
    exists <- doesDirectoryExist parent
    unless exists (ioError (mkIOError doesNotExistErrorType "save transcript" Nothing (Just parent)))
    Module.publishText path source

fresh :: IORef Integer -> IO Integer
fresh counter = atomicModifyIORef' counter (\identity -> (identity + 1, identity))

present :: Executor.Result -> IO ()
present = putStr . View.terminal

next :: Executor.Executor -> IORef Integer -> IO Executor.Result
next executor counter = do
    current <- Executor.currentDocument executor
    identity <- fresh counter
    case current of
        Nothing -> return (Executor.failure Nothing "no-document" "No document is open.")
        Just opened -> do
            let reference = Protocol.Reference (Executor.openIdentity opened) (Executor.openIncarnation opened) (Executor.openRevision opened) (Document.documentState (Executor.openDocument opened))
            awaitOperation executor (Executor.ProtocolOperation (Protocol.Request identity (Protocol.Next reference)))

runRemaining :: Executor.Executor -> IORef Integer -> IO ()
runRemaining executor counter = do
    result <- next executor counter
    present result
    case (Executor.resultError result, Executor.resultReply result) of
        (Nothing, Just reply)
            | Document.replyFailure reply == Nothing, not (Document.replyAtEnd reply) -> runRemaining executor counter
        _ -> return ()

complete :: String -> Bool
complete source = case Front.lexAt (1, 1) source of
    Left problem -> Front.frontCode problem `notElem` ["L-Comment", "L-String"]
    Right [] -> True
    Right tokens -> Front.tokenKind (last tokens) == "."

prompt :: Maybe Executor.OpenDocument -> String
prompt current = case current >>= Document.documentProof . Executor.openDocument of
    Nothing -> "LoL> "
    Just pending -> header (Document.pendingHeader pending) where
        header command = case command of
            Front.CUniverses _ _ inner -> header inner
            Front.CDefinition _ _ name _ _ _ -> (showString (Front.nameText name) . showChar '[' . shows state . showString "]> ") ""
            _ -> "Proof> "
        state = Proof.proofStateId (Document.pendingView pending)
