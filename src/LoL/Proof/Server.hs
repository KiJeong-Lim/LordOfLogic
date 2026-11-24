{-# LANGUAGE ScopedTypeVariables #-}
module LoL.Proof.Server where

import Control.Concurrent
import Control.Exception
import Control.Monad (unless, void, when)
import Data.IORef
import qualified LoL.Proof.Json as Json
import qualified LoL.Proof.Protocol as Protocol
import System.Exit (exitFailure)
import System.IO
import System.IO.Error (ioeGetErrorString)

data Handlers
    = Handlers
        { executeRequest :: Protocol.Request -> IO Json.Value
        , cancelRequest  :: Protocol.Request -> Integer -> IO Json.Value
        , shutdownServer :: IO ()
        }
    deriving ()

-- Only the worker executes state-changing requests. The reader remains
-- available for cancellation, and a lock makes each output one whole frame.
serve :: Handle -> Handle -> Handle -> Handlers -> IO ()
serve input output logging handlers = mask $ \restore -> do
    mapM_ (\handle -> hSetEncoding handle utf8) [input, output, logging]
    hSetBuffering output LineBuffering
    writeLock <- newMVar ()
    active <- newMVar Nothing
    inbox <- newEmptyMVar
    stopped <- newEmptyMVar
    closing <- newIORef False
    failed <- newIORef False
    latest <- newIORef 0
    reader <- myThreadId
    let emit value = withMVar writeLock $ \() -> case Json.encode value of
            Left problem -> ioError (userError ("Cannot encode protocol response: " ++ problem))
            Right line -> hPutStrLn output line >> hFlush output
        run request = do
            result <- try (executeRequest handlers request)
            modifyMVar_ active $ \current -> return $ case current of
                Just (identity, completed, _) -> Just (identity, completed, True)
                Nothing -> Nothing
            case result of
                Right response -> emit response
                Left (exception :: SomeException) -> do
                    writeIORef failed True
                    case fromException exception of
                        Just (_ :: AsyncException) -> throwIO exception
                        Nothing -> do
                            emit (Protocol.failure (Just (Protocol.requestId request)) "internal-error" "The request failed unexpectedly; the session is closed.")
                            hPutStrLn logging ("LoL server: " ++ displayException exception)
                            shutdownServer handlers
                            throwIO exception
        worker = do
            (request, completed) <- takeMVar inbox
            run request `finally` (modifyMVar_ active (const (return Nothing)) >> void (tryPutMVar completed ()))
            worker
    owner <- forkFinally (restore worker) $ \result -> do
        void (tryPutMVar stopped ())
        ended <- readIORef closing
        case result of
            Left exception
                | not ended -> throwTo reader exception
            _ -> return ()
    let stop = do
            writeIORef closing True
            (shutdownServer handlers >> drain) `finally` killThread owner
            readMVar stopped
        drain = do
            current <- readMVar active
            case current of
                Nothing -> return ()
                Just (_, completed, _) -> readMVar completed
        admit request = do
            outcome <- modifyMVar active $ \current -> do
                unavailable <- (||) <$> readIORef failed <*> readIORef closing
                if unavailable then return (current, Left Nothing) else case current of
                    Just (_, completed, True) -> return (current, Left (Just completed))
                    Just _ -> return (current, Left Nothing)
                    Nothing -> do
                        completed <- newEmptyMVar
                        putMVar inbox (request, completed)
                        return (Just (Protocol.requestId request, completed, False), Right ())
            case outcome of
                Right () -> return True
                Left Nothing -> return False
                Left (Just completed) -> readMVar completed >> admit request
        loop = do
            frame <- Json.readFrame input `catch` \problem -> do
                hPutStrLn logging ("LoL server: could not read UTF-8 input: " ++ ioeGetErrorString problem)
                exitFailure
            case frame of
                Left problem -> emit (Protocol.failure Nothing "frame-too-large" problem)
                Right Nothing -> drain
                Right (Just source) -> do
                    case Protocol.decodeRequestWithId source of
                        Left (identity, problem) -> do
                            previous <- readIORef latest
                            case identity of
                                Just supplied
                                    | supplied <= previous -> emit (Protocol.failure identity "reused-request" "Request IDs must increase within a server connection.")
                                    | otherwise -> writeIORef latest supplied >> emit (Protocol.failure identity "invalid-request" problem)
                                Nothing -> emit (Protocol.failure Nothing "invalid-request" problem)
                            loop
                        Right request -> do
                            previous <- readIORef latest
                            let identity = Protocol.requestId request
                            if identity <= previous then do
                                emit (Protocol.failure (Just identity) "reused-request" "Request IDs must increase within a server connection.")
                                loop
                            else do
                                writeIORef latest identity
                                case Protocol.requestBody request of
                                    Protocol.Shutdown -> do
                                        drain
                                        shutdownServer handlers
                                        emit (Protocol.reply (Just identity) "ok" [("message", Json.String "The server is closed.")])
                                    Protocol.Cancel target -> do
                                        response <- cancelRequest handlers request target
                                        emit response
                                        loop
                                    _ -> do
                                        ended <- not <$> isEmptyMVar stopped
                                        accepted <- if ended then return False else admit request
                                        terminal <- (|| ended) <$> readIORef failed
                                        unless accepted (emit (Protocol.failure (Just identity) (if terminal then "closed" else "busy") (if terminal then "The server execution worker is closed." else "Another request is running; wait for its response or cancel it.")))
                                        when (not terminal) loop
    restore (emit ready >> loop) `finally` stop
    where
        ready = Json.object
            [ ("protocol", Json.Integer Protocol.protocolVersion)
            , ("event", Json.String "ready")
            , ("message", Json.String "LoL V1 server is ready.")
            , ("requestByteLimit", Json.Integer (toInteger Json.messageBytes))
            , ("positionEncoding", Json.String "unicode-scalar-1-based")
            ]
