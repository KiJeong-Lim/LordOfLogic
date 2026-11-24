{-# LANGUAGE CApiFFI #-}
module X.Machine (Machine, createMachine, closeMachine, withMachine, nextAnswer, withTerminalInterrupts) where

import Control.Concurrent (forkFinally, killThread, myThreadId, throwTo, yield)
import Control.Concurrent.MVar
import Control.Exception (AsyncException (UserInterrupt), allowInterrupt, bracket, finally, mask, mask_, onException)
import Control.Monad (unless, void)
import Data.Dynamic (toDyn)
import GHC.Conc (ensureIOManagerIsRunning)
import qualified GHC.Conc.Signal as Signal
import Data.Int (Int64)
import Foreign.C.String (peekCString)
import Foreign.C.Types
import Foreign.ForeignPtr
import Foreign.Marshal.Alloc (free)
import Foreign.Marshal.Array
import Foreign.Ptr
import Foreign.Storable (sizeOf)

data CMachine
    deriving ()

newtype Machine = Machine (MVar (Maybe (ForeignPtr CMachine)))
    deriving ()

foreign import ccall safe "hol_v1_create" c_create :: Ptr Int64 -> CSize -> IO (Ptr CMachine)
foreign import ccall safe "hol_v1_next" c_next :: Ptr CMachine -> IO CInt
foreign import ccall safe "hol_v1_answer_size" c_answerSize :: Ptr CMachine -> IO CSize
foreign import ccall safe "hol_v1_answer" c_answer :: Ptr CMachine -> Ptr Int64 -> CSize -> IO CInt
foreign import ccall safe "hol_v1_error" c_error :: Ptr CMachine -> IO (Ptr CChar)
foreign import ccall safe "hol_v1_destroy" c_destroyNow :: Ptr CMachine -> IO ()
foreign import ccall "&hol_v1_destroy" c_destroy :: FinalizerPtr CMachine
foreign import ccall safe "hol_terminal_interrupt_begin" c_interruptBegin :: IO CInt
foreign import ccall safe "hol_terminal_interrupt_signal" c_interruptSignal :: IO CInt
foreign import ccall safe "stg_sig_install" c_installSignal :: CInt -> CInt -> Ptr () -> IO CInt
foreign import ccall safe "hol_terminal_interrupt_end" c_interruptEnd :: IO ()

-- The RTS supplies persistent OS delivery. A bounded mailbox coalesces
-- repeated signals; only the scoped watcher can interrupt the terminal owner.
withTerminalInterrupts :: IO a -> IO a
withTerminalInterrupts action = mask $ \restore -> do
    installed <- c_interruptBegin
    unless (installed /= 0) (ioError (userError "A terminal interrupt handler is already active."))
    flip finally c_interruptEnd $ do
        owner <- myThreadId
        pending <- newEmptyMVar
        done <- newEmptyMVar
        number <- c_interruptSignal
        ensureIOManagerIsRunning
        let notify = void (tryPutMVar pending ())
        previous <- Signal.setHandler number (Just (const notify, toDyn notify))
        mode <- c_installSignal number (-4) nullPtr `onException` void (Signal.setHandler number previous)
        if mode == -3 then do
            void (Signal.setHandler number previous)
            ioError (userError "The terminal interrupt handler could not be installed.")
        else do
            let restoreHandler
                    | mode == -1 || mode == -2 = void (c_installSignal number mode nullPtr) >> void (Signal.setHandler number previous)
                    | otherwise = void (Signal.setHandler number previous) >> void (c_installSignal number mode nullPtr)
                watch = takeMVar pending >> throwTo owner UserInterrupt >> watch
            watcher <- forkFinally watch (const (void (tryPutMVar done ()))) `onException` restoreHandler
            restore action `finally` ((killThread watcher >> readMVar done) `finally` restoreHandler)

createMachine :: [Int64] -> IO Machine
createMachine code = mask_ $ withArrayLen code $ \count words -> do
    pointer <- c_create words (fromIntegral count)
    if pointer == nullPtr then
        ioError (userError "Hol V1 machine allocation failed")
    else do
        owner <- newForeignPtr c_destroy pointer `onException` c_destroyNow pointer
        Machine <$> newMVar (Just owner)

closeMachine :: Machine -> IO ()
closeMachine (Machine state) = modifyMVar_ state $ \current -> do
    maybe (return ()) finalizeForeignPtr current
    return Nothing

withMachine :: [Int64] -> (Machine -> IO a) -> IO a
withMachine code = bracket (createMachine code) closeMachine

nextAnswer :: Machine -> IO (Either String (Maybe [Int64]))
nextAnswer (Machine state) = withMVar state $ \current -> case current of
    Nothing -> return (Left "Hol V1 machine is closed")
    Just owner -> withForeignPtr owner $ \pointer -> do
        status <- nextStatus pointer
        if status < 0 then
            Left <$> readError pointer
        else if status == 0 then
            return (Right Nothing)
        else do
            count <- c_answerSize pointer
            if toInteger count > toInteger ((maxBound :: Int) `div` sizeOf (0 :: Int64)) then
                return (Left "Hol V1 answer exceeds the host array size")
            else bracket (mallocArray (fromIntegral count)) free $ \output -> do
                copied <- c_answer pointer output count
                if copied < 0 then
                    Left <$> readError pointer
                else
                    Right . Just <$> peekArray (fromIntegral count) output
    where
        nextStatus pointer = do
            status <- c_next pointer
            -- Let signal and timeout threads run even when this loop allocates nothing.
            if status == 2 then yield >> allowInterrupt >> nextStatus pointer else return status
        readError pointer = c_error pointer >>= peekCString
