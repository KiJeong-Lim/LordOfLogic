{-# LANGUAGE CPP #-}
module LoL.ImportCache (Location, Inputs, location, newInputs, sawImport, sawProgram, readEntry, writeEntry, hit) where

import Control.Exception (bracketOnError)
import Control.Monad (guard, unless, void, when)
import Data.IORef
import Data.List (nub)
import qualified Data.Map.Strict as Map
import qualified Hol.V2.Embedding as Hol
import LoL.Hol.Session (Kernel (..), Limits)
import qualified LoL.Module as Module
import qualified LoL.Object as Object
import System.Directory (XdgDirectory (XdgCache), getXdgDirectory, removeFile, renameFile)
import System.Environment (lookupEnv)
import System.FilePath ((</>), isAbsolute, takeDirectory)
import System.IO (hClose, hPutStr, hPutStrLn, stderr, hSetEncoding, openTempFile, utf8)
import System.IO.Error (tryIOError)
import Text.Read (readMaybe)
import X.Digest (sha256IO)
#ifndef mingw32_HOST_OS
import Data.Bits ((.&.))
import System.IO.Error (isAlreadyExistsError, isDoesNotExistError)
import qualified System.Posix.Directory as Posix
import qualified System.Posix.Files as Files
import System.Posix.User (getEffectiveUserID)
#endif

-- A hit saves source elaboration and tactic execution. The object contains
-- explicit terms and is admitted by the caller's current Hol kernel.
data Location = Location FilePath String
data Inputs = Inputs (IORef (Map.Map String String)) (IORef (Maybe [(FilePath, Hol.ProgramInputs)]))

schema :: String
schema = "LoL imports 1"

newInputs :: IO Inputs
newInputs = Inputs <$> newIORef Map.empty <*> newIORef (Just [])

sawImport :: Maybe Inputs -> Module.Unit -> IO ()
sawImport Nothing _ = return ()
sawImport (Just (Inputs imports _)) unit = modifyIORef' imports (Map.insert (Module.unitName unit) (Module.unitDigest unit))

sawProgram :: Maybe Inputs -> FilePath -> Kernel -> IO ()
sawProgram Nothing _ _ = return ()
sawProgram (Just (Inputs _ programs)) path program = modifyIORef' programs $ \prior -> do
    seen <- prior
    snapshot <- manifest program
    return (nub ((path, snapshot) : seen))

-- Retain exactly the sources and lookup edges used to compile this running
-- program. Loader warnings and the cold/warm origin of Hol bytecode are
-- absent from its semantics. Host callbacks have no reusable identity.
manifest :: Kernel -> Maybe Hol.ProgramInputs
manifest kernel = do
    case kernelAsked kernel of { Just _ -> Nothing; Nothing -> Just () }
    Hol.programInputs (kernelReady kernel)

location :: Kernel -> Maybe Kernel -> Limits -> FilePath -> FilePath -> String -> IO (Maybe Location)
location kernel program limits root path source = do
    enabled <- lookupEnv "LOL_IMPORT_CACHE"
    case (enabled, inputs) of
        (Just "off", _) -> return Nothing
        (_, Nothing) -> return Nothing
        (_, Just targets) -> optional $ do
            directory <- getXdgDirectory XdgCache ("lord-of-logic" </> "imports")
            safe <- privateDirectory directory
            if not safe then return Nothing else do
                compiler <- Hol.cacheCompiler (kernelFresh kernel)
                digest <- sha256IO source
                key <- sha256IO (show (schema, compiler, targets, limits, root, path, digest))
                file <- sha256IO (show (root, path))
                return (Just (Location (directory </> file ++ ".loc") key))
    where
        inputs = do
            base <- manifest kernel
            elab <- traverse manifest (kernelElaborator kernel)
            supplied <- traverse bundled program
            return (base, elab, supplied)
        bundled p = do
            guard (kernelBundled p)
            manifest p

optional :: IO (Maybe a) -> IO (Maybe a)
optional action = either (const Nothing) id <$> tryIOError action

-- Object checks do not establish that well-typed axioms came from the
-- source. Only the current user's private, non-substitutable files may
-- attest that a packet was published by a successful source execution.
privateDirectory :: FilePath -> IO Bool
privateFile :: FilePath -> IO Bool
#ifdef mingw32_HOST_OS
privateDirectory _ = return False
privateFile _ = return False
#else
privateDirectory path
    | not (isAbsolute path) = return False
    | otherwise = getEffectiveUserID >>= \uid -> inspect uid path
    where
        inspect uid current = do
            let parent = takeDirectory current
            ancestors <- if parent == current then return True else inspect uid parent
            if not ancestors then return False else do
                status <- tryIOError (Files.getSymbolicLinkStatus current)
                entry <- case status of
                    Left e | isDoesNotExistError e -> do
                        made <- tryIOError (Posix.createDirectory current 0o700)
                        either (\err -> unless (isAlreadyExistsError err) (ioError err)) return made
                        Files.getSymbolicLinkStatus current
                    result -> either ioError return result
                let mode = Files.fileMode entry
                    owner = Files.fileOwner entry
                    private = owner == uid && mode .&. 0o077 == 0
                    trusted = (owner == uid || owner == 0) && mode .&. 0o022 == 0
                    sticky = owner == 0 && mode .&. 0o1000 /= 0
                return (Files.isDirectory entry && (if current == path then private else trusted || sticky))

privateFile path = do
    uid <- getEffectiveUserID
    file <- Files.getSymbolicLinkStatus path
    return (Files.isRegularFile file && Files.fileOwner file == uid && Files.fileMode file .&. 0o077 == 0)
#endif

readEntry :: Location -> String -> IO (Maybe Object.ObjectFile)
readEntry (Location file key) name = optional $ do
    safe <- privateFile file
    if not safe then return Nothing else do
        contents <- Module.readInput (Object.objectTextLimit + manifestLimit + 160) file
        case contents of
            Left _ -> return Nothing
            Right packet -> case lines3 packet of
                Just (found, checksum, metadata, object) | found == key, length metadata <= manifestLimit -> do
                    actual <- sha256IO (key ++ "\n" ++ metadata ++ "\n" ++ object)
                    if checksum /= actual then return Nothing else case readMaybe metadata :: Maybe [(FilePath, Hol.ProgramInputs)] of
                        Nothing -> return Nothing
                        Just inputs -> do
                            valid <- and <$> mapM (uncurry Hol.currentProgramInputs) inputs
                            return $ do
                                guard valid
                                parsed <- either (const Nothing) Just (Object.decodeObject object)
                                guard (Object.objectModule parsed == name)
                                return parsed
                _ -> return Nothing
    where
        line input = case break (== '\n') input of
            (first, _:rest) -> Just (first, rest)
            _ -> Nothing
        lines3 input = do
            (k, r1) <- line input
            (s, r2) <- line r1
            (m, object) <- line r2
            return (k, s, m, object)

manifestLimit :: Int
manifestLimit = 1024 * 1024

writeEntry :: Location -> Inputs -> Module.Unit -> IO ()
writeEntry (Location file key) (Inputs imports programs) unit = void $ tryIOError $ do
    seen <- readIORef imports
    proofs <- readIORef programs
    let stored = Module.unitObject unit
    -- Undo may have removed a previously executed Import from the object.
    -- In that case replaying its published graph would skip a source check.
    when (seen == Map.fromList (Object.objectImports stored)) $ case proofs of
        Nothing -> return ()
        Just used -> do
            let metadata = show used
                object = Object.encodeObject stored
            when (length metadata <= manifestLimit && length object <= Object.objectTextLimit) $ do
                digest <- sha256IO (key ++ "\n" ++ metadata ++ "\n" ++ object)
                bracketOnError (openTempFile (takeDirectory file) ".import-") cleanup $ \(temporary, handle) -> do
                    hSetEncoding handle utf8
                    hPutStr handle (key ++ "\n" ++ digest ++ "\n" ++ metadata ++ "\n" ++ object)
                    hClose handle
                    renameFile temporary file
                Hol.prunePackets ".loc" file
    where
        cleanup (temporary, handle) = do
            void (tryIOError (hClose handle))
            void (tryIOError (removeFile temporary))

-- Optional diagnostics for measuring a real source-import cache hit.
hit :: String -> IO ()
hit name = do
    enabled <- lookupEnv "LOL_IMPORT_CACHE_TRACE"
    when (enabled == Just "1") (void (tryIOError (hPutStrLn stderr ("LoL import cache hit: " ++ name))))
