module Hol.V2.Cache
    ( Manifest (..), manifestFor, cachePath, readCache, writeCache, compilerIdentity, pruneCache
    , cachePathWith, readCacheWith, writeCacheWith
    ) where

import Control.Exception (IOException, bracket, bracketOnError, evaluate, try)
import Control.Monad
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import qualified Data.Vector.Unboxed as Vector
import qualified Data.Vector.Unboxed.Mutable as Mutable
import Data.List (sortOn)
import Hol.BETA.ModuleLoader
import Hol.V1.FullBytecode
import Hol.V1.Checked (CheckedProgram)
import qualified Hol.V2.Wire as Wire
import System.Directory
import System.FilePath
import System.Environment (getExecutablePath)
import System.Exit (ExitCode (ExitSuccess))
import System.IO.Error (tryIOError)
import System.Process (CreateProcess (..), StdStream (..), proc, waitForProcess, withCreateProcess)
import System.IO hiding (utf8)
import Text.Read (readMaybe)
import X.Digest (sha256IO, sha256PrefixedIO, sha256FileIO)
import Z.Hash

-- Source hashes are taken from the exact text read by the module loader.
-- Import edges are resolved again on a hit: adding a nearer module or changing
-- a symlink must invalidate the cache even if all old target files still exist.
data Manifest
    = Manifest
        { manifestRoot     :: FilePath
        , manifestMain     :: FilePath
        , manifestSources  :: [(FilePath, String, [(String, FilePath)])]
        , manifestCompiler :: String
        , manifestWarnings :: [String]
        }
    deriving (Eq, Read, Show)

schema :: String
schema = "HolPrepared 7 native6 artifact7 executable-identity"

compilerIdentity :: IO String
compilerIdentity = do
    running <- doesFileExist "/proc/self/exe"
    path <- if running then return "/proc/self/exe" else getExecutablePath
    accelerated <- tryIOError $ withBinaryFile path ReadMode $ \input -> do
        let command = (proc "/usr/bin/sha256sum" []) { std_in = UseHandle input, std_out = CreatePipe, std_err = NoStream }
        withCreateProcess command $ \_ output _ child -> case output of
            Nothing -> return Nothing
            Just handle -> do
                line <- hGetLine handle
                status <- waitForProcess child
                let (digest, name) = splitAt 64 line
                return (if status == ExitSuccess && name == "  -" && all hexadecimal digest then Just digest else Nothing)
    case accelerated of
        Right (Just digest) -> return digest
        _ -> sha256FileIO path
    where
        hexadecimal character = character >= '0' && character <= '9' || character >= 'a' && character <= 'f'

manifestFor :: LoadedModule -> IO Manifest
manifestFor loaded = do
    root <- getCurrentDirectory >>= canonicalizePath
    return (Manifest root (moduleEnvPath (loadedMain loaded)) sources "" (loadedWarnings loaded))
    where
        sources =
            [ (moduleEnvPath env, moduleEnvSourceHash env, zip (moduleEnvImports env) (moduleEnvImportPaths env))
            | env <- Map.elems (loadedAll loaded)
            ]

cachePath :: FilePath -> IO FilePath
cachePath main = compilerIdentity >>= \compiler -> cachePathWith compiler main

cachePathWith :: String -> FilePath -> IO FilePath
cachePathWith compiler main = do
    root <- getCurrentDirectory >>= canonicalizePath
    canonical <- canonicalizePath main
    directory <- getXdgDirectory XdgCache ("lol" </> "hol-v2")
    return (directory </> sha256 (utf8 (show (schema, compiler, root, canonical))) <.> "hpc")

cacheLimit :: Int
cacheLimit = 16 * 1024 * 1024

-- Force the packet before closing its Handle. The second limit covers a file
-- that grows after hFileSize. Keeping characters preserves the text encoding
-- of the manifest and sources; only the wire payload has an ASCII alphabet.
boundedText :: FilePath -> IO (Either String (Vector.Vector Char))
boundedText path = bracket (openFile path ReadMode) hClose $ \handle -> do
    bytes <- hFileSize handle
    if bytes > fromIntegral cacheLimit then return (Left "prepared cache exceeds 16 MiB") else do
        text <- hGetContents handle
        packet <- evaluate $ Vector.create $ do
            buffer <- Mutable.new (fromIntegral bytes + 1)
            fill buffer 0 text
        return (if Vector.length packet > cacheLimit then Left "prepared cache exceeds 16 MiB" else Right packet)
    where
        fill buffer used contents
            | used > cacheLimit = return (Mutable.take used buffer)
            | otherwise = case contents of
                [] -> return (Mutable.take used buffer)
                character : rest
                    | used == Mutable.length buffer -> do
                        grown <- Mutable.grow buffer (min used (cacheLimit + 1 - used))
                        fill grown used contents
                    | otherwise -> do
                        Mutable.write buffer used character
                        fill buffer (used + 1) rest

ioResult :: IO (Either String a) -> IO (Either String a)
ioResult action = do
    result <- try action
    return (either (Left . show . (id :: IOException -> IOException)) id result)

readCache :: FilePath -> FilePath -> IO (Either String (Manifest, CheckedProgram))
readCache storage main = ioResult (compilerIdentity >>= \compiler -> readCacheWith compiler storage main)

readCacheWith :: String -> FilePath -> FilePath -> IO (Either String (Manifest, CheckedProgram))
readCacheWith compiler storage main = ioResult $ do
    contents <- boundedText storage
    root <- getCurrentDirectory >>= canonicalizePath
    canonical <- canonicalizePath main
    case contents >>= envelope of
        Left message -> return (Left message)
        Right (manifest, manifestText, digest, payload)
            | manifestRoot manifest /= root || manifestMain manifest /= canonical -> return (Left "prepared cache belongs to another source or project root")
            | manifestCompiler manifest /= compiler -> return (Left "prepared cache belongs to another executable/compiler")
            | otherwise -> do
                actual <- sha256PrefixedIO (manifestText ++ "\n") payload
                if actual /= digest then return (Left "prepared cache checksum mismatch") else do
                    valid <- checkSources manifest
                    return $ do
                        valid
                        program <- Wire.decodePacked payload
                        return (manifest, program)
    where
        envelope text = do
            (version, rest) <- line text
            unless (Vector.toList version == schema) (Left "prepared cache format/compiler version mismatch")
            (manifestLine, next) <- line rest
            let manifestText = Vector.toList manifestLine
            manifest <- maybe (Left "invalid prepared cache source manifest") Right (readMaybe manifestText)
            (digestLine, payload) <- line next
            unless (Vector.length digestLine == 64 && Vector.all hexadecimal digestLine) (Left "invalid prepared cache payload digest")
            return (manifest, manifestText, Vector.toList digestLine, payload)
        line text = case Vector.elemIndex '\n' text of
            Just end -> Right (Vector.take end text, Vector.drop (end + 1) text)
            Nothing -> Left "truncated prepared cache header"
        hexadecimal character = elem character "0123456789abcdef"

-- Include the dependency graph, not only the compiled payload.
cacheDigest :: String -> String -> IO String
cacheDigest manifestText payload = sha256IO (manifestText ++ "\n" ++ payload)

checkSources :: Manifest -> IO (Either String ())
checkSources manifest
    | null rows || length rows /= Set.size paths || not (Set.member (manifestMain manifest) paths) = return (Left "invalid prepared cache source closure")
    | otherwise = foldM check (Right ()) rows
    where
        rows = manifestSources manifest
        paths = Set.fromList [path | (path, _, _) <- rows]
        check failed@(Left _) _ = return failed
        check (Right ()) (path, digest, imports) = do
            canonical <- canonicalizePath path
            text <- boundedText path
            if canonical /= path || outside path then return (Left "prepared cache source path changed") else case text of
                Left message -> return (Left message)
                Right source -> do
                    actual <- sha256PrefixedIO "" source
                    if actual /= digest then return (Left ("prepared cache source changed: " ++ path)) else foldM (edge path) (Right ()) imports
        outside path = not (isRelative relative) || elem ".." (splitDirectories relative) where
            relative = makeRelative (manifestRoot manifest) path
        edge _ failed@(Left _) _ = return failed
        edge importer (Right ()) (name, target)
            | not (Set.member target paths) = return (Left "prepared cache omits an imported source")
            | null name || any null (segments name) = return (Left "invalid prepared cache import name")
            | otherwise = do
                resolved <- resolveImport (takeDirectory importer) (manifestRoot manifest) name
                return (if resolved == Just target then Right () else Left ("prepared cache import resolution changed: " ++ name))
        segments source = case break (== '.') source of
            (first, []) -> [first]
            (first, _ : rest) -> first : segments rest

writeCache :: FilePath -> Manifest -> FullProgram -> IO (Either String ())
writeCache storage manifest program = ioResult (compilerIdentity >>= \compiler -> writeCacheWith compiler storage manifest program)

writeCacheWith :: String -> FilePath -> Manifest -> FullProgram -> IO (Either String ())
writeCacheWith compiler storage manifest0 program = ioResult $ case Wire.encode program of
    Left message -> return (Left message)
    Right payload -> do
        valid <- checkSources manifest
        case valid of
            Left message -> return (Left message)
            Right () -> do
                let manifestText = show manifest
                digest <- cacheDigest manifestText payload
                let text = concat [schema, "\n", manifestText, "\n", digest, "\n", payload]
                if length text > cacheLimit then return (Left "prepared cache exceeds 16 MiB") else do
                    createDirectoryIfMissing True (takeDirectory storage)
                    bracketOnError (openTempFile (takeDirectory storage) ".hol-prepared-") cleanup $ \(temporary, handle) -> do
                        hPutStr handle text
                        hClose handle
                        renameFile temporary storage
                    return (Right ())
    where
        manifest = manifest0 { manifestCompiler = compiler }
        cleanup (temporary, handle) = do
            _ <- try (hClose handle) :: IO (Either IOException ())
            _ <- try (removeFile temporary) :: IO (Either IOException ())
            return ()

-- Only automatic cache entries are evicted; explicit prepared files are not.
-- Concurrent writers may briefly exceed this budget, then each prunes again.
-- An entry that cannot be removed is no longer counted: another process took
-- it, or it is not this user's to manage. Counting it would remove the newer
-- entries in its place.
pruneCache :: FilePath -> IO ()
pruneCache storage = void $ ioResult $ do
    names <- listDirectory directory
    entries <- concat <$> mapM entry names
    discard (sum [size | (_, _, size) <- entries]) (length entries) (sortOn (\(time, path, _) -> (time, path)) entries)
    return (Right ())
    where
        directory = takeDirectory storage
        owned name = takeExtension name == ".hpc" && length (dropExtension name) == 64 && all (`elem` "0123456789abcdef") (dropExtension name)
        entry name
            | not (owned name) = return []
            | otherwise = do
                let path = directory </> name
                result <- ioResult $ do
                    size <- getFileSize path
                    time <- getModificationTime path
                    return (Right (time, path, size))
                return (either (const []) (: []) result)
        discard _ _ [] = return ()
        discard bytes count ((_, path, size) : remaining)
            | bytes <= 64 * 1024 * 1024 && count <= 128 = return ()
            | otherwise = do
                removed <- try (removeFile path) :: IO (Either IOException ())
                case removed of
                    Left _ -> discard (bytes - size) (count - 1) remaining
                    Right () -> discard (bytes - size) (count - 1) remaining
