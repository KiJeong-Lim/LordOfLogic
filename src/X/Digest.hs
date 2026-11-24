{-# LANGUAGE ForeignFunctionInterface #-}
module X.Digest (sha256IO, sha256PrefixedIO, sha256FileIO) where

import Data.Word (Word8)
import qualified Data.Vector.Unboxed as Vector
import Z.Hash (utf8)
import Data.Char (ord)
import Data.Bits ((.|.), (.&.), shiftR)
import Foreign.C.Types
import Foreign.C.String (CString, withCString)
import Foreign.Marshal.Array
import Foreign.Ptr
import Foreign.Storable (pokeElemOff)
import Numeric (showHex)

foreign import ccall safe "hol_sha256" c_sha256 :: Ptr Word8 -> CSize -> Ptr Word8 -> IO ()
foreign import ccall safe "hol_sha256_file" c_sha256_file :: CString -> Ptr Word8 -> IO CInt

sha256FileIO :: FilePath -> IO String
sha256FileIO path
    | '\0' `elem` path = ioError (userError "A digest file path cannot contain NUL")
    | otherwise = withCString path $ \source -> allocaArray 32 $ \output -> do
        accepted <- c_sha256_file source output
        if accepted == 0 then ioError (userError "Cannot fingerprint the running executable") else digestText output

digestText :: Ptr Word8 -> IO String
digestText output = concatMap hexadecimal <$> peekArray 32 output where
    hexadecimal value = if value < 16 then '0' : showHex value "" else showHex value ""

-- Prepared bytecode uses a compact ASCII alphabet. Copy it directly from the
-- packed packet alongside its UTF-8 header, preserving the general text hash
-- for malformed packets that contain other characters.
sha256PrefixedIO :: String -> Vector.Vector Char -> IO String
sha256PrefixedIO header payload
    | Vector.any ((> 127) . ord) payload = sha256IO (header ++ Vector.toList payload)
    | prefixLength > maxBound - Vector.length payload = ioError (userError "SHA-256 input size overflow")
    | otherwise = allocaArray count $ \bytes -> allocaArray 32 $ \output -> do
        pokeArray bytes prefix
        Vector.imapM_ (\index character -> pokeElemOff bytes (prefixLength + index) (fromIntegral (ord character))) payload
        c_sha256 bytes (fromIntegral count) output
        digestText output
    where
        prefix = utf8 header
        prefixLength = length prefix
        count = prefixLength + Vector.length payload

-- Explicit IO keeps the FFI boundary visible. Pure object fingerprints still
-- use Z.Hash; the cache can hash already-read payloads without a pure facade.
sha256IO :: String -> IO String
sha256IO source = do
    count <- encodedLength 0 source
    allocaArray count $ \bytes -> allocaArray 32 $ \output -> do
        fill bytes 0 source
        c_sha256 bytes (fromIntegral count) output
        digestText output
    where
        width character
            | character < 0x80 = 1
            | character < 0x800 = 2
            | character < 0x10000 = 3
            | otherwise = 4
        encodedLength count [] = return count
        encodedLength count (character : rest)
            | count > maxBound - size = ioError (userError "SHA-256 input size overflow")
            | otherwise = encodedLength (count + size) rest
            where
                size = width (ord character)
        fill _ _ [] = return ()
        fill bytes offset (character : rest) = do
            let code = ord character
                value = if code >= 0xd800 && code <= 0xdfff then 0xfffd else code
                put at byte = pokeElemOff bytes (offset + at) (fromIntegral byte :: Word8)
                tailByte at shift = put at (0x80 .|. ((value `shiftR` shift) .&. 0x3f))
            case width value of
                1 -> put 0 value
                2 -> put 0 (0xc0 .|. (value `shiftR` 6)) >> tailByte 1 0
                3 -> put 0 (0xe0 .|. (value `shiftR` 12)) >> tailByte 1 6 >> tailByte 2 0
                _ -> put 0 (0xf0 .|. (value `shiftR` 18)) >> tailByte 1 12 >> tailByte 2 6 >> tailByte 3 0
            fill bytes (offset + width value) rest
