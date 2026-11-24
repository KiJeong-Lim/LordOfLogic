module Z.Hash (utf8, sha256) where

import Data.Array (Array, (!), listArray)
import Data.Bits ((.&.), (.|.), complement, rotateR, shiftL, shiftR, xor)
import Data.Char (ord)
import Data.List (foldl')
import Data.Word (Word8, Word32, Word64)
import Numeric (showHex)

utf8 :: String -> [Word8]
utf8 = concatMap bytes where
    bytes character
        | point < 0x80 = [fromIntegral point]
        | point < 0x800 = [fromIntegral (0xc0 .|. shiftR point 6), continuation point]
        | point < 0x10000 = [fromIntegral (0xe0 .|. shiftR point 12), continuation (shiftR point 6), continuation point]
        | otherwise = [fromIntegral (0xf0 .|. shiftR point 18), continuation (shiftR point 12), continuation (shiftR point 6), continuation point]
        where
            point = if ord character >= 0xd800 && ord character <= 0xdfff then 0xfffd else ord character
    continuation point = fromIntegral (0x80 .|. (point .&. 0x3f))

data HashState = HashState !Word32 !Word32 !Word32 !Word32 !Word32 !Word32 !Word32 !Word32 deriving ()

-- FIPS 180-4, sections 4.2.2, 5.1.1, 5.3.3 and 6.2. Word32 arithmetic
-- supplies the specified modular sums; all words and the length are big endian.
sha256 :: [Word8] -> String
sha256 bytes = render (consume initial 0 bytes) where
    initial = HashState 0x6a09e667 0xbb67ae85 0x3c6ef372 0xa54ff53a 0x510e527f 0x9b05688c 0x1f83d9ab 0x5be0cd19
    render (HashState a b c d e f g h) = concatMap hexadecimal [a, b, c, d, e, f, g, h]
    hexadecimal value = replicate (8 - length encoded) '0' ++ encoded where
        encoded = showHex value ""
    consume :: HashState -> Word64 -> [Word8] -> HashState
    consume state count source
        | length block == 64 = next `seq` count `seq` consume next (count + 64) rest
        | otherwise = foldl' hashBlock state (chunks 64 padded)
        where
            (block, rest) = splitAt 64 source
            next = hashBlock state block
            bits = (count + fromIntegral (length block)) * 8
            padded = concat [block, [0x80], replicate ((55 - length block) `mod` 64) 0, [fromIntegral (shiftR bits offset) | offset <- [56, 48 .. 0]]]

chunks :: Int -> [a] -> [[a]]
chunks _ [] = []
chunks size values = first : chunks size rest where
    (first, rest) = splitAt size values

hashBlock :: HashState -> [Word8] -> HashState
hashBlock initial@(HashState a b c d e f g h) bytes = finish (foldl' turn initial (zip hashConstants [0 .. 63])) where
    schedule :: Array Int Word32
    schedule = listArray (0, 63) (map word (chunks 4 bytes) ++ [small1 (schedule ! (n - 2)) + schedule ! (n - 7) + small0 (schedule ! (n - 15)) + schedule ! (n - 16) | n <- [16 .. 63]])
    word = foldl' (\value byte -> shiftL value 8 .|. fromIntegral byte) 0
    small0 x = rotateR x 7 `xor` rotateR x 18 `xor` shiftR x 3
    small1 x = rotateR x 17 `xor` rotateR x 19 `xor` shiftR x 10
    large0 x = rotateR x 2 `xor` rotateR x 13 `xor` rotateR x 22
    large1 x = rotateR x 6 `xor` rotateR x 11 `xor` rotateR x 25
    turn (HashState a b c d e f g h) (constant, index) = HashState (first + second) a b c (d + first) e f g where
        first = h + large1 e + ((e .&. f) `xor` (complement e .&. g)) + constant + schedule ! index
        second = large0 a + ((a .&. b) `xor` (a .&. c) `xor` (b .&. c))
    finish (HashState u v w x y z s t) = HashState (a + u) (b + v) (c + w) (d + x) (e + y) (f + z) (g + s) (h + t)

hashConstants :: [Word32]
hashConstants =
    [ 0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5
    , 0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174
    , 0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da
    , 0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967
    , 0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85
    , 0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070
    , 0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3
    , 0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2
    ]

