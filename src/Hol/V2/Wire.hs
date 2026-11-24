-- A compact, bounded cache encoding of the existing FullArtifact DTO. It does
-- not replace .hbc, infer types or omit any runtime metadata. All payload bytes
-- are in 32..127, including encoded Unicode code points. There are no CR/LF
-- bytes for platform newline conversion to change.
module Hol.V2.Wire (encode, decode, decodePacked) where

import Control.Monad
import Control.Monad.Trans.Class
import Control.Monad.Trans.State.Strict
import Data.Char (chr, ord)
import Data.Int (Int64)
import Data.Word (Word64)
import qualified Data.Vector.Unboxed as Vector
import Data.Bits ((.|.), (.&.), complement, shiftL, shiftR)
import qualified Data.IntMap.Strict as IntMap
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Hol.V1.FullBytecode
import Hol.V1.Checked

type Get = StateT (Int, Vector.Vector Char) (Either String)

bad :: String -> Get a
bad message = lift (Left ("invalid prepared payload: " ++ message))

byte :: Get Int
byte = do
    (count, source) <- get
    when (count <= 0) (bad "truncated or non-ASCII byte")
    let value = ord (source Vector.! (Vector.length source - count))
    unless (value >= 32 && value < 128) (bad "truncated or non-ASCII byte")
    put (count - 1, source)
    return (value - 32)

tag :: Int -> ShowS
tag = (:) . chr . (+ 32)

-- Five payload bits, bit 6 for continuation. No host-endian representation or
-- unchecked machine-integer addition enters the persistent format.
putNatural :: Integer -> ShowS
putNatural value
    | value < 32 = tag (fromInteger value)
    | otherwise = tag (64 + fromInteger (mod value 32)) . putNatural (div value 32)

getNatural :: Get Integer
getNatural = getNaturalWithin Nothing

getNaturalWithin :: Maybe Integer -> Get Integer
getNaturalWithin bound = go 1 0 where
    go scale total = do
        value <- byte
        unless (value < 32 || value >= 64 && value < 96) (bad "natural number digit")
        let next = total + scale * toInteger (mod value 32)
        when (maybe False (next >) bound) (bad "machine integer overflow")
        if value < 32 then return next else do
            when (maybe False (scale * 32 >) bound) (bad "machine integer overflow")
            go (scale * 32) next

putInteger :: Integer -> ShowS
putInteger value = putNatural (if value < 0 then -2 * value - 1 else 2 * value)

getInteger :: Get Integer
getInteger = do
    value <- getNatural
    return (if odd value then negate (div value 2) - 1 else div value 2)

-- Machine fields dominate a prepared program. Decode their bounded digits
-- without constructing an Integer at every byte. Arbitrary naturals and
-- Presburger coefficients continue through getInteger above.
{-# INLINE getMachineNatural #-}
getMachineNatural :: Word64 -> Get Word64
getMachineNatural maximum = StateT $ \(remaining, source) -> go 0 0 remaining source where
    go shift total remaining source
        | remaining == 0 = invalid "truncated or non-ASCII byte"
        | otherwise = do
            let character = source Vector.! (Vector.length source - remaining)
            unless (ord character >= 32 && ord character < 128) (invalid "truncated or non-ASCII byte")
            let value = ord character - 32
            let digit = fromIntegral (value .&. 31)
            unless (value < 32 || value >= 64 && value < 96) (invalid "natural number digit")
            when (digit > maximum `shiftR` shift) (invalid "machine integer overflow")
            let next = total .|. (digit `shiftL` shift)
            when (next > maximum) (invalid "machine integer overflow")
            if value < 32 then Right (next, (remaining - 1, source)) else do
                when (shift >= 60 || maximum `shiftR` (shift + 5) == 0) (invalid "machine integer overflow")
                go (shift + 5) next (remaining - 1) source
    invalid = Left . ("invalid prepared payload: " ++)

putNumber :: Integral a => a -> ShowS
putNumber = putInteger . toInteger

-- All bounded fields in FullArtifact are signed Int or Int64. Decode the
-- zigzag magnitude in Word64, then complement its representable signed half.
-- The complement also represents minBound without a signed negation overflow.
getNumber :: Get Int
getNumber = do
    encoded <- getMachineNatural (2 * fromIntegral (maxBound :: Int) + 1)
    let magnitude = fromIntegral (encoded `shiftR` 1)
    let value = if odd encoded then complement magnitude else magnitude
    value `seq` return value

{-# INLINE getWordNumber #-}
getWordNumber :: Get Int64
getWordNumber = do
    encoded <- getMachineNatural maxBound
    let magnitude = fromIntegral (encoded `shiftR` 1)
    let value = if odd encoded then complement magnitude else magnitude
    value `seq` return value

putList :: (a -> ShowS) -> [a] -> ShowS
putList render values = putNatural (toInteger (length values)) . foldr ((.) . render) id values

{-# INLINE getList #-}
getList :: Get a -> Get [a]
getList item = do
    (remaining, _) <- get
    size <- getMachineNatural (fromIntegral remaining)
    unless (size <= fromIntegral remaining) (bad "impossible sequence length")
    replicateM (fromIntegral size) item

putText :: String -> ShowS
putText = putList (putNatural . toInteger . ord)

getText :: Get String
getText = getList $ do
    point <- getMachineNatural 0x10ffff
    unless (point <= 0x10ffff) (bad "Unicode code point")
    return (chr (fromIntegral point))

putMaybe :: (a -> ShowS) -> Maybe a -> ShowS
putMaybe _ Nothing = tag 0
putMaybe render (Just value) = tag 1 . render value

getMaybe :: Get a -> Get (Maybe a)
getMaybe item = do
    value <- byte
    case value of
        0 -> return Nothing
        1 -> Just <$> item
        _ -> bad "optional value tag"

putPair :: (a -> ShowS) -> (b -> ShowS) -> (a, b) -> ShowS
putPair first second (a, b) = first a . second b

getPair :: Get a -> Get b -> Get (a, b)
getPair = liftM2 (,)

putBoolean :: Bool -> ShowS
putBoolean value = tag (if value then 1 else 0)

getBoolean :: Get Bool
getBoolean = do
    value <- byte
    case value of
        0 -> return False
        1 -> return True
        _ -> bad "Boolean tag"

nest :: Int -> Get a -> Get a
nest depth action
    | depth >= 8192 = bad "metadata nesting limit"
    | otherwise = action

putCon :: StoredCon -> ShowS
putCon constant = case constant of
    SCData name -> tag 0 . putText name
    SCType name -> tag 1 . putText name
    SCDataUnique key hint -> tag 2 . putNumber key . putMaybe putText hint
    SCTypeUnique key -> tag 3 . putNumber key
    SCBuiltin key -> tag 4 . putNumber key
    SCLogical key -> tag 5 . putNumber key
    SCChar character -> tag 6 . putNatural (toInteger (ord character))
    SCNat value -> tag 7 . putInteger value

getCon :: Get StoredCon
getCon = do
    value <- byte
    case value of
        0 -> SCData <$> getText
        1 -> SCType <$> getText
        2 -> SCDataUnique <$> getNumber <*> getMaybe getText
        3 -> SCTypeUnique <$> getNumber
        4 -> SCBuiltin <$> getNumber
        5 -> SCLogical <$> getNumber
        6 -> do
            point <- getMachineNatural 0x10ffff
            unless (point <= 0x10ffff) (bad "character code point")
            return (SCChar (chr (fromIntegral point)))
        7 -> SCNat <$> getInteger
        _ -> bad "constant tag"

putKind :: StoredKind -> ShowS
putKind kind = case kind of
    SKStar -> tag 0
    SKArrow first second -> tag 1 . putKind first . putKind second

getKind :: Int -> Get StoredKind
getKind depth = nest depth $ do
    value <- byte
    case value of
        0 -> return SKStar
        1 -> SKArrow <$> getKind (depth + 1) <*> getKind (depth + 1)
        _ -> bad "kind tag"

putType :: StoredType -> ShowS
putType typ = case typ of
    STVar key -> tag 0 . putNumber key
    STMeta key -> tag 1 . putNumber key
    STCon constant kind -> tag 2 . putCon constant . putKind kind
    STApp function argument -> tag 3 . putType function . putType argument

getType :: Int -> Get StoredType
getType depth = nest depth $ do
    value <- byte
    case value of
        0 -> STVar <$> getNumber
        1 -> STMeta <$> getNumber
        2 -> STCon <$> getCon <*> getKind (depth + 1)
        3 -> STApp <$> getType (depth + 1) <*> getType (depth + 1)
        _ -> bad "type tag"

putVar :: StoredVar -> ShowS
putVar variable = case variable of
    SVNamed name -> tag 0 . putText name
    SVGenerated key hint -> tag 1 . putNumber key . putMaybe putText hint
    SVType key -> tag 2 . putNumber key

getVar :: Get StoredVar
getVar = do
    value <- byte
    case value of
        0 -> SVNamed <$> getText
        1 -> SVGenerated <$> getNumber <*> getMaybe getText
        2 -> SVType <$> getNumber
        _ -> bad "variable tag"

putPterm :: StoredPterm -> ShowS
putPterm term = case term of
    SPVar variable -> tag 0 . putInteger variable
    SPZero -> tag 1
    SPSucc body -> tag 2 . putPterm body
    SPPlus first second -> tag 3 . putPterm first . putPterm second

getPterm :: Int -> Get StoredPterm
getPterm depth = nest depth $ do
    value <- byte
    case value of
        0 -> SPVar <$> getInteger
        1 -> return SPZero
        2 -> SPSucc <$> getPterm (depth + 1)
        3 -> SPPlus <$> getPterm (depth + 1) <*> getPterm (depth + 1)
        _ -> bad "Presburger term tag"

putFormula :: StoredFormula -> ShowS
putFormula formula = case formula of
    SFTruth value -> tag 0 . putBoolean value
    SFRelation relation first second -> tag 1 . putNumber relation . putPterm first . putPterm second
    SFModulo first modulus second -> tag 2 . putPterm first . putInteger modulus . putPterm second
    SFNot body -> tag 3 . putFormula body
    SFConnect connective first second -> tag 4 . putNumber connective . putFormula first . putFormula second
    SFQuant universal variable body -> tag 5 . putBoolean universal . putInteger variable . putFormula body

getFormula :: Int -> Get StoredFormula
getFormula depth = nest depth $ do
    value <- byte
    case value of
        0 -> SFTruth <$> getBoolean
        1 -> SFRelation <$> getNumber <*> getPterm (depth + 1) <*> getPterm (depth + 1)
        2 -> SFModulo <$> getPterm (depth + 1) <*> getInteger <*> getPterm (depth + 1)
        3 -> SFNot <$> getFormula (depth + 1)
        4 -> SFConnect <$> getNumber <*> getFormula (depth + 1) <*> getFormula (depth + 1)
        5 -> SFQuant <$> getBoolean <*> getInteger <*> getFormula (depth + 1)
        _ -> bad "Presburger formula tag"

putLocation :: Maybe ((Int, Int), (Int, Int)) -> ShowS
putLocation = putMaybe (putPair (putPair putNumber putNumber) (putPair putNumber putNumber))

getLocation :: Get (Maybe ((Int, Int), (Int, Int)))
getLocation = getMaybe (getPair (getPair getNumber getNumber) (getPair getNumber getNumber))

putSymbol :: StoredSymbol -> ShowS
putSymbol symbol = case symbol of
    SSConstant constant -> tag 0 . putCon constant
    SSPresburger formula variables location -> tag 1 . putFormula formula . putList putInteger variables . putLocation location

getSymbol :: Get StoredSymbol
getSymbol = do
    value <- byte
    case value of
        0 -> SSConstant <$> getCon
        1 -> SSPresburger <$> getFormula 0 <*> getList getInteger <*> getLocation
        _ -> bad "symbol tag"

putMetadata :: Map.Map StoredType Int -> (Maybe String, Maybe StoredType, Maybe ((Int, Int), (Int, Int))) -> ShowS
putMetadata types (hint, typ, location) = putMaybe putText hint . putMaybe (putNumber . (types Map.!)) typ . putLocation location

getMetadata :: IntMap.IntMap StoredType -> Get (Maybe String, Maybe StoredType, Maybe ((Int, Int), (Int, Int)))
getMetadata types = (,,) <$> getMaybe getText <*> getMaybe typ <*> getLocation where
    typ = do
        index <- getNumber
        maybe (bad "metadata type index") return (IntMap.lookup index types)

putTypeEntry :: (StoredCon, [String], StoredType) -> ShowS
putTypeEntry (constant, names, typ) = putCon constant . putList putText names . putType typ

getTypeEntry :: Get (StoredCon, [String], StoredType)
getTypeEntry = (,,) <$> getCon <*> getList getText <*> getType 0

encode :: FullProgram -> Either String String
encode program = do
    validateFullBytecode program
    return (render (storeFullArtifact program) "")
    where
        render (FullArtifact version words symbols variables metadata kinds types queryTypes) = putNumber version . putList putNumber words . putList putSymbol symbols . putList putVar variables . putList putType annotations . putList (putMetadata indices) metadata . putList (putPair putCon putKind) kinds . putList putTypeEntry types . putList (putPair putVar putType) queryTypes where
            annotations = Set.toAscList (Set.fromList [typ | (_, Just typ, _) <- metadata])
            indices = Map.fromDistinctAscList (zip annotations [0 ..])

decode :: String -> Either String CheckedProgram
decode = decodePacked . Vector.fromList

decodePacked :: Vector.Vector Char -> Either String CheckedProgram
decodePacked source = do
    (artifact, (remaining, _)) <- runStateT parser (Vector.length source, source)
    unless (remaining == 0) (Left "trailing prepared payload")
    restoreCheckedArtifact artifact
    where
        parser = do
            version <- getNumber
            words <- getList getWordNumber
            symbols <- getList getSymbol
            variables <- getList getVar
            types <- getList (getType 0)
            let annotations = IntMap.fromDistinctAscList (zip [0 ..] types)
            FullArtifact version words symbols variables <$> getList (getMetadata annotations) <*> getList (getPair getCon (getKind 0)) <*> getList getTypeEntry <*> getList (getPair getVar (getType 0))
