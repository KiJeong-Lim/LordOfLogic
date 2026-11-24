module LoL.Proof.Json where

import Control.Monad (foldM, unless, when)
import Data.Char (chr, digitToInt, isHexDigit, ord)
import qualified Data.Map.Strict as Map
import qualified Json.JsonAst as Parsed
import qualified Json.JsonParser as Parsed
import Numeric (showHex)
import System.IO (Handle, hGetChar, hIsEOF)
import Text.Read (readMaybe)

data Value
    = Object (Map.Map String Value)
    | Array [Value]
    | String String
    | Integer Integer
    | Boolean Bool
    | Null
    deriving (Eq, Show)

messageBytes :: Int
messageBytes = 1024 * 1024

-- The reader stops before allocating an unbounded line. An oversized frame
-- is fatal: draining a peer's never-ending line would itself be unbounded.
readFrame :: Handle -> IO (Either String (Maybe String))
readFrame handle = loop 0 [] where
    loop count reversed = do
        ended <- hIsEOF handle
        if ended then return (Right (if null reversed then Nothing else Just (reverse reversed))) else do
            character <- hGetChar handle
            let next = count + utf8Size character
            if character == '\n' then return (Right (Just (reverse reversed))) else
                if next > messageBytes then return (Left "The request exceeds the 1048576-byte limit.") else loop next (character : reversed)

utf8Size :: Char -> Int
utf8Size character
    | ord character < 0x80 = 1
    | ord character < 0x800 = 2
    | ord character < 0x10000 = 3
    | otherwise = 4

decode :: String -> Either String Value
decode source = do
    checked <- preflight source
    parsed <- Parsed.readjson checked
    convert parsed
    where
        convert value = case value of
            Parsed.ValueRep_object fields -> Object <$> foldM field Map.empty fields
            Parsed.ValueRep_array values -> Array <$> mapM convert values
            Parsed.ValueRep_string literal -> String <$> stringValue literal
            Parsed.ValueRep_number (Parsed.NumberRep_integer literal)
                | length literal > 20 -> Left "A protocol integer exceeds 20 characters."
                | otherwise -> case readMaybe literal of
                    Just number -> Right (Integer number)
                    Nothing -> Left "Invalid JSON integer."
            Parsed.ValueRep_number _ -> Left "Protocol numbers must be integers."
            Parsed.ValueRep_true -> Right (Boolean True)
            Parsed.ValueRep_false -> Right (Boolean False)
            Parsed.ValueRep_null -> Right Null
        field previous (literal, value) = do
            key <- stringValue literal
            when (Map.member key previous) (Left ("Duplicate JSON field: " ++ diagnosticName key))
            converted <- convert value
            return (Map.insert key converted previous)

-- Keep the generated JSON grammar unchanged. Bound its input and nesting,
-- reject raw string controls, and translate legal JSON whitespace it lacks.
preflight :: String -> Either String String
preflight source = scan 0 0 0 False False [] source where
    scan bytes depth tokens quoted escaped reversed remaining
        | bytes > messageBytes = Left "The request exceeds the 1048576-byte limit."
        | depth > 64 = Left "JSON nesting exceeds 64 levels."
        | tokens > 65536 = Left "JSON input exceeds 65536 delimiters."
        | otherwise = case remaining of
            []
                | quoted -> Left "Unterminated JSON string."
                | depth /= 0 -> Left "Unbalanced JSON delimiters."
                | otherwise -> Right (reverse reversed)
            character : more
                | not (scalar character) -> Left "A JSON string contains an invalid Unicode scalar value."
                | quoted && ord character < 0x20 -> Left "Unescaped control character in a JSON string."
                | quoted && escaped -> next depth tokens True False character
                | quoted && character == '\\' -> next depth tokens True True character
                | character == '"' -> next depth (tokens + 1) (not quoted) False character
                | quoted -> next depth tokens True False character
                | character `elem` "[{" -> next (depth + 1) (tokens + 1) False False character
                | character `elem` "]}" -> if depth <= 0 then Left "Unbalanced JSON delimiters." else next (depth - 1) (tokens + 1) False False character
                | character `elem` ",:" -> next depth (tokens + 1) False False character
                | character `elem` "\t\r" -> next depth tokens False False ' '
                | otherwise -> next depth tokens False False character
                where
                    next level count inside slash emitted = scan (bytes + utf8Size character) level count inside slash (emitted : reversed) more

scalar :: Char -> Bool
scalar character = ord character < 0xd800 || ord character > 0xdfff

stringValue :: String -> Either String String
stringValue ('"' : source) = loop [] source where
    loop reversed ['"'] = Right (reverse reversed)
    loop reversed ('\\' : escape : more) = case escape of
        '"' -> loop ('"' : reversed) more
        '\\' -> loop ('\\' : reversed) more
        '/' -> loop ('/' : reversed) more
        'b' -> loop ('\b' : reversed) more
        'f' -> loop ('\f' : reversed) more
        'n' -> loop ('\n' : reversed) more
        'r' -> loop ('\r' : reversed) more
        't' -> loop ('\t' : reversed) more
        'u' -> do
            (first, rest) <- hex4 more
            if first >= 0xd800 && first <= 0xdbff then case rest of
                '\\' : 'u' : suffix -> do
                    (second, tail) <- hex4 suffix
                    unless (second >= 0xdc00 && second <= 0xdfff) (Left "A high surrogate must be followed by a low surrogate.")
                    loop (chr (0x10000 + (first - 0xd800) * 1024 + second - 0xdc00) : reversed) tail
                _ -> Left "A high surrogate must be followed by a low surrogate."
            else if first >= 0xdc00 && first <= 0xdfff then Left "An isolated low surrogate is invalid." else loop (chr first : reversed) rest
        _ -> Left "Invalid JSON escape."
    loop reversed (character : more)
        | character /= '"' && ord character >= 0x20 && scalar character = loop (character : reversed) more
    loop _ _ = Left "Invalid JSON string."
    hex4 input = case splitAt 4 input of
        (digits, rest)
            | length digits == 4 && all isHexDigit digits -> Right (foldl (\value digit -> value * 16 + digitToInt digit) 0 digits, rest)
        _ -> Left "A Unicode escape requires four hexadecimal digits."
stringValue _ = Left "Expected a quoted JSON string."

encode :: Value -> Either String String
encode value = ($ "") <$> render value where
    render item = case item of
        Object fields -> do
            members <- mapM field (Map.toAscList fields)
            return (showChar '{' . separated members . showChar '}')
        Array values -> do
            members <- mapM render values
            return (showChar '[' . separated members . showChar ']')
        String text -> do
            unless (all scalar text) (Left "Cannot encode an invalid Unicode scalar value.")
            return (quoted text)
        Integer number -> Right (shows number)
        Boolean True -> Right (showString "true")
        Boolean False -> Right (showString "false")
        Null -> Right (showString "null")
    field (key, item) = do
        name <- render (String key)
        body <- render item
        return (name . showChar ':' . body)
    separated [] = id
    separated (first : rest) = first . foldr (\next tail -> showChar ',' . next . tail) id rest
    quoted text = showChar '"' . foldr (\character tail -> escape character . tail) id text . showChar '"'
    escape character = case character of
        '"' -> showString "\\\""
        '\\' -> showString "\\\\"
        '\n' -> showString "\\n"
        '\r' -> showString "\\r"
        '\t' -> showString "\\t"
        _
            | ord character < 0x20 -> showString "\\u" . showString (replicate (4 - length digits) '0') . showString digits
            | otherwise -> showChar character
            where
                digits = showHex (ord character) ""

object :: [(String, Value)] -> Value
object = Object . Map.fromList

-- Diagnostic excerpts are not identities: quote at most 64 scalars and mark
-- an omitted suffix explicitly. Looking at one tail constructor bounds the
-- work even when a decoded input name approaches the frame limit.
diagnosticName :: String -> String
diagnosticName value = show prefix ++ case remaining of
    [] -> ""
    _ : _ -> "..."
    where (prefix, remaining) = splitAt 64 value
