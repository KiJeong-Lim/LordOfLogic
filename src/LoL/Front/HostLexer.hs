module LoL.Front.HostLexer where

import Data.Char (GeneralCategory (MathSymbol), generalCategory, isAsciiLower, isAsciiUpper)
import Data.List (foldl')
import LoL.Front.Syntax

keywords :: [String]
keywords = words "Arguments Axiom Check Compute Definition Fixpoint Import Inductive Infix Lemma Numerals Polymorphic Print Prop Set Theorem Type as end fix for forall fun in let match return struct with"

contextWords :: [String]
contextWords = words "Assumptions associativity at left level no right"

advance :: Position -> Char -> Position
advance (row, col) character
    | character == '\n' = strict (row + 1) 1
    | otherwise = strict row (col + 1)
    where
        strict line column = line `seq` column `seq` (line, column)

digit :: Char -> Bool
digit c = '0' <= c && c <= '9'

identStart :: Char -> Bool
identStart c = isAsciiLower c || isAsciiUpper c || c == '_'

identContinue :: Char -> Bool
identContinue c = identStart c || digit c || c == '\''

symbol :: Char -> Bool
symbol c = c `elem` "!#$%&*+-/<=>?^~\\|:" || c > '\x7f' && generalCategory c == MathSymbol

-- Scan directly at the caller's origin. End positions are inclusive.
lexHost :: Position -> String -> Either FrontError [Token]
lexHost = scan [] where
    scan acc _ [] = Right (reverse acc)
    scan acc start ('(' : '*' : more) = comment start acc (advance (advance start '(') '*') more
    scan acc start input@('"' : more) = case break (== '"') more of
        (_, []) -> failure start "L-String" "Unterminated String."
        (value, _ : rest) -> emit acc start "string" value (take (2 + length value) input) rest
    scan acc start input@(first : more)
        | sourceSpace first = (scan acc $! advance start first) more
        | identStart first = qualified acc start [] input
        | digit first = let (value, rest) = span digit input in emit acc start "numeral" value value rest
        | take 2 input `elem` ["#[", ".(", "@{"] = fixed (take 2 input) (drop 2 input)
        | symbol first = case span symbol input of
            (value, rest)
                | value `elem` [":", "|", ":=", "=>", "->"] -> fixed value rest
                | otherwise -> emit acc start "operator" value value rest
        | first == '.', next : _ <- more, not (sourceSpace next) = failure start "L-Dot" "A command-ending dot must be followed by whitespace or end of input."
        | first `elem` "[];(){},.@" = fixed [first] more
        | otherwise = failure start "L-Character" "Unrecognized character."
        where
            fixed value = emit acc start value value value
    qualified acc start previous input = case span identContinue input of
        (name, '.' : rest@(first : _))
            | identStart first -> qualified acc start (name : previous) rest
        (name, rest) -> case previous of
            []
                | name == "_" || name `elem` keywords || name `elem` contextWords -> emit acc start name name name rest
                | otherwise -> emit acc start "ident" name name rest
            _
                | any (\part -> part == "_" || part `elem` keywords) parts -> failure start "L-Qualified" "Every qualified-name component must be an identifier."
                | otherwise -> emit acc start "qualid" full full rest
                where
                    parts = reverse (name : previous)
                    full = foldr1 (\a b -> a ++ '.' : b) parts
    comment start _ _ [] = failure start "L-Comment" "Unterminated Comment."
    comment _ acc position ('*' : ')' : more) = (scan acc $! advance (advance position '*') ')') more
    comment start acc position (c : more) = (comment start acc $! advance position c) more
    emit acc start kind value consumed rest = case foldl' step (start, start) consumed of
        (end, next) -> scan (Token (Span start end) kind value : acc) next rest
    step (_, current) c = let next = advance current c in next `seq` (current, next)
    failure position code message = Left (FrontError (Span position position) "LoL-LexError" code message)
