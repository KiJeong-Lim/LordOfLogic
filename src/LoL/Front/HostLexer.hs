module LoL.Front.HostLexer where

import Data.Char (GeneralCategory (..), generalCategory, isLetter)
import Data.List (foldl', isPrefixOf, sortOn)
import qualified Data.Map.Strict as Map
import Data.Ord (Down (..))
import qualified Data.Set as Set
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
identStart c = c == '_' || isLetter c

identContinue :: Char -> Bool
identContinue c = identStart c || digit c || c == '\'' || c > '\x7f' && c `notElem` "⁰¹²³⁴⁵⁶⁷⁸⁹" && generalCategory c `elem` [DecimalNumber, LetterNumber, OtherNumber, NonSpacingMark]

symbol :: Char -> Bool
symbol c = c `elem` "!#$%&*+-/<=>?^~\\|:" || c > '\x7f' && generalCategory c == MathSymbol

-- Scan directly at the caller's origin. End positions are inclusive.
lexHost :: Position -> String -> Either FrontError [Token]
lexHost = lexHostWith Set.empty

-- Grammar terminals are lexical keywords. Read the longest contiguous
-- terminal before the fixed punctuation scanner, without matching through
-- spaces, comments, identifiers, strings or command boundaries.
lexHostWith :: Set.Set String -> Position -> String -> Either FrontError [Token]
lexHostWith literals = scan [] where
    byInitial = Map.map (sortOn (Down . length)) (Map.fromListWith (++) [(head word,[word]) | word <- Set.toList literals, not (null word), not (identStart (head word)), not (digit (head word))])
    terminal input@(c:_) = case Map.lookup c byInitial of
        Just options -> case filter (\w -> w `isPrefixOf` input && not (any (longer w) fixedWords)) options of
            w : _ -> Just w
            _ -> Nothing
        Nothing -> Nothing
        where
            longer w other = length other > length w && other `isPrefixOf` input
    terminal [] = Nothing
    fixedWords = ["#[", ".(", "@{", "..", ":=", "=>", "->"]

    scan acc _ [] = Right (reverse acc)
    scan acc start ('(' : '*' : more) = comment start acc (advance (advance start '(') '*') more
    scan acc start input@('"' : more) = case break (== '"') more of
        (_, []) -> failure start "L-String" "Unterminated String."
        (value, _ : rest) -> emit acc start "string" value (take (2 + length value) input) rest
    scan acc start input@(first : more)
        | sourceSpace first = (scan acc $! advance start first) more
        | identStart first = qualified acc start [] input
        | digit first = let (value, rest) = span digit input in emit acc start "numeral" value value rest
        | Just word <- terminal input =
            let kind = if word `elem` fixedWords || word `elem` map pure "[];(){},.@:|" then word else "operator"
            in emit acc start kind word word (drop (length word) input)
        | take 2 input `elem` ["#[", ".(", "@{", ".."] = fixed (take 2 input) (drop 2 input)
        | symbol first = case span symbol input of
            (value, rest)
                | value == "%" -> emit acc start "scope-delimiter" value value rest
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
