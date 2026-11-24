module LoL.Front.Format (Doc, plain, output, application, patternSpacing, validate, formatted) where

import Control.Monad (guard)
import Data.Char (isSpace)
import Data.List (foldl')
import LoL.Front.Syntax (RulePart (..), ruleEntry)

data Mode = Flow | Vertical | HorizontalVertical deriving (Eq)
data Mark = Symbol String | Space Int | Open Mode Int | Close | Break Int Int | Newline deriving (Eq)
data Piece = Text String | Hint Int Int | Line | Box Mode Int !Int [Piece] | Applied Bool !Int [Piece]

-- Difference lists keep ordinary term assembly compositional while preserving
-- layout boxes until the surrounding declaration or term is complete.
type Doc = [Piece] -> [Piece]

plain :: String -> Doc
plain "" = id
plain s = (Text s :)

output :: Doc -> ShowS
output document = snd (render Flow False 0 0 (document []))

application :: Doc -> Doc -> Doc
application function argument = (Applied rich (width content) content :) where
    lhs = function []
    rhs = argument []
    rich = any structured lhs || any structured rhs
    structured Box {} = True
    structured (Applied yes _ _) = yes
    structured _ = False
    content = lhs ++ (if rich then Hint 1 0 else Text " ") : rhs

-- An extra space in the quoted production controls its unparser even when
-- there is no format modifier. Materialize those gaps in a format string so
-- the installed and serialized interpretation share the same layout.
patternSpacing :: [RulePart] -> [String] -> String -> Either String (Maybe String)
patternSpacing parts names source = do
    let fields = wordsWithGaps (dropWhile isSpace source)
        gaps = map (max 0 . subtract 1 . fst) fields
        agrees (index, sep) = let around i = take (sep + 1) (drop i gaps) in around (index + 1) == around (index + sep + 2)
    (_, ranges) <- maybe (Left "Invalid notation pattern variables.") Right (shape parts names)
    if all agrees ranges then Right (layout fields) else Left "Spaces differ on the two sides of a recursive notation."
    where
        layout [] = Nothing
        layout (first : rest) = do
            guard (any ((> 1) . fst) rest)
            let text = literal (snd first) ++ fill (snd first) rest
            case validate parts names text of
                Right () -> Just text
                Left _ -> Nothing
        wordsWithGaps [] = []
        wordsWithGaps input = (0,word) : more rest where
            (word,rest) = break isSpace input
        more input = case span isSpace input of
            (_,[]) -> []
            (gap,rest) -> (length gap,word) : more after where
                (word,after) = break isSpace rest
        literal s = case s of
            '\'' : rest | not (null rest) && last rest == '\'' -> init rest
            _ -> s
        fill _ [] = ""
        fill previous ((count,current):xs) = replicate (gap + 1) ' ' ++ "'/' " ++ literal current ++ fill current xs where
            a = literal previous
            b = literal current
            gap
                | count > 1 = count - 1
                | (a,b) `elem` [("(",")"),("[","]"),("{","}")] = 1
                | a `elem` ["(","[","{"] || b `elem` [")","]","}",",",";"] = 0
                | otherwise = 1

-- The first space separates format tokens. Extra spaces print literally,
-- or provide the flat width of a break. Spaces inside a directive indent.
marks :: String -> Maybe [Mark]
marks = scan 0 where
    scan _ [] = Just []
    scan skip input = do
        let (padding, rest) = span (== ' ') input
            width = max 0 (length padding - skip)
            spaces xs = if width == 0 then xs else Space width : xs
        case rest of
            [] -> Just (spaces [])
            '\'' : c : cs | c /= ' ' -> do
                (word, more) <- quoted [] (c : cs)
                item <- directive width word
                let emit = case item of
                        Break {} -> id
                        Newline -> id
                        _ -> spaces
                emit . (item :) <$> scan 1 more
            _ -> do
                let (word, more) = break (== ' ') rest
                spaces . (Symbol word :) <$> scan 1 more
    quoted acc ('\'' : rest) | null rest || head rest == ' ' = Just (reverse acc, rest)
    quoted acc (c : cs) = quoted (c : acc) cs
    quoted _ [] = Nothing
    directive width word = case word of
        "]" -> Just Close
        "//" -> Just Newline
        '/' : suffix | blanks suffix -> Just (Break width (length suffix))
        '[' : 'h' : 'v' : suffix | blanks suffix -> Just (Open HorizontalVertical (length suffix))
        '[' : 'v' : suffix | blanks suffix -> Just (Open Vertical (length suffix))
        '[' : suffix | blanks suffix -> Just (Open Flow (length suffix))
        first : _ | first `elem` "[/" -> Nothing
        _ | not (null word) && all (/= ' ') word -> Just (Symbol word)
        _ -> Nothing
    blanks = all (== ' ')

-- Remember where the recursive range starts. Its two copies of the
-- separator must describe the same layout as well as the same symbols.
shape :: [RulePart] -> [String] -> Maybe ([String], [(Int, Int)])
shape marked = walk 0 (snd (ruleEntry marked)) where
    walk _ [] [] = Just ([], [])
    walk i (Literal w : ps) ns = prefix i [w] ps ns
    walk i (RepeatSlot sep _ : ps) (x : y : ns) = do
        let separator = words sep
            range = [x] ++ separator ++ [".."] ++ separator ++ [y]
        (tailWords, ranges) <- walk (i + length range) ps ns
        Just (range ++ tailWords, (i, length separator) : ranges)
    walk i (_ : ps) (x : ns) = prefix i [x] ps ns
    walk _ _ _ = Nothing
    prefix i ws ps ns = do
        (more, range) <- walk (i + length ws) ps ns
        Just (ws ++ more, range)

atSymbol :: Int -> [Mark] -> Maybe ([Mark], String, [Mark])
atSymbol 0 (Symbol w : more) = Just ([], w, more)
atSymbol n (m : more) = do
    let step = case m of { Symbol _ -> 1; _ -> 0 }
    (before, w, after) <- atSymbol (n - step) more
    Just (m : before, w, after)
atSymbol _ [] = Nothing

-- Read the actual cardinalities from the matched RHS. Two adjacent ranges
-- may have equally spelled separators and different lengths.
expand :: [(Int, Int)] -> [Int] -> [Mark] -> Maybe [Mark]
expand ranges sizes = walk 0 ranges sizes where
    walk _ [] [] xs = Just xs
    walk consumed ((index, sep) : more) (count : rest) xs = do
        guard (count > 0)
        (prefix, x, afterX) <- atSymbol (index - consumed) xs
        (left, dots, afterDots) <- atSymbol sep afterX
        (right, _, suffix) <- atSymbol sep afterDots
        guard (dots == ".." && left == right)
        tailMarks <- walk (index + 3 + 2 * sep) more rest suffix
        Just (prefix ++ Symbol x : concat (replicate (count - 1) (left ++ [Symbol x])) ++ tailMarks)
    walk _ _ _ _ = Nothing

pieces :: [Mark] -> [Doc] -> Maybe [Piece]
pieces xs values = do
    (result, [], []) <- group False xs values
    Just result
    where
        group True (Close : more) vs = Just ([],more,vs)
        group True [] _ = Nothing
        group False [] vs = Just ([],[],vs)
        group _ (Close : _) _ = Nothing
        group inner (mark : more) vs = do
            (piece, rest, tailValues) <- case mark of
                Symbol _ | v : tail' <- vs -> Just (v,more,tail')
                Open mode indent -> do
                    (content, after, tail') <- group True more vs
                    Just ((Box mode indent (width content) content :),after,tail')
                Space n -> Just (plain (replicate n ' '),more,vs)
                Break n indent -> Just ((Hint n indent :),more,vs)
                Newline -> Just ((Line :),more,vs)
                _ -> Nothing
            (siblings, end, final) <- group inner rest tailValues
            Just (piece siblings,end,final)

prepare :: [RulePart] -> [String] -> String -> Maybe ([Mark], [(Int, Int)])
prepare parts names fmt = do
    (expected, range) <- shape parts names
    xs <- marks fmt
    guard ([w | Symbol w <- xs] == expected)
    Just (xs, range)

validate :: [RulePart] -> [String] -> String -> Either String ()
validate parts names fmt = maybe (Left "The format does not match the notation or has unbalanced boxes.") (const (Right ())) checkedFormat where
    checkedFormat = do
        (xs, ranges) <- prepare parts names fmt
        expanded <- expand ranges (map (const 1) ranges) xs
        pieces expanded [id | Symbol _ <- expanded]

formatted :: [RulePart] -> [String] -> [Int] -> String -> [(String, Doc)] -> Maybe Doc
formatted parts names sizes fmt written = do
    (xs, ranges) <- prepare parts names fmt
    expanded <- expand ranges sizes xs
    tree <- pieces expanded (map snd written)
    Just (Box Flow 0 (width tree) tree :)

-- Rocq 9.2 starts at a printing width of 78. A horizontal/vertical box
-- chooses once. A flowing box chooses at each hint before the next chunk.
margin :: Int
margin = 78

flat :: Piece -> Int
flat (Text s) = if '\n' `elem` take (margin + 1) s then margin + 1 else length (take (margin + 1) s)
flat (Hint n _) = n
flat Line = margin + 1
flat (Box _ _ size _) = size
flat (Applied _ size _) = size

width :: [Piece] -> Int
width = measure 0 where
    measure n _ | n > margin = margin + 1
    measure n [] = n
    measure n (p : ps) = measure (n + flat p) ps

render :: Mode -> Bool -> Int -> Int -> [Piece] -> (Int, ShowS)
render _ _ _ col [] = (col, id)
render mode broken base col (p : rest) = (final, output . following) where
    (next, output) = case p of
        Text s -> (foldl' advance col s, showString s)
            where
                advance _ '\n' = 0
                advance n _ = n + 1
        Hint n indent
            | broken || mode == Flow && col + n + width (takeWhile inline rest) >= margin -> line (base + indent)
            | otherwise -> (col + n, showString (replicate n ' '))
        Line -> line base
        Applied True _ children -> render Flow False (col + 2) col children
        Applied False _ children -> render mode broken base col children
        Box inner indent size children -> render inner (inner == Vertical || inner == HorizontalVertical && col + size >= margin) (col + indent) col children
    (final, following) = render mode broken base next rest
    inline Hint {} = False
    inline Line = False
    inline _ = True
    line indent = (indent, showChar '\n' . showString (replicate indent ' '))
