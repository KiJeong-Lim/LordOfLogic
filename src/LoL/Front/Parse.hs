module LoL.Front.Parse where

import Data.Bifunctor (first)
import qualified Data.Set as Set
import Data.List (foldl')
import LoL.Core (Global)
import qualified LoL.Front.Grammar as Grammar
import qualified LoL.Front.HostLexer as Host
import qualified LoL.Front.RocqNotation as RocqNotation
import qualified LoL.Front.Notation as Notation
import LoL.Front.Syntax

keywords :: [String]
keywords = Host.keywords

-- The longest source text that is read, in characters. It bounds the memory
-- that reading, lexing and parsing a text takes: raise it only with a cheaper
-- front end.
inputLimit :: Int
inputLimit = 524288

-- Both numbers of the result are evaluated: a scan of a long input that advances
-- with `$!` leaves no chain of pending additions behind.
advance :: Position -> Char -> Position
advance = Host.advance

lexSource :: String -> Either FrontError [Token]
lexSource = lexAt (1, 1)

lexAt :: Position -> String -> Either FrontError [Token]
lexAt origin source = branching <$> Host.lexHost origin source

-- The `with` of a match is followed by a branch or by `end`; any other `with`
-- continues a block of definitions. One token of lookahead cannot tell them
-- apart after a `fix`, so the two are distinct tokens for the parser.
branching :: [Token] -> [Token]
branching tokens = zipWith mark tokens (drop 1 (map tokenKind tokens) ++ [""]) where
    mark token next
        | tokenKind token == "with" && next `elem` ["|", "end"] = token { tokenKind = "with-match" }
        | otherwise = token

parseTerm :: String -> Either FrontError Term
parseTerm = parseTermWith []

parseTermWith :: [SyntaxRule Global] -> String -> Either FrontError Term
parseTermWith rules source = do
    parsed <- parsedAtWith rules (1, 1) source
    case parsed of
        Left term -> Right term
        Right _ -> Left (FrontError (Span (1, 1) (1, 1)) "LoL-ParseError" "P-Term" "Expected a term.")

parseSource :: String -> Either FrontError [Command]
parseSource = sequence . parseCommands

parseText :: String -> Either FrontError [Command]
parseText = parseSource

-- Each command starts at its original document position.
parseCommands :: String -> [Either FrontError Command]
parseCommands source = concatMap (either (pure . Left) (map Right) . parseChunkWith []) (commandChunks source)

parseChunkWith :: [SyntaxRule Global] -> (Position, String) -> Either FrontError [Command]
parseChunkWith = parseChunkIndexed . Notation.fromRules

parseChunkIndexed :: Notation.Rules -> (Position, String) -> Either FrontError [Command]
parseChunkIndexed rules (origin, text) = do
    parsed <- parsedAtIndexed rules origin text
    case parsed of
        Right commands -> Right commands
        Left value -> Left (FrontError (termSpan value) "LoL-ParseError" "P-Command" "Expected a command ending in a dot.")

parsedAt :: Position -> String -> Either FrontError (Either Term [Command])
parsedAt = parsedAtWith []

parsedAtWith :: [SyntaxRule Global] -> Position -> String -> Either FrontError (Either Term [Command])
parsedAtWith = parsedAtIndexed . Notation.fromRules

parsedAtIndexed :: Notation.Rules -> Position -> String -> Either FrontError (Either Term [Command])
parsedAtIndexed rules origin source = do
    tokens <- branching <$> Host.lexHostWith (Notation.termLiterals rules) origin source
    let end = foldl' advance origin source
    first (parseError (Span end end)) (readTokens rules tokens)

parseError :: Span -> Grammar.Problem -> FrontError
parseError end (Grammar.Unexpected unexpected) = FrontError location "LoL-ParseError" "P-Syntax" message where
    location = maybe end tokenSpan unexpected
    message = maybe "Unexpected end of input." unexpectedMessage unexpected
parseError _ (Grammar.Association token) = FrontError (tokenSpan token) "LoL-ScopeError" "H-Infix" "operators at this level require explicit parentheses"

unexpectedMessage :: Token -> String
unexpectedMessage token = "Unexpected token " ++ quoted (tokenText token) ++ "."

-- Only the first words of a declaration select attributes. An inner term
-- named Record still passes unchanged to the ordinary term grammar.
parseTokens :: [Token] -> Either (Maybe Token) (Either Term [Command])
parseTokens = parseTokensWith []

parseTokensWith :: [SyntaxRule Global] -> [Token] -> Either (Maybe Token) (Either Term [Command])
parseTokensWith = parseTokensIndexed . Notation.fromRules

parseTokensIndexed :: Notation.Rules -> [Token] -> Either (Maybe Token) (Either Term [Command])
parseTokensIndexed rules = first Grammar.problemToken . readTokens rules

readTokens :: Notation.Rules -> [Token] -> Either Grammar.Problem (Either Term [Command])
readTokens rules tokens
    | start : _ <- tokens, (loc, rest@(mark : _)) <- RocqNotation.splitLocal tokens, loc /= DefaultSyntax, tokenText mark == "Arguments" = do
        parsed <- readTokens rules rest
        case parsed of
            Right [CArguments pos name args opts] -> Right (Right [CSetArguments (tokenSpan start <> pos) loc name args opts])
            _ -> Left (Grammar.Unexpected (Just mark))
    | firstToken : _ <- tokens, tokenText firstToken `elem` ["Inductive","Fixpoint","Polymorphic","#["], tokenKind (last tokens) == "."
    , (prefix, clauses@(_:_)) <- splitWhere tokens = do
        parsed <- readTokens rules (prefix ++ [last tokens])
        case parsed of
            Right [base] -> do
                interpretations <- mapM (first Grammar.Unexpected . RocqNotation.declaration rules) clauses
                Right (Right [CWhere (tokenSpan firstToken <> tokenSpan (last tokens)) base interpretations])
            _ -> Left (Grammar.Unexpected (Just firstToken))
    | first : _ <- tokens, tokenKind first == "ident", tokenText first == "Search", tokenKind (last tokens) == "." = Right . pure <$> Grammar.searchCommand (termGrammar rules tokens) tokens
    | RocqNotation.handles rules tokens = first Grammar.Unexpected (Right . (: []) <$> RocqNotation.declaration rules tokens)
    | Notation.isDeclaration tokens, not (null tokens), tokenKind (last tokens) == "." = first Grammar.Unexpected (Right . (: []) <$> Notation.declaration tokens)
    | otherwise = ordinaryWith Grammar.Unexpected (Grammar.readRaw (termGrammar rules tokens)) tokens

-- A where/and clause begins with a quoted notation and :=. A variable
-- named where or and in a declaration is therefore not a clause delimiter.
splitWhere :: [Token] -> ([Token], [[Token]])
splitWhere input = case split "where" input of
    (pre, mark:rest) -> (pre, clauses mark rest)
    (_, []) -> (input, [])
    where
        split _ [] = ([],[])
        split word allTokens@(t:s:a:_) | tokenText t == word, tokenKind s == "string", tokenKind a == ":=" = ([],allTokens)
        split word (t:rest) = let (pre,post) = split word rest in (t:pre,post)
        clauses mark rest = case split "and" rest of
            (body,[]) -> [header mark : body]
            (body,next:tail') -> (header mark : body ++ [last input]) : clauses next tail'
        header t = t { tokenKind = "ident", tokenText = "Notation" }

termGrammar :: Notation.Rules -> [Token] -> Grammar.Grammar
termGrammar rules tokens
    | not (Set.null literals), any active tokens = Notation.indexedGrammar rules
    | otherwise = Grammar.fixed
    where
        literals = Notation.termLiterals rules
        active token = Notation.literalToken token && Set.member (tokenText token) literals

parseOrdinary :: ([Token] -> Either (Maybe Token) (Either Term [Command])) -> [Token] -> Either (Maybe Token) (Either Term [Command])
parseOrdinary = ordinaryWith id

sectionHead :: Token -> Bool
sectionHead token = tokenKind token == "ident" && tokenText token `elem` ["Section", "End", "Context", "Variable", "Variables", "Hypothesis", "Hypotheses"]

ordinaryWith :: (Maybe Token -> e) -> ([Token] -> Either e (Either Term [Command])) -> [Token] -> Either e (Either Term [Command])
ordinaryWith unexpected parseRaw tokens = case tokens of
    first : rest
        | sectionHead first, tokenKind (last tokens) == "." ->
            parseRaw (first { tokenKind = "section-command" } : rest)
    first : _
        | tokenKind first == "#[" -> attributes first False False tokens
    first : _
        | recordHead first, tokenKind (last tokens) == "." -> declaration first False False tokens
    first : ind : _
        | tokenKind first == "Polymorphic", recordHead ind -> declaration first False False tokens
        | tokenKind first == "Polymorphic", tokenKind ind == "Inductive" -> inductive first False True tokens ind (drop 2 tokens)
    ind : body
        | tokenKind ind == "Inductive" -> inductive ind False False tokens ind body
    _ -> parseRaw tokens
    where
        problem = Left . unexpected
        recordHead token = tokenKind token == "ident" && tokenText token == "Record"
        attributes start template primitive (open : rest)
            | tokenKind open == "#[" = attribute start template primitive rest
        attributes start template primitive rest = declaration start template primitive rest
        attribute start template primitive (key : lp : val : rp : delim : rest)
            | map tokenKind [key, lp, val, rp] == ["ident", "(", "ident", ")"] = do
                (nextTemplate, nextPrimitive) <- case (tokenText key, tokenText val) of
                    ("universes", "template")
                        | not template -> Right (True, primitive)
                    ("projections", "primitive")
                        | not primitive -> Right (template, True)
                    _ -> problem (Just key)
                case tokenKind delim of
                    "]" -> attributes start nextTemplate nextPrimitive rest
                    "," -> attribute start nextTemplate nextPrimitive rest
                    _ -> problem (Just delim)
        attribute _ _ _ (bad : _) = problem (Just bad)
        attribute _ _ _ [] = problem Nothing
        declaration start template primitive rest = case rest of
            poly : more
                | tokenKind poly == "Polymorphic" -> case more of
                    record : body
                        | not template && recordKind record -> fromRecord start template primitive True record body
                    _ -> problem (Just poly)
            record : body
                | recordKind record -> fromRecord start template primitive False record body
            ind : _
                | template && not primitive && tokenKind ind == "Inductive" -> inductive start template False rest ind (drop 1 rest)
            bad : _ -> problem (Just bad)
            [] -> problem Nothing
            where
                recordKind token = recordHead token || primitive && tokenKind token == "Inductive"
        inductive start template polymorphic allTokens ind body = case parseRaw input of
            Right (Right [command]) -> Right (Right [if template then CTemplate (tokenSpan start <> commandSpan command) command else command])
            Left failure -> case fromRecord start template False polymorphic ind body of
                Left _ -> Left failure
                accepted -> accepted
            other -> other
            where
                -- The polymorphic production already reads the
                -- optional universe binder. Keep its context under CTemplate.
                input = case body of
                    _ : levels : _
                        | template && tokenKind levels == "@{" -> ind { tokenKind = "Polymorphic", tokenText = "Polymorphic" } : allTokens
                    _ -> allTokens
        fromRecord start template primitive polymorphic record body = do
            let keyword = if primitive then "primitive-record" else tokenText record
            result <- parseRaw (record { tokenKind = "record-command", tokenText = keyword } : body)
            case result of
                Right [command] -> (Right . (: [])) <$> decorate command
                _ -> problem (Just record)
            where
                decorate (CRecordDefinitions at _ inner definitions) = (\base -> CRecordDefinitions at (recordHead record) base definitions) <$> decorate inner
                decorate (COrdinaryRecord _ _ CUniverses {})
                    | not polymorphic && not template, _ : levels : _ <- body = problem (Just levels)
                decorate (COrdinaryRecord original fields inner) = do
                    let at = tokenSpan start <> original
                        block = case inner of
                            CUniverses {} -> inner
                            _
                                | polymorphic -> CUniverses at Nothing inner
                            _ -> inner
                        decorated = if primitive then CPrimitive at (recordHead record) (map fst fields) block else COrdinaryRecord at fields block
                    Right (if template then CTemplate at decorated else decorated)
                decorate _ = problem (Just record)

data ChunkMode
    = Plain
    | Quoted
    | Comment
    deriving (Eq, Show)

-- A chunk is a prefix of the input from where the chunk begins. The scan counts
-- the characters of the chunk and holds no second copy of them.
commandChunks :: String -> [(Position, String)]
commandChunks source = scan (1, 1) (1, 1) Plain (0 :: Int) source source where
    scan start _ _ size begin [] = [(start, begin) | size > 0]
    scan start position Plain size begin ('(' : '*' : more) = step start (advance (advance position '(') '*') Comment (size + 2) begin more
    scan start position Comment size begin ('*' : ')' : more) = step start (advance (advance position '*') ')') Plain (size + 2) begin more
    scan start position Plain size begin ('.' : '.' : more) = step start (advance (advance position '.') '.') Plain (size + 2) begin more
    scan start position mode size begin (character : more)
        | mode == Plain && character == '.' && maybe True sourceSpace (first more) = (start, take (size + 1) begin) : step next next Plain 0 more more
        | otherwise = step start next following (size + 1) begin more
        where
            next = advance position character
            following
                | character == '"' && mode == Plain = Quoted
                | character == '"' && mode == Quoted = Plain
                | otherwise = mode
    step start position mode size = position `seq` size `seq` scan start position mode size
    first [] = Nothing
    first (value : _) = Just value
