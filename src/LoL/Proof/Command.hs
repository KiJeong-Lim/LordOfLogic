-- Surface tactics build the existing proof commands. Terms and declarations
-- always use the same host grammar and document-local notation environment.
module LoL.Proof.Command where

import Control.Monad (unless)
import Data.Array ((!), accumArray, listArray)
import qualified Data.Set as Set
import qualified LoL.Front.Grammar as Grammar
import qualified LoL.Front.Parse as Parse
import LoL.Core (Global)
import qualified LoL.Front.Notation as Notation
import qualified LoL.Front.Syntax as Front

type Span = Front.Span

data Command
    = Ordinary Front.Command
    | TheoremHeader Span Front.Command
    | ProofStart Span
    | ShowProof Span
    | ShowUniverses Span
    | UndoProof Span
    | AbortProof Span
    | QedProof Span
    | RunTactic Span Tactic
    | LoadTactics Span FilePath
    deriving (Eq, Show)

data Tactic
    = Primitive Span Primitive
    | Then Span Tactic Tactic
    | Try Span Tactic
    | Repeat Span Tactic
    | First Span [Tactic]
    | All Span Tactic
    | Bullet Span Char Int Tactic
    deriving (Eq, Show)

data Target
    = GoalTarget
    | HypothesisTarget Front.Name
    deriving (Eq, Show)

data Direction
    = Forward
    | Backward
    deriving (Eq, Show)

data Primitive
    = RefineProof Front.Term
    | ExactProof Front.Term
    | IntroProof [Front.Name]
    | IntrosProof [Front.Name]
    | ApplyProof Front.Term
    | AssumptionProof
    | ReflexivityProof
    | SymmetryProof
    | TransitivityProof Front.Term
    | ExistsProof [Front.Term]
    | SplitProof
    | LeftProof
    | RightProof
    | ConstructorProof (Maybe Integer)
    | ExfalsoProof
    | DestructProof Front.Term [Front.Name]
    | InductionProof Front.Term [Front.Name]
    | RewriteProof Direction Front.Term Target
    | UnfoldProof [Front.Name] Target
    | SimplProof Target
    | SimplAtProof Front.Name Bool [Integer] Target
    | ChangeProof Front.Term Target
    | DiscriminateProof (Maybe Front.Term) Target
    | InjectionProof Front.Term Target
    | AssertProof Front.Name Front.Term
    | SpecializeProof Front.Term
    | UserProof Front.Name [Front.Term]
    deriving (Eq, Show)

commandSpan :: Command -> Span
commandSpan command = case command of
    Ordinary ordinary -> Front.commandSpan ordinary
    TheoremHeader location _ -> location
    ProofStart location -> location
    ShowProof location -> location
    ShowUniverses location -> location
    UndoProof location -> location
    AbortProof location -> location
    QedProof location -> location
    RunTactic location _ -> location
    LoadTactics location _ -> location

tacticSpan :: Tactic -> Span
tacticSpan tactic = case tactic of
    Primitive location _ -> location
    Then location _ _ -> location
    Try location _ -> location
    Repeat location _ -> location
    First location _ -> location
    All location _ -> location
    Bullet location _ _ _ -> location

parseSource :: String -> Either Front.FrontError [Command]
parseSource = sequence . parseCommands

parseCommands :: String -> [Either Front.FrontError Command]
parseCommands source = concatMap one (Parse.commandChunks source) where
    one (origin, text) = case parseCommandAt origin text of
        Left failure -> [Left failure]
        Right Nothing -> []
        Right (Just command) -> [Right command]

parseCommandAt :: Front.Position -> String -> Either Front.FrontError (Maybe Command)
parseCommandAt = parseCommandAtWith []

type Rules = [Front.SyntaxRule Global]

parseCommandAtWith :: Rules -> Front.Position -> String -> Either Front.FrontError (Maybe Command)
parseCommandAtWith = parseCommandAtIndexed . Notation.fromRules

parseCommandAtIndexed :: Notation.Rules -> Front.Position -> String -> Either Front.FrontError (Maybe Command)
parseCommandAtIndexed rules origin source = do
    tokens <- proofTokens origin source
    case tokens of
        [] -> Right Nothing
        _ -> do
            unless (Front.tokenKind (last tokens) == ".") $ case tokens of
                first : _
                    | Front.tokenKind first `elem` Parse.keywords || Notation.isDeclaration tokens -> case Parse.parsedAtIndexed rules origin source of
                        Left problem -> Left problem
                        _ -> failure (tokensSpan tokens) "P-Syntax" "Expected a command ending in a dot."
                _ -> failure (tokensSpan tokens) "P-ProofDot" "Expected a command ending in a dot."
            command <- commandTokensIndexed rules tokens
            return (Just command)

commandTokens :: [Front.Token] -> Either Front.FrontError Command
commandTokens = commandTokensIndexed Notation.emptyRules

commandTokensWith :: Rules -> [Front.Token] -> Either Front.FrontError Command
commandTokensWith = commandTokensIndexed . Notation.fromRules

commandTokensIndexed :: Notation.Rules -> [Front.Token] -> Either Front.FrontError Command
commandTokensIndexed rules tokens
    = case tokens of
        first : _
            | text first `elem` ["Theorem", "Lemma"] -> headerOrOrdinary
            | text first == "Polymorphic", second : _ <- drop 1 tokens, text second `elem` ["Theorem", "Lemma"] -> headerOrOrdinary
            | Front.tokenKind first `elem` Parse.keywords || Front.tokenKind first == "#[" || text first == "Record" || Notation.isDeclaration tokens -> ordinary
        _ -> proof
    where
        location = tokensSpan tokens
        body = init tokens
        ordinary = Ordinary <$> ordinaryTokensIndexed rules tokens
        headerOrOrdinary = case ordinaryTokensIndexed rules tokens of
            Right command -> Right (Ordinary command)
            Left original -> case reverse tokens of
                dot : before -> case Parse.readTokens rules (reverse before ++ [synthetic dot ":=", synthetic dot "_", dot]) of
                    Right (Right [header])
                        | theoremHeader header -> Right (TheoremHeader location header)
                    _ -> Left original
                [] -> ordinary
        keyword label token = Front.tokenKind token == "ident" && text token == label
        synthetic dot kind = Front.Token (Front.tokenSpan dot) kind kind
        theoremHeader (Front.CDefinition _ kind _ _ _ _) = kind `elem` ["Theorem", "Lemma"]
        theoremHeader (Front.CUniverses _ _ inner) = theoremHeader inner
        theoremHeader _ = False
        proof = case body of
            [word]
                | keyword "Proof" word -> Right (ProofStart location)
                | keyword "Show" word -> Right (ShowProof location)
                | keyword "Undo" word -> Right (UndoProof location)
                | keyword "Abort" word -> Right (AbortProof location)
                | keyword "Qed" word -> Right (QedProof location)
            [show, universes]
                | keyword "Show" show && keyword "Universes" universes -> Right (ShowUniverses location)
            [load, tactics, path]
                | keyword "Load" load && keyword "Tactics" tactics && Front.tokenKind path == "string" -> Right (LoadTactics location (text path))
            _ -> RunTactic location <$> parseTacticEnding rules (Front.tokenSpan (last tokens)) body

ordinaryTokens :: [Front.Token] -> Either Front.FrontError Front.Command
ordinaryTokens = ordinaryTokensIndexed Notation.emptyRules

ordinaryTokensWith :: Rules -> [Front.Token] -> Either Front.FrontError Front.Command
ordinaryTokensWith = ordinaryTokensIndexed . Notation.fromRules

ordinaryTokensIndexed :: Notation.Rules -> [Front.Token] -> Either Front.FrontError Front.Command
ordinaryTokensIndexed rules tokens = case Parse.readTokens rules tokens of
    Right (Right [command]) -> Right command
    Right _ -> failure (tokensSpan tokens) "P-Command" "Expected exactly one declaration or command."
    Left problem -> Left (Parse.parseError (tokensSpan tokens) problem)

termTokens :: [Front.Token] -> Either Front.FrontError Front.Term
termTokens = termTokensIndexed Notation.emptyRules

termTokensWith :: Rules -> [Front.Token] -> Either Front.FrontError Front.Term
termTokensWith = termTokensIndexed . Notation.fromRules

termTokensIndexed :: Notation.Rules -> [Front.Token] -> Either Front.FrontError Front.Term
termTokensIndexed _ [] = failure (Front.Span (1, 1) (1, 1)) "P-ProofTerm" "Expected a term."
termTokensIndexed rules tokens = case Parse.readTokens rules (Parse.branching tokens) of
    Right (Left term) -> Right term
    Right _ -> failure (tokensSpan tokens) "P-ProofTerm" "Expected a term."
    Left problem -> Left (Parse.parseError (tokensSpan tokens) problem)

unexpectedToken :: [Front.Token] -> Maybe Front.Token -> Either Front.FrontError a
unexpectedToken tokens unexpected = failure location "P-Syntax" message where
    location = maybe (tokensSpan tokens) Front.tokenSpan unexpected
    message = maybe "Unexpected end of input." Parse.unexpectedMessage unexpected

failure :: Span -> String -> String -> Either Front.FrontError a
failure location code message = Left (Front.FrontError location "LoL-ParseError" code message)

text :: Front.Token -> String
text = Front.tokenText

tokensSpan :: [Front.Token] -> Span
tokensSpan [] = Front.Span (1, 1) (1, 1)
tokensSpan tokens = Front.tokenSpan (head tokens) <> Front.tokenSpan (last tokens)

proofTokens :: Front.Position -> String -> Either Front.FrontError [Front.Token]
proofTokens = Parse.lexAt

parseTactic :: [Front.Token] -> Either Front.FrontError Tactic
parseTactic = parseTacticIndexed Notation.emptyRules

parseTacticWith :: Rules -> [Front.Token] -> Either Front.FrontError Tactic
parseTacticWith = parseTacticIndexed . Notation.fromRules

parseTacticIndexed :: Notation.Rules -> [Front.Token] -> Either Front.FrontError Tactic
parseTacticIndexed rules tokens = parseTacticEnding rules (tokensSpan (take 1 (reverse tokens))) tokens

parseTacticEnding :: Notation.Rules -> Span -> [Front.Token] -> Either Front.FrontError Tactic
parseTacticEnding = indexedTactic Nothing

-- Registered sub-tactics parse a range of the same command. Parentheses,
-- separators and the token array are indexed once for the whole command.
indexedTactic :: Maybe (Span, Front.SyntaxRule Global) -> Notation.Rules -> Span -> [Front.Token] -> Either Front.FrontError Tactic
indexedTactic entry rules boundary tokens = checked where
    checked = case filter ((== "string") . Front.tokenKind) tokens of
        token : _ -> unexpectedToken tokens (Just token)
        [] -> case entry of
            Just (location, rule) -> registered location rule 0 count
            Nothing -> parse 0 count
    tacticRules = Notation.tacticRules rules
    count = length tokens
    items = listArray (0, count - 1) (Parse.branching tokens)
    matches = accumArray (\_ replacement -> replacement) count (0, count) (pair [] (zip [0 ..] tokens))
    pair _ [] = []
    pair stack ((index, token) : rest)
        | kind `elem` ["(", ".(", "{", "@{", "[", "match", "let"] = pair ((close kind, index) : stack) rest
        | (expected, opening) : more <- stack, kind == expected = (opening, index) : pair more rest
        | otherwise = pair stack rest
        where kind = Front.tokenKind token
    close "(" = ")"
    close ".(" = ")"
    close "[" = "]"
    close "match" = "end"
    close "let" = "in"
    close _ = "}"
    slice start end = [items ! index | index <- [start .. end - 1]]
    atEnd end = if end < count then Front.tokenSpan (items ! end) else boundary
    separators delimiter = table where
        table = listArray (0, count) [next index | index <- [0 .. count]]
        next index
            | index == count = count
            | matches ! index < count = table ! (matches ! index + 1)
            | text (items ! index) == delimiter = index
            | otherwise = table ! (index + 1)
    semicolons = separators ";"
    bars = separators "|"
    parse start end
        | start >= end = failure location "P-Tactic" "Expected a tactic."
        | Just (marker, depth) <- Notation.bulletMark (text first) = Bullet location marker depth <$> parse (start + 1) end
        | text first == "all", start + 1 < end, text (items ! (start + 1)) == ":" = All location <$> parse (start + 2) end
        | separator <- semicolons ! start, separator < end = Then location <$> parse start separator <*> parse (separator + 1) end
        | text first == "(", matches ! start == end - 1 = parse (start + 1) (end - 1)
        | text first == "try" = Try location <$> parse (start + 1) end
        | text first == "repeat" = Repeat location <$> parse (start + 1) end
        | text first == "first" = if start + 2 < end && text (items ! (start + 1)) == "[" && matches ! (start + 1) == end - 1
            then First location <$> alternatives (start + 2) (end - 1)
            else failure location "P-First" "Expected first [tactic | tactic ...]."
        | Just rule <- Notation.select tacticRules (slice start end) = registered location rule start end
        | otherwise = Primitive location <$> primitiveTokensIndexed rules first (slice (start + 1) end)
        where
            first = items ! start
            location = if start < end then Front.tokenSpan first <> Front.tokenSpan (items ! (end - 1)) else boundaryAtEnd
            boundaryAtEnd = atEnd end
    alternatives start end
        | separator <- bars ! start, separator < end = (:) <$> parse start separator <*> alternatives (separator + 1) end
        | otherwise = (: []) <$> parse start end

    registered location (Front.SyntaxRule parts _ _ (Front.TacticTarget target)) start end = consume parts start (slice start end) >>= buildTactic location target where
        malformed = failure location "P-Notation" "The tactic does not match the registered syntax."
        consume [] _ [] = Right []
        consume (Front.Literal literal : more) index (token : rest)
            | Notation.matchesLiteral literal token = consume more (index + 1) rest
        consume (Front.NameSlot : more) index (token : rest) = do
            name <- binderName rules token
            (NameArgument name :) <$> consume more (index + 1) rest
        consume (Front.TermSlot : more) _ input = case input of
            [] -> failure (atEnd end) "P-ProofTerm" "Expected a term."
            token : _ -> case more of
                [] -> (: []) . TermArgument <$> termTokensIndexed rules input
                Front.Literal delimiter : _
                    | Notation.matchesLiteral delimiter token -> failure (Front.tokenSpan token) "P-ProofTerm" "Expected a term."
                    | otherwise -> case Grammar.runParser Grammar.term (Notation.delimitedGrammar [delimiter] rules) input of
                        Left issue -> Left (Parse.parseError (atEnd end) issue)
                        Right (value, rest) -> (TermArgument value :) <$> consume more (end - length rest) rest
                _ -> malformed
        consume (Front.TacticSlot : more) index _ = do
            stop <- case more of
                [] -> Right end
                Front.Literal delimiter : _ -> untilLiteral delimiter index
                _ -> malformed
            child <- parse index stop
            (NestedArgument child :) <$> consume more stop (slice stop end)
        consume _ _ _ = malformed
        untilLiteral delimiter index
            | index >= end = malformed
            | Notation.matchesLiteral delimiter (items ! index) = Right index
            | closing <- matches ! index, closing < end = untilLiteral delimiter (closing + 1)
            | otherwise = untilLiteral delimiter (index + 1)
    registered location _ _ _ = failure location "P-Notation" "Expected a tactic notation."

-- The delimiter stack protects term parentheses, universe braces, first
-- alternatives, match branches, and let binders from tactical separators.
splitTop :: String -> [Front.Token] -> Maybe ([Front.Token], [Front.Token])
splitTop delimiter = walk [] [] where
    walk _ _ [] = Nothing
    walk stack reversed (token : rest)
        | null stack && text token == delimiter = Just (reverse reversed, rest)
        | otherwise = walk (nest stack token) (token : reversed) rest

splitEvery :: String -> [Front.Token] -> [[Front.Token]]
splitEvery delimiter tokens = case splitTop delimiter tokens of
    Nothing -> [tokens]
    Just (before, after) -> before : splitEvery delimiter after

nest :: [String] -> Front.Token -> [String]
nest stack token
    | kind `elem` ["(", ".(", "{", "@{", "[", "match", "let"] = closing kind : stack
    | expected : more <- stack, kind == expected = more
    | otherwise = stack
    where
        kind = Front.tokenKind token
        closing "(" = ")"
        closing ".(" = ")"
        closing "[" = "]"
        closing "match" = "end"
        closing "let" = "in"
        closing _ = "}"

enclosed :: String -> String -> [Front.Token] -> Maybe [Front.Token]
enclosed opening closing tokens = case tokens of
    first : rest
        | text first == opening -> finish [closing] [] rest
    _ -> Nothing
    where
        finish _ _ [] = Nothing
        finish stack reversed (token : more)
            | [expected] <- stack, text token == expected = if null more then Just (reverse reversed) else Nothing
            | otherwise = finish (nest stack token) (token : reversed) more

primitiveTokens :: Front.Token -> [Front.Token] -> Either Front.FrontError Primitive
primitiveTokens = primitiveTokensIndexed Notation.emptyRules

primitiveTokensWith :: Rules -> Front.Token -> [Front.Token] -> Either Front.FrontError Primitive
primitiveTokensWith = primitiveTokensIndexed . Notation.fromRules

primitiveTokensIndexed :: Notation.Rules -> Front.Token -> [Front.Token] -> Either Front.FrontError Primitive
primitiveTokensIndexed rules first tokens
    = case text first of
        "refine" -> RefineProof <$> term
        "exact" -> ExactProof <$> term
        "intro" -> do
            names <- binderNames rules tokens
            unless (length names <= 1) (failure location "P-Intro" "Use intros for more than one name.")
            unless (all ((/= "_") . Front.nameText) names) (failure location "P-Intro" "Use intros _ to discard a hypothesis.")
            return (IntroProof names)
        "intros" -> IntrosProof <$> binderNames rules tokens
        "apply" -> ApplyProof <$> term
        "assumption" -> noArguments AssumptionProof
        "reflexivity" -> noArguments ReflexivityProof
        "symmetry" -> noArguments SymmetryProof
        "transitivity" -> TransitivityProof <$> term
        "exists"
            | null tokens -> ExistsProof . (: []) <$> term
            | otherwise -> ExistsProof <$> termsTokensIndexed rules tokens
        "split" -> noArguments SplitProof
        "left" -> noArguments LeftProof
        "right" -> noArguments RightProof
        "constructor" -> case tokens of
            [] -> Right (ConstructorProof Nothing)
            [number]
                | Front.tokenKind number == "numeral", value <- read (text number), value > 0 -> Right (ConstructorProof (Just value))
            _ -> failure location "P-Constructor" "A constructor index must be a positive integer."
        "exfalso" -> noArguments ExfalsoProof
        "destruct" -> destruct DestructProof
        "induction" -> destruct InductionProof
        "rewrite" -> do
            let (direction, body) = case tokens of
                    arrow : more
                        | text arrow == "<-" -> (Backward, more)
                    _ -> (Forward, tokens)
            (value, target) <- termTargetIndexed rules body
            return (RewriteProof direction value target)
        "unfold" -> do
            (body, target) <- targetTokens tokens
            names <- concat <$> mapM namesPart (splitEvery "," body)
            unless (not (null names)) (failure location "P-Unfold" "Expected at least one constant name.")
            return (UnfoldProof names target)
        "simpl" -> do
            (body, target) <- case splitTop "in" tokens of
                Just (prefix, h : at : sites)
                    | text at == "at" -> do
                        hypothesis <- nameToken h
                        return (prefix ++ at : sites, HypothesisTarget hypothesis)
                _ -> targetTokens tokens
            case body of
                [] -> return (SimplProof target)
                [name] -> do
                    function <- nameToken name
                    return (SimplAtProof function True [] target)
                name : at : sites
                    | text at == "at" -> do
                        function <- nameToken name
                        let (include, numbers) = case sites of
                                minus : rest
                                    | text minus == "-" -> (False, rest)
                                _ -> (True, sites)
                        unless (not (null numbers) && all ((== "numeral") . Front.tokenKind) numbers) (failure location "P-Simpl" "Expected positive occurrence numbers after at.")
                        let occurrences = map (read . text) numbers
                        unless (all (> 0) occurrences) (failure location "P-Simpl" "Occurrence numbers start at one.")
                        return (SimplAtProof function include occurrences target)
                _ -> failure location "P-Simpl" "Expected simpl, or simpl followed by a name and optional occurrences."
        "change" -> uncurry ChangeProof <$> termTargetIndexed rules tokens
        "discriminate" -> do
            (body, target) <- targetTokens tokens
            value <- if null body then Right Nothing else Just <$> termTokensIndexed rules body
            return (DiscriminateProof value target)
        "injection" -> uncurry InjectionProof <$> termTargetIndexed rules tokens
        "assert" -> case enclosed "(" ")" tokens of
            Just (name : colon : typ)
                | text colon == ":" -> AssertProof <$> binderName rules name <*> termTokensIndexed rules typ
            Just body -> AssertProof (Front.Name location "") <$> termTokensIndexed rules body
            _ -> failure location "P-Assert" "Expected assert (type) or assert (name : type)."
        "specialize" -> SpecializeProof <$> term
        "tactic" -> case tokens of
            name : arguments -> UserProof <$> nameToken name <*> userArgumentsIndexed rules arguments
            _ -> failure location "P-UserTactic" "Expected tactic name followed by parenthesized arguments."
        _ -> failure location "P-Tactic" ("Unknown tactic " ++ Front.quoted (text first) ++ ".")
    where
        location = if null tokens then Front.tokenSpan first else Front.tokenSpan first <> tokensSpan tokens
        term = if null tokens then failure (Front.tokenSpan first) "P-ProofTerm" "Expected a term." else termTokensIndexed rules tokens
        noArguments result = if null tokens then Right result else failure location "P-TacticArguments" "This tactic takes no arguments."
        namesPart [] = failure location "P-Unfold" "Expected a constant name between commas."
        namesPart part = mapM nameToken part
        destruct constructor = case splitTop "as" tokens of
            Nothing -> constructor <$> term <*> pure []
            Just (body, names) -> constructor <$> termTokensIndexed rules body <*> binderNames rules names

binderNames :: Notation.Rules -> [Front.Token] -> Either Front.FrontError [Front.Name]
binderNames rules = mapM (binderName rules)

binderName :: Notation.Rules -> Front.Token -> Either Front.FrontError Front.Name
binderName rules token
    | Set.member (text token) (Notation.binderWords rules) = failure (Front.tokenSpan token) "P-ProofName" "This binder name is a notation keyword."
    | Front.tokenKind token == "_" = Right (Front.tokenName token)
    | Front.tokenKind token == "qualid" = failure (Front.tokenSpan token) "P-ProofName" "A local name cannot be qualified."
    | otherwise = nameToken token

namesTokens :: [Front.Token] -> Either Front.FrontError [Front.Name]
namesTokens = binderNames Notation.emptyRules

nameToken :: Front.Token -> Either Front.FrontError Front.Name
nameToken token = case termTokens [token] of
    Right (Front.Term _ (Front.SName name)) -> Right name
    _ -> failure (Front.tokenSpan token) "P-ProofName" "Expected an identifier."

termsTokens :: [Front.Token] -> Either Front.FrontError [Front.Term]
termsTokens = termsTokensIndexed Notation.emptyRules

termsTokensWith :: Rules -> [Front.Token] -> Either Front.FrontError [Front.Term]
termsTokensWith = termsTokensIndexed . Notation.fromRules

termsTokensIndexed :: Notation.Rules -> [Front.Token] -> Either Front.FrontError [Front.Term]
termsTokensIndexed rules [] = (: []) <$> termTokensIndexed rules []
termsTokensIndexed rules tokens = case Grammar.runParser arguments (Parse.termGrammar rules input) input of
    Right (values, []) -> Right values
    Right (_, token : _) -> unexpectedToken tokens (Just token)
    Left issue -> Left (Parse.parseError (tokensSpan tokens) issue)
    where
        input = Parse.branching tokens
        arguments = (:) <$> Grammar.term <*> Grammar.series (== ",") (Grammar.want "," >> Grammar.term)

targetTokens :: [Front.Token] -> Either Front.FrontError ([Front.Token], Target)
targetTokens tokens = case splitTop "in" tokens of
    Nothing -> Right (tokens, GoalTarget)
    Just (body, [name]) -> do
        target <- nameToken name
        return (body, HypothesisTarget target)
    Just _ -> failure (tokensSpan tokens) "P-TacticTarget" "Expected in followed by one hypothesis name."

termTarget :: [Front.Token] -> Either Front.FrontError (Front.Term, Target)
termTarget = termTargetIndexed Notation.emptyRules

termTargetWith :: Rules -> [Front.Token] -> Either Front.FrontError (Front.Term, Target)
termTargetWith = termTargetIndexed . Notation.fromRules

termTargetIndexed :: Notation.Rules -> [Front.Token] -> Either Front.FrontError (Front.Term, Target)
termTargetIndexed rules tokens = do
    (body, target) <- targetTokens tokens
    value <- termTokensIndexed rules body
    return (value, target)

userArguments :: [Front.Token] -> Either Front.FrontError [Front.Term]
userArguments = userArgumentsIndexed Notation.emptyRules

userArgumentsWith :: Rules -> [Front.Token] -> Either Front.FrontError [Front.Term]
userArgumentsWith = userArgumentsIndexed . Notation.fromRules

userArgumentsIndexed :: Notation.Rules -> [Front.Token] -> Either Front.FrontError [Front.Term]
userArgumentsIndexed _ [] = Right []
userArgumentsIndexed rules tokens = case group tokens of
    Just (argument, rest) -> (:) <$> termTokensIndexed rules argument <*> userArgumentsIndexed rules rest
    Nothing -> failure (tokensSpan tokens) "P-UserTactic" "Each user tactic argument must be parenthesized."
    where
        group (opening : rest)
            | text opening == "(" = scan [")"] [opening] rest
        group _ = Nothing
        scan _ _ [] = Nothing
        scan stack reversed (token : rest)
            | stack == [")"] && text token == ")" = Just (reverse (token : reversed), rest)
            | otherwise = scan (nest stack token) (token : reversed) rest

data TacticArgument = TermArgument Front.Term | NameArgument Front.Name | NestedArgument Tactic deriving (Eq, Show)

registeredTactic :: Rules -> Span -> Front.SyntaxRule Global -> [Front.Token] -> Either Front.FrontError Tactic
registeredTactic rules location = registeredTacticAt (Notation.fromRules rules) location location

registeredTacticAt :: Notation.Rules -> Span -> Span -> Front.SyntaxRule Global -> [Front.Token] -> Either Front.FrontError Tactic
registeredTacticAt rules location boundary rule = indexedTactic (Just (location, rule)) rules boundary

buildTactic :: Span -> String -> [TacticArgument] -> Either Front.FrontError Tactic
buildTactic location target args = case (target, args) of
    ("try", [NestedArgument child]) -> Right (Try location child)
    ("repeat", [NestedArgument child]) -> Right (Repeat location child)
    ("all", [NestedArgument child]) -> Right (All location child)
    ("first", [NestedArgument one, NestedArgument two]) -> Right (First location [one, two])
    ("then", [NestedArgument one, NestedArgument two]) -> Right (Then location one two)
    _ -> Primitive location <$> primitive
    where
        malformed = failure location "P-Notation" "The tactic does not match the registered syntax."
        primitive = case (target, args) of
            ("exact", [TermArgument t]) -> Right (ExactProof t)
            ("refine", [TermArgument t]) -> Right (RefineProof t)
            ("apply", [TermArgument t]) -> Right (ApplyProof t)
            ("rewrite", [TermArgument t]) -> Right (RewriteProof Forward t GoalTarget)
            ("transitivity", [TermArgument t]) -> Right (TransitivityProof t)
            ("exists", [TermArgument t]) -> Right (ExistsProof [t])
            ("change", [TermArgument t]) -> Right (ChangeProof t GoalTarget)
            ("specialize", [TermArgument t]) -> Right (SpecializeProof t)
            ("intros", _) -> IntrosProof <$> mapM nameArg args
            ("intro", _) -> IntroProof <$> mapM nameArg args
            ("assumption", []) -> Right AssumptionProof
            ("reflexivity", []) -> Right ReflexivityProof
            ("symmetry", []) -> Right SymmetryProof
            ("split", []) -> Right SplitProof
            ("left", []) -> Right LeftProof
            ("right", []) -> Right RightProof
            ("constructor", []) -> Right (ConstructorProof Nothing)
            ("exfalso", []) -> Right ExfalsoProof
            _
                | take 7 target == "tactic." -> UserProof (Front.Name location (drop 7 target)) <$> mapM termArg args
                | otherwise -> malformed
        nameArg (NameArgument name) = Right name
        nameArg _ = malformed
        termArg (TermArgument term) = Right term
        termArg _ = malformed
