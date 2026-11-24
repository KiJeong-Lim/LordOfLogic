module LoL.Front.Notation where

import Control.Monad (foldM, unless)
import Data.List (foldl', isPrefixOf, stripPrefix)
import Control.Applicative ((<|>))
import qualified Data.Map.Strict as Map
import qualified Data.IntSet as IntSet
import qualified Data.Set as Set
import LoL.Core (Global)
import qualified LoL.Front.Grammar as G
import qualified LoL.Front.HostLexer as Lex
import LoL.Front.Syntax
import Text.Read (readMaybe)

-- The dispatch trie ends before the first hole. Two rules may share a run of
-- literal words, but registration rejects choices requiring a parsed argument
-- to be discarded and parsed again.
data Trie a = Trie (Maybe a) (Map.Map String (Trie a)) deriving (Eq, Show)

emptyTrie :: Trie a
emptyTrie = Trie Nothing Map.empty

insertTrie :: [String] -> a -> Trie a -> Trie a
insertTrie [] value (Trie _ next) = Trie (Just value) next
insertTrie (word : more) value (Trie old next) = Trie old (Map.alter (Just . insertTrie more value . maybe emptyTrie id) word next)

select :: Trie a -> [Token] -> Maybe a
select (Trie (Just result) _) _ = Just result
select (Trie _ next) (token : rest)
    | literalToken token = Map.lookup (tokenText token) next >>= flip select rest
select _ _ = Nothing

literalToken :: Token -> Bool
literalToken token = tokenKind token `elem` ("ident" : "operator" : "," : Lex.contextWords)

matchesLiteral :: String -> Token -> Bool
matchesLiteral literal token = literalToken token && tokenText token == literal

literalPrefix :: [RulePart] -> [String]
literalPrefix (Literal literal : more) = literal : literalPrefix more
literalPrefix _ = []

led :: [RulePart] -> Bool
led (TermSlot : _) = True
led _ = False

ruleKey :: SyntaxRule a -> (Bool, Bool, [String])
ruleKey (SyntaxRule parts _ _ target) = (tactic, led parts, literalPrefix (if led parts then drop 1 parts else parts)) where
    tactic = case target of
        TacticTarget {} -> True
        _ -> False

rulesConflict :: SyntaxRule a -> SyntaxRule b -> Bool
rulesConflict a b = ta == tb && la == lb && (ka `isPrefixOf` kb || kb `isPrefixOf` ka) where
    (ta, la, ka) = ruleKey a
    (tb, lb, kb) = ruleKey b

-- A tactic expansion consists solely of a known, typed constructor or a
-- reference to a Hol user tactic with term arguments. No declaration can
-- invoke another parser on its own generated text.
validateRule :: SyntaxRule a -> Either String ()
validateRule rule@(SyntaxRule parts level assoc target) = do
    unless (level >= 0 && level <= 200 && assoc `elem` ["left", "right", "no"]) (Left "Invalid notation binding level or associativity.")
    unless (not (null key)) (Left "A notation needs a distinguishing literal before its first argument.")
    mapM_ checkLiteral [literal | Literal literal <- parts]
    unless (not (any adjacent (zip parts (drop 1 parts)))) (Left "Adjacent notation slots require a literal separator.")
    (binders, mentioned) <- foldM checkScope (IntSet.empty, IntSet.empty) (zip [1 ..] slots)
    case target of
        TermTarget _ -> do
            unless (TacticSlot `notElem` slots) (Left "A term notation cannot take a tactic.")
            unless (binders == mentioned) (Left "Every binder slot must bind a later scoped term.")
        TacticTarget name -> do
            unless (not leftward) (Left "A tactic notation must begin with a literal.")
            unless (level == 0 && assoc == "no") (Left "Tactic notations do not have term precedence.")
            unless (head key `notElem` proofWords && bulletMark (head key) == Nothing) (Left "This literal already begins a built-in proof command.")
            unless (signature name slots) (Left "The target tactic does not accept these slots.")
    where
        (_, leftward, key) = ruleKey rule
        slots = [part | part <- parts, not (literalPart part)]
        literalPart Literal {} = True
        literalPart _ = False
        adjacent (a, b) = not (literalPart a || literalPart b)
        checkLiteral value = case Lex.lexHost (1, 1) value of
            Right [token]
                | tokenText token == value
                , tokenKind token `elem` ("ident" : "operator" : "," : Lex.contextWords)
                , value /= "," || not (value `elem` key) -> Right ()
            _ -> Left ("Unusable notation literal: " ++ value)
        checkScope (binders, used) (index, NameSlot) = Right (IntSet.insert index binders, used)
        checkScope (binders, used) (_, ScopedSlot k)
            | IntSet.member k binders = Right (binders, IntSet.insert k used)
            | otherwise = Left "A scoped term must refer to an earlier binder slot."
        checkScope seen _ = Right seen
        signature name args
            | Just called <- stripPrefix "tactic." name = all (== TermSlot) args && case Lex.lexHost (1, 1) called of
                Right [token] -> tokenKind token == "ident" && tokenText token == called
                _ -> False
            | name `elem` words "exact apply refine rewrite exists change transitivity specialize" = args == [TermSlot]
            | name == "intro" = args `elem` [[], [NameSlot]]
            | name == "intros" = all (== NameSlot) args
            | name `elem` words "assumption reflexivity symmetry split left right constructor exfalso" = null args
            | name `elem` words "try repeat all" = args == [TacticSlot]
            | name `elem` words "first then" = args == [TacticSlot, TacticSlot]
            | otherwise = False

bulletMark :: String -> Maybe (Char, Int)
bulletMark (first : rest)
    | first `elem` "-+*", all (== first) rest = Just (first, 1 + length rest)
bulletMark _ = Nothing

proofWords :: [String]
proofWords = words "Proof Show Undo Abort Qed Load Record Notation Local Tactic all try repeat first refine exact intro intros apply assumption reflexivity symmetry transitivity exists split left right constructor exfalso destruct induction rewrite unfold simpl change discriminate injection assert specialize tactic"

-- Slots are individual words inside the quoted pattern. Literal tokens must
-- round-trip through the host lexer without splitting. The one-based number
-- on $bodyN identifies exactly the binder whose scope includes that term.
patternParts :: String -> Maybe [RulePart]
patternParts = mapM part . words where
    part "$term" = Just TermSlot
    part "$name" = Just NameSlot
    part "$tactic" = Just TacticSlot
    part word
        | Just suffix <- stripPrefix "$body" word = do
            number <- readMaybe suffix
            if show number == suffix then Just (ScopedSlot number) else Nothing
        | otherwise = Just (Literal word)

isDeclaration :: [Token] -> Bool
isDeclaration (local : more)
    | matchesLiteral "Local" local = isDeclaration more
isDeclaration (tactic : notation : _)
    | matchesLiteral "Tactic" tactic = matchesLiteral "Notation" notation
isDeclaration (notation : _) = matchesLiteral "Notation" notation
isDeclaration [] = False

declaration :: [Token] -> Either (Maybe Token) Command
declaration tokens = case input of
    notation : patternToken : assign : target : more
        | matchesLiteral "Notation" notation, tokenKind patternToken == "string", tokenKind assign == ":=" -> do
            parts <- maybe (Left (Just patternToken)) Right (patternParts (tokenText patternToken))
            unless (tokenKind target `elem` ("qualid" : "ident" : Lex.contextWords)) (Left (Just target))
            (level, assoc, dot) <- options more
            let rhs = if tactic then TacticTarget (tokenText target) else TermTarget (tokenName target)
            pure (CNotation (tokenSpan (head tokens) <> tokenSpan dot) local (SyntaxRule parts level assoc rhs))
    _ -> Left (firstOf input)
    where
        (local, afterLocal) = flag "Local" tokens
        (tactic, input) = flag "Tactic" afterLocal
        flag word (token : more)
            | matchesLiteral word token = (True, more)
        flag _ more = (False, more)
        firstOf [] = Nothing
        firstOf (token : _) = Just token
        options [dot]
            | tokenKind dot == "." = Right (0, "no", dot)
        options [opening, at, level, number, comma, direction, assoc, closing, dot]
            | not tactic
            , map tokenKind [opening, at, level, number, comma, assoc, closing, dot] == ["(", "at", "level", "numeral", ",", "associativity", ")", "."]
            , tokenKind direction `elem` ["no", "left", "right"] = Right (read (tokenText number), tokenText direction, dot)
        options more = Left (firstOf more)

indexRules :: Bool -> Bool -> [SyntaxRule a] -> Trie (SyntaxRule a)
indexRules tactic leftward = foldl' add emptyTrie where
    add index rule
        | (tactic, leftward) == (category, left) = insertTrie key rule index
        | otherwise = index
        where
            (category, left, key) = ruleKey rule

-- The document stores a persistent index. Legacy Infix entries stay in
-- their original map so unextended expressions retain ALPHA's diagnostics.
data Rules = Rules
    { prefixRules   :: !(Trie (SyntaxRule Global))
    , suffixRules   :: !(Trie (SyntaxRule Global))
    , tacticRules   :: !(Trie (SyntaxRule Global))
    , infixRules    :: !(Map.Map String (Global, Integer, String))
    , termLiterals  :: !(Set.Set String)
    , binderWords   :: !(Set.Set String)
    } deriving (Eq, Show)

emptyRules :: Rules
emptyRules = Rules emptyTrie emptyTrie emptyTrie Map.empty Set.empty Set.empty

addRule :: SyntaxRule Global -> Rules -> Rules
addRule rule@(SyntaxRule parts level _ target) rules = case target of
    TacticTarget _ -> rules { tacticRules = insertTrie key rule (tacticRules rules) }
    TermTarget _
        | leftward -> updated { suffixRules = insertTrie key rule (suffixRules rules) }
        | otherwise -> updated { prefixRules = insertTrie key rule (prefixRules rules) }
    where
        (_, leftward, key) = ruleKey rule
        literals = Set.fromList [word | Literal word <- parts]
        -- A terminal must distinguish the continuation after a term slot.
        -- A second literal and a literal after a name slot need no keyword.
        -- Rocq also allows the leading word to remain a name at level zero.
        keywords _ [] = []
        keywords needed (Literal word : rest)
            | needed = word : keywords False rest
            | otherwise = keywords False rest
        keywords _ (part : rest) = keywords (termSlot part) rest
        termSlot TermSlot = True
        termSlot (ScopedSlot _) = True
        termSlot _ = False
        updated = rules
            { termLiterals = Set.union literals (termLiterals rules)
            , binderWords = Set.union (Set.fromList (keywords (level /= 0) parts)) (binderWords rules)
            }

fromRules :: [SyntaxRule Global] -> Rules
fromRules = foldl' (flip addRule) emptyRules

-- Registration rejects equal and proper-prefix overlaps. Valid existing
-- paths therefore have a single leaf or a subtree with at least one leaf.
overlapping :: SyntaxRule Global -> Rules -> Maybe (SyntaxRule Global)
overlapping rule rules = walk key table where
    (tactic, leftward, key) = ruleKey rule
    table
        | tactic = tacticRules rules
        | leftward = suffixRules rules
        | otherwise = prefixRules rules
    walk _ (Trie (Just found) _) = Just found
    walk (k : ks) (Trie _ branches) = Map.lookup k branches >>= walk ks
    walk [] (Trie _ branches) = Map.lookupMin branches >>= walk [] . snd

grammar :: [SyntaxRule Global] -> G.Grammar
grammar = indexedGrammar . fromRules

indexedGrammar :: Rules -> G.Grammar
indexedGrammar = delimitedGrammar []

-- A tactic's term slot stops at its next literal. Binders and mixfix terms
-- consume their own internal delimiters before returning to that slot.
delimitedGrammar :: [String] -> Rules -> G.Grammar
delimitedGrammar delimiters rules
    | null delimiters && Set.null (termLiterals rules) = G.fixed
    | otherwise = scope delimiters
    where
        scope stops = G.Grammar (readTerm stops 200 Nothing) (readTerm [] 200 Nothing) (\word -> Set.member word (binderWords rules))
        prefixes = prefixRules rules
        suffixes = suffixRules rules
        suffixAt tokens = select suffixes tokens <|> legacy tokens
        legacy (token : _)
            | tokenKind token == "operator" = do
                let op = tokenText token
                (global, level, assoc) <- Map.lookup op (infixRules rules)
                pure (SyntaxRule [TermSlot, Literal op, TermSlot] level assoc (TermTarget global))
        legacy _ = Nothing
        selected lookupRule = G.Parser $ \_ tokens -> Right (lookupRule tokens, tokens)
        readTerm = readOperand True
        readOperand allowApplication stops limit enclosing = do
            token <- G.peek
            case token of
                Just t | literalToken t && tokenText t `elem` stops -> G.bad
                _ -> pure ()
            prefix <- selected (select prefixes)
            first <- case prefix of
                Just rule -> expansion stops Nothing rule
                Nothing -> baseWith stops
            if G.openPrefix first then pure first else continue allowApplication stops limit enclosing Nothing first
        -- A parenthesis or match has its own closing delimiter. The body of
        -- an unparenthesized let or binder instead ends at the surrounding
        -- mixfix delimiter.
        baseWith stops = do
            kind <- G.ahead
            if kind `elem` ["let", "forall", "fun", "fix"] then
                G.Parser $ \_ tokens -> G.runParser G.base (scope stops) tokens
            else grouped G.base
        grouped parser = G.Parser $ \_ tokens -> G.runParser parser (scope []) tokens
        continue allowApplication stops limit enclosing previous left = do
            next <- G.peek
            case next of
                Nothing -> pure left
                Just token
                    | literalToken token && tokenText token `elem` stops -> pure left
                    | otherwise -> following token
            where
                following token = do
                    suffix <- selected suffixAt
                    case suffix of
                        Just rule@(SyntaxRule _ level assoc _)
                            | level <= limit -> do
                                checkEqual token previous level assoc
                                checkEqual token enclosing level assoc
                                value <- expansion stops (Just left) rule
                                continue allowApplication stops limit enclosing (Just (level, assoc)) value
                            | otherwise -> pure left
                        Nothing
                            | tokenKind token `elem` ["->", ":"] -> special token
                            | otherwise -> do
                                prefix <- selected (select prefixes)
                                case prefix of
                                    Just rule@(SyntaxRule _ level _ _)
                                        | not allowApplication -> pure left
                                        | level >= 10 -> G.bad
                                        | otherwise -> expansion stops Nothing rule >>= applyArgument
                                    Nothing
                                        | G.startsAtom (tokenKind token) -> if allowApplication then grouped G.atom >>= applyArgument else pure left
                                        | tokenKind token == "operator", limit >= 0 -> do
                                            symbol <- G.takeToken
                                            right <- readTerm stops 0 Nothing
                                            continue allowApplication stops limit enclosing Nothing (operators (left, [(tokenName symbol, right)]))
                                        | otherwise -> pure left
                applyArgument argument = continue allowApplication stops limit enclosing Nothing (application left argument)
                checkEqual token peer level assoc = case peer of
                    Just (old, direction)
                        | old == level && (assoc == "no" || direction /= assoc) -> G.Parser $ \_ _ -> Left (G.Association token)
                    _ -> pure ()
                special token
                    | level > limit = pure left
                    | otherwise = do
                        _ <- G.takeToken
                        rhs <- readTerm stops 200 Nothing
                        pure (if tokenKind token == "->" then arrowTo left rhs else castTo left rhs)
                    where
                        level = if tokenKind token == "->" then 99 else 100
        -- A projection can follow a closed notation literal directly.
        -- A trailing term slot consumes its own projections, subject to the
        -- same syntactic restriction on an unparenthesized match.
        expansion stops initial rule@(SyntaxRule parts _ _ _) = do
            value <- expand stops initial rule
            case last parts of
                Literal _ -> G.projectionTail value
                _ -> pure value
        expand stops initial (SyntaxRule parts level assoc (TermTarget global)) = do
            start <- G.peek
            let initialArgs = maybe [] (: []) initial
                remaining = if null initialArgs then parts else drop 1 parts
            (args, end) <- slots (not (null initialArgs) || level >= 10) stops level assoc (length initialArgs) Map.empty (reverse initialArgs) remaining Nothing
            case (start, end) of
                (Just token, Just lastSpan) -> do
                    let firstSpan = maybe (tokenSpan token) termSpan initial
                        location = firstSpan <> lastSpan
                        result = foldl' attach (Term (tokenSpan token) (SGlobal global)) (reverse args)
                    pure result { termSpan = location }
                _ -> G.bad
        expand _ _ _ = G.bad
        -- An infix target is between its two source operands. Every
        -- intermediate application must cover its children in source order.
        attach function argument = Term (Span (min (spanFrom a) (spanFrom b)) (max (spanTill a) (spanTill b))) (SApp function argument) where
            a = termSpan function
            b = termSpan argument
        slots _ _ _ _ _ _ args [] end = pure (args, end)
        slots finalApplication stops level assoc index names args (part : more) _ = case part of
            Literal value -> do
                token <- G.takeIf (matchesLiteral value)
                next index names args (tokenSpan token)
            NameSlot -> do
                name <- G.boundIdent
                next (index + 1) (Map.insert (index + 1) name names) args (nameSpan name)
            TermSlot -> argument Nothing
            ScopedSlot k -> case Map.lookup k names of
                Just name -> argument (Just name)
                Nothing -> G.bad
            TacticSlot -> G.bad
            where
                next i ns vs position = slots finalApplication stops level assoc i ns vs more (Just position)
                argument binder = do
                    let (boundaries, strength) = case more of
                            Literal delimiter : _ -> (delimiter : stops, 200)
                            _ -> (stops, if assoc == "right" then level else level - 1)
                    value <- readOperand (finalApplication || not (null more)) boundaries strength (if null more && assoc == "right" then Just (level, assoc) else Nothing)
                    let raw = case binder of
                            Nothing -> value
                            Just name -> Term (nameSpan name <> termSpan value) (SLambda [Binder (nameSpan name) [name] Nothing False] value)
                    next (index + 1) names (raw : args) (termSpan value)
