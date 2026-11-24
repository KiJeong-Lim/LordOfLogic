module LoL.Front.Notation where

import Control.Monad (foldM, unless)
import Data.List (find, foldl', isPrefixOf, isSuffixOf, nubBy, sortOn, stripPrefix)
import Data.Maybe (listToMaybe)
import Data.Ord (Down (..))
import Control.Applicative ((<|>))
import qualified Data.Map.Strict as Map
import qualified Data.IntSet as IntSet
import qualified Data.Set as Set
import LoL.Core (Global)
import qualified LoL.Front.Grammar as G
import qualified LoL.Front.HostLexer as Lex
import qualified LoL.Front.Template as Template
import qualified LoL.Front.Format as Format
import LoL.Front.Syntax
import Text.Read (readMaybe)

-- A token prefix selects a small set of productions. A later terminal
-- can differentiate productions whose first metavariable is the same.
data Trie a = Trie [a] (Map.Map String (Trie a)) deriving (Eq, Show)

emptyTrie :: Trie a
emptyTrie = Trie [] Map.empty

insertTrie :: [String] -> a -> Trie a -> Trie a
insertTrie [] value (Trie old next) = Trie (value : old) next
insertTrie (word : more) value (Trie old next) = Trie old (Map.alter (Just . insertTrie more value . maybe emptyTrie id) word next)

matches :: Trie a -> [Token] -> [a]
matches (Trie here next) (token : rest) = maybe [] (flip matches rest) (Map.lookup (tokenText token) next) ++ here
matches (Trie here _) [] = here

select :: Trie a -> [Token] -> Maybe a
select trie = listToMaybe . matches trie

literalToken :: Token -> Bool
literalToken token = tokenKind token `notElem` ["string", "qualid"]

matchesLiteral :: String -> Token -> Bool
matchesLiteral literal token = literalToken token && tokenText token == literal

literalPrefix :: [RulePart] -> [String]
literalPrefix (Literal literal : more) = literal : literalPrefix more
literalPrefix _ = []

led :: [RulePart] -> Bool
led (EntryRoot entry : EntrySlot (Just target) _ : _ : _) = entry == target
led (EntryRoot _ : parts) = led parts
led (TermSlot : _) = True
led (LevelSlot _ : _) = True
led _ = False

ruleKey :: SyntaxRule a -> (Bool, Bool, [String])
ruleKey (SyntaxRule parts _ _ target) = (tactic, led parts, literalPrefix (if led parts then drop 1 patternParts else patternParts)) where
    (_, patternParts) = ruleEntry parts
    tactic = case target of
        TacticTarget {} -> True
        _ -> False

rulesConflict :: SyntaxRule a -> SyntaxRule b -> Bool
rulesConflict a@(SyntaxRule ap _ _ _) b@(SyntaxRule bp _ _ _) = fst (ruleEntry ap) == fst (ruleEntry bp) && ta == tb && la == lb && (ka `isPrefixOf` kb || kb `isPrefixOf` ka) where
    (ta, la, ka) = ruleKey a
    (tb, lb, kb) = ruleKey b

-- A tactic expansion consists solely of a known, typed constructor or a
-- reference to a Hol user tactic with term arguments. No declaration can
-- invoke another parser on its own generated text.
-- Rocq reads grammar levels as nonnegative OCaml machine integers.
-- The parser compares levels directly, including in sparse custom entries.
maxRocqLevel :: Integer
maxRocqLevel = toInteger (maxBound :: Int) `div` 2

validLevel :: Integer -> Bool
validLevel level = 0 <= level && level <= maxRocqLevel

validateRule :: Eq a => SyntaxRule a -> Either String ()
validateRule (SyntaxRule (AliasHead name : slots) 10 "left" (RocqTarget Nothing ns use body)) = do
    Template.validateIteration slots ns body
    unless (all argument slots && length slots == length ns && length ns == Set.size (Set.fromList ns) && use `elem` [BothWays,ParsingOnly] && validName name) (Left "Invalid abbreviation signature.")
    where
        argument (AliasArg scope) = maybe True validName scope
        argument _ = False
        validName (c:cs) = Lex.identStart c && all Lex.identContinue cs
        validName [] = False
validateRule rule@(SyntaxRule parts level assoc target) = do
    unless (validLevel level && (case target of { RocqTarget {} -> True; _ -> level <= 200 }) && assoc `elem` ["left", "right", "no"]) (Left "Invalid notation binding level or associativity.")
    unless (not (null key) || customFallback || printingRule) (Left "A notation needs a distinguishing literal before its first argument.")
    case target of
        RocqTarget _ names use body -> do
            unless (use == ReservedSyntax) $ do
                Template.validateIteration parts names (snd (Template.printFormat body))
                Template.validatePatternSlots parts names body
            mapM_ (Format.validate parts names) (fst (Template.printFormat body))
            unless (Template.slotBindings parts names) (Left "Invalid Rocq notation variables.")
            unless (all validPart parts) (Left "Invalid Rocq notation symbol.")
        _ -> do
            unless (entry == Nothing && not (any entryPart parts)) (Left "Custom entry slots require a Rocq term notation.")
            mapM_ checkLiteral [literal | Literal literal <- parts]
    unless (entry /= Nothing || not (any adjacent (zip patternParts (drop 1 patternParts)))) (Left "Adjacent notation slots require a literal separator.")
    (binders, mentioned) <- foldM checkScope (IntSet.empty, IntSet.empty) (zip [1 ..] slots)
    case target of
        RocqTarget {} -> unless (TacticSlot `notElem` slots) (Left "A term notation cannot take a tactic.")
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
        (entry, patternParts) = ruleEntry parts
        printingRule = case target of
            RocqTarget _ _ PrintingOnly _ -> True
            _ -> False
        customFallback = case (entry,patternParts) of
            (Just _, NameSlot : _) -> True
            (Just _, TokenSlot _ : _) -> True
            (Just _, PatternSlot {} : _) -> True
            (Just e, EntrySlot dest _ : tailParts) -> dest /= Just e || not (null tailParts)
            (Just _, TermSlot : _ : _) -> True
            (Just _, LevelSlot _ : _ : _) -> True
            _ -> False
        entryPart AsNameSlot {} = True
        entryPart EntrySlot {} = True
        entryPart EntryRoot {} = True
        entryPart _ = False
        validPart AliasHead {} = False
        validPart AliasArg {} = False
        validPart (EntryRoot n) = entryName n && entry == Just n && EntryRoot n `notElem` patternParts
        validPart (AsNameSlot _ e n) = validPart (EntrySlot e n)
        validPart (EntrySlot e n) = maybe True entryName e && maybe True validLevel n
        validPart (Literal word) = not (null word) && all (not . sourceSpace) word && case Lex.lexHostWith (Set.singleton word) (1,1) word of
            Right [t] -> tokenText t == word && tokenKind t `notElem` ["string", ".", ".."]
            _ -> False
        validPart (RepeatSlot sep item) = repeatOperand item && validPart item && all (validPart . Literal) (words sep)
        validPart (PatternSlot kind _ bound) = validPart (EntrySlot (patternEntry entry kind) bound)
        validPart (TokenSlot k) = k `elem` ["name","global","bigint","closed binder"]
        validPart (LevelSlot n) = validLevel n
        validPart _ = True
        validName (c:cs) = Lex.identStart c && all Lex.identContinue cs
        validName _ = False
        slots = [part | part <- patternParts, not (literalPart part)]
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
    , customRules   :: !(Map.Map String Rules)
    , entryPaths    :: !(Map.Map String String)
    , knownEntries  :: !(Set.Set String)
    } deriving (Eq, Show)

emptyRules :: Rules
emptyRules = Rules emptyTrie emptyTrie emptyTrie Map.empty Set.empty Set.empty Map.empty Map.empty Set.empty

entryName :: String -> Bool
entryName name = case break (== '.') name of
    (c:cs, tailName) -> Lex.identStart c && all Lex.identContinue cs && case tailName of
        [] -> True
        _:more -> entryName more
    _ -> False

entryPath :: Rules -> String -> String
entryPath rules name
    | Set.member name (knownEntries rules) = name
    | Just visible <- Map.lookup name (entryPaths rules) = visible
    | [only] <- entryCandidates rules name = only
    | otherwise = name

entryCandidates :: Rules -> String -> [String]
entryCandidates rules name = filter (isSuffixOf ('.' : name)) (Set.toAscList (knownEntries rules))

publishEntry :: String -> Rules -> Rules
publishEntry name rules = rules { knownEntries = Set.insert name (knownEntries rules), entryPaths = foldr (flip Map.insert name) (entryPaths rules) (aliases name) } where
    aliases path = path : case dropWhile (/= '.') path of
        _:suffix -> aliases suffix
        [] -> []

entryRules :: Maybe String -> Rules -> Rules
entryRules Nothing rules = rules
entryRules (Just entry) rules = Map.findWithDefault emptyRules entry (customRules rules)

addRule :: SyntaxRule Global -> Rules -> Rules
addRule (SyntaxRule _ _ _ (RocqTarget _ _ PrintingOnly _)) rules = rules
addRule (SyntaxRule (AliasHead _ : _) _ _ _) rules = rules
addRule rule@(SyntaxRule marked _ _ _) rules = case fst (ruleEntry marked) of
    Nothing -> insertRule rule rules
    entry@(Just name) -> rules
        { customRules = Map.insert name updated (customRules rules)
        , termLiterals = Set.union (termLiterals updated) (termLiterals rules)
        , binderWords = Set.union (binderWords updated) (binderWords rules)
        }
        where updated = insertRule rule (entryRules entry rules)

insertRule :: SyntaxRule Global -> Rules -> Rules
insertRule rule@(SyntaxRule marked level _ target) rules = case target of
    TacticTarget _ -> rules { tacticRules = insertTrie key rule (tacticRules rules) }
    _
        | leftward -> updated { suffixRules = insertTrie key rule (suffixRules rules) }
        | otherwise -> updated { prefixRules = insertTrie key rule (prefixRules rules) }
    where
        (_, leftward, key) = ruleKey rule
        (_, parts) = ruleEntry marked
        literals = Set.fromList [word | Literal word <- parts]
        -- A terminal must distinguish the continuation after a term slot.
        -- A second literal and a literal after a name slot need no keyword.
        -- Rocq also allows the leading word to remain a name at level zero.
        keywords _ [] = []
        keywords needed (Literal word : rest)
            | needed = word : keywords False rest
            | otherwise = keywords False rest
        keywords _ (part : rest) = keywords (termSlot part) rest
        termSlot AsNameSlot {} = True
        termSlot EntrySlot {} = True
        termSlot LevelSlot {} = True
        termSlot RepeatSlot {} = True
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
overlapping rule@(SyntaxRule parts _ _ _) allRules = walk key table where
    rules = entryRules (fst (ruleEntry parts)) allRules
    (tactic, leftward, key) = ruleKey rule
    table
        | tactic = tacticRules rules
        | leftward = suffixRules rules
        | otherwise = prefixRules rules
    walk _ (Trie (found:_) _) = Just found
    walk (k : ks) (Trie _ branches) = Map.lookup k branches >>= walk ks
    walk [] (Trie _ branches) = Map.lookupMin branches >>= walk [] . snd

-- A reserved production contributes its level and associativity when the
-- later interpretation omits them. Variables may be renamed in that command.
production :: Rules -> [RulePart] -> Maybe (SyntaxRule Global)
production rules parts = do
    let probe = SyntaxRule parts 0 "no" (RocqTarget Nothing [] BothWays (TSort "_"))
    let (_, leftward, key) = ruleKey probe
        table = entryRules (fst (ruleEntry parts)) rules
        trie = if leftward then suffixRules table else prefixRules table
        candidates = exact key trie
        exact [] (Trie choices _) = choices
        exact (k:ks) (Trie _ branches) = maybe [] (exact ks) (Map.lookup k branches)
    let shape (Literal s) = Literal s
        shape (RepeatSlot sep _) = RepeatSlot sep TermSlot
        shape (EntryRoot n) = EntryRoot n
        shape _ = TermSlot
    let infixRule = case parts of
            [TermSlot,Literal symbol,TermSlot] -> do
                (global, precedence, direction) <- Map.lookup symbol (infixRules table)
                return (SyntaxRule parts precedence direction (TermTarget global))
            _ -> Nothing
    find (\(SyntaxRule registered _ _ _) -> map shape parts == map shape registered) candidates <|> infixRule

grammar :: [SyntaxRule Global] -> G.Grammar
grammar = indexedGrammar . fromRules

indexedGrammar :: Rules -> G.Grammar
indexedGrammar = delimitedGrammar []

-- A tactic's term slot stops at its next literal. Binders and mixfix terms
-- consume their own internal delimiters before returning to that slot.
delimitedGrammar :: [String] -> Rules -> G.Grammar
delimitedGrammar delimiters rules
    | null delimiters && Set.null (termLiterals rules) = G.fixed
    | otherwise = G.Grammar (readAt delimiters) (readAt []) (\word -> Set.member word (binderWords rules)) patternAt
    where
        -- The flat constructor check runs after scope-dependent expansion.
        -- Keep the fixed parser's diagnostics for ordinary Gallina branches.
        patternAt = G.Parser $ \grammar tokens -> case G.runParser (readAt ["=>"]) grammar tokens of
            Right (value, rest@(arrow : _))
                | tokenKind arrow == "=>", interpreted value -> Right (RawPattern value, rest)
            _ -> G.runParser G.patternP grammar tokens
        interpreted (Term _ form) = case form of
            SNotation {} -> True
            SDelimited {} -> True
            SGlobal {} -> True
            SOperators {} -> True
            SApp f x -> interpreted f || interpreted x
            SParen x -> interpreted x
            _ -> False
        readAt stops = entryTerm rules Nothing Nothing True stops 200 Nothing

-- Entering another grammar without consuming a token may form a cycle.
-- The guard is scoped to the parser call and its input position.
entryTerm :: Rules -> Maybe (Span, Set.Set (Maybe String)) -> Maybe String -> Bool -> [String] -> Integer -> Maybe (Integer, String) -> G.Parser Term
entryTerm tables parents active allow stops limit peer = do
    token <- G.peek
    case token of
        Nothing -> G.bad
        Just t -> do
            let here = tokenSpan t
                visited = case parents of
                    Just (prior, entries) | prior == here -> entries
                    _ -> Set.empty
            if Set.member active visited then G.bad else
                readOperandWith (parents /= Nothing) tables (Just (here, Set.insert active visited)) active allow stops limit peer

readOperandWith :: Bool -> Rules -> Maybe (Span, Set.Set (Maybe String)) -> Maybe String -> Bool -> [String] -> Integer -> Maybe (Integer, String) -> G.Parser Term
readOperandWith inNotation tables ancestry active = readOperand
    where
        rules = entryRules active tables
        scope stops = delimitedGrammar stops tables
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
            let prefixLevel (SyntaxRule _ level _ _) = inNotation || level <= max 200 limit
            prefix <- selected (find prefixLevel . matches prefixes)
            first <- case prefix of
                Just rule -> expansion prefixLevel stops Nothing rule
                _ | active == Nothing -> baseWith stops
                _ -> G.bad
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
                suffixLevel (SyntaxRule _ level _ target) = level <= limit && case target of
                    RocqTarget {} -> inNotation || active /= Nothing || level < 200
                    _ -> True
                following token = do
                    suffix <- selected suffixAt
                    case suffix of
                        Just rule@(SyntaxRule _ level assoc _)
                            | suffixLevel rule -> do
                                checkEqual token previous level assoc
                                checkEqual token enclosing level assoc
                                let advance = do
                                        value <- expansion suffixLevel stops (Just left) rule
                                        continue allowApplication stops limit enclosing (Just (level, assoc)) value
                                case ruleKey rule of
                                    (_,_,[]) -> G.Parser $ \grammar tokens -> case G.runParser advance grammar tokens of
                                        Left _ -> Right (left,tokens)
                                        success -> success
                                    _ -> advance
                            | otherwise -> pure left
                        Nothing
                            | active /= Nothing -> pure left
                            | tokenKind token `elem` ["->", ":"] -> special token
                            | otherwise -> do
                                prefix <- selected (select prefixes)
                                case prefix of
                                    Just rule@(SyntaxRule _ level _ _)
                                        | not allowApplication -> pure left
                                        | level >= 10 -> G.bad
                                        | otherwise -> expansion (\(SyntaxRule _ n _ _) -> n < 10) stops Nothing rule >>= applyArgument
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
        expansion permitted stops initial firstRule = G.Parser $ \grammar tokens ->
            let trie = maybe prefixes (const suffixes) initial
                shape (SyntaxRule ps _ _ _) = ps
                candidates = nubBy (\a b -> shape a == shape b) (filter permitted (matches trie tokens) ++ [firstRule])
                ordered = sortOn (Down . length . shape) candidates
                try [] = G.runParser G.bad grammar tokens
                try [r] = G.runParser (one r) grammar tokens
                try (r:rs) = case G.runParser (one r) grammar tokens of
                    Right answer -> Right answer
                    Left _ -> try rs
                one rule@(SyntaxRule parts _ _ _) = do
                    value <- expand stops initial rule
                    case last parts of
                        Literal _ | active == Nothing -> G.projectionTail value
                        _ -> pure value
            in try ordered
        expand stops initial (SyntaxRule marked level assoc target) = do
            start <- G.peek
            let (_,parts) = ruleEntry marked
                initialArgs = maybe [] (: []) initial
                remaining = if null initialArgs then parts else drop 1 parts
            let legacyBinder = case target of { TermTarget {} -> True; _ -> False }
            (args, end) <- slots legacyBinder (not (null initialArgs) || level >= 10) stops level assoc (length initialArgs) Map.empty (reverse initialArgs) remaining Nothing
            case (start, end) of
                (Just token, Just lastSpan) -> do
                    let firstSpan = maybe (tokenSpan token) termSpan initial
                        location = firstSpan <> lastSpan
                        arguments = reverse args
                    case target of
                        TermTarget global -> pure ((foldl' attach (Term (tokenSpan token) (SGlobal global)) arguments) { termSpan = location })
                        RocqTarget {} -> pure (Term location (SNotation marked arguments))
                        TacticTarget {} -> G.bad
                _ -> G.bad
        -- An infix target is between its two source operands. Every
        -- intermediate application must cover its children in source order.
        attach function argument = Term (Span (min (spanFrom a) (spanFrom b)) (max (spanTill a) (spanTill b))) (SApp function argument) where
            a = termSpan function
            b = termSpan argument
        slots _ _ _ _ _ _ _ args [] end = pure (args, end)
        slots legacyBinder finalApplication stops level assoc index names args (part : more) _ = case part of
            Literal value -> do
                token <- G.takeIf (matchesLiteral value)
                next index names args (tokenSpan token)
            NameSlot -> do
                name <- G.boundIdent
                next (index + 1) (Map.insert (index + 1) name names) (if legacyBinder then args else Term (nameSpan name) (SName name) : args) (nameSpan name)
            TokenSlot "name" -> do
                name <- G.variable
                let value = Term (nameSpan name) (if nameText name == "_" then SHole else SName name)
                next (index + 1) names (value : args) (termSpan value)
            TokenSlot "global" -> do
                name <- G.qname
                next (index + 1) names (Term (nameSpan name) (SName name) : args) (nameSpan name)
            TokenSlot "bigint" -> do
                token <- G.want "numeral"
                let value = Term (tokenSpan token) (SNumeral (read (tokenText token)))
                next (index + 1) names (value : args) (termSpan value)
            TokenSlot "closed binder" -> do
                kind <- G.ahead
                if kind `elem` ["(","{"] then pure () else G.bad
                b <- G.binder
                next (index + 1) names (binderOperand b : args) (binderSpan b)
            TokenSlot _ -> G.bad
            AliasHead _ -> G.bad
            AliasArg _ -> G.bad
            BinderSlot -> do
                binder <- G.binder
                next (index + 1) names (binderOperand binder : args) (binderSpan binder)
            RepeatSlot sep operand -> do
                let separators = words sep
                    ends = [v | Literal v <- take 1 more] ++ stops
                    boundaries = take 1 separators ++ ends
                    destination = case operand of { EntrySlot dest _ -> dest; _ -> active }
                    strength = case operand of
                        LevelSlot bound -> bound
                        EntrySlot _ (Just bound) -> bound
                        _ -> if destination == Nothing then 200 else maxRocqLevel
                    group = case operand of
                        BinderSlot -> binders False
                        TokenSlot "closed binder" -> binders True
                        _ -> (: []) <$> entryTerm tables ancestry destination (strength >= 10) boundaries strength Nothing
                    binders closed = do
                        kind <- G.ahead
                        if closed && kind `notElem` ["(", "{"] then G.bad else pure ()
                        b <- G.binder
                        return [binderOperand b { binderVars = [n] } | n <- binderVars b]
                    tailItems = do
                        token <- G.peek
                        case token of
                            Just t | firstSep : _ <- separators, matchesLiteral firstSep t -> do
                                mapM_ (G.takeIf . matchesLiteral) separators
                                (++) <$> group <*> tailItems
                            Just t | null separators, not (any (flip matchesLiteral t) ends) ->
                                G.Parser $ \grammar input -> case G.runParser group grammar input of
                                    Right (values, rest) -> G.runParser ((values ++) <$> tailItems) grammar rest
                                    Left _ -> Right ([], input)
                            _ -> pure []
                items <- (++) <$> group <*> tailItems
                let location = termSpan (head items) <> termSpan (last items)
                next (index + 1) names (Term location (SSequence items) : args) location
            EntryRoot _ -> G.bad
            AsNameSlot _ dest strength -> argument dest strength Nothing
            EntrySlot dest strength -> argument dest strength Nothing
            PatternSlot kind _ strength -> argument (patternEntry active kind) strength Nothing
            LevelSlot strength -> argument active (Just strength) Nothing
            TermSlot -> argument active Nothing Nothing
            ScopedSlot k -> case Map.lookup k names of
                Just name -> argument active Nothing (Just name)
                Nothing -> G.bad
            TacticSlot -> G.bad
            where
                binderOperand b = Term (binderSpan b) (SLambda [b] (Term (binderSpan b) SHole))
                next i ns vs position = slots legacyBinder finalApplication stops level assoc i ns vs more (Just position)
                argument dest specified binder = do
                    let (boundaries, strength) = case more of
                            Literal delimiter : _ -> (delimiter : stops, 200)
                            _ -> (stops, if assoc == "right" then level else level - 1)
                    let crossing = dest /= active
                        slotLevel = case more of
                            -- Rocq tolerates a looser operand before a delimiter.
                            Literal _ : _ | not legacyBinder -> maxRocqLevel
                            _ -> maybe (if crossing && dest /= Nothing then maxRocqLevel else if crossing then 200 else strength) id specified
                        applicationAllowed = if crossing then slotLevel >= 10 else finalApplication || not (null more)
                        peer = if not crossing && null more && assoc == "right" then Just (level, assoc) else Nothing
                    value <- entryTerm tables ancestry dest applicationAllowed boundaries slotLevel peer
                    let raw = case binder of
                            Nothing -> value
                            Just name -> Term (nameSpan name <> termSpan value) (SLambda [Binder (nameSpan name) [name] Nothing False] value)
                    next (index + 1) names (raw : args) (termSpan value)
