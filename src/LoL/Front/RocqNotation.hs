module LoL.Front.RocqNotation where

import Control.Monad (unless)
import Control.Applicative ((<|>))
import Data.List (break, nub, stripPrefix)
import qualified Data.Map.Strict as Map
import qualified LoL.Front.Grammar as G
import qualified LoL.Front.Format as Format
import qualified LoL.Front.Template as Template
import qualified LoL.Front.Notation as Notation
import qualified LoL.Front.HostLexer as Lex
import LoL.Front.Syntax
import Text.Read (readMaybe)

type Result a = Either (Maybe Token) a

-- Scope and locality commands are contextual. Programs may still use Scope,
-- Open or Declare as ordinary names in an expression.
splitLocal :: [Token] -> (SyntaxLocality, [Token])
splitLocal (t : rest)
    | tokenText t == "Local" = (LocalSyntax, rest)
    | tokenText t == "Global" = (GlobalSyntax, rest)
splitLocal (op : t : cl : rest)
    | tokenKind op == "#[", tokenKind cl == "]", tokenText t == "local" = (LocalSyntax, rest)
    | tokenKind op == "#[", tokenKind cl == "]", tokenText t == "global" = (GlobalSyntax, rest)
splitLocal tokens = (DefaultSyntax, tokens)

handles :: Notation.Rules -> [Token] -> Bool
handles rules tokens = case map tokenText (snd (splitLocal tokens)) of
    "#[" : attr : "]" : "Bind" : "Scope" : _ | attr `elem` ["add_top", "add_bottom"] -> True
    "Arguments" : _ | fst (splitLocal tokens) /= DefaultSyntax -> True
    verb : "Notation" : _ | verb `elem` ["Enable","Disable"] -> True
    "Declare" : "Custom" : "Entry" : _ -> True
    verb : "Scope" : _ -> verb `elem` ["Bind","Declare","Delimit","Undelimit","Open","Close"]
    cmd : _ | cmd `elem` ["Abbreviation","Notation"], name : _ <- drop 1 (snd (splitLocal tokens)), G.identifier (tokenKind name) -> True
    "Reserved" : variant : _ -> variant `elem` ["Notation","Infix"]
    "Notation" : pattern' : _ -> not (any (\word -> word `elem` ["$term","$name","$tactic"] || take 5 word == "$body") (words pattern')) && (not (plainLegacy pattern') || any (\t -> tokenText t `elem` ["custom","only","format"]) tokens)
    "Infix" : op : _ -> existing op || wideLevel || plainLegacy op || complexTarget || structured op || not (any ((== "level") . tokenText) tokens) || any (\t -> tokenText t `elem` ["only","format","custom","next"]) tokens || any ((== ":") . tokenKind) tokens || fst (splitLocal tokens) /= DefaultSyntax
    _ -> False
    where
        wideLevel = or [n > 200 | (a,b) <- zip tokens (drop 1 tokens), tokenText a == "level", Just n <- [readMaybe (tokenText b) :: Maybe Integer]]
        complexTarget = case drop 3 (snd (splitLocal tokens)) of
            t:rest -> not ((G.identifier (tokenKind t) || tokenKind t == "qualid") && case rest of { n:_ -> tokenKind n `elem` [".","(",":"]; [] -> False })
            [] -> False
        structured op = not (any sourceSpace op) && any (`elem` "[](){}") op && not (any (`elem` " *") op)
        existing op = case Notation.production rules [TermSlot, Literal op, TermSlot] of
            Just (SyntaxRule _ _ _ RocqTarget {}) -> True
            _ -> False
        plainLegacy (c:cs) = Lex.identStart c && all Lex.identContinue cs
        plainLegacy [] = False

declaration :: Notation.Rules -> [Token] -> Result Command
declaration rules original = case input of
    verb : notation : rest
        | tokenText verb `elem` ["Enable","Disable"], tokenText notation == "Notation", not (null rest), tokenKind (last rest) == "." -> do
            let (before,scope) = case reverse (init rest) of
                    kw : no : c : xs | map tokenText [c,no,kw] == [":","no","scope"] -> (reverse xs,Just "")
                    n : c : xs | tokenKind c == ":", simple n -> (reverse xs,Just (tokenText n))
                    _ -> (init rest,Nothing)
                (header,interpretation) = break ((== ":=") . tokenKind) before
                (selector,params,flags) = case header of
                    t:xs | tokenKind t == "string" -> (PatternSelector (tokenText t), filter patternName (words (tokenText t)), xs)
                    t:xs | simple t || tokenKind t == "qualid" -> let (ns, opts) = span simple xs in (AliasSelector (tokenText t),map tokenText ns,opts)
                    _ -> (EveryNotation,[],header)
                patternName n = entryName n && n /= "_"
                (rhs,options) = case interpretation of
                    [] -> ([],flags)
                    _:xs -> let (body,mods) = modifiers xs in (body, flags ++ mods)
            fields <- case options of
                [] -> Right []
                t:xs | tokenKind t == "(", not (null xs), tokenKind (last xs) == ")" -> Right (map (map tokenText) (groups (init xs)))
                _ | not (null interpretation), null flags -> Right (map (map tokenText) (groups options))
                _ -> Left (first options)
            let option prior field = do
                    (mode,many,entry) <- prior
                    case field of
                        ["only","parsing"] | mode == BothWays -> Right (ParsingOnly,many,entry)
                        ["only","printing"] | mode == BothWays -> Right (PrintingOnly,many,entry)
                        ["all"] | not many -> Right (mode,True,entry)
                        ["in","constr"] | entry == Nothing -> Right (mode,many,Just "")
                        ["in","custom",e] | entry == Nothing, Notation.entryName e -> Right (mode,many,Just (Notation.entryPath rules e))
                        _ -> Left (first options)
            (mode,many,entry) <- foldl option (Right (BothWays,False,Nothing)) fields
            unless (selector /= EveryNotation || scope /= Nothing || entry /= Nothing || many || not (null interpretation)) (Left (Just notation))
            let setting = Activation (tokenText verb == "Enable") mode many selector scope entry
            if null interpretation then Right (CScope location local (ToggleNotation setting)) else CSelectNotation location local setting params <$> parseRhs rhs
    op : attr : close : rest
        | tokenText op == "#[", tokenKind close == "]", tokenText attr `elem` ["add_top", "add_bottom"] -> do
            inner <- declaration rules rest
            case inner of
                CScope _ locality (BindScope name ReplaceScopes classes) ->
                    Right (CScope location (if local == DefaultSyntax then locality else local) (BindScope name (if tokenText attr == "add_top" then AddTop else AddBottom) classes))
                _ -> Left (Just attr)
    verb : scope : n : with : args
        | map tokenText [verb, scope, with] == ["Bind", "Scope", "with"], simple n, length args >= 2, tokenKind (last args) == "." -> do
            classes <- mapM scopeClass (init args)
            Right (CScope location local (BindScope (tokenText n) ReplaceScopes classes))
    [verb, custom, entry, n, dot]
        | map tokenText [verb, custom, entry, dot] == ["Declare","Custom","Entry","."], simple n ->
            Right (CScope location local (DeclareCustomEntry (tokenText n)))
    [verb, s, n, dot]
        | tokenText s == "Scope", simple n, tokenKind dot == "." -> do
            op <- case tokenText verb of
                "Declare" -> Right DeclareScope
                "Open" -> Right OpenScope
                "Close" -> Right CloseScope
                "Undelimit" -> Right UndelimitScope
                _ -> Left (Just verb)
            Right (CScope location local (op (tokenText n)))
    [verb, s, n, with, key, dot]
        | map tokenText [verb,s,with,dot] == ["Delimit","Scope","with","."], simple n, simple key ->
            Right (CScope location local (DelimitScope (tokenText n) (tokenText key)))
    cmd : name : tailTokens
        | tokenText cmd `elem` ["Abbreviation","Notation"], simple name -> do
            let (parameters, definition) = break ((== ":=") . tokenKind) tailTokens
            unless (all simple parameters && not (null definition) && tokenKind (last definition) == ".") (Left (Just name))
            let ns = map tokenText parameters
                (rhs, mods) = modifiers (init (drop 1 definition))
                option prior field = do
                    (use, scopes) <- prior
                    case field of
                        ["only","parsing"] | use == BothWays -> Right (ParsingOnly,scopes)
                        [v,"in","scope",sc] | v `elem` ns, Map.notMember v scopes -> Right (use, Map.insert v sc scopes)
                        _ -> Left (Just name)
            (use,scopes) <- foldl option (Right (BothWays,Map.empty)) (groupedVariables (map (map tokenText) (groups mods)))
            term <- parseRhs rhs
            let parts = AliasHead (tokenText name) : [AliasArg (Map.lookup v scopes) | v <- ns]
            Right (CRocqNotation location local parts 10 "left" Nothing ns use Nothing term)
    reserved : notation : lhs : rest
        | tokenText reserved == "Reserved", tokenText notation `elem` ["Notation","Infix"], tokenKind lhs == "string" -> do
            let synthetic kind = lhs { tokenText = kind, tokenKind = kind }
                patternToken = if tokenText notation == "Infix" then lhs { tokenText = unwords ["x",infixSymbol lhs,"y"] } else lhs
            declaration rules (take (length original - length input) original ++ [notation { tokenText = "Notation" },patternToken,synthetic ":=",synthetic "_"] ++ rest) >>= \command -> case command of
                CRocqNotation pos locality parts level assoc Nothing vars BothWays fmt rhs ->
                    Right (CRocqNotation (tokenSpan reserved <> pos) locality parts level assoc Nothing vars ReservedSyntax fmt rhs)
                _ -> Left (Just lhs)
    cmd : lhs : assign : rest
        | tokenText cmd `elem` ["Notation","Infix"], tokenKind lhs == "string", tokenKind assign == ":=", not (null rest), tokenKind (last rest) == "." -> do
            let (raw, scope) = case reverse (init rest) of
                    n : c : earlier | tokenKind c == ":", simple n -> (reverse earlier, Just (tokenText n))
                    _ -> (init rest, Nothing)
                (rhs, mods) = modifiers raw
                infix' = tokenText cmd == "Infix"
            (fmt, rawFields) <- formatOptions (groups mods)
            let fields = groupedVariables rawFields
            (destination, restFields) <- customOptions fields
            unless (not (all (flip elem restFields) [["only","parsing"],["only","printing"]])) (Left (Just lhs))
            (explicitLevel, assoc, mode, entries) <- foldOptions restFields
            let words' = if infix' then ["x", infixSymbol lhs, "y"] else words (tokenText lhs)
            (parts, names) <- if null words' && mode == PrintingOnly && Map.null entries then Right ([],[]) else patternWords lhs entries words'
            let closed = case parts of
                    Literal _ : _ -> case last parts of
                        Literal _ -> True
                        _ -> False
                    _ -> False
            let patternShape = map (mapRuleEntry (Notation.entryPath rules)) (maybe parts (\entry -> EntryRoot entry : parts) destination)
                previous = Notation.production rules patternShape
                assocIsGiven = any (elem "associativity") fields
                direction = if assocIsGiven then assoc else maybe assoc (\(SyntaxRule _ _ a _) -> a) previous
            level <- case explicitLevel of
                Just n -> Right n
                Nothing | Just (SyntaxRule _ n _ _) <- previous -> Right n
                Nothing | mode == PrintingOnly || closed || destination /= Nothing && length parts == 1 -> Right 0
                Nothing -> Left (Just lhs)
            let patternHome = fst (ruleEntry patternShape)
            unless (and [patternEntry patternHome kind == patternHome | PatternSlot kind _ (Just (-1)) <- patternShape]) (Left (Just lhs))
            let adjust (LevelSlot (-1)) = LevelSlot (max 0 (level - 1))
                adjust (RepeatSlot separator item) = RepeatSlot separator (adjust item)
                adjust (PatternSlot kind strict (Just (-1))) = PatternSlot kind strict (Just (max 0 (level - 1)))
                adjust (AsNameSlot strict e (Just (-1))) = AsNameSlot strict e (Just (max 0 (level - 1)))
                adjust (EntrySlot e (Just (-1))) = EntrySlot e (Just (max 0 (level - 1)))
                adjust other = other
                declared = case previous of
                    Just (SyntaxRule old _ _ _) -> zipWith inherit patternShape old
                    Nothing -> map adjust patternShape
                inherit TermSlot prior = prior
                inherit (RepeatSlot _ TermSlot) prior@RepeatSlot {} = prior
                inherit new _ = adjust new
            rawTerm <- parseRhs rhs
            spacing <- if infix' then Right Nothing else either (const (Left (Just lhs))) Right (Format.patternSpacing declared names (tokenText lhs))
            let body = if infix' then foldl application rawTerm [Term location (SName (Name location x)) | x <- names] else rawTerm
                output = if mode == ParsingOnly then Nothing else fmt <|> spacing <|> inheritedFormat previous
            Right (CRocqNotation location local declared level direction scope names mode output body)
    _ -> Left (first input)
    where
        (local,input) = splitLocal original
        location = tokenSpan (head original) <> tokenSpan (last original)
        first [] = Nothing
        first (x:_) = Just x
        simple = G.identifier . tokenKind
        scopeClass t = case tokenText t of
            "Sortclass" -> Right SortClass
            "Funclass" -> Right FunClass
            _ | simple t || tokenKind t == "qualid" -> Right (ReferenceClass (Name (tokenSpan t) (tokenText t)))
            _ -> Left (Just t)
        infixSymbol t
            | entryName (tokenText t) = "'" ++ tokenText t ++ "'"
            | otherwise = tokenText t
        parseRhs tokens = case G.runParser G.term (Notation.indexedGrammar rules) (ellipsis tokens) of
            Right (term, []) -> Right term
            Right (_, t:_) -> Left (Just t)
            Left err -> Left (G.problemToken err)
        -- The two dots are a notation iteration marker only on a RHS.
        ellipsis = mark False
        mark _ [] = []
        mark inside (t:ts)
            | tokenKind t == "..", inside = t { tokenKind = ")", tokenText = ")" } : mark False ts
            | tokenKind t == ".." = t { tokenKind = "(", tokenText = "(" } : t { tokenKind = "ident" } : mark True ts
            | otherwise = t : mark inside ts
        inheritedFormat (Just (SyntaxRule _ _ _ (RocqTarget _ _ _ body))) = fst (Template.printFormat body)
        inheritedFormat _ = Nothing
        formatOptions = foldr splitFormat (Right (Nothing, [])) where
            splitFormat field later = do
                (existing, fields) <- later
                case field of
                    [keyword, value] | tokenText keyword == "format", tokenKind value == "string", existing == Nothing ->
                        Right (Just (tokenText value), fields)
                    keyword : _ | tokenText keyword == "format" -> Left (Just keyword)
                    _ -> Right (existing, map tokenText field : fields)
        groupedVariables (([v]):rest) | entryName v, (group:more) <- groupedVariables rest, _ : op : _ <- group, op `elem` ["at","in"] = (v : tail group) : group : more
        groupedVariables (group:more) = group : groupedVariables more
        groupedVariables [] = []
        customOptions = foldr option (Right (Nothing, [])) where
            option field prior = do
                (selected, others) <- prior
                case field of
                    "in":"custom":name:level | selected == Nothing && Notation.entryName name && (null level || take 2 level == ["at","level"]) ->
                        Right (Just name, if null level then others else level:others)
                    "in":"custom":_ -> Left (first original)
                    _ -> Right (selected, field:others)
        entryName (c:cs) = Lex.identStart c && all Lex.identContinue cs
        entryName _ = False
        foldOptions = foldl step (Right (Nothing, "no", BothWays, Map.empty))
        step prior words' = do
            (level, assoc, usage, entries) <- prior
            case words' of
                [] -> prior
                ["at","level",n] | Just k <- number n -> Right (Just k, assoc, usage, entries)
                [a,"associativity"] | a `elem` ["left","right","no"] -> Right (level, a, usage, entries)
                ["only","parsing"] | usage == BothWays -> Right (level, assoc, ParsingOnly, entries)
                ["only","printing"] | usage == BothWays -> Right (level, assoc, PrintingOnly, entries)
                [x,"at","next","level"] -> Right (level, assoc, usage, Map.insert x (LevelSlot (-1)) entries)
                [x,"at","level",n] | Just k <- number n -> Right (level, assoc, usage, Map.insert x (LevelSlot k) entries)
                x : opts | (prefix,["as",kind]) <- break (== "as") opts, kind `elem` ["name","ident"] -> do
                    let (destination,rest) = case prefix of
                            "custom":e:xs -> (Just e,xs)
                            "constr":xs -> (Nothing,xs)
                            xs -> (Nothing,xs)
                    strength <- entryLevel rest
                    Right (level,assoc,usage,Map.insert x (AsNameSlot (kind == "ident") destination strength) entries)
                x : opts | Just patternSlot <- patternOption opts -> Right (level, assoc, usage, Map.insert x patternSlot entries)
                x : "custom" : name : rest | Notation.entryName name -> entrySlot prior x (Just name) rest
                x : "constr" : rest -> entrySlot prior x Nothing rest
                [x,"binder"] -> Right (level, assoc, usage, Map.insert x BinderSlot entries)
                [x,"ident"] -> Right (level, assoc, usage, Map.insert x NameSlot entries)
                [x,kind] | kind `elem` ["name","global","bigint"] -> Right (level, assoc, usage, Map.insert x (TokenSlot kind) entries)
                [x,"closed","binder"] -> Right (level, assoc, usage, Map.insert x (TokenSlot "closed binder") entries)
                _ -> Left (first original)
        patternOption opts = case opts of
            "pattern" : rest -> PatternSlot NativePattern False <$> nativeLevel rest
            "strict" : "pattern" : rest -> PatternSlot NativePattern True <$> nativeLevel rest
            _ -> case break (== "as") opts of
                (prefix, "as" : suffix) | suffix == ["pattern"] || suffix == ["strict","pattern"] -> do
                    let (kind, rest) = case prefix of
                            "custom" : e : xs | Notation.entryName e -> (OtherPattern (Just e), xs)
                            "constr" : xs -> (OtherPattern Nothing, xs)
                            xs -> (CurrentPattern, xs)
                    either (const Nothing) (Just . PatternSlot kind (length suffix == 2)) (entryLevel rest)
                _ -> Nothing
            where
                nativeLevel [] = Just Nothing
                nativeLevel ["at","level",n] = Just <$> number n
                nativeLevel _ = Nothing
        entrySlot prior x entry rest = do
            (level, assoc, usage, entries) <- prior
            strength <- entryLevel rest
            Right (level,assoc,usage,Map.insert x (EntrySlot entry strength) entries)
        entryLevel [] = Right Nothing
        entryLevel ["at","level",n] | Just value <- number n = Right (Just value)
        entryLevel ["at","next","level"] = Right (Just (-1))
        entryLevel _ = Left (first original)
        number s = do
            n <- readMaybe s
            if Notation.validLevel n then Just n else Nothing

-- A trailing group of production modifiers is separate from a parenthesized
-- RHS. Looking for balanced delimiters preserves nested casts and binders.
modifiers :: [Token] -> ([Token], [Token])
modifiers tokens = case reverse tokens of
    close : rev | tokenKind close == ")" -> findGroup (1 :: Int) [] rev
    _ -> (tokens,[])
    where
        isOption xs = any (option . map tokenText) (groups xs)
        option ["all"] = True
        option ["in","constr"] = True
        option (kw : _) | kw `elem` ["at","only","format"] = True
        option ["in","custom",_] = True
        option ("in":"custom":_:"at":_) = True
        option [dir,"associativity"] = dir `elem` ["left","right","no"]
        option (_:kind:_) = kind `elem` ["at","in","as","ident","name","pattern","strict","closed","binder","global","bigint","custom","constr"]
        option _ = False
        findGroup _ _ [] = (tokens,[])
        findGroup depth inside (t:ts) = case tokenKind t of
            "(" | depth == 1, not (null ts), isOption inside -> (reverse ts, inside)
                | depth == 1 -> (tokens,[])
                | otherwise -> findGroup (depth-1) (t:inside) ts
            ")" -> findGroup (depth+1) (t:inside) ts
            _ -> findGroup depth (t:inside) ts

groups :: [Token] -> [[Token]]
groups [] = []
groups xs = let (a,b) = break ((== ",") . tokenKind) xs in a : groups (drop 1 b)

patternWords :: Token -> Map.Map String RulePart -> [String] -> Result ([RulePart], [String])
patternWords at options words' = do
    (parts,names) <- walk words'
    unless (length names == length (nub names) && all (`elem` names) (Map.keys options) && not (null parts)) bad
    Right (parts,names)
    where
        bad = Left (Just at)
        identifier [] = False
        identifier (c:cs) = Lex.identStart c && all Lex.identContinue cs && (c:cs) /= "_"
        walk [] = Right ([],[])
        walk (x:rest)
            | identifier x
            , (separators, "..":afterDots) <- break (== "..") rest
            , all (not . identifier) separators
            , Just (y:after) <- stripPrefix separators afterDots
            , identifier y = do
                let first = Map.lookup x options
                    lastItem = Map.lookup y options
                    item = maybe TermSlot id (first <|> lastItem)
                unless (repeatOperand item && (first == Nothing || lastItem == Nothing || first == lastItem)) bad
                (parts,ns) <- walk after
                Right (RepeatSlot (unwords (map literal separators)) item : parts, x : y : ns)
        walk (s:rest) = do
            (parts,ns) <- walk rest
            if identifier s then Right (Map.findWithDefault TermSlot s options : parts, s:ns)
            else if s == ".." then bad else Right (Literal (literal s):parts,ns)
        literal s = case stripPrefix "'" s of
            Just suffix | not (null suffix), last suffix == '\'' -> init suffix
            _ -> s
