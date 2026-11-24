module LoL.Front.Unnotation where

import Control.Applicative ((<|>))
import Control.Monad (foldM, guard)
import Data.Functor.Const (Const (..))
import Data.List (elemIndex, find, partition)
import qualified Data.Map.Strict as Map
import Data.Maybe (mapMaybe)
import Data.Monoid (Any (..))
import qualified Data.Set as Set
import qualified LoL.Core as C
import qualified LoL.Env as Env
import qualified LoL.Front.ArgumentScopes as ArgumentScopes
import LoL.Front.Syntax
import qualified LoL.Front.Template as Template

-- An operand lives under the binders through which its RHS was matched.
-- Keep those hints for the regular printer, which allocates fresh names.
type Path = [String]
data Operand = Operand Bool Path [String] C.Term | BinderName Path C.Term | ConstructorBinder Path C.Global Int [(String, Bool)] | DummyBinder deriving (Eq)
data Chunk = RepeatLength Int | Word String | Slot (Maybe String) Integer (Maybe String) Operand | BinderSlotText Bool Operand | RefSlotText Operand | PatternSlotText (Maybe String) Integer Bool Operand
data Choice = Choice (SyntaxRule C.Global) (Maybe (String, String))

choices :: Env.Syntax -> [Choice]
choices syntax = available ++ delimited where
    rules = unique Set.empty (Env.syntaxHistory syntax)
    unique _ [] = []
    unique seen (Right rule : rest)
        | Set.notMember rule seen = rule : unique (Set.insert rule seen) rest
    unique seen (_ : rest) = unique seen rest
    (available, delimited) = partition direct (mapMaybe choose rules)
    direct (Choice _ key) = key == Nothing
    choose rule@(SyntaxRule parts _ _ (RocqTarget scope _ mode _))
        | (mode /= BothWays && mode /= PrintingOnly) || not (Env.enabledFor syntax PrintingOnly rule) = Nothing
        | AliasHead alias : _ <- parts = if Map.lookup alias (Env.syntaxAliases syntax) == Just rule then Just (Choice rule Nothing) else Nothing
        | (mode == PrintingOnly || not (Env.enabledFor syntax ParsingOnly rule)) && maybe True (`elem` Env.syntaxOpen syntax) scope = Just (Choice rule Nothing)
        | Env.activeInterpretation syntax parts == Just rule = Just (Choice rule Nothing)
        | Just owner <- scope, mode == PrintingOnly || Env.activeInterpretation (open owner syntax) parts == Just rule
        , Just key <- Env.scopeDelimiter syntax owner, Map.lookup key (Env.syntaxKeys syntax) == Just owner = Just (Choice rule (Just (owner, key)))
    choose _ = Nothing

-- A custom entry has no built-in parentheses. When parentheses were
-- actually declared as an identity production, the printer can use them
-- without recursively trying that identity interpretation on the same term.
parentheses :: Env.Syntax -> String -> Integer -> Integer -> Bool
parentheses syntax entry limit child = any accepts (Env.syntaxRules syntax) where
    accepts rule@(SyntaxRule parts level _ (RocqTarget _ [variable] use source))
        | (Just target, [Literal "(", slot, Literal ")"]) <- ruleEntry parts
        , target == entry, level <= limit, use /= PrintingOnly, Env.activeInterpretation syntax parts == Just rule
        , TVariable operand <- snd (Template.printFormat source), variable == operand = case slot of
            TermSlot -> True
            LevelSlot n -> child <= n
            EntrySlot (Just e) bound -> e == entry && maybe True (child <=) bound
            _ -> False
    accepts _ = False

open :: String -> Env.Syntax -> Env.Syntax
open owner syntax = syntax { Env.syntaxHistory = Left (OpenScope owner) : Env.syntaxHistory syntax, Env.syntaxOpen = owner : Env.syntaxOpen syntax }

type Captures = Map.Map String [Operand]

match :: Env.Syntax -> SyntaxRule C.Global -> C.Term -> Maybe [Chunk]
match syntax (SyntaxRule allParts level assoc (RocqTarget _ variables _ source)) original = do
    guard (root /= TSort "_" || entry /= Nothing && original == C.Hole 0)
    (shape,_) <- plan
    walk [] True shape original >>= finish
    where
        (_, root) = Template.printFormat source
        (entry, parts) = ruleEntry allParts
        finish found = spell found True parts variables
        patterns = Map.fromList [(key, (mode /= NativePattern, strict)) | (key, PatternSlot mode strict _) <- zip variables (expandParts parts)]
        expandParts (Literal _ : rest) = expandParts rest
        expandParts (AliasHead _ : rest) = expandParts rest
        expandParts (p@RepeatSlot {} : rest) = p : p : expandParts rest
        expandParts (p : rest) = p : expandParts rest
        expandParts [] = []
        policies = Map.fromList [(key, ss) | (keys, ss) <- zip (operands parts variables) (ArgumentScopes.slotPolicies allParts variables source), key <- keys]
        operands (AliasHead _ : rest) ns = operands rest ns
        operands (Literal _ : rest) ns = operands rest ns
        operands (RepeatSlot _ _ : rest) (x : y : ns) = [x, y] : operands rest ns
        operands (_ : rest) (x : ns) = [x] : operands rest ns
        operands _ _ = []
        plan = either (const Nothing) Just (Template.iterationPlan (Template.rangeNames parts variables) root)
        iterator key = snd <$> (plan >>= Map.lookup key . snd)
        extract range key found = do
            item <- Map.lookup key found
            let tailItems = Map.findWithDefault [] range found
            return (Map.insert range (item ++ tailItems) (Map.delete key found))
        bind key value = Map.singleton key [value]
        combine left right = do
            guard (and (Map.intersectionWith (==) left right))
            return (Map.union left right)
        collect = foldr (\r rest -> r >>= \a -> rest >>= combine a) (Just Map.empty)
        walk bound same template term = case (template, term) of
            (TVariable key@('#':_), _) | Just it <- iterator key ->
                (walk bound same (Template.iterStep it) term >>= extract key (Template.iterFirst it))
                <|> (walk bound same (Template.iterBase it) term >>= extract key (Template.iterLast it))
            (TVariable key, _)
                | Just i <- elemIndex key (map fst bound) -> guard (term == C.Var i) >> return Map.empty
                | key `elem` variables, not (captured bound term) -> return (bind key (Operand same (path bound) (Map.findWithDefault [] key policies) term))
            (TUniverse patternLevel, C.Type level) | levelMatches patternLevel level -> return Map.empty
            (TInstance _ g levels, _) | global term == Just g, Just actual <- universes term
                , length levels == length actual && and (zipWith levelMatches levels actual) -> return Map.empty
            (TCase subject alias family motive arms, C.Case b i _ params hints result value branches) -> do
                guard (not (null hints))
                -- A nondependent motive is normally omitted as Rocq renders
                -- its case expression. Never discard a dependent motive.
                let dependent = captured (replicate (length hints) ("", "")) result
                guard (maybe (not dependent) (const dependent) motive)
                let parameters = length params
                    owner = C.GlobalInd b i
                indices <- case family of
                    Nothing -> Just (replicate (length hints - 1) "")
                    Just (ConstructorPattern explicit g ns) | g == owner -> patternNames explicit g parameters ns
                    _ -> Nothing
                (inner, binders) <- introduce bound (indices ++ [maybe "" id alias]) hints
                let pick j = find (namesArm (C.GlobalCon b i j)) arms <|> find wildcard arms
                    branch j (names, body) | Just (TemplateBranch (VariablePattern key) rhs) <- pick j = do
                        guard (Map.member key patterns)
                        let usage = zip names [uses k body | k <- reverse [0 .. length names - 1]]
                            operand = ConstructorBinder (path bound) (C.GlobalCon b i j) parameters usage
                            scope = reverse (map ((,) "#field") names) ++ bound
                        collect [Just (bind key operand), walk scope False rhs body]
                    branch j (names, body) = do
                        TemplateBranch arm rhs <- pick j
                        labels <- case arm of
                            AnyPattern -> Just (replicate (length names) "")
                            VariablePattern _ -> Nothing
                            ConstructorPattern explicit g ns -> patternNames explicit g parameters ns
                        (below, named) <- introduce bound labels names
                        combine named =<< walk below False rhs body
                guard (all (applies b i (length branches)) arms)
                collect (Just binders : walk bound False subject value : maybe (Just Map.empty) (\r -> walk inner False r result) motive : zipWith branch [0 ..] branches)
            (TFix declared chosen, C.Fix index functions) -> do
                let labels = [n | TemplateFunction n _ _ _ _ <- declared]
                guard (length declared == length functions && case chosen of
                    Nothing -> length functions == 1 && index == 0
                    Just name -> elemIndex name labels == Just index)
                (recursive, named) <- introduce bound labels (map C.functionName functions)
                let function (TemplateFunction _ groups decreasing result rhs) actual = do
                        let variables' = [n | (_, ns, _) <- groups, n <- ns]
                            close product' = foldr (\(impl, ns, ty) body -> foldr (\n -> TAbstraction product' impl n ty) body ns)
                        guard (maybe True (\n -> elemIndex n variables' == Just (C.functionArgN actual)) decreasing)
                        collect [walk bound False (close True result groups) (C.functionType actual), walk recursive False (close False rhs groups) (C.functionBody actual)]
                collect (Just named : zipWith function declared functions)
            (TProjection receiver (C.GlobalProj b i), C.Proj c j value)
                | b == c && i == j -> walk bound False receiver value
            (TReference _ g, _) | global term == Just g -> return Map.empty
            (TApply {}, _) -> case (applications template [], arguments term []) of
                ((TReference explicit g, patterns), (headTerm, args)) | global headTerm == Just g -> do
                    let actual = if explicit then args else visible (Map.findWithDefault [] g (Env.syntaxArguments syntax)) args
                    guard (length patterns == length actual)
                    collect (zipWith (walk bound False) patterns actual)
                _ -> case (template, term) of
                    (TApply f x, C.App g y) -> collect [walk bound False f g, walk bound False x y]
                    _ -> Nothing
            (TAbstraction True _ key ty body, C.Pi hint a b) -> binder bound key hint ty a body b
            (TAbstraction False _ key ty body, C.Lam hint a b) -> binder bound key hint ty a body b
            (TLet key ty value body, C.Let hint assigned annotation inner) -> collect [walk bound False value assigned, binder bound key hint ty annotation body inner]
            (TArrow a b, C.Pi hint x y) -> collect [walk bound False a x, walk (("", hint) : bound) False b y]
            (TCast a b, C.Cast x y) -> collect [walk bound False a x, walk bound False b y]
            (TSort "_", _) -> return Map.empty
            (TSort "Prop", C.Prop) -> return Map.empty
            (TSort "Set", C.Type (C.Closed 0)) -> return Map.empty
            (TSort "Type", C.Type _) -> return Map.empty
            (TSort s, C.Type (C.Closed n)) | s == "Type@" ++ show n -> return Map.empty
            (TNumber n, _) | Just (zero, successor) <- Env.syntaxNumerals syntax, numeral zero successor n term -> return Map.empty
            _ -> Nothing
        introduce bound labels hints = do
            guard (length labels == length hints)
            foldM add (bound, Map.empty) (zip labels hints)
            where
                add (outer, seen) pair@(key, _) = do
                    let inner = pair : outer
                    named <- if key `elem` variables then combine seen (bind key (BinderName (path inner) (C.Hole 0))) else Just seen
                    return (inner, named)
        patternNames explicit g parameters written = do
            let flags = if explicit then [] else Map.findWithDefault [] g (Env.syntaxArguments syntax)
                fill [] ns = Just ns
                fill (True : fs) ns = ("" :) <$> fill fs ns
                fill (False : fs) (n : ns) = (n :) <$> fill fs ns
                fill _ [] = Nothing
            expanded <- fill flags written
            guard (length expanded >= parameters && all (\s -> null s || s == "_") (take parameters expanded))
            return (drop parameters expanded)
        namesArm g (TemplateBranch (ConstructorPattern _ r _) _) = r == g
        namesArm _ _ = False
        wildcard (TemplateBranch AnyPattern _) = True
        wildcard (TemplateBranch (VariablePattern _) _) = True
        wildcard _ = False
        applies b i count (TemplateBranch (ConstructorPattern _ (C.GlobalCon c j k) _) _) = b == c && i == j && k >= 0 && k < count
        applies _ _ _ arm = wildcard arm
        path = reverse . map snd
        binder bound key hint annotation domain body inner = do
            let below = (key, hint) : bound
                normal = do
                    guard (Map.lookup key patterns /= Just (False, True))
                    let operand = if Map.member key patterns && not (uses 0 inner) then DummyBinder else BinderName (path below) domain
                    collect [Just (if key `elem` variables then bind key operand else Map.empty), walk below False body inner]
            -- Core has no surface pattern-lambda marker. Rocq's printer
            -- after Compute treats its resulting lambda and case separately.
            collect [maybe (Just Map.empty) (\a -> walk bound False a domain) annotation, normal]
        uses index = descend 0 where
            descend depth (C.Var i) = i == depth + index
            descend depth value = getAny (getConst (C.descend (\d sub -> Const (Any (descend d sub))) depth value))
        -- Fixed RHS binders have no corresponding name in the notation.
        -- A captured operand referring to one would escape on re-reading.
        captured bound
            | Set.null hidden = const False
            | otherwise = used 0
            where
                hidden = Set.fromList [index | (index, (key, _)) <- zip [0 ..] bound, key /= "#field", key `notElem` variables]
                used depth (C.Var i) = Set.member (i - depth) hidden
                used depth value = getAny (getConst (C.descend (\d t -> Const (Any (used d t))) depth value))
        visible [] xs = xs
        visible _ [] = []
        visible (implicit : rest) (x : xs)
            | implicit = visible rest xs
            | otherwise = x : visible rest xs
        applications (TApply f x) xs = applications f (x : xs)
        applications f xs = (f, xs)
        arguments (C.App f x) xs = arguments f (x : xs)
        arguments f xs = (f, xs)
        universes term = case term of
            C.Cst _ us -> Just us
            C.Ind _ _ us -> Just us
            C.Con _ _ _ us -> Just us
            C.PField _ _ us -> Just us
            _ -> Nothing
        levelMatches patternLevel actual = case (patternLevel, actual) of
            (UHole, _) -> True
            (UNumber n, C.Closed m) -> n == m
            (UOffset base n, _) | n >= 0 -> offset base n actual
            (UMaximum a b, C.Maximum x y) -> levelMatches a x && levelMatches b y
            _ -> False
        offset base 0 actual = levelMatches base actual
        offset base n (C.Successor inner) = offset base (n - 1) inner
        offset (UNumber m) n (C.Closed k) = m + n == k
        offset _ _ _ = False
        numeric zero suc n (C.App f t) | global f == Just suc = numeric zero suc (n + 1) t
        numeric zero _ n t | global t == Just zero = Just n
        numeric _ _ _ _ = Nothing
        numeral zero _ 0 t = global t == Just zero
        numeral zero suc n (C.App headTerm arg) = n > 0 && global headTerm == Just suc && numeral zero suc (n - 1) arg
        numeral _ _ _ _ = False
        spell _ _ [] [] = Just []
        spell found _ (AliasHead name : rest) ns = (Word name :) <$> spell found False rest ns
        spell found _ (Literal word : rest) ns = (Word word :) <$> spell found False rest ns
        spell found _ (RepeatSlot sep operand : rest) (x : _ : ns) = do
            (_, iterations) <- plan
            let occurrences = [(marker,it) | (marker,(name,it)) <- Map.toList iterations, name == x]
                recover (marker,it) = do
                    values <- Map.lookup marker found
                    return (if Template.iterReverse it then reverse values else values)
            firstUse : otherUses <- mapM recover occurrences
            guard (all (== firstUse) otherUses)
            let allValues = firstUse
            suffixChunks <- spell found False rest ns
            case allValues of
                first : more -> do
                    let item = case operand of
                            BinderSlot -> BinderSlotText True
                            TokenSlot "closed binder" -> BinderSlotText True
                            LevelSlot n -> Slot entry n Nothing
                            EntrySlot dest bound -> Slot dest (maybe 200 id bound) Nothing
                            _ -> Slot entry 200 Nothing
                        separator = map Word (words sep)
                    return (RepeatLength (length allValues) : item first : concatMap (\next -> separator ++ [item next]) more ++ suffixChunks)
                [] -> Nothing
        spell found initial (part : rest) (key : ns) = do
            [value] <- Map.lookup key found
            let target = case part of
                    EntrySlot other _ -> other
                    _ -> entry
            let (limit, side) = case part of
                    AliasArg {} -> (9, Nothing)
                    LevelSlot strength -> (strength, Nothing)
                    EntrySlot _ (Just strength) -> (strength, Nothing)
                    _
                        | target /= entry -> (200, Nothing)
                        | initial -> (level, Just "left")
                        | Literal _ : _ <- rest -> (200, Nothing)
                        | otherwise -> (level, Just "right")
                peer = if side == Just assoc then side else Nothing
                strength = if side /= Nothing && peer == Nothing then limit - 1 else limit
                chunk = case part of
                    PatternSlot mode _ bound -> PatternSlotText (patternEntry entry mode) (maybe strength id bound) (maybe (mode == NativePattern) (< 10) bound) value
                    BinderSlot -> BinderSlotText True value
                    NameSlot -> BinderSlotText False value
                    AsNameSlot {} -> BinderSlotText False value
                    TokenSlot "name" -> BinderSlotText False value
                    TokenSlot "global" -> RefSlotText value
                    TokenSlot "closed binder" -> BinderSlotText True value
                    _ -> Slot target strength peer value
            case (part, value, Env.syntaxNumerals syntax) of
                (TokenSlot "bigint", Operand _ _ _ number, Just (zero, successor)) -> do
                    n <- numeric zero successor (0 :: Integer) number
                    (Word (show n) :) <$> spell found False rest ns
                (TokenSlot "bigint", _, _) -> Nothing
                _ -> (chunk :) <$> spell found False rest ns
        spell _ _ _ _ = Nothing
match _ _ _ = Nothing

global :: C.Term -> Maybe C.Global
global term = case term of
    C.Cst c _ -> Just (C.GlobalCst c)
    C.Ind b i _ -> Just (C.GlobalInd b i)
    C.Con b i j _ -> Just (C.GlobalCon b i j)
    C.PField b i _ -> Just (C.GlobalProj b i)
    _ -> Nothing
