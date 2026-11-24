module LoL.Pretty where

import Control.Applicative ((<|>))
import Data.Char (isAsciiLower, isAsciiUpper, isDigit)
import Data.List (mapAccumL, sortOn)
import qualified Data.IntMap.Strict as IntMap
import qualified Data.IntSet as IntSet
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import LoL.Core
import qualified LoL.Env as Env
import qualified LoL.Front.ArgumentScopes as ArgumentScopes
import qualified LoL.Front.Format as Format
import qualified LoL.Front.Template as Template
import qualified LoL.Front.HostLexer as HostLexer
import qualified LoL.Front.Syntax as Syntax
import qualified LoL.Front.Unnotation as Unnotation
import Data.Maybe (fromMaybe, listToMaybe, mapMaybe)

-- The keywords of Rocq 9.2.0 under -noinit, as its Print Keywords lists them,
-- and Inline, which Axiom reads as an option of its own.
rocqKeywords :: Set.Set String
rocqKeywords = Set.fromList (words "Axiom CoFixpoint Definition Fixpoint Hypothesis Inline Parameter Prop SProp Set Theorem Type Variable as at cofix else end fix for forall fun if in let match return then where with")

keywords :: Set.Set String
keywords = Set.fromList (words "Arguments Axiom Check Compute Definition Fixpoint Import Inductive Infix Lemma Numerals Polymorphic Print Prop Set Theorem Type as end fix for forall fun in let match return struct with")

identifier :: String -> Bool
identifier name = name /= "_" && Set.notMember name keywords && case name of
    first : rest -> HostLexer.identStart first && all HostLexer.identContinue rest
    [] -> False

qualified :: String -> Bool
qualified name = all identifier (components name) where
    components input = case break (== '.') input of
        (first, []) -> [first]
        (first, _ : rest) -> first : components rest

-- The names in scope: the name of each binder by its level, every name in use,
-- and for each base name the first suffix that may still be free.
data Names
    = Names
        { namesTable :: IntMap.IntMap String
        , namesTaken :: Set.Set String
        , namesNexts :: Map.Map String Int
        }
    deriving ()

-- A printed term: 0 an atom, 1 an application, 2 an arrow, 3 a term that
-- extends to the right. pieceFree has the levels of its free variables.
data Piece
    = Piece
        { pieceRank :: Int
        , pieceFree :: IntSet.IntSet
        , pieceDoc  :: Format.Doc
        , pieceUniv :: Integer
        }
    deriving ()

pieceText :: Piece -> ShowS
pieceText = Format.output . pieceDoc

-- Rocq: every product is a forall, and a sort is Set or a named universe.
data Style
    = Surface
    | Rocq
    deriving (Eq, Show)

-- What a printer is told: the name of a global, the number of parameters of
-- an inductive block, and the names that a binder does not take.
data Naming
    = Naming
        { namingGlobal     :: Global -> Maybe String
        , namingParams     :: ConstId -> Int
        , namingBanned     :: String -> Bool
        , namingLiteral    :: String -> Bool
        , namingAtMark     :: Global -> Bool
        , namingInMark     :: ConstId -> Int -> Bool
        , namingTemplate   :: ConstId -> Bool
        , namingLevelHints :: ConstId -> [String]
        , namingUniverses  :: [String]
        , namingLocalBlock :: Maybe ConstId
        }
    deriving ()

-- A term at a depth with the names of the binders above it, a new binder, and
-- why a term has no spelling.
data Printer
    = Printer
        { printerShow :: Int -> Names -> Term -> Piece
        , printerBind :: Int -> Names -> Hint -> (String, Names)
        , printerFail :: Int -> Term -> Maybe String
        }
    deriving ()

globalName :: Env.Env -> Global -> Maybe String
globalName env global
    = case original of
        Just name
            | Map.lookup name (Env.envNames env) == Just global -> Just name
        _ -> case sortOn (\name -> (length name, name)) [name | (name, found) <- Map.toList (Env.envNames env), found == global] of
            name : _ -> Just name
            [] -> original
    where
        original = case global of
            GlobalCst c -> Env.entryName <$> Map.lookup c (Env.envDecls env)
            GlobalInd b i -> Env.familyName <$> family b i
            GlobalProj b field -> family b 0 >>= Env.familyRecord >>= at field . Env.recordFields
            GlobalCon b i j -> family b i >>= \found -> fst <$> at j (Env.familyCons found)
        family b i = case Map.lookup b (Env.envDecls env) of
            Just (Env.Entry { Env.entryDecl = Env.Inductive _ families }) -> at i families
            _ -> Nothing
        at place items = if 0 <= place && place < length items then Just (items !! place) else Nothing

parametersOf :: Env.Env -> ConstId -> Int
parametersOf env b
    = case Map.lookup b (Env.envDecls env) of
        Just (Env.Entry { Env.entryDecl = Env.Inductive count _ }) -> count
        _ -> 0

-- A binder does not get a name of the environment, nor a short name that is
-- ambiguous there because several constructors have it: a pattern reads
-- neither as a variable.
naming :: Env.Env -> Naming
naming env = Naming { namingGlobal = globalName env, namingParams = parametersOf env, namingBanned = banned, namingLiteral = (`Set.member` literals), namingAtMark = explicit, namingInMark = familyNeedsIn env, namingTemplate = templateIn (Env.envDecls env), namingLevelHints = levelHints (Env.envDecls env), namingUniverses = [], namingLocalBlock = Nothing } where
    -- The explicit reader sees imported notation. A binder must stay an
    -- identifier in every occurrence; @ escapes a global of the same name.
    literals = Env.notationWords (Env.envSyntax env)
    banned name = Map.member name (Env.envNames env) || Set.member name (Env.envAmbiguous env) || Set.member name literals
    explicit global = or (Map.findWithDefault [] global (Env.envArguments env)) || not (Set.null literals) && maybe False ((`Set.member` literals) . short) (globalName env global)
    short name = case break (== '.') name of
        (_, '.' : rest) -> short rest
        _ -> name

levelHints :: Map.Map ConstId Env.Entry -> ConstId -> [String]
levelHints entries b = maybe [] (universeNames . Env.entryUniverses) (Map.lookup b entries)

templateIn :: Map.Map ConstId Env.Entry -> ConstId -> Bool
templateIn entries block = case Env.entryDecl <$> Map.lookup block entries of
    Just (Env.Inductive _ families) -> any Env.familyTemplate families
    _ -> False

-- An explicit reader cannot count indices through a type alias. The Core
-- motive already gives that count, so retain its otherwise unused binders.
familyNeedsIn :: Env.Env -> ConstId -> Int -> Bool
familyNeedsIn env block index = case Map.lookup block (Env.envDecls env) of
    Just (Env.Entry { Env.entryDecl = Env.Inductive _ families })
        | index >= 0 && index < length families -> not (visible (Env.familyType (families !! index)))
    _ -> False
    where
        visible (Pi _ _ body) = visible body
        visible Prop = True
        visible (Type _) = True
        visible _ = False

term :: Env.Env -> Term -> Either String String
term env = renderTerm (naming env)

-- Constants alone, by a table of their names.
termWithNames :: Map.Map ConstId String -> Term -> Either String String
termWithNames names = renderTerm (Naming { namingGlobal = constant, namingParams = const 0, namingBanned = (`Set.member` unavailable), namingLiteral = const False, namingAtMark = const False, namingInMark = \_ _ -> False, namingTemplate = const False, namingLevelHints = const [], namingUniverses = [], namingLocalBlock = Nothing }) where
    unavailable = Set.fromList (Map.elems names)
    constant global = case global of
        GlobalCst c -> Map.lookup c names
        _ -> Nothing

renderTerm :: Naming -> Term -> Either String String
renderTerm names input = snd <$> renderWith Surface names input

renderWith :: Style -> Naming -> Term -> Either String (Integer, String)
renderWith style names input = maybe (Right (pieceUniv output, pieceText output "")) Left (printerFail printer 0 input) where
    printer = printerOf style names
    output = printerShow printer 0 noNames input

-- Diagnostics may contain the free locals of the rejected rule. The hints
-- are in de Bruijn-index order; normal declaration printing remains closed.
renderOpen :: Naming -> [Hint] -> Term -> Either String String
renderOpen names hints = renderClosure names hints []

renderClosure :: Naming -> [Hint] -> [Hint] -> Term -> Either String String
renderClosure names free bound input = maybe (Right (prefix . abstraction . pieceText output $ "")) Left (printerFail printer depth input) where
    printer = printerOf Surface names
    depth = length free + length bound
    (scope, given) = mapAccumL (\inner (level, hint) -> let (name, next) = printerBind printer level inner hint in (next, name)) noNames (zip [0 ..] (reverse free ++ bound))
    output = printerShow printer depth scope input
    prefix = if null free then id else showString "under free names [" . showString (unwords (take (length free) given)) . showString "]: "
    abstraction = if null bound then id else showString "fun " . showString (unwords (drop (length free) given)) . showString " => "

noNames :: Names
noNames = Names IntMap.empty Set.empty Map.empty

closedUniversePeak :: Level -> Integer
closedUniversePeak = walk 0 where
    walk offset level = case level of
        Closed number -> number + offset
        DefaultLevel {} -> 0
        Parameter _ -> 0
        Successor inner -> walk (offset + 1) inner
        Maximum left right -> max (walk offset left) (walk offset right)

printableLevel :: Naming -> Level -> Bool
printableLevel names level = case level of
    Closed number -> number >= 0
    DefaultLevel owner slot -> slot >= 0 && maybe False (const True) (namingGlobal names (GlobalInd owner 0))
    Parameter index -> index >= 0 && index < length (namingUniverses names)
    Successor inner -> printableLevel names inner
    Maximum left right -> printableLevel names left && printableLevel names right

printableInstance :: Naming -> Level -> Bool
printableInstance names level = case level of
    Closed {} -> printableLevel names level
    DefaultLevel {} -> printableLevel names level
    Parameter {} -> printableLevel names level
    _ -> False

-- Distribute printed offsets over max because Rocq's sort grammar accepts
-- max(u+1,v+1), but not max(u,v)+1. This is syntax transport, not a judgment.
levelText :: Style -> Naming -> Level -> ShowS
levelText style names level = combine (parts 0 level) where
    parts offset expression = case expression of
        Successor inner -> parts (offset + 1) inner
        Maximum left right -> parts offset left ++ parts offset right
        Closed number -> [atom (Closed (number + offset))]
        _ -> [atom expression . if offset == 0 then id else showChar '+' . shows offset]
    atom (Closed number)
        | style == Surface = shows number
        | number == 0 = showString "Set"
        | otherwise = showChar 'L' . shows number
    atom (DefaultLevel owner slot) = showString (maybe "unknown" id (namingGlobal names (GlobalInd owner 0))) . showChar '.' . showString (maybe ("u" ++ show slot) id (lookup slot (zip [0 ..] (templateHints style (namingLevelHints names owner)))))
    atom (Parameter index) = showString (case drop index (namingUniverses names) of
        hint : _ | index >= 0 -> hint
        _ -> "u" ++ show index)
    atom _ = id
    combine [] = id
    combine [single] = single
    combine (first : rest)
        | style == Surface = showString "max(" . first . showChar ',' . combine rest . showChar ')'
        | otherwise = showString "max(" . first . foldr (.) id [showChar ',' . next | next <- rest] . showChar ')'

-- Rocq writes a level in an instance, and no expression. A term that has an
-- expression there has no spelling of Rocq (printerOf): the export gives
-- the expression a universe of its own first (Export.Rocq.prepareEntries),
-- and nothing writes a hole for it, which Rocq would fill as it likes.
instanceText :: Style -> Naming -> UniverseInstance -> ShowS
instanceText _ _ [] = id
instanceText style names instance_ = showString "@{" . foldr1 (\left right -> left . showChar ' ' . right) (map (levelText style names) instance_) . showChar '}'

universeHints :: Naming -> [Hint] -> [String]
universeHints names = chooseUniverseHints (\name -> namingBanned names name || levelAlias name)

-- Template slots are visible as Owner.slot. Their rendered names depend
-- only on the defining header and the target language, including on import.
templateHints :: Style -> [Hint] -> [String]
templateHints Surface = chooseUniverseHints (const False)
templateHints Rocq = chooseUniverseHints (\name -> Set.member name rocqKeywords || levelAlias name)

levelAlias :: String -> Bool
levelAlias ('L' : digits) = not (null digits) && all isDigit digits
levelAlias _ = False

chooseUniverseHints :: (String -> Bool) -> [Hint] -> [String]
chooseUniverseHints reserved hints = snd (mapAccumL choose Set.empty (zip [0 :: Int ..] hints)) where
    choose taken (index, hint) = (Set.insert fresh taken, fresh) where
        base = if identifier hint then hint else "u" ++ show index
        fresh = head [candidate | suffix <- [0 :: Int ..], let candidate = if suffix == 0 then base else base ++ "_" ++ show suffix, not (reserved candidate), Set.notMember candidate taken]

universeHeader :: Style -> Naming -> UniverseContext -> Either String ShowS
universeHeader _ _ context
    | context == emptyUniverses = Right id
universeHeader style names context = do
    constraints <- mapM (universeRelation style names) (universeConstraints context)
    return (showString "@{" . showString (unwords (namingUniverses names)) . relations constraints . showChar '}')
    where
        -- Without the explicit bar Rocq may silently strengthen the context.
        relations [] = if style == Rocq then showString " | " else id
        relations constraints = showString " | " . foldr1 (\left right -> left . showString ", " . right) constraints

universeRelation :: Style -> Naming -> UniverseConstraint -> Either String ShowS
universeRelation style names constraint = case constraint of
    UniverseLe (Successor left) right -> atomic left " < " right
    UniverseLe left right -> atomic left " <= " right
    UniverseEq left right -> atomic left " = " right
    where
        -- LoL writes a left side that is some steps above a level, `u+1 < v`
        -- (a proof may need it of the universes of its theorem). Rocq has no
        -- such constraint.
        atomic left operator right
            | printableInstance names (below left) && printableInstance names right && (style == Surface || printableInstance names left) = Right (levelText style names left . showString operator . levelText style names right)
            | otherwise = Left "an algebraic universe constraint has no supported declaration spelling"
        below level = case level of
            Successor inner -> below inner
            _ -> level

termWithUniverses :: Env.Env -> UniverseContext -> Term -> Either String String
termWithUniverses env = renderUniverses env (printerOf Surface)

displayTerm :: Env.Env -> Term -> Either String String
displayTerm env = displayTermWithUniverses env emptyUniverses

displayTermWithUniverses :: Env.Env -> UniverseContext -> Term -> Either String String
displayTermWithUniverses env = renderUniverses env (displayPrinter env)

renderUniverses :: Env.Env -> (Naming -> Printer) -> UniverseContext -> Term -> Either String String
renderUniverses env makePrinter context value = do
    header <- universeHeader Surface names context
    let printer = makePrinter names
    body <- maybe (Right (pieceText (printerShow printer 0 noNames value) "")) Left (printerFail printer 0 value)
    return ((if context == emptyUniverses then id else showString "(* Universes " . header . showString ". *)\n") . showString body $ "")
    where
        base = naming env
        names = base { namingUniverses = universeHints base (universeNames context) }

-- The number of binders that the type `forall xs : As, B` and the body
-- `fun xs : As => t` of a function share, in a block of `count` functions.
shared :: Int -> Function -> Int
shared count function = go 0 (functionType function) (functionBody function) where
    go place (Pi _ domain rest) (Lam _ annotation body)
        | lift place count domain == annotation = go (place + 1) rest body
    go place _ _ = place

printerOf :: Style -> Naming -> Printer
printerOf style = printerWith style Nothing

displayPrinter :: Env.Env -> Naming -> Printer
displayPrinter env = printerWith Surface (Just (Env.envSyntax env))

printerWith :: Style -> Maybe Env.Syntax -> Naming -> Printer
printerWith style syntax names = Printer { printerShow = render, printerBind = bind, printerFail = problem } where
    showString = Format.plain
    showChar c = Format.plain [c]
    hasFormats = maybe False (any withFormat . Env.syntaxRules) syntax
    withFormat (Syntax.SyntaxRule _ _ _ (Syntax.RocqTarget _ _ _ template)) = maybe False (const True) (fst (Template.printFormat template))
    withFormat _ = False
    showParen yes doc = if yes then showChar '(' . doc . showChar ')' else doc
    known global = maybe False qualified (namingGlobal names global)
    written = if style == Rocq then printableInstance names else printableLevel names
    problem depth value = case value of
        Type level
            | not (printableLevel names level) -> Just "an invalid or unbound universe level has no surface spelling"
        Cst constant instance_
            | not (all written instance_) -> Just "an invalid universe instance, or one that is an expression for Rocq, has no spelling"
            | not (known (GlobalCst constant)) -> Just "a constant has no printable global name"
        Ind block index instance_
            | not (namingTemplate names block || all written instance_) -> Just "an invalid universe instance, or one that is an expression for Rocq, has no spelling"
            | not (known (GlobalInd block index)) -> Just "an inductive family has no printable global name"
        Con block index place instance_
            | not (namingTemplate names block || all written instance_) -> Just "an invalid universe instance, or one that is an expression for Rocq, has no spelling"
            | not (known (GlobalCon block index place)) -> Just "a constructor has no printable global name"
        PField block field instance_
            | not (namingTemplate names block || all written instance_) -> Just "an invalid universe instance on a projection has no spelling"
            | not (known (GlobalProj block field)) -> Just "a field has no printable global name"
        Proj block field receiver
            | not (known (GlobalProj block field)) -> Just "a field has no printable global name"
            | otherwise -> problem depth receiver
        Var index
            | index < 0 -> Just "a negative variable index has no surface spelling"
            | index >= depth -> Just "an open variable has no surface spelling"
        Pi _ domain body -> problem depth domain <|> problem (depth + 1) body
        Lam _ domain body -> problem depth domain <|> problem (depth + 1) body
        Let _ bound annotation body -> problem depth bound <|> problem depth annotation <|> problem (depth + 1) body
        Cast given annotation -> problem depth given <|> problem depth annotation
        App function argument -> problem depth function <|> problem depth argument
        Case block index instance_ _ hints clause scrutinee branches
            | not (namingTemplate names block || all written instance_) -> Just "an invalid universe instance, or one that is an expression for Rocq, has no spelling"
            | not (known (GlobalInd block index)) -> Just "an inductive family has no printable global name"
            | not (all (known . GlobalCon block index) [0 .. length branches - 1]) -> Just "a constructor has no printable global name"
            | otherwise -> foldr (<|>) Nothing (problem (depth + length hints) clause : problem depth scrutinee : [problem (depth + length bound) body | (bound, body) <- branches])
        Fix chosen functions
            | chosen < 0 || chosen >= length functions -> Just "a fix that selects no function has no surface spelling"
            | any (\function -> shared (length functions) function <= functionArgN function) functions -> Just "a fix whose binders are not those of its type has no surface spelling"
            | otherwise -> foldr (<|>) Nothing (concat [[problem depth (functionType function), problem (depth + length functions) (functionBody function)] | function <- functions])
        _ -> Nothing
    bind depth scope hint = (name, Names (IntMap.insert depth name (namesTable scope)) (Set.insert name (namesTaken scope)) (Map.insert base next (namesNexts scope))) where
        base = if identifier hint then hint else "x"
        (name, next) = head [(candidate, suffix + 1) | suffix <- [Map.findWithDefault 0 base (namesNexts scope) ..], let candidate = if suffix == 0 then base else base ++ show suffix, not (namingBanned names candidate), Set.notMember candidate (namesTaken scope)]
    -- The binders at the levels from `depth` on, in order.
    binds depth scope hints = (map fst bound, if null bound then scope else snd (last bound)) where
        bound = drop 1 (scanl (\(_, inner) (level, hint) -> bind level inner hint) ("", scope) (zip [depth ..] hints))
    -- The variables of a pattern: one that is not `named` is written `_`.
    patternBinds depth scope hints = (map fst bound, if null bound then scope else snd (last bound)) where
        bound = drop 1 (scanl (\(_, inner) (level, (hint, named)) -> if named then bind level inner hint else ("_", inner)) ("", scope) (zip [depth ..] hints))
    wrap limit piece = showParen (pieceRank piece > limit) (pieceDoc piece)
    free depth outer inner = IntSet.union (pieceFree outer) (IntSet.delete depth (pieceFree inner))
    outside depth piece = IntSet.filter (< depth) (pieceFree piece)
    global reference = (if namingAtMark names reference then showChar '@' else id) . maybe id showString (namingGlobal names reference)
    reference symbol instance_ = Piece 0 IntSet.empty (global symbol . showString (instanceText style names printedInstance "")) (maximum (0 : map closedUniversePeak instance_)) where
        printedInstance = case symbol of
            GlobalInd block _
                | namingTemplate names block -> []
            GlobalCon block _ _
                | namingTemplate names block -> []
            GlobalProj block _
                | namingTemplate names block -> []
            GlobalInd block _
                | style == Rocq && namingLocalBlock names == Just block -> []
            _ -> instance_
    rocqField depth scope block field receiver = showString "(match " . receiver . showString " with | {| " . label . showString " := " . showString name . showString " |} => " . showString name . showString " end)" where
        label = maybe id showString (namingGlobal names (GlobalProj block field))
        (name, _) = bind depth scope "field_value"
    quantified depth keyword separator name domain body = Piece 3 (free depth domain body) (showString keyword . showString name . showString " : " . wrap 2 domain . showString separator . wrap 3 body) (max (pieceUniv domain) (pieceUniv body))
    -- Which variables occur in a term does not depend on their names, so a
    -- product can ask whether its body mentions its variable before it decides
    -- whether that variable gets a name.
    render = interpreted (fmap prepare syntax)
    prepare current = (current, options, options) where
        options = Unnotation.choices current
    temporary (current, base, _) [] = (current, base, base)
    temporary (current, base, _) scopes = (current, base, Unnotation.choices (foldr Unnotation.open current scopes))
    forClass Nothing _ = []
    forClass (Just (current, _, _)) cls = ArgumentScopes.syntaxClassScopes current cls
    typeClass expression = case expression of
        App f _ -> typeClass f
        Pi {} -> Just Syntax.FunClass
        Prop -> Just Syntax.SortClass
        Type {} -> Just Syntax.SortClass
        _ -> Syntax.ReferenceClass <$> Unnotation.global expression
    interpreted Nothing = raw Nothing
    interpreted current@(Just table) = showAt where
        -- A binder name depends on whether its body mentions it. Scope-
        -- sensitive notation selection can inspect that very name, so keep
        -- free variables and universe metadata independent of selection.
        showAt depth scope value = original { pieceDoc = pieceDoc output, pieceRank = pieceRank output } where
            original = raw current depth scope value
            output = maybe original (\(_, _, piece) -> piece) (sugared table Nothing Set.empty depth scope value)
    sugared table@(current, _, options) entry visited depth scope value = listToMaybe (mapMaybe choose options) where
        choose (Unnotation.Choice rule@(Syntax.SyntaxRule parts level assoc target) delimiter)
            | fst (Syntax.ruleEntry parts) /= entry = Nothing
            | Syntax.AliasHead name : _ <- parts, Set.member name (namesTaken scope) = Nothing
            | otherwise = do
                chunks <- Unnotation.match current rule value
                let next = maybe (temporary table []) (\(owner, _) -> prepare (Unnotation.open owner current)) delimiter
                let sizes = [count | Unnotation.RepeatLength count <- chunks]
                    isSource (Unnotation.RepeatLength _) = False
                    isSource _ = True
                written <- mapM (spell next) (filter isSource chunks)
                let custom = case target of
                        Syntax.RocqTarget _ slots _ body -> fst (Template.printFormat body) >>= \fmt -> Format.formatted parts slots sizes fmt written
                        _ -> Nothing
                    text = fromMaybe (joinChunks written) custom
                    -- LoL checks a return-less match against its expected
                    -- type. Keep the kernel's nondependent motive available
                    -- when the displayed expression is read on its own.
                    motive = case (target, value) of
                        (Syntax.RocqTarget _ _ _ source, Case _ _ _ _ hints result _ _)
                            | Syntax.TCase _ _ _ Nothing _ <- snd (Template.printFormat source) -> Just (lift 0 (negate (length hints)) result)
                        _ -> Nothing
                    strength = case (motive, parts) of
                        (Just _, _) -> 0
                        (_, [Syntax.AliasHead _]) -> 0
                        _ -> level
                    rank = if strength == 0 || delimiter /= Nothing then 0 else 3
                    scoped = maybe text (\(_, key) -> showChar '(' . text . showString ")%" . showString key) delimiter
                    printed = case motive of
                        Just typ -> showChar '(' . scoped . showString " : " . pieceDoc (interpreted (Just (temporary table [])) depth scope typ) . showChar ')'
                        Nothing -> scoped
                    original = raw (Just table) depth scope value
                return (if delimiter == Nothing then strength else 0, assoc, original { pieceRank = rank, pieceDoc = printed })
        spell next (Unnotation.PatternSlotText target@(Just _) limit _ value) = case value of
            Unnotation.DummyBinder -> patternTerm [] (Hole 0)
            Unnotation.BinderName path _ -> patternTerm path (Var 0)
            Unnotation.ConstructorBinder path g parameters fields ->
                let width = length fields
                    values = [if used then Var i else Hole 0 | (i, (_, used)) <- zip (reverse [0 .. width - 1]) fields]
                    application = foldl App (fromGlobal g) (replicate parameters (Hole 0) ++ values)
                in patternTerm (path ++ map fst fields) application
            operand@(Unnotation.Operand _ _ _ _) -> spell next (Unnotation.Slot target limit Nothing operand)
            where
                patternTerm path term = spell next (Unnotation.Slot target limit Nothing (Unnotation.Operand False path [] term))
        spell _ (Unnotation.PatternSlotText Nothing _ _ Unnotation.DummyBinder) = Just ("", showChar '_')
        spell next (Unnotation.PatternSlotText Nothing _ _ named@Unnotation.BinderName {}) = spell next (Unnotation.BinderSlotText False named)
        spell _ (Unnotation.PatternSlotText Nothing _ group (Unnotation.ConstructorBinder hints g params fields)) = do
            label <- namingGlobal names g
            let (_, above) = binds depth scope hints
                (variables, _) = binds (depth + length hints) above (map fst fields)
                args = replicate params "_" ++ zipWith (\name (_, used) -> if used then name else "_") variables fields
                written = (if namingAtMark names g then showChar '@' else id) . showString (unwords (label : args))
            return ("", showParen (group && not (null args)) written)
        spell next (Unnotation.PatternSlotText Nothing _ group operand@(Unnotation.Operand same hints ss t)) =
            case flatHead t of
                Var _ -> spell next (Unnotation.BinderSlotText False operand)
                Con {} -> spell next (Unnotation.Slot Nothing (if group then 0 else 10) Nothing (Unnotation.Operand same hints ss t))
                _ -> Nothing
            where
                flatHead (App f (Var _)) = flatHead f
                flatHead t = t
        spell _ (Unnotation.Word text) = Just (text, showString text)
        spell next (Unnotation.Slot _ _ _ named@Unnotation.BinderName {}) = spell next (Unnotation.BinderSlotText False named)
        spell _ (Unnotation.BinderSlotText True (Unnotation.BinderName _ (Hole _))) = Nothing
        spell next (Unnotation.BinderSlotText typed (Unnotation.BinderName hints annotation)) = case reverse hints of
            [] -> Nothing
            hint : outer -> do
                let (_, above) = binds depth scope (reverse outer)
                    at = depth + length outer
                    (name, _) = bind at above hint
                    domain = interpreted (Just (temporary next (forClass (Just next) Syntax.SortClass))) at above annotation
                    written = if typed then showChar '(' . showString name . showString " : " . pieceDoc domain . showChar ')' else showString name
                return ("", written)
        spell next (Unnotation.BinderSlotText _ (Unnotation.Operand _ hints _ term))
            | Var _ <- term = Just ("", pieceDoc named)
            | otherwise = Nothing
            where
                (_, below) = binds depth scope hints
                named = raw (Just next) (depth + length hints) below term
        spell next (Unnotation.RefSlotText operand@(Unnotation.Operand _ _ _ term))
            | Just g <- Unnotation.global term, Just name <- namingGlobal names g, qualified name, Set.notMember name (namesTaken scope) = Just ("", showString name)
            | otherwise = spell next (Unnotation.BinderSlotText False operand)
        spell next (Unnotation.RefSlotText operand) = spell next (Unnotation.BinderSlotText False operand)
        spell next@(parent, _, _) (Unnotation.Slot target limit peer (Unnotation.Operand same hints scopes term)) = do
            let (_, below) = binds depth scope hints
                at = depth + length hints
                seen = if same then Set.insert entry visited else Set.empty
            if same && Set.member target seen then Nothing else do
                let notation = sugared (temporary next scopes) target seen at below term
                    ordinary = raw (Just next) at below term
                (strength, assoc, piece) <- case notation of
                    Just result -> Just result
                    Nothing | target == Nothing -> Just ([0, 10, 99, 200] !! pieceRank ordinary, "", ordinary)
                    _ -> Nothing
                let equal = maybe True (== assoc) peer
                    parens = strength > limit || strength == limit && not equal
                case target of
                    Just entryName | parens, not (Unnotation.parentheses (foldr Unnotation.open parent scopes) entryName limit strength) -> Nothing
                    _ -> return ("", showParen parens (pieceDoc piece))
        spell _ _ = Nothing
    joinChunks [] = id
    joinChunks ((first, text) : rest) = text . append first rest where
        append _ [] = id
        append left ((word, next) : more) = space . next . append word more where
            space
                | (left, word) `elem` [("(", ")"), ("[", "]"), ("{", "}")] = showChar ' '
                | left `elem` ["(", "[", "{"] || word `elem` [")", "]", "}", ",", ";"] = id
                | otherwise = showChar ' '
    raw table depth scope value = case value of
        Hole _ -> Piece 0 IntSet.empty (showChar '_') 0
        Prop -> Piece 0 IntSet.empty (showString "Prop") 0
        Type level -> Piece 0 IntSet.empty (sortText level) (closedUniversePeak level)
        Cst constant instance_ -> reference (GlobalCst constant) instance_
        Ind block index instance_ -> reference (GlobalInd block index) instance_
        Con block index place instance_ -> reference (GlobalCon block index place) instance_
        PField block field instance_
            | style == Rocq, namingTemplate names block -> Piece 0 IntSet.empty expansion 0
            | otherwise -> reference (GlobalProj block field) instance_
            where
                count = namingParams names block
                (params, inner) = binds depth scope (replicate count "param")
                (receiver, body) = bind (depth + count) inner "receiver"
                args = foldr (.) id [showChar ' ' . showString name | name <- params]
                family = maybe id showString (namingGlobal names (GlobalInd block 0))
                expansion = showString "(fun" . args . showString " (" . showString receiver . showString " : @" . family . args . showString ") => " . rocqField (depth + count + 1) body block field (showString receiver) . showChar ')'
        Proj block field receiver
            | style == Rocq, namingTemplate names block -> piece { pieceRank = 0, pieceDoc = selected }
            | otherwise -> piece { pieceRank = 0, pieceDoc = dotted }
            where
                piece = render depth scope receiver
                label = maybe id showString (namingGlobal names (GlobalProj block field))
                parameters = if style == Rocq then foldr (.) id (replicate (namingParams names block) (showString " _")) else id
                dotted = wrap 0 piece . showString ".(" . (if style == Rocq then showChar '@' else id) . label . parameters . showChar ')'
                -- Rocq's prefix constant for a template projection has its
                -- declaration universe. A one-field record pattern elaborates
                -- to the primitive projection at the receiver's universe.
                selected = rocqField depth scope block field (pieceDoc piece)
        Var index -> Piece 0 (IntSet.singleton (depth - index - 1)) (showString (namesTable scope IntMap.! (depth - index - 1))) 0
        Pi hint domain body -> if dependent || style == Rocq then quantified depth "forall " ", " (if dependent then name else "_") left right else Piece 2 (free depth left right) (wrap 1 left . showString " -> " . wrap 3 right) (max (pieceUniv left) (pieceUniv right)) where
            (name, inner) = bind depth scope hint
            dependent = IntSet.member depth (pieceFree right)
            left = typeTerm depth scope domain
            right = typeTerm (depth + 1) (if dependent then inner else scope) body
        -- A binder that its body does not mention is written `_`, as Rocq
        -- prints it. The binders of a `fix` and of a `let` keep their names.
        Lam hint domain body -> quantified depth "fun " " => " (if dependent then name else "_") (typeTerm depth scope domain) right where
            (name, inner) = bind depth scope hint
            dependent = IntSet.member depth (pieceFree right)
            right = render (depth + 1) (if dependent then inner else scope) body
        -- The type of a `let` is written unless the kernel left it out for
        -- the display: one that is not a proposition (LoL.Env.visible).
        Let hint bound (Hole _) body -> Piece 3 (free depth given rest) (showString "let " . showString name . showString " := " . wrap 2 given . showString " in " . wrap 3 rest) (max (pieceUniv given) (pieceUniv rest)) where
            (name, inner) = bind depth scope hint
            given = render depth scope bound
            rest = render (depth + 1) inner body
        Let hint bound annotation body -> Piece 3 (IntSet.union (pieceFree given) (free depth typed rest)) (showString "let " . showString name . showString " : " . wrap 2 typed . showString " := " . wrap 2 given . showString " in " . wrap 3 rest) (maximum [pieceUniv given, pieceUniv typed, pieceUniv rest]) where
            (name, inner) = bind depth scope hint
            given = render depth scope bound
            typed = typeTerm depth scope annotation
            rest = render (depth + 1) inner body
        -- A cast is written in parentheses wherever it stands. What is
        -- cast is an application at most: a binder or an arrow before the
        -- colon would take the cast for itself.
        Cast bound annotation -> Piece 0 (IntSet.union (pieceFree given) (pieceFree typed)) (showChar '(' . wrap 1 given . showString " : " . wrap 3 typed . showChar ')') (max (pieceUniv given) (pieceUniv typed)) where
            given = inScopes (maybe [] (forClass table) (typeClass annotation)) depth scope bound
            typed = typeTerm depth scope annotation
        App function argument -> Piece 1 (IntSet.union (pieceFree left) (pieceFree right)) applied (max (pieceUniv left) (pieceUniv right)) where
            applied
                | hasFormats = Format.application (wrap 1 left) (wrap 0 right)
                | otherwise = wrap 1 left . showChar ' ' . wrap 0 right
            left = render depth scope function
            right = inScopes (policy function) depth scope argument
        -- `as` and `in` are written when the return clause mentions what they
        -- bind, and `in` when no branch names the family. A
        -- variable of a pattern that its branch does not mention is written
        -- `_`, as Rocq prints it, and takes no name from the binders after it.
        Case block index instance_ _ hints clause scrutinee branches -> Piece 1 (IntSet.unions (pieceFree subject : outside depth returned : map (\(_, _, body) -> outside depth body) arms)) (showString "match " . wrap 2 subject . alias . family . showString " return " . wrap 2 returned . showString " with" . foldr (.) id (map arm arms) . showString " end") (maximum (pieceUniv subject : pieceUniv returned : map (\(_, _, body) -> pieceUniv body) arms ++ map closedUniversePeak instance_)) where
            count = length hints
            (bound, inner) = patternBinds depth scope [(hint, used level) | (level, hint) <- zip [depth ..] hints]
            subject = render depth scope scrutinee
            returned = render (depth + count) inner clause
            used level = IntSet.member level (pieceFree returned)
            holes = foldr (.) id (replicate (namingParams names block) (showString " _"))
            -- Rocq takes a scrutinee that is a variable for its own alias when
            -- there is no `as`; LoL does not. So the text for
            -- Rocq has `as _` where the clause mentions that variable itself.
            alias
                | count > 0 && used (depth + count - 1) = showString " as " . showString (last bound)
                | style == Rocq, Var index <- scrutinee, IntSet.member (depth - index - 1) (pieceFree returned) = showString " as _"
                | otherwise = id
            family = if namingInMark names block index || null branches || any used [depth .. depth + count - 2] then showString " in " . global (GlobalInd block index) . holes . foldr (.) id [showChar ' ' . showString (if used level then name else "_") | (level, name) <- zip [depth ..] (take (count - 1) bound)] else id
            arms = zipWith branch [0 ..] branches
            -- Which variables a branch mentions does not depend on their names.
            branch place (given, body) = (place, fst named, shown) where
                shown = render (depth + length given) (snd named) body
                named = patternBinds depth scope [(hint, IntSet.member level (pieceFree shown)) | (level, hint) <- zip [depth ..] given]
            arm (place, given, body) = showString " | " . patternText . showString " => " . wrap 3 body where
                constructor = GlobalCon block index place
                patternText = case syntax of
                    Nothing -> global constructor . holes . foldr (.) id [showChar ' ' . showString name | name <- given]
                    Just _ -> pieceDoc (render (depth + width) temporary application)
                -- Parameter holes and unused branch binders are names for
                -- this printing pass only. Their levels are never admitted.
                labels = replicate (namingParams names block) "_" ++ given
                width = length labels
                temporary = scope { namesTable = IntMap.union (IntMap.fromList (zip [depth ..] labels)) (namesTable scope) }
                application = foldl App (fromGlobal constructor) [Var i | i <- reverse [0 .. width - 1]]
        -- `fix f (xs : As) {struct x} : B := t`: the binders are those that
        -- the type and the body share. A body in a block of several functions
        -- is an application at most: a body that ends in a `fix`, as an arrow
        -- can, would take the `with` or `for` after it for its own.
        -- Rocq does not apply a `fix ... for f` that has no parentheses.
        Fix chosen functions -> Piece 3 (IntSet.unions (map (\(free', _, _) -> free') clauses)) (showString "fix " . foldr1 (\left right -> left . showString " with " . right) (map (\(_, text, _) -> text) clauses) . (if count == 1 then id else showString " for " . showString (given !! chosen))) (maximum (map (\(_, _, level) -> level) clauses)) where
            count = length functions
            (given, inner) = binds depth scope (map functionName functions)
            clauses = zipWith clause given functions
            clause name function = (IntSet.unions (outside depth result : outside depth value : map (outside depth) domains), showString name . foldr (.) id [showString " (" . showString variable . showString " : " . wrap 3 domain . showChar ')' | (variable, domain) <- zip variables domains] . showString " {struct " . showString (variables !! functionArgN function) . showString "} : " . wrap 3 result . showString " := " . wrap (if count == 1 then 3 else 1) value, maximum (pieceUniv result : pieceUniv value : map pieceUniv domains)) where
                width = shared count function
                (annotations, body) = lambdas width (functionBody function)
                ((_, below), named) = mapAccumL (\(level, above) (hint, annotation) -> let (variable, next) = bind level above hint in ((level + 1, next), (variable, render level above annotation))) (depth + count, inner) annotations
                variables = map fst named
                domains = map snd named
                value = render (depth + count + width) below body
                result = render (depth + width) (below { namesTable = IntMap.union (IntMap.fromList (zip [depth ..] variables)) (namesTable scope) }) (codomain width (functionType function))
        where
            render = interpreted (fmap (\t -> temporary t []) table)
            inScopes scopes = interpreted (fmap (\t -> temporary t scopes) table)
            typeTerm = inScopes (forClass table Syntax.SortClass)
            policy function = case table of
                Just (current, _, _) | ArgumentScopes.hasPolicies current -> lookupArg current 0 function
                _ -> []
            lookupArg current n (App f _) = lookupArg current (n + 1) f
            lookupArg current n headTerm = case Unnotation.global headTerm of
                Nothing -> []
                Just g -> case drop n (ArgumentScopes.globalPositions current g True) of
                    first : _ -> first
                    [] -> []
    lambdas width value = case value of
        Lam hint annotation body
            | width > 0 -> (\(rest, inner) -> ((hint, annotation) : rest, inner)) (lambdas (width - 1) body)
        _ -> ([], value)
    codomain width value = case value of
        Pi _ _ body
            | width > 0 -> codomain (width - 1) body
        _ -> value
    sortText level
        | style == Rocq && level == Closed 0 = showString "Set"
        | otherwise = showString "Type@{" . showString (levelText style names level "") . showChar '}'

declaration :: Env.Env -> ConstId -> Env.Entry -> Either String String
declaration = declarationWith True

-- What a declaration states: a theorem without its term (two proofs of one
-- statement are one theorem), and any other declaration as it is.
statement :: Env.Env -> ConstId -> Env.Entry -> Either String String
statement = declarationWith False

declarationWith :: Bool -> Env.Env -> ConstId -> Env.Entry -> Either String String
declarationWith proved = writeDeclaration (const (printerOf Surface)) proved

displayDeclaration :: Env.Env -> ConstId -> Env.Entry -> Either String String
displayDeclaration = writeDeclaration displayPrinter True

writeDeclaration :: (Env.Env -> Naming -> Printer) -> Bool -> Env.Env -> ConstId -> Env.Entry -> Either String String
writeDeclaration make proved env c entry = snd <$> commandUsing (make env) proved Surface names c entry where
    own = Map.fromList [(global, name) | (name, global) <- Env.declGlobals c (Env.entryName entry) (Env.entryDecl entry)]
    names = (naming env) { namingGlobal = \global -> Map.lookup global own <|> globalName env global }

-- Declaration `c` as a command. The names are those that `names` gives; a
-- theorem of Rocq is a definition.
command :: Style -> Naming -> ConstId -> Env.Entry -> Either String (Integer, String)
command = commandWith True

-- `proved`: with the term of a theorem.
commandWith :: Bool -> Style -> Naming -> ConstId -> Env.Entry -> Either String (Integer, String)
commandWith proved style = commandUsing (printerOf style) proved style

commandUsing :: (Naming -> Printer) -> Bool -> Style -> Naming -> ConstId -> Env.Entry -> Either String (Integer, String)
commandUsing makePrinter proved = commandBodies makePrinter True proved

-- The object report prints the signature of every definition as well as every theorem.
commandBodies :: (Naming -> Printer) -> Bool -> Bool -> Style -> Naming -> ConstId -> Env.Entry -> Either String (Integer, String)
commandBodies makePrinter definitions proved style outerNames c entry
    = do
        declarations <- mapM (universeRelation Rocq names) [edge | published, edge <- universeConstraints context]
        (peak, body) <- case Env.entryDecl entry of
            Env.Axiom a -> constant "Axiom" a Nothing
            Env.Definition a t -> constant "Definition" a (if definitions then Just t else Nothing)
            Env.Theorem a t -> constant (if style == Rocq then "Definition" else "Theorem") a (if proved then Just t else Nothing)
            Env.Inductive count [family]
                | Just record <- Env.familyRecord family -> recordDeclaration count family record
            Env.Inductive count families -> inductive count families
        return (peak, concatMap (\relation -> "Constraint " ++ relation ".\n") declarations ++ body)
    where
        showString = Format.plain
        showChar c = Format.plain [c]
        finish doc = Format.output doc ""
        published = style == Rocq && null (universeNames context) && not (Set.null (constraintOwners context))
        context = Env.entryUniverses entry
        names = outerNames { namingUniverses = (if isTemplate then templateHints style else universeHints outerNames) (universeNames context), namingLocalBlock = localBlock }
        localBlock = case Env.entryDecl entry of
            Env.Inductive {} -> Just c
            _ -> Nothing
        isTemplate = case Env.entryDecl entry of
            Env.Inductive _ families -> any Env.familyTemplate families
            _ -> False
        polymorphic
            | isTemplate = showString "#[universes(template)] "
            | context == emptyUniverses || published = id
            | otherwise = showString "Polymorphic "
        contextPeak = maximum (0 : concatMap levels (universeConstraints context)) where
            levels (UniverseLe left right) = map closedUniversePeak [left, right]
            levels (UniverseEq left right) = map closedUniversePeak [left, right]
        printer = makePrinter names
        printed value = maybe (Right (printerShow printer 0 noNames value)) Left (printerFail printer 0 value)
        given global = case namingGlobal names global of
            Just name
                | identifier name -> Right name
            _ -> Left "a declaration has no printable identifier"
        constant kind annotation body = do
            name <- given (GlobalCst c)
            universes <- declHeader
            typed <- printed annotation
            value <- mapM printed body
            return (maximum (contextPeak : pieceUniv typed : map pieceUniv (maybe [] pure value)), finish (polymorphic . showString kind . showChar ' ' . showString name . universes . showString " : " . pieceDoc typed . maybe id (\piece -> showString " := " . pieceDoc piece) value . showChar '.'))
        -- The parameters are named once, from the type of the first family, and
        -- every type of the block is printed under those names.
        inductive count families = do
            universes <- declHeader
            mapM_ printed (Env.declTypes (Env.entryDecl entry))
            (parameters, scope) <- case families of
                first : _ -> telescope count 0 noNames (Env.familyType first)
                [] -> Left "an inductive block without a family has no surface spelling"
            bodies <- mapM (body count scope) (zip [0 ..] families)
            let header = foldr (.) id [showString " (" . showString name . showString " : " . pieceDoc domain . showChar ')' | (name, domain) <- parameters]
            return (maximum (contextPeak : map pieceUniv (map snd parameters ++ concatMap snd bodies)), finish (polymorphic . showString "Inductive " . foldr1 (\left right -> left . showString " with " . right) [showString name . (if index == (0 :: Int) then universes else id) . header . showString " : " . pieceDoc arity . showString " :=" . foldr (.) id [showString " | " . showString constructor . showString " : " . pieceDoc signature | (constructor, signature) <- zip constructors signatures] | (index, ((name, constructors), arity : signatures)) <- zip [0 ..] bodies] . showChar '.'))
        declHeader
            | published = Right id
            | otherwise = (\header -> showString (header "")) <$> universeHeader style names context
        recordDeclaration count family record = do
            name <- given (GlobalInd c 0)
            constructor <- given (GlobalCon c 0 0)
            universes <- declHeader
            mapM_ printed (Env.declTypes (Env.entryDecl entry))
            (parameters, scope) <- telescope count 0 noNames (Env.familyType family)
            result <- under count (Env.familyType family)
            let arity = case result of
                    Type (Maximum (Closed 0) level)
                        | isTemplate -> printerShow printer count scope (Type level)
                    Type level
                        | isTemplate && inferredSort level -> Piece 0 IntSet.empty (Format.plain "Type") 0
                    _ -> printerShow printer count scope result
                -- For an inferred minimum the spelled-out symbolic sort of
                -- Record would impose Set, even when every field is a proof.
                -- Preserve a fixed result level that no parameter supplies.
                inferredSort level = not (Set.null slots) && slots `Set.isSubsetOf` parameterSlots count (Env.familyType family) where
                    slots = levelParameters level
            signature <- case Env.familyCons family of
                [(_, typ)] -> under count typ
                _ -> Left "a record must have one constructor"
            fields <- fieldTelescope count scope [0 .. length (Env.recordFields record) - 1] signature
            let header = foldr (.) id [showString " (" . showString label . showString " : " . pieceDoc typ . showChar ')' | (label, typ) <- parameters]
                member (label, typ) = showString label . showString " : " . pieceDoc typ
                members = foldr1 (\left right -> left . showString "; " . right) (map member fields)
                keyword = if Env.recordEta record then "Record " else "Inductive "
                prefix = showString "#[projections(primitive)] " . polymorphic . showString keyword . showString name . universes . header
            return (maximum (contextPeak : pieceUniv arity : map (pieceUniv . snd) (parameters ++ fields)), finish (prefix . showString " : " . pieceDoc arity . showString " := " . showString constructor . showString " { " . (if null fields then id else members) . showString " }."))
        parameterSlots n (Pi _ domain body)
            | n > 0 = Set.union (termParameters domain) (parameterSlots (n - 1) body)
        parameterSlots _ _ = Set.empty
        fieldTelescope depth scope indices signature = case (indices, signature) of
            ([], _) -> Right []
            (field : more, Pi _ domain rest) -> do
                label <- given (GlobalProj c field)
                -- The label is public. Its occurrences in later field
                -- domains refer to this bound variable even if a notation
                -- with the same spelling is visible to the explicit reader.
                let occurrence = if style == Surface && namingLiteral names label then '@' : label else label
                    inner = scope { namesTable = IntMap.insert depth occurrence (namesTable scope), namesTaken = Set.insert label (namesTaken scope) }
                ((label, printerShow printer depth scope domain) :) <$> fieldTelescope (depth + 1) inner more rest
            _ -> Left "the constructor telescope has fewer entries than the record has fields"
        telescope count depth scope value = case value of
            _
                | count == (0 :: Int) -> Right ([], scope)
            Pi hint domain rest -> (\(more, final) -> ((name, printerShow printer depth scope domain) : more, final)) <$> telescope (count - 1) (depth + 1) inner rest where
                (name, inner) = printerBind printer depth scope hint
            _ -> Left "an inductive family without its parameters has no surface spelling"
        under count value = case value of
            _
                | count == (0 :: Int) -> Right value
            Pi _ _ rest -> under (count - 1) rest
            _ -> Left "a type of an inductive block without its parameters has no surface spelling"
        body count scope (index, family) = do
            name <- given (GlobalInd c index)
            constructors <- mapM (given . GlobalCon c index) [0 .. length (Env.familyCons family) - 1]
            pieces <- mapM (fmap (printerShow printer count scope) . under count) (Env.familyType family : map snd (Env.familyCons family))
            return ((name, constructors), pieces)
