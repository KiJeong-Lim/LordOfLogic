module LoL.Front.Scope where

import Data.List (elemIndex, elemIndices)
import Data.Functor.Const (Const (..))
import Data.Monoid (Any (..))
import qualified Data.Map.Strict as Map
import qualified LoL.Core as Core
import LoL.Diagnostic
import qualified LoL.Env as Env
import LoL.Front.Syntax

-- Core is an unchanged transport type. The parallel tree retains a position
-- for every resulting node, including binders introduced by syntax expansion.
data PositionedTerm
    = PositionedTerm
        { placedTerm :: Core.Term
        , placedSpan :: Span
        , placedSubs :: [PositionedTerm]
        }
    deriving (Eq, Show)

-- The number of leading products of a type, as it is written.
products :: Core.Term -> Int
products value
    = case value of
        Core.Pi _ _ body -> 1 + products body
        _ -> 0

-- `globals` are the names in scope. A match reads the shape of its family
-- from `decls`: the number of parameters and indices and the constructors.
-- The parameters that a match keeps are holes: the kernel gives them when it
-- types the match.
translate :: Map.Map String Core.Global -> Map.Map Core.ConstId Env.Entry -> Term -> Either Diagnostic PositionedTerm
translate = translateUnder (const False) []

-- `hidden` says which short names are ambiguous and have a constructor.
-- `outer` has the names of binders around the term, the innermost first.
translateUnder :: (String -> Bool) -> [String] -> Map.Map String Core.Global -> Map.Map Core.ConstId Env.Entry -> Term -> Either Diagnostic PositionedTerm
translateUnder = translateSyntax Nothing

-- Search patterns share the ordinary scope resolver. Only the search reader
-- retains anonymous holes and inserts wildcards in implicit argument slots.
-- Its result is inspected as syntax and never proposed to the kernel.
translateSyntax :: Maybe (Map.Map Core.Global [Bool]) -> (String -> Bool) -> [String] -> Map.Map String Core.Global -> Map.Map Core.ConstId Env.Entry -> Term -> Either Diagnostic PositionedTerm
translateSyntax search hidden outer globals decls = resolve outer where
    leaf position value = PositionedTerm value position []
    binary position constructor left right = PositionedTerm (constructor (placedTerm left) (placedTerm right)) position [left, right]
    unknown name = Left (Diagnostic (nameSpan name) "LoL-ScopeError" "H-Name" ("unknown name: " ++ nameText name) [nameText name])
    global name = maybe (unknown name) Right (lookupReference globals name)
    hintOf name = if nameText name == "_" then "" else nameText name
    resolve locals source = case termForm source of
        SName name -> positioned <$> named name
        SDeclared name -> leaf position . Core.fromGlobal <$> global name
        SBound index -> Right (leaf position (Core.Var index))
        SMask prefix count expr -> resolve (maskLocals (const "") prefix count locals) expr
        SWithout name expr -> translateSyntax search hidden locals (Map.delete (nameText name) globals) decls expr
        SExplicitGlobal reference -> Right (leaf position (Core.fromGlobal reference))
        SGlobal reference -> Right (leaf position (Core.fromGlobal reference))
        SExplicit name -> positioned <$> named name
        SProp -> Right (leaf position Core.Prop)
        SSet -> Right (leaf position (Core.Type (Core.Closed 0)))
        SType level -> Right (leaf position (Core.Type (Core.Closed level)))
        SInferredType | Just _ <- search -> Right (leaf position (Core.Hole 1))
        SInferredType -> unavailable "inferred universe"
        SUniverse _ -> unavailable "symbolic universe"
        SInstance {} -> unavailable "explicit universe instance"
        SApp {} | Just modes <- search -> do
            let (headSource, args) = spine [] source
            function <- resolve locals headSource
            arguments <- mapM (resolve locals) args
            let slots = maybe [] (\g -> Map.findWithDefault [] g modes) (implicitHead locals headSource)
            return (foldl (binary position Core.App) function (fill slots arguments))
        SApp function argument -> binary position Core.App <$> resolve locals function <*> resolve locals argument
        SProjection receiver field -> do
            accessor <- global field
            value <- resolve locals receiver
            case accessor of
                Core.GlobalProj block index -> Right (PositionedTerm (Core.Proj block index (placedTerm value)) position [value])
                _ -> Left (Diagnostic (nameSpan field) "LoL-ScopeError" "H-Projection" "expected a primitive projection" [nameText field])
        SArrow domain body -> binary position (Core.Pi "") <$> resolve locals domain <*> resolve ("" : locals) body
        SForall binders body -> positioned <$> expand Core.Pi locals binders body
        SLambda binders body -> positioned <$> expand Core.Lam locals binders body
        SLet name (Just annotation) value body -> do
            translatedAnnotation <- resolve locals annotation
            translatedValue <- resolve locals value
            translatedBody <- resolve (nameText name : locals) body
            return (PositionedTerm (Core.Let (nameText name) (placedTerm translatedValue) (placedTerm translatedAnnotation) (placedTerm translatedBody)) position [translatedValue, translatedAnnotation, translatedBody])
        SParen inner -> do
            translated <- resolve locals inner
            return translated { placedSpan = position }
        SMatch scrutinee alias family (Just clause) branches -> match locals position scrutinee alias family clause branches
        SFix bodies selected -> fixpoint locals position bodies selected
        SHole | Just _ <- search -> Right (leaf position (Core.Hole 0))
        SHole -> unavailable "_"
        SNumeral _ -> unavailable "numeral"
        SOperators _ _ -> unavailable "operator sequence"
        SLet _ Nothing _ _ -> unavailable "let without a type annotation"
        SAnnotation value annotation -> do
            translatedAnnotation <- resolve locals annotation
            translatedValue <- resolve locals value
            return (binary position Core.Cast translatedValue translatedAnnotation)
        SMatch _ _ _ Nothing _ -> unavailable "match without a return clause"
        where
            position = termSpan source
            named name = maybe (leaf position . Core.fromGlobal <$> global name) (Right . leaf position . Core.Var) (elemIndex (nameText name) locals)
            positioned translated = translated { placedSpan = position }
            unavailable syntax = Left (unsupported position syntax)
            fill (True : flags) args = leaf position (Core.Hole 0) : fill flags args
            fill (False : flags) (x : xs) = x : fill flags xs
            fill _ args = args
    spine args (Term _ (SApp f a)) = spine (a : args) f
    spine args (Term _ (SParen t)) = spine args t
    spine args t = (t, args)
    implicitHead locals value = case termForm value of
        SName name | nameText name `notElem` locals -> lookupReference globals name
        SGlobal g -> Just g
        SMask prefix count expr -> implicitHead (maskLocals (const "") prefix count locals) expr
        _ -> Nothing
    expand constructor locals [] body = resolve locals body
    expand constructor locals (binder : rest) body
        | binderImpl binder, Nothing <- search = Left (unsupported (binderSpan binder) "implicit binder {x : A}")
        | otherwise = case binderType binder of
            Nothing | Just _ <- search -> names constructor locals (binderSpan binder) (binderVars binder) (leaf (binderSpan binder) (Core.Hole 0)) rest body
            Nothing -> Left (unsupported (binderSpan binder) "binder without a type")
            Just annotation -> do
                translated <- resolve locals annotation
                names constructor locals (binderSpan binder) (binderVars binder) translated rest body
    names constructor locals position [] _ rest body = expand constructor locals rest body
    names constructor locals position (name : remaining) annotation rest body
        | not (null remaining), Just index <- elemIndex (nameText name) locals, refers index 0 (placedTerm annotation) = Left (Diagnostic (nameSpan name) "LoL-ScopeError" "H-Binders" ("a shared binder annotation depends on the local name that this binder shadows: " ++ nameText name) [nameText name])
        | otherwise = do
            next <- names constructor (hintOf name : locals) position remaining (shiftPositioned 1 annotation) rest body
            return (binary position (constructor (hintOf name)) annotation next)
    refers index depth term = case term of
        Core.Var found -> found == index + depth
        _ -> getAny (getConst (Core.descend (\below part -> Const (Any (refers index below part))) depth term))
    -- The family of a match is that of its `in` clause, or else that of the
    -- constructor of its first branch. Without the elaborator a branch names
    -- the constructor at its own place in the declaration.
    match locals position scrutinee alias family clause branches = do
        (block, index, given) <- case (family, branches) of
            (Just (Pattern at _ name items), _) -> do
                found <- familyOf locals name
                case found of
                    Core.GlobalInd b i -> Right (b, i, Just (at, items))
                    _ -> Left (unsupported at "an `in` clause that does not name an inductive family")
            (Just (RawPattern raw), _) -> Left (unsupported (termSpan raw) "unexpanded pattern notation")
            (Just (WildPattern at), _) -> Left (unsupported at "an `in` clause without a family")
            (Nothing, Branch at (Pattern _ _ name _) _ : _) -> do
                found <- familyOf locals name
                case found of
                    Core.GlobalCon b i _ -> Right (b, i, Nothing)
                    _ -> Left (unsupported at "a pattern that does not name a constructor")
            (Nothing, Branch at (RawPattern _) _ : _) -> Left (unsupported at "unexpanded pattern notation")
            (Nothing, Branch at (WildPattern _) _ : _) -> Left (unsupported at "a `_` pattern")
            (Nothing, []) -> Left (unsupported position "match without a branch and without an `in` clause")
        (parameters, shape) <- case Map.lookup block decls of
            Just (Env.Entry { Env.entryDecl = Env.Inductive count families })
                | index < length families -> Right (count, families !! index)
            _ -> Left (unsupported position "match on a family that is not declared yet")
        indices <- case given of
            Just (at, items) -> map hintOf <$> arguments at parameters items
            Nothing -> Right (replicate (products (Env.familyType shape) - parameters) "")
        let bound = indices ++ [maybe "" hintOf alias]
        translatedScrutinee <- resolve locals scrutinee
        translatedClause <- resolve (reverse bound ++ locals) clause
        translatedBranches <- mapM (branch locals block index parameters) (zip [0 ..] branches)
        return (PositionedTerm (Core.Case block index [] (replicate parameters (Core.Hole 0)) bound (placedTerm translatedClause) (placedTerm translatedScrutinee) [(hints, placedTerm body) | (hints, body) <- translatedBranches]) position (translatedClause : translatedScrutinee : map snd translatedBranches))
    familyOf _ name@ResolvedName {} = global name
    familyOf locals name
        | nameText name `elem` locals = Left (unsupported (nameSpan name) "a pattern that names a local variable")
        | otherwise = global name
    -- The items of a pattern after `_` for each parameter: variables, each
    -- bound once. A constructor there would be a pattern inside a pattern,
    -- and so would a name that is ambiguous and has a constructor.
    arguments at parameters items
        | length items < parameters || any ((/= "_") . nameText) (take parameters items) = Left (unsupported at "a pattern without `_` for each parameter")
        | nested : _ <- [item | item <- bound, constructor (nameText item)] = Left (unsupported (nameSpan nested) "a pattern inside a pattern")
        | repeated : _ <- [item | (place, item) <- zip [0 ..] bound, nameText item /= "_", nameText item `elem` map nameText (take place bound)] = Left (Diagnostic (nameSpan repeated) "LoL-ScopeError" "H-Match" ("a variable is bound twice in a pattern: " ++ nameText repeated) [nameText repeated])
        | otherwise = Right bound
        where
            bound = drop parameters items
            constructor name = hidden name || case Map.lookup name globals of
                Just (Core.GlobalCon {}) -> True
                _ -> False
    branch locals block index parameters (place, Branch at pattern body) = case pattern of
        RawPattern raw -> Left (unsupported (termSpan raw) "unexpanded pattern notation")
        WildPattern _ -> Left (unsupported at "a `_` pattern")
        Pattern _ _ name items -> do
            found <- familyOf locals name
            if found /= Core.GlobalCon block index place then Left (unsupported at "a branch that is not at the place of its constructor in the declaration") else Right ()
            bound <- map hintOf <$> arguments at parameters items
            translated <- resolve (reverse bound ++ locals) body
            return (bound, translated)
    -- [H-Binders] for the functions of a `fix`. The types are outside the
    -- block, so the annotations of a body are those of its type, moved under
    -- the functions.
    fixpoint locals position bodies selected = do
        chosen <- case (selected, bodies) of
            (Just name, _) -> maybe (unknown name) Right (elemIndex (nameText name) [nameText given | FixBody _ given _ _ _ _ <- bodies])
            (Nothing, [_]) -> Right 0
            (Nothing, _) -> Left (unsupported position "a block of several functions without `for`")
        functions <- mapM (member locals (reverse [nameText name | FixBody _ name _ _ _ _ <- bodies])) bodies
        return (PositionedTerm (Core.Fix chosen (map fst functions)) position (concatMap snd functions))
    member locals siblings (FixBody at name binders struct annotation body) = do
        signature <- expand Core.Pi locals binders annotation
        let variables = concatMap binderVars binders
        position <- case struct of
            Nothing -> Left (unsupported at "fix without {struct x}")
            Just argument -> case elemIndices (nameText argument) (map nameText variables) of
                [] -> unknown argument
                [found] -> Right found
                _ -> Left (ambiguousStruct (nameSpan argument) (nameText argument))
        let bound = map hintOf variables
            count = length siblings
            domains = take (length bound) (annotations signature)
        value <- resolve (reverse bound ++ siblings ++ locals) body
        let definition = foldr (\(place, hint, domain) rest -> binary at (Core.Lam hint) (shiftFrom place count domain) rest) value (zip3 [0 ..] bound domains)
        return (Core.Function (nameText name) position (placedTerm signature) (placedTerm definition), [signature, definition])
    annotations positioned = case (placedTerm positioned, placedSubs positioned) of
        (Core.Pi {}, [domain, body]) -> domain : annotations body
        _ -> []

-- Expanding a shared binder annotation must not capture one of its free
-- indices when the preceding names of the group enter scope.
shiftPositioned :: Int -> PositionedTerm -> PositionedTerm
shiftPositioned = shiftFrom 0

-- `shiftFrom cutoff amount`: the indices that `cutoff` binders do not bind grow by `amount`.
shiftFrom :: Int -> Int -> PositionedTerm -> PositionedTerm
shiftFrom cutoff amount = move cutoff where
    move depth positioned = positioned { placedTerm = Core.lift depth amount (placedTerm positioned), placedSubs = zipWith move depths (placedSubs positioned) } where
        depths = case placedTerm positioned of
            Core.Pi {} -> [depth, depth + 1]
            Core.Lam {} -> [depth, depth + 1]
            Core.Let {} -> [depth, depth, depth + 1]
            Core.Case _ _ _ _ bound _ _ branches -> depth + length bound : depth : [depth + length hints | (hints, _) <- branches]
            Core.Fix _ functions -> concat [[depth, depth + length functions] | _ <- functions]
            _ -> repeat depth
