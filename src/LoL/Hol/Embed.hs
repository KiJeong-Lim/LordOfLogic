module LoL.Hol.Embed where

import Control.Monad (foldM)
import qualified Control.Monad.Trans.Class as Trans
import Control.Monad.Trans.State.Strict (StateT, evalStateT, get, put, runState, state)
import Data.Char (isAsciiLower, isAsciiUpper, isDigit)
import Data.Containers.ListUtils (nubOrd)
import Data.Functor.Identity (runIdentity)
import Data.List (elemIndex, nub)
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Hol.V2.Embedding hiding (Closed)
import qualified Hol.V2.Embedding as Notation
import LoL.Core

-- The constants of this module are those of `lol/hol/kernel.hol`.

data Report
    = Report
        { reportRule :: String
        , reportArgs :: [String]
        , reportCore :: [Maybe ReportValue]
        }
    deriving (Eq, Show)

data ReportValue
    = ReportTerm [Hint] Term
    | ReportBinders [Hint] [Hint] Term
    | ReportHole Hint [Hint]
    | ReportField String (Maybe ReportValue)
    | ReportConstraint [Hint] String UniverseConstraint
    deriving (Eq, Show)

-- What `ind_info` says of a family: the number of its parameters, whether a
-- match on it may return a type of every sort, and for each constructor which
-- of its arguments are recursive. The kernel computes it.
data Info
    = Info
        { infoParN :: Int
        , infoElim :: Bool
        , infoRecs :: [[Bool]]
        }
    deriving (Eq, Show)

named :: SmallId -> TermNode
named = mkNCon . DC_Named

natural :: Integer -> TermNode
natural = mkNCon . DC_NatL

-- A list whose elements have the given type.
embedList :: TermNode -> [TermNode] -> TermNode
embedList kind items = assertNonnegativeTerms (kind : items) `seq` foldr cons nil items where
    nil = NApp (mkNCon DC_Nil) kind Nothing
    cons item rest = NApp (NApp (NApp (mkNCon DC_Cons) kind Nothing) item Nothing) rest Nothing

kindOf :: SmallId -> TermNode
kindOf = mkNCon . TC_Named

listOf :: TermNode -> TermNode
listOf = mkNApp (kindOf "list")

terms :: [TermNode] -> TermNode
terms = embedList (kindOf "tm")

embedLevel :: Level -> TermNode
embedLevel = checkedCoreEmbedding . buildCoreLevel

buildCoreLevel :: Level -> TermNode
buildCoreLevel level = case level of
    Closed number
        | number < 0 -> error "LoL.Hol.Embed: negative Core universe level."
        | number == 0 -> named "lz"
        | otherwise -> NApp (named "ls") (buildCoreLevel (Closed (number - 1))) Nothing
    DefaultLevel owner slot -> foldlNApp (named "lg") [natural owner, natural (toInteger slot)]
    Parameter index
        | index < 0 -> error "LoL.Hol.Embed: negative Core universe parameter."
        | otherwise -> NApp (named "lp") (natural (toInteger index)) Nothing
    Successor inner -> NApp (named "lu") (buildCoreLevel inner) Nothing
    Maximum left right -> NApp (NApp (named "lm") (buildCoreLevel left) Nothing) (buildCoreLevel right) Nothing

embedTerm :: Term -> TermNode
embedTerm = embedUnder []

-- A Core binder is one Hol abstraction, so the de Bruijn indices coincide,
-- except that the functions of a `fix` share one abstraction `f`: function J
-- is `f J`. The scope has Nothing for an ordinary binder and the number of the
-- function for a binder of a `fix`, the innermost binder first.
-- These pure transport entrypoints are partial on malformed negative Core
-- fields, just as the underlying checked Hol constructors are. They do not
-- perform CIC typing or decide whether a nonnegative free index is admissible.
embedUnder :: [Maybe Int] -> Term -> TermNode
embedUnder scope = checkedCoreEmbedding . buildCoreUnder scope

checkedCoreEmbedding :: TermNode -> TermNode
checkedCoreEmbedding value = assertNonnegativeIndices value `seq` value

-- Only this internal construction group bypasses repeated descendant checks.
-- The supported transport entrypoints validate the complete result once.
buildCoreUnder :: [Maybe Int] -> Term -> TermNode
buildCoreUnder scope term
    = case term of
        Prop -> named "prop"
        Type l -> app (named "typ") (buildCoreLevel l)
        Cst c instance' -> apps (named "cst") [natural c, buildCoreInstance instance']
        Ind b i instance' -> apps (named "ind") [natural b, natural (toInteger i), buildCoreInstance instance']
        Con b i j instance' -> apps (named "con") [natural b, natural (toInteger i), natural (toInteger j), buildCoreInstance instance']
        Proj b j r -> apps (named "proj") [natural b, natural (toInteger j), buildCoreUnder scope r]
        PField b j us -> apps (named "pfield") [natural b, natural (toInteger j), buildCoreInstance us]
        Var i
            | i < 0 -> error "LoL.Hol.Embed: negative Core variable index."
            | otherwise -> case splitAt i scope of
                (inner, Just j : _) -> app (mkNIdx (abstractions inner)) (natural (toInteger j))
                (inner, _) -> mkNIdx (abstractions inner)
        Pi x a b -> apps (named "prod") [buildCoreUnder scope a, binder x b]
        Lam x a t -> apps (named "lam") [buildCoreUnder scope a, binder x t]
        Let x t a u -> apps (named "letin") [buildCoreUnder scope t, buildCoreUnder scope a, binder x u]
        Cast t a -> apps (named "cast") [buildCoreUnder scope t, buildCoreUnder scope a]
        App t u -> apps (named "app") [buildCoreUnder scope t, buildCoreUnder scope u]
        Case b i instance' qs ys p t bs -> apps (named "cas") [foldl (\family q -> apps (named "app") [family, buildCoreUnder scope q]) (apps (named "ind") [natural b, natural (toInteger i), buildCoreInstance instance']) qs, buildCoreBinders scope ys p, buildCoreUnder scope t, coreTerms [buildCoreBinders scope zs body | (zs, body) <- bs]]
        Hole n
            | n < 0 -> error "LoL.Hol.Embed: negative Core hole index."
            | otherwise -> apps (mkLVar (holeVar n)) [mkNIdx h | h <- reverse [0 .. abstractions scope - 1]]
        Fix k fs -> apps (named "fix") [natural (toInteger k), coreList (kindOf "nat") (map (natural . toInteger . functionArgN) fs), coreTerms (map (buildCoreUnder scope . functionType) fs), NLam (binderHint (concatMap functionName (take 1 fs))) noLamType (coreTerms (map (buildCoreUnder (functions ++ scope) . functionBody) fs)) Nothing] where
            functions = map Just (reverse [0 .. length fs - 1])
    where
        app function argument = NApp function argument Nothing
        apps = foldl app
        binder hint body = NLam (binderHint hint) noLamType (buildCoreUnder (Nothing : scope) body) Nothing
        abstractions = length . filter (maybe True (== 0))

coreList :: TermNode -> [TermNode] -> TermNode
coreList kind = foldr cons nil where
    nil = NApp (mkNCon DC_Nil) kind Nothing
    cons item rest = NApp (NApp (NApp (mkNCon DC_Cons) kind Nothing) item Nothing) rest Nothing

coreTerms :: [TermNode] -> TermNode
coreTerms = coreList (kindOf "tm")

buildCoreInstance :: UniverseInstance -> TermNode
buildCoreInstance = coreList (kindOf "lvl") . map buildCoreLevel

embedInstance :: UniverseInstance -> TermNode
embedInstance = checkedCoreEmbedding . buildCoreInstance

-- The binders of a return clause or of a branch: `abs (x\ ...)` for each.
binders :: [Maybe Int] -> [Hint] -> Term -> TermNode
binders scope hints = checkedCoreEmbedding . buildCoreBinders scope hints

buildCoreBinders :: [Maybe Int] -> [Hint] -> Term -> TermNode
buildCoreBinders scope hints body
    = case hints of
        [] -> buildCoreUnder scope body
        hint : rest -> NApp (named "abs") (NLam (binderHint hint) noLamType (buildCoreBinders (Nothing : scope) rest body) Nothing) Nothing

embedFamily :: ConstId -> Int -> TermNode
embedFamily b i = embedFamilyAt b i []

embedFamilyAt :: ConstId -> Int -> UniverseInstance -> TermNode
embedFamilyAt b i instance' = foldlNApp (named "ind") [natural b, natural (toInteger i), embedInstance instance']

-- The name of a binder as a hint of Hol, which is a small identifier: a name
-- that is one is its own hint, and any other is written after `lol_` with
-- the number of each character that is no letter or digit (`recoverHint`).
binderHint :: Hint -> Maybe SmallId
binderHint hint
    = case hint of
        first : rest
            | isAsciiLower first && all hintChar rest && Set.notMember hint reservedNamedIdentifiers && take 4 hint /= "lol_" -> Just hint
            | otherwise -> Just ("lol_" ++ concatMap escaped hint)
        _ -> Nothing
    where
        hintChar ch = isAsciiLower ch || isAsciiUpper ch || isDigit ch || ch == '_'
        escaped ch = if isAsciiLower ch || isAsciiUpper ch || isDigit ch then [ch] else '_' : shows (fromEnum ch) "_"

recoverLevel :: TermNode -> Either String Level
recoverLevel node
    = case node of
        NCon (DC (DC_Named "lz")) _ -> Right (Closed 0)
        NApp (NCon (DC (DC_Named "ls")) _) level _ -> recoverLevel level >>= successor
        NApp (NCon (DC (DC_Named "lu")) _) level _ -> Successor <$> recoverLevel level
        NApp (NCon (DC (DC_Named "lp")) _) (NCon (DC (DC_NatL index)) _) _
            | index >= 0 && index <= toInteger (maxBound :: Int) -> Right (Parameter (fromInteger index))
        NApp (NApp (NCon (DC (DC_Named "lg")) _) (NCon (DC (DC_NatL owner)) _) _) (NCon (DC (DC_NatL slot)) _) _
            | owner >= 0 && slot >= 0 && slot <= toInteger (maxBound :: Int) -> Right (DefaultLevel owner (fromInteger slot))
        NApp (NApp (NCon (DC (DC_Named "lm")) _) left _) right _ -> Maximum <$> recoverLevel left <*> recoverLevel right
        _ -> Left "not a level"
    where
        -- lz/ls is the legacy unary numeral wire. Only that concrete encoding
        -- is collapsed; symbolic successors and maxima remain explicit syntax.
        successor (Closed number) = Right (Closed (number + 1))
        successor _ = Left "not a closed unary level"

recoverInstance :: TermNode -> Either String UniverseInstance
recoverInstance node = recoverList node >>= mapM recoverLevel

embedUniverseConstraints :: [UniverseConstraint] -> TermNode
embedUniverseConstraints = embedList (kindOf "uconstraint") . map constraint where
    constraint value = case value of
        UniverseLe left right -> foldlNApp (named "uc_le") [embedLevel left, embedLevel right]
        UniverseEq left right -> foldlNApp (named "uc_eq") [embedLevel left, embedLevel right]

recoverUniverseConstraints :: TermNode -> Either String [UniverseConstraint]
recoverUniverseConstraints node = recoverList node >>= mapM recoverConstraint

recoverConstraint :: TermNode -> Either String UniverseConstraint
recoverConstraint value = case unfoldlNApp value of
    (NCon (DC (DC_Named "uc_le")) _, [left, right]) -> UniverseLe <$> recoverLevel left <*> recoverLevel right
    (NCon (DC (DC_Named "uc_eq")) _, [left, right]) -> UniverseEq <$> recoverLevel left <*> recoverLevel right
    _ -> Left "not a universe constraint"

-- u_satisfiable emits closed logical syntax. This translation only changes
-- representation; the existing Hol Presburger service decides the formula.
universeFormula :: TermNode -> Either String TermNode
universeFormula node = do
    syntax <- evalStateT (formula [] node) 1
    return (NPresburgerCheck syntax Map.empty Nothing)
    where
        formula :: [Integer] -> TermNode -> StateT Integer (Either String) (PresburgerFormula PresburgerTermRep)
        formula bound value = case unfoldlNApp value of
            (NCon (DC (DC_Named "uf_true")) _, []) -> return (ValF True)
            (NCon (DC (DC_Named "uf_le")) _, [left, right]) -> LeqF <$> Trans.lift (number bound left) <*> Trans.lift (number bound right)
            (NCon (DC (DC_Named "uf_eq")) _, [left, right]) -> EqnF <$> Trans.lift (number bound left) <*> Trans.lift (number bound right)
            (NCon (DC (DC_Named "uf_and")) _, [left, right]) -> ConF <$> formula bound left <*> formula bound right
            (NCon (DC (DC_Named "uf_or")) _, [left, right]) -> DisF <$> formula bound left <*> formula bound right
            (NCon (DC (DC_Named "uf_exists")) _, [binder]) -> do
                variable <- get
                put (variable + 1)
                ExsF variable <$> formula (variable : bound) (snd (binderOf binder))
            _ -> Trans.lift (Left "not a closed universe satisfiability formula")
        number :: [Integer] -> TermNode -> Either String PresburgerTermRep
        number bound value = case unfoldlNApp value of
            (NCon (DC (DC_Named "lz")) _, []) -> Right Zero
            (NCon (DC (DC_Named operator)) _, [inner])
                | operator `elem` ["ls", "lu"] -> Succ <$> number bound inner
            (NCon (DC (DC_Named "lv")) _, [NIdx index])
                | index >= 0 -> case drop index bound of
                    variable : _ -> Right (IVar variable)
                    _ -> Left "unbound universe formula variable"
            _ -> Left "not a closed universe formula numeral"

-- Only the canonical level table gives runtime cells a parameter index.
-- Ordinary term variables are untouched. This is used for scoped oracle/UI
-- transport; recoverLevel still refuses every private runtime marker.
reifyUniverseLevels :: [TermNode] -> TermNode -> Either String TermNode
reifyUniverseLevels parameters node = universeSlots parameters >>= (\slots -> reifyUniverseSlots slots node)

reifyUniverseSlots :: [TermNode] -> TermNode -> Either String TermNode
reifyUniverseSlots slots = \value -> assertNonnegativeIndices value `seq` walk value where
    positions = Map.fromListWith min (zip slots [0 ..])
    walk value = case value of
        NApp (NCon (DC (DC_Named "lv")) _) cell _ -> case cell of
            NCon (DC (DC_NatL number)) _
                | number >= 0 -> Right (embedLevel (Closed number))
            _ -> case Map.lookup cell positions of
                Just index -> Right (embedLevel (Parameter index))
                Nothing -> Left "a runtime universe cell is outside its published context"
        NApp function argument location -> NApp <$> walk function <*> walk argument <*> pure location
        NLam hint typ body location -> NLam hint typ <$> walk body <*> pure location
        NPresburgerCheck formula free location -> NPresburgerCheck formula <$> mapM walk free <*> pure location
        _ -> Right value

-- The nominal in the proof's p_u_pool assumption is the only function
-- whose application denotes a universe. A fresh proof binds a fresh one.
universePool :: [TermNode] -> Either String (Maybe Unique)
universePool hypotheses = case [pool | NApp (NCon (DC (DC_Named "p_u_pool")) _) pool _ <- hypotheses] of
    [] -> Right Nothing
    [NCon (DC (DC_Unique pool _)) _] -> Right (Just pool)
    _ -> Left "the proof universe pool is not a single nominal"

universeSlots :: [TermNode] -> Either String [TermNode]
universeSlots = scopedUniverseSlots Nothing

scopedUniverseSlots :: Maybe Unique -> [TermNode] -> Either String [TermNode]
scopedUniverseSlots pool parameters = nubOrd . concat <$> mapM slot parameters where
    slot level = case unfoldlNApp level of
        (NCon (DC (DC_Named "lv")) _, [cell]) -> case cell of
            LVar (LV_ty_var _) -> Left "a type variable is not a universe level cell"
            LVar _ -> Right [cell]
            NCon (DC (DC_Unique _ _)) _ -> Right [cell]
            NCon (DC (DC_NatL number)) _
                | number >= 0 -> Right []
            NApp (NCon (DC (DC_Unique owner _)) _) (NCon (DC (DC_NatL index)) _) _
                | Just owner == pool && index >= 0 -> Right [cell]
            _ -> Left "a universe level cell is neither a variable, a nominal, a natural nor an index of this proof's pool"
        _ -> Left "not a published runtime universe level"

-- The inference table is deliberately distinct from an admitted context.
-- Its whitelisted cells are reabstracted only through lv; any remaining
-- ordinary hole is still rejected by closedOracleInput/recoverBlock/Local.
recoverOracleUniverses :: [TermNode] -> TermNode -> Either String (UniverseContext, [TermNode], TermNode)
recoverOracleUniverses hypotheses payload = do
    (parameters, constraints) <- case (first "u_inference_parameters", first "u_inference_context") of
        (Just table, Just context) -> (,) <$> recoverOpenList table <*> pure context
        (Nothing, Nothing) -> case (first "u_parameters", first "u_context") of
            (Just table, Just context) -> (,) <$> recoverList table <*> pure context
            (Nothing, Nothing) -> Right ([], embedUniverseConstraints [])
            _ -> Left "the oracle universe context is incomplete"
        _ -> Left "the oracle inference universe context is incomplete"
    pool <- universePool hypotheses
    slots <- scopedUniverseSlots pool parameters
    let reify = reifyUniverseSlots slots
    obligations <- reify constraints >>= recoverUniverseConstraints
    let arity = length slots
        context = UniverseContext ["u" ++ show index | index <- [0 .. arity - 1]] obligations
        valid (UniverseLe left right) = wellScopedLevel arity left && wellScopedLevel arity right
        valid (UniverseEq left right) = wellScopedLevel arity left && wellScopedLevel arity right
    if all valid obligations then return () else Left "the oracle universe context has an escaping parameter"
    closedPayload <- reify payload
    closedHypotheses <- mapM (\hypothesis -> if kernelContext hypothesis || universeContextHypothesis hypothesis then ended hypothesis >>= reify else Right hypothesis) hypotheses
    return (context, closedHypotheses, closedPayload)
    where
        -- The table of a proof ends in the variable where its registry
        -- grows: the oracle is given the table as it is now.
        ended hypothesis = case unfoldlNApp hypothesis of
            (predicate@(NCon (DC (DC_Named "u_inference_parameters")) _), [table]) -> (\cells -> foldlNApp predicate [embedList (kindOf "lvl") cells]) <$> recoverOpenList table
            _ -> Right hypothesis
        first predicate = case [value | hypothesis <- hypotheses, (NCon (DC (DC_Named actual)) _, [value]) <- [unfoldlNApp hypothesis], actual == predicate] of
            value : _ -> Just value
            [] -> Nothing

universeContextHypothesis :: TermNode -> Bool
universeContextHypothesis hypothesis = case unfoldlNApp hypothesis of
    (NCon (DC (DC_Named predicate)) _, [_]) -> predicate `elem` ["u_parameters", "u_context", "u_inference_parameters", "u_inference_context"]
    _ -> False

-- A hole (LoL.Core) is a logic variable applied to the abstractions around
-- it, the outermost first: the kernel gives it a value that may have their
-- variables.
holeVar :: Int -> LogicVar
holeVar n = LV_Named ("Hole" ++ show n)

-- The terms with their holes numbered from 0, in the order in which they are
-- read, and the number of the holes.
numberHoles :: [Term] -> ([Term], Int)
numberHoles items = runState (mapM (number 0) items) 0 where
    number depth term = case term of
        Hole _ -> state (\next -> (Hole next, next + 1))
        _ -> descend number depth term


-- The value that the kernel gave to a hole that `embedUnder` met under `scope`.
recoverHole :: [Maybe Int] -> TermNode -> Either String Term
recoverHole scope = recoverUnder (abstracted scope) . strip (length (abstracted scope)) where
    strip count node = if count <= 0 then node else strip (count - 1 :: Int) (snd (binderOf node))
    abstracted entries = case entries of
        [] -> []
        Nothing : rest -> Nothing : abstracted rest
        Just j : rest -> Just (j + 1) : abstracted (drop j rest)

recoverTerm :: TermNode -> Either String Term
recoverTerm = recoverUnder []

-- The scope has, for each Hol abstraction, Nothing or the number of functions
-- that it binds.
recoverUnder :: [Maybe Int] -> TermNode -> Either String Term
recoverUnder = recoverWith (const Nothing)

-- `free` gives the place of a variable that no abstraction of the term binds:
-- a constant that a `pi` of the kernel made.
recoverWith :: (TermNode -> Maybe Int) -> [Maybe Int] -> TermNode -> Either String Term
recoverWith free scope node
    = case node of
        NApp (NApp (NApp (NCon (DC (DC_Named "proj")) _) block _) field _) receiver _ ->
            Proj <$> recoverNumber block <*> recoverNatural field <*> recover scope receiver
        NApp (NApp (NApp (NCon (DC (DC_Named "pfield")) _) block _) field _) levels _ ->
            PField <$> recoverNumber block <*> recoverNatural field <*> recoverInstance levels
        -- A mark is no part of the term: its variable is a Hol abstraction that binds no variable of Core.
        NApp (NApp (NApp (NCon (DC (DC_Named "letin")) _) (NApp (NCon (DC (DC_Named "p_mark")) _) _ _) _) _ _) rest _ -> recoverWith free (Just 0 : scope) (snd (binderOf rest))
        NCon (DC (DC_Named "prop")) _ -> Right Prop
        NCon (DC (DC_Named "untyped")) _ -> Right (Hole 0)
        -- The variable of a mark is in the context of what the mark is over, with the mark for its body. Nothing mentions it.
        NApp (NCon (DC (DC_Named "p_mark")) _) _ _ -> Right Prop
        NApp (NCon (DC (DC_Named "typ")) _) level _ -> Type <$> recoverLevel level
        NApp (NApp (NCon (DC (DC_Named "cst")) _) c _) instance' _ -> Cst <$> recoverNumber c <*> recoverInstance instance'
        NApp (NApp (NApp (NCon (DC (DC_Named "ind")) _) b _) i _) instance' _ -> Ind <$> recoverNumber b <*> recoverNatural i <*> recoverInstance instance'
        NApp (NApp (NApp (NApp (NCon (DC (DC_Named "con")) _) b _) i _) j _) instance' _ -> Con <$> recoverNumber b <*> recoverNatural i <*> recoverNatural j <*> recoverInstance instance'
        NIdx h
            | h < 0 -> Left "negative de Bruijn index"
            | otherwise -> case splitAt h scope of
                (inner, Nothing : _) -> Right (Var (width inner))
                _ -> Left ("not a Core term: " ++ display node)
        NApp (NIdx h) (NCon (DC (DC_NatL j)) _) _
            | h < 0 || j < 0 -> Left "negative recursive variable index"
            | otherwise -> case splitAt h scope of
                (inner, Just count : _)
                    | j < toInteger count -> Right (Var (width inner + count - 1 - fromInteger j))
                _ -> Left ("not a Core term: " ++ display node)
        NApp (NApp (NCon (DC (DC_Named "prod")) _) a _) binder _ -> Pi (hint binder) <$> recover scope a <*> below binder
        NApp (NApp (NCon (DC (DC_Named "lam")) _) a _) binder _ -> Lam (hint binder) <$> recover scope a <*> below binder
        NApp (NApp (NApp (NCon (DC (DC_Named "letin")) _) t _) a _) binder _ -> Let (hint binder) <$> recover scope t <*> recover scope a <*> below binder
        NApp (NApp (NCon (DC (DC_Named "cast")) _) t _) a _ -> Cast <$> recover scope t <*> recover scope a
        NApp (NApp (NApp (NApp (NCon (DC (DC_Named "cas")) _) family _) p _) t _) bs _
            | Just (b, i, instance', qs) <- kept family [] -> do
                block <- recoverNumber b
                index <- recoverNatural i
                levels <- recoverInstance instance'
                parameters <- mapM (recover scope) qs
                (ys, clause) <- recoverBindersWith free scope p
                scrutinee <- recover scope t
                branches <- recoverList bs >>= mapM (recoverBindersWith free scope)
                return (Case block index levels parameters ys clause scrutinee branches)
        NApp (NApp (NCon (DC (DC_Named "app")) _) t _) u _ -> App <$> recover scope t <*> recover scope u
        NApp (NApp (NApp (NApp (NCon (DC (DC_Named "fix")) _) k _) ns _) fs _) (NLam f _ ts _) _ -> do
            selected <- recoverNatural k
            positions <- recoverList ns >>= mapM recoverNatural
            types <- recoverList fs >>= mapM (recover scope)
            items <- recoverList ts
            let count = length types
            bodies <- mapM (recover (Just count : scope)) items
            let names = concatMap marks (take 1 items) ++ repeat (recoverHint f)
            if selected < count && length positions == count && length bodies == count then return (Fix selected (zipWith ($) (zipWith3 Function names positions types) bodies)) else Left "inconsistent mutual fixpoint block"
        _ -> maybe (Left ("not a Core term: " ++ display node)) (\place -> Right (Var (width scope + place))) (free node)
    where
        recover = recoverWith free
        width = sum . map (maybe 1 id)
        hint binder = case marks (snd (binderOf binder)) of
            name@(_ : _) : _ -> name
            _ -> recoverHint (fst (binderOf binder))
        below = recover (Nothing : scope) . snd . binderOf
        -- The family of a match, applied to the parameters that the match keeps.
        kept family qs = case family of
            NApp (NApp (NApp (NCon (DC (DC_Named "ind")) _) b _) i _) instance' _ -> Just (b, i, instance', qs)
            NApp (NApp (NCon (DC (DC_Named "app")) _) function _) q _ -> kept function (q : qs)
            _ -> Nothing

-- The names of the marks at the head of a term of a proof. A binder that a
-- proof names has the mark of its name at the head of what it binds
-- (lol/hol/elab.hol, e_marked): `let _ : Prop := p_mark "name" in ...`. It is
-- no part of the term. The binders of a branch have theirs after the last of
-- them, one for each; a mark without a name leaves the binder as it is.
marks :: TermNode -> [Hint]
marks node
    = case node of
        NApp (NApp (NApp (NCon (DC (DC_Named "letin")) _) (NApp (NCon (DC (DC_Named "p_mark")) _) label _) _) _ _) rest _
            | Right name <- recoverString (rewrite NF label) -> name : marks (snd (binderOf rest))
        _ -> []

-- The name and the body of a binder. A term of Hol is eta-normal, so the
-- binder `x\ app M x` comes back from the engine as `app M`: its body is that
-- function applied to the variable.
binderOf :: TermNode -> (Maybe SmallId, TermNode)
binderOf node
    = case node of
        NLam x _ body _ -> (x, body)
        _ -> (Nothing, mkNApp (rewriteWithSusp node 0 1 [] NF) (mkNIdx 0))

recoverBinders :: [Maybe Int] -> TermNode -> Either String ([Hint], Term)
recoverBinders = recoverBindersWith (const Nothing)

recoverBindersWith :: (TermNode -> Maybe Int) -> [Maybe Int] -> TermNode -> Either String ([Hint], Term)
recoverBindersWith free outer whole = (\(hints, names, inner) -> (zipWith (\hint name -> if null name then hint else name) hints (names ++ repeat ""), inner)) <$> go outer whole where
    go scope node = case node of
        NApp (NCon (DC (DC_Named "abs")) _) binder _ -> (\(hints, names, inner) -> (recoverHint (fst (binderOf binder)) : hints, names, inner)) <$> go (Nothing : scope) (snd (binderOf binder))
        _ -> (,,) [] (marks node) <$> recoverWith free scope node

recoverNumber :: TermNode -> Either String Integer
recoverNumber node = case node of
    NCon (DC (DC_NatL n)) _
        | n >= 0 -> Right n
    _ -> Left "not a natural numeral"

recoverNatural :: TermNode -> Either String Int
recoverNatural node = do
    n <- recoverNumber node
    if n <= toInteger (maxBound :: Int) then Right (fromInteger n) else Left "natural index exceeds the host Int range"

recoverHint :: Maybe SmallId -> Hint
recoverHint hint
    = case hint of
        Just original@('l' : 'o' : 'l' : '_' : written) -> maybe original id (plain written)
        _ -> maybe "" id hint
    where
        plain text = case text of
            '_' : rest
                | (digits@(_ : _), '_' : after) <- span isDigit rest -> do
                    let limit = fromEnum (maxBound :: Char)
                    if length digits > length (show limit) then Nothing else do
                        let code = read digits
                        if code > limit then Nothing else (toEnum code :) <$> plain after
            ch : rest -> (ch :) <$> plain rest
            [] -> Just []

recoverList :: TermNode -> Either String [TermNode]
recoverList node
    = case node of
        NCon (DC DC_Nil) _ -> Right []
        NApp (NCon (DC DC_Nil) _) _ _ -> Right []
        NApp (NApp (NCon (DC DC_Cons) _) x _) xs _ -> (x :) <$> recoverList xs
        NApp (NApp (NApp (NCon (DC DC_Cons) _) _ _) x _) xs _ -> (x :) <$> recoverList xs
        _ -> Left "not a list"

-- The items of a list that may end in a variable (the cells of a proof are
-- registered in such a list): those before the variable. A list that ends
-- in anything else is none: what a program made of its registry is not read
-- as a shorter one.
recoverOpenList :: TermNode -> Either String [TermNode]
recoverOpenList node
    = case node of
        NApp (NApp (NCon (DC DC_Cons) _) x _) xs _ -> (x :) <$> recoverOpenList xs
        NApp (NApp (NApp (NCon (DC DC_Cons) _) _ _) x _) xs _ -> (x :) <$> recoverOpenList xs
        LVar _ -> Right []
        _ -> either (const (Left "a list of universe cells ends in neither a variable nor the empty list")) Right (recoverList node)

recoverString :: TermNode -> Either String String
recoverString node = recoverList node >>= mapM character where
    character (NCon (DC (DC_ChrL ch)) _) = Right ch
    character _ = Left "not a character"

-- Keep the wire display for protocol consumers (including source IDs), and
-- decode terms for user diagnostics. Free kernel nominals are displayed as
-- explicit local names, not mistaken for global declarations.
recoverReport :: TermNode -> Either String Report
recoverReport node = case unfoldlNApp node of
    (NCon (DC (DC_Named "rep")) _, [rule, args]) -> terms rule [] args
    (NCon (DC (DC_Named "rep_fields")) _, [rule, fields, args]) -> do
        roles <- recoverList fields >>= mapM recoverString
        terms rule roles args
    (NCon (DC (DC_Named "rep_constraint")) _, [rule, role, relation]) -> do
        label <- recoverString rule
        field <- recoverString role
        value <- recoverConstraint relation
        return (Report label [display relation] [Just (ReportConstraint [] field value)])
    _ -> Left "not a report"
    where
        terms rule roles args = do
            label <- recoverString rule
            values <- recoverList args
            let locals = nub (concatMap atoms values)
                hints = [prefix atom ++ show index | (index, atom) <- zip [0 :: Int ..] locals]
                prefix atom = case atom of
                    LVar _ -> "_hole"
                    _ -> "_local"
                decoded value = case unfoldlNApp value of
                    (head'@(LVar _), _) -> Just (ReportHole (maybe "_hole" (hints !!) (elemIndex head' locals)) [hint | (hint, NCon (DC (DC_Unique _ _)) _) <- zip hints locals])
                    _ -> case recoverWith (`elemIndex` locals) [] value of
                        Right term -> Just (ReportTerm hints term)
                        Left _ -> either (const Nothing) (\(binders, term) -> Just (ReportBinders hints binders term)) (recoverBindersWith (`elemIndex` locals) [] value)
                field "source" value = decoded value
                field role value = Just (ReportField role (decoded value))
                fields = if length roles == length values then zipWith field roles values else map decoded values
            return (Report label (map display values) fields)
        atoms term = case term of
            NCon (DC (DC_Unique _ _)) _ -> [term]
            LVar _ -> [term]
            NApp function argument _ -> atoms function ++ atoms argument
            NLam _ _ body _ -> atoms body
            _ -> []

display :: TermNode -> String
display node = prettyTerm Notation.initial initialCache node ""

embedInfo :: Info -> [TermNode]
embedInfo info = [natural (toInteger (infoParN info)), named (if infoElim info then "elim_all" else "elim_prop"), embedList (listOf (kindOf "mark")) (map (embedList (kindOf "mark") . map mark) (infoRecs info))] where
    mark recursive = named (if recursive then "rec" else "nonrec")

recoverInfo :: TermNode -> Either String Info
recoverInfo node
    = case node of
        NApp (NApp (NApp (NCon (DC (DC_Named "info")) _) n _) (NCon (DC (DC_Named elim)) _) _) ms _
            | elim `elem` ["elim_all", "elim_prop"] -> Info <$> recoverNatural n <*> pure (elim == "elim_all") <*> (recoverList ms >>= mapM (\marks -> recoverList marks >>= mapM mark))
        _ -> Left "not the info of a family"
    where
        mark (NCon (DC (DC_Named "rec")) _) = Right True
        mark (NCon (DC (DC_Named "nonrec")) _) = Right False
        mark _ = Left "not a mark"

cstTypeFact :: ConstId -> Term -> TermNode
cstTypeFact = cstTypeSchemeFact emptyUniverses

cstTypeSchemeFact :: UniverseContext -> ConstId -> Term -> TermNode
cstTypeSchemeFact context c = universeTermFact context "cst_type" [natural c]

cstBodyFact :: ConstId -> Term -> TermNode
cstBodyFact = cstBodySchemeFact emptyUniverses

cstBodySchemeFact :: UniverseContext -> ConstId -> Term -> TermNode
cstBodySchemeFact context c = universeTermFact context "cst_body" [natural c]

indTypeFact :: ConstId -> Int -> Term -> TermNode
indTypeFact = indTypeSchemeFact emptyUniverses

indTypeSchemeFact :: UniverseContext -> ConstId -> Int -> Term -> TermNode
indTypeSchemeFact context b i = universeTermFact context "ind_type" [natural b, natural (toInteger i)]

conTypeFact :: ConstId -> Int -> Int -> Term -> TermNode
conTypeFact = conTypeSchemeFact emptyUniverses

conTypeSchemeFact :: UniverseContext -> ConstId -> Int -> Int -> Term -> TermNode
conTypeSchemeFact context b i j = universeTermFact context "con_type" [natural b, natural (toInteger i), natural (toInteger j)]

indInfoFact :: ConstId -> Int -> Info -> TermNode
indInfoFact = indInfoSchemeFact emptyUniverses

indInfoSchemeFact :: UniverseContext -> ConstId -> Int -> Info -> TermNode
indInfoSchemeFact context b i info
    | null (universeNames context) = headFor (embedInstance [])
    | otherwise = forallType (mkTyList levelType) (rule (headFor (mkNIdx 0)) (instanceGuard context (mkNIdx 0)))
    where
        headFor instance' = foldlNApp (named "ind_info") (natural b : natural (toInteger i) : instance' : embedInfo info)

-- Saved scheme clauses contain only de Bruijn binders and closed templates.
-- Every occurrence gets an explicit instance checked by the Hol kernel before
-- structural parameter substitution; no host inference meta enters the Env.
universeTermFact :: UniverseContext -> String -> [TermNode] -> Term -> TermNode
universeTermFact context predicate keys term
    | null (universeNames context) = headFor (embedInstance []) (embedTerm term)
    | otherwise = forallType (mkTyList levelType) (forallType termType (rule
        (headFor (mkNIdx 1) (mkNIdx 0))
        (foldlNApp (mkNCon LO_and)
            [ instanceGuard context (mkNIdx 1)
            , foldlNApp (named "u_term") [mkNIdx 1, embedTerm term, mkNIdx 0]
            ])))
    where
        headFor instance' body = foldlNApp (named predicate) (keys ++ [instance', body])

instanceGuard :: UniverseContext -> TermNode -> TermNode
instanceGuard context instance' = foldlNApp (named "u_instance")
    [natural (toInteger (length (universeNames context))), embedUniverseConstraints (universeConstraints context), instance']

forallType :: MonoType Int -> TermNode -> TermNode
forallType typ = mkNApp (mkNCon LO_pi) . mkNLamHintTy Nothing (mkLamType typ)

rule :: TermNode -> TermNode -> TermNode
rule conclusion premise = foldlNApp (mkNCon LO_if) [conclusion, premise]

levelType, termType :: MonoType Int
levelType = TyCon (TCon (TC_Named "lvl") Star)
termType = TyCon (TCon (TC_Named "tm") Star)

-- The terms of the goals below are terms of the kernel: embedded Core terms,
-- or the variables that hold their elaborated forms (`elaborated`).
admitAxGoal :: TermNode -> TermNode
admitAxGoal a = mkNApp (named "admit_ax") a

admitDefGoal :: TermNode -> TermNode -> TermNode
admitDefGoal a t = foldlNApp (named "admit_def") [a, t]

-- `families` has, for each family, its type and the types of its constructors, parameters included.
blockOf :: ConstId -> Int -> [(TermNode, [TermNode])] -> TermNode
blockOf b parameters families = foldlNApp (named "block") [natural b, natural (toInteger parameters), embedList (kindOf "family") [foldlNApp (named "family") [a, terms ts] | (a, ts) <- families]]

embedBlock :: ConstId -> Int -> [(Term, [Term])] -> TermNode
embedBlock b parameters families = blockOf b parameters [(embedTerm a, map embedTerm ts) | (a, ts) <- families]

recordInfoFact :: ConstId -> Int -> Bool -> TermNode
recordInfoFact block fields eta = foldlNApp (named "record_info")
    [natural block, natural (toInteger fields), natural (if eta then 1 else 0)]

withTemplateShape :: UniverseContext -> TermNode -> TermNode -> TermNode
withTemplateShape context block admission = foldlNApp (mkNCon LO_and)
    [foldlNApp (named "template_shape") [natural (toInteger (length (universeNames context))), embedUniverseConstraints (universeConstraints context), block], admission]

withRecordShape :: UniverseContext -> TermNode -> Int -> Bool -> LogicVar -> TermNode -> TermNode
withRecordShape context block fields eta info admission = foldlNApp (mkNCon LO_and)
    [ admission
    , foldlNApp (named "u_record_shape")
        [ natural (toInteger (length (universeNames context)))
        , embedUniverseConstraints (universeConstraints context)
        , block, natural (toInteger fields), natural (if eta then 1 else 0), mkLVar info
        ]
    ]

admitIndGoal :: ConstId -> Int -> [(TermNode, [TermNode])] -> LogicVar -> TermNode
admitIndGoal b parameters families output = foldlNApp (named "admit_ind") [blockOf b parameters families, mkLVar output]

typeGoal :: TermNode -> LogicVar -> TermNode
typeGoal t output = foldlNApp (named "infer") [t, mkLVar output]

-- The type of the term in normal form by beta and iota, which `Check` shows.
shownGoal :: TermNode -> LogicVar -> LogicVar -> TermNode
shownGoal t typ output = foldlNApp (mkNCon LO_and) [typeGoal t typ, foldlNApp (named "bi") [mkLVar typ, mkLVar output]]

-- The term is typed before it is normalised.
normalGoal :: TermNode -> LogicVar -> LogicVar -> TermNode
normalGoal t typ output = foldlNApp (mkNCon LO_and) [typeGoal t typ, foldlNApp (named "norm") [t, mkLVar output]]

-- Elaboration. `written` is a goal about terms as
-- they are written: it is run under `pretyping`, which gives the matches of
-- the terms their parameters. Then each term of `forms` has its elaborated
-- form in the variable beside it, and `final` is a goal about those forms.
elaborated :: TermNode -> [(TermNode, LogicVar)] -> TermNode -> TermNode
elaborated written forms final = foldr1 both (foldlNApp (mkNCon LO_imply) [named "pretyping", written] : [foldlNApp (named "elab") [term, mkLVar form] | (term, form) <- forms] ++ [final]) where
    both left right = foldlNApp (mkNCon LO_and) [left, right]

-- The weak head normal form of a term in a local context: the innermost
-- variable first, each with its body when it is a local definition. The
-- output is applied to the variables, the outermost first. The kernel handles
-- the request; with `halting`, a `let` at the head of the term stays.
headGoal :: Bool -> [Maybe Term] -> Term -> LogicVar -> TermNode
headGoal halting context term output = close (reverse context) 0 where
    request = named (if halting then "oracle_halt" else "oracle_head")
    close entries depth = case entries of
        [] -> foldlNApp (named "oracle_answer") [mkNApp request (embedUnder (replicate depth Nothing) term), foldlNApp (mkLVar output) [mkNIdx h | h <- reverse [0 .. depth - 1]]]
        entry : rest -> mkNApp (mkNCon LO_pi) (mkNLamHint Nothing (maybe id (assume depth) entry (close rest (depth + 1))))
    assume depth body goal = foldlNApp (mkNCon LO_imply) [foldlNApp (named "var_body") [mkNIdx 0, embedUnder (replicate (depth + 1) Nothing) (lift 0 1 body)], goal]

-- The universe-aware dialogue uses the same local closure as headGoal. Local
-- definitions remain templates until the kernel publishes its fresh level
-- parameters; this guarded fact structurally instantiates each body there.
headGoalWithUniverses :: UniverseContext -> Bool -> [Maybe Term] -> Term -> LogicVar -> TermNode
headGoalWithUniverses universes halting context term output
    | universes == emptyUniverses = headGoal halting context term output
    | otherwise = close (reverse context) 0
    where
        request = named (if halting then "oracle_halt" else "oracle_head")
        close entries depth = case entries of
            [] -> foldlNApp (named "u_oracle_answer")
                [ natural (toInteger (length (universeNames universes)))
                , embedUniverseConstraints (universeConstraints universes)
                , mkNApp request (embedUnder (replicate depth Nothing) term)
                , foldlNApp (mkLVar output) [mkNIdx h | h <- reverse [0 .. depth - 1]] ]
            entry : rest -> mkNApp (mkNCon LO_pi) (mkNLamHint Nothing
                (foldlNApp (mkNCon LO_imply) [mkNApp (named "u_local") (mkNIdx 0), maybe id (assume depth) entry (close rest (depth + 1))]))
        assume depth body goal = foldlNApp (mkNCon LO_imply) [fact, goal] where
            template = embedUnder (replicate (depth + 1) Nothing) (lift 0 1 body)
            moved = rewriteWithSusp template 0 2 [] NF
            premise = foldlNApp (mkNCon LO_and)
                [ mkNApp (named "u_parameters") (mkNIdx 0)
                , foldlNApp (named "u_term") [mkNIdx 0, moved, mkNIdx 1] ]
            conclusion = foldlNApp (named "var_body") [mkNIdx 1, mkNIdx 0]
            fact = mkNApp (mkNCon LO_pi) (mkNLamHint Nothing
                (foldlNApp (mkNCon LO_if) [conclusion, mkNApp (mkNCon LO_sigma) (mkNLamHint Nothing premise)]))

-- The answer to `headGoal` for a context of `count` variables.
recoverHead :: Int -> TermNode -> Either String Term
recoverHead count = recoverHole (replicate count Nothing)

-- A block, as `admit_ind` has it.
recoverBlock :: TermNode -> Either String (ConstId, Int, [(Term, [Term])])
recoverBlock node
    = case node of
        NApp (NApp (NApp (NCon (DC (DC_Named "block")) _) b _) n _) fs _ -> (,,) <$> recoverNumber b <*> recoverNatural n <*> (recoverList fs >>= mapM family)
        _ -> Left "not a block"
    where
        family item = case item of
            NApp (NApp (NCon (DC (DC_Named "family")) _) a _) ts _ -> (,) <$> recoverTerm a <*> (recoverList ts >>= mapM recoverTerm)
            _ -> Left "not a family"

-- The oracle judges a closed Core payload and the kernel context it can use.
-- Proof machinery and other Hol predicates may carry unrelated open cells.
-- A recognized context clause is checked in full, including recursive type
-- premises; even an unused open kernel assumption is conservatively refused.
-- This selects transport syntax. It performs no CIC typing or reduction.
closedOracleInput :: TermNode -> [TermNode] -> Bool
closedOracleInput term hypotheses = all closed (term : filter (\hypothesis -> kernelContext hypothesis || universeContextHypothesis hypothesis) hypotheses) where
    closed = Set.null . Set.filter ordinary . getLVars
    ordinary (LV_ty_var _) = False
    ordinary _ = True

kernelContext :: TermNode -> Bool
kernelContext hypothesis = case unfoldlNApp hypothesis of
    (NCon (DC (DC_Named predicate)) _, _) -> predicate `elem` ["var_type", "var_body"]
    (NCon (DC (DC_LO operator)) _, [NLam _ _ body _])
        | operator == LO_pi || operator == LO_ty_pi -> kernelContext body
    (NCon (DC (DC_LO LO_if)) _, [conclusion, _]) -> kernelContext conclusion
    (NCon (DC (DC_LO LO_imply)) _, [_, conclusion]) -> kernelContext conclusion
    (NCon (DC (DC_LO LO_and)) _, facts) -> any kernelContext facts
    _ -> False

-- The local context of a goal of the kernel, from the hypotheses of the
-- goal, the latest first, and a term of that context. A variable is a
-- constant that a `pi` made: `var_type` gives it, `var_body` gives its body,
-- and the functions of a `fix` are one constant applied to their numbers. The
-- context has the innermost variable first, with its body when it has one.
recoverLocal :: [TermNode] -> TermNode -> Either String ([Maybe Term], Term)
recoverLocal hypotheses node = do
    slots <- foldM extend [] (reverse hypotheses)
    term <- recoverWith (place (map fst slots)) [] node
    return (map snd slots, term)
    where
        extend slots hypothesis = case hypothesis of
            -- A conversion of a hypothesis gives its variable a second type (lol/hol/proof.hol, pn_retype): it is one variable.
            NApp (NApp (NCon (DC (DC_Named "var_type")) _) (NCon made _) _) _ _
                | unique made, (made, Nothing) `notElem` map fst slots -> Right (((made, Nothing), Nothing) : slots)
            NApp (NApp (NCon (DC (DC_Named "var_body")) _) (NCon made _) _) body _
                | (slot, Nothing) : outer <- slots, slot == (made, Nothing) -> (\value -> (slot, Just value) : outer) <$> recoverWith (place (map fst outer)) [] body
            NApp (NCon (DC (DC_LO LO_pi)) _) (NLam _ _ (NApp (NCon (DC (DC_LO LO_pi)) _) (NLam _ _ (NApp (NApp (NCon (DC (DC_LO LO_if)) _) (NApp (NApp (NCon (DC (DC_Named "var_type")) _) (NApp (NCon made _) (NIdx 1) _) _) (NIdx 0) _) _) premise _) _) _) _) _
                | unique made, Just types <- functions premise [] -> (\count -> [((made, Just j), Nothing) | j <- reverse [0 .. toInteger (length count) - 1]] ++ slots) <$> recoverList types
            _ -> Right slots
        -- `nth J Fs A`, with or without the type at which `nth` is used
        functions premise arguments = case premise of
            NApp function argument _ -> functions function (argument : arguments)
            NCon (DC (DC_Named "nth")) _
                | [_, types, _] <- drop (length arguments - 3) arguments -> Just types
            _ -> Nothing
        unique made = case made of
            DC (DC_Unique _ _) -> True
            _ -> False
        place slots item = case item of
            NCon made _ -> elemIndex (made, Nothing) slots
            NApp (NCon made _) (NCon (DC (DC_NatL j)) _) _ -> elemIndex (made, Just j) slots
            _ -> Nothing
