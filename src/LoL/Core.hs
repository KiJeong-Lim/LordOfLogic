module LoL.Core where

import Data.Functor.Const (Const (..))
import Data.Monoid (Any (..))
import qualified Data.Set as Set

data Level
    = Closed Integer
    | Parameter Int
    | DefaultLevel ConstId Int
    | Successor Level
    | Maximum Level Level
    deriving (Eq, Ord, Show)

type UniverseInstance = [Level]

data UniverseConstraint
    = UniverseLe Level Level
    | UniverseEq Level Level
    deriving (Eq, Ord, Show)

data UniverseContext
    = UniverseContext
        { universeNames       :: [Hint]
        , universeConstraints :: [UniverseConstraint]
        }
    deriving (Eq, Ord, Show)

emptyUniverses :: UniverseContext
emptyUniverses = UniverseContext [] []

type ConstId = Integer

type Hint = String

-- Variables are de Bruijn indices. `Let x t a u` is `let x := t : a in u`.
-- `Cast t a` is `(t : a)`, the term `t` with the type that is written for it.
-- `Ind b i us` is family `i` of the inductive block `b`, and `Con b i j us`
-- is constructor `j` of that family, at universe instance `us`.
-- `Case b i us qs ys p t bs` is a match on that
-- family: `qs` are the parameters of the family that the match keeps, `p` is
-- the return clause under the binders `ys`, which are the indices and then the
-- scrutinee `t`, and each branch is under the arguments of its constructor.
-- `Fix k fs` is the function `k` of the block `fs`. `Hole n` is a parameter of
-- a match that the kernel has not given yet: no term
-- of the environment has one. The copy of a term that is printed has one for
-- the type of a `let` that is not shown (LoL.Env.visible).
data Term
    = Prop
    | Type Level
    | Cst ConstId UniverseInstance
    | Ind ConstId Int UniverseInstance
    | Con ConstId Int Int UniverseInstance
    | PField ConstId Int UniverseInstance
    | Proj ConstId Int Term
    | Var Int
    | Pi Hint Term Term
    | Lam Hint Term Term
    | Let Hint Term Term Term
    | Cast Term Term
    | App Term Term
    | Case ConstId Int UniverseInstance [Term] [Hint] Term Term [([Hint], Term)]
    | Fix Int [Function]
    | Hole Int
    deriving (Show)

-- `f (xs : As) {struct x} : B := t` has the type `forall xs : As, B` and the
-- body `fun xs : As => t`; functionArgN is the position of `x` among `xs`. The
-- functions of the block are bound in the bodies, the first one outermost, and
-- not in the types.
data Function
    = Function
        { functionName :: Hint
        , functionArgN :: Int
        , functionType :: Term
        , functionBody :: Term
        }
    deriving (Show)

-- What a global name stands for.
data Global
    = GlobalCst ConstId
    | GlobalInd ConstId Int
    | GlobalCon ConstId Int Int
    | GlobalProj ConstId Int
    deriving (Eq, Ord, Show)

-- Binder names are display hints: equality is alpha-equivalence.
instance Eq Term where
    Prop == Prop = True
    Type l1 == Type l2 = l1 == l2
    Cst c1 us1 == Cst c2 us2 = c1 == c2 && us1 == us2
    Ind b1 i1 us1 == Ind b2 i2 us2 = b1 == b2 && i1 == i2 && us1 == us2
    Con b1 i1 j1 us1 == Con b2 i2 j2 us2 = b1 == b2 && i1 == i2 && j1 == j2 && us1 == us2
    PField b j us == PField c k vs = b == c && j == k && us == vs
    Proj b j t == Proj c k u = b == c && j == k && t == u
    Var i1 == Var i2 = i1 == i2
    Pi _ a1 b1 == Pi _ a2 b2 = a1 == a2 && b1 == b2
    Lam _ a1 t1 == Lam _ a2 t2 = a1 == a2 && t1 == t2
    Let _ t1 a1 u1 == Let _ t2 a2 u2 = t1 == t2 && a1 == a2 && u1 == u2
    Cast t1 a1 == Cast t2 a2 = t1 == t2 && a1 == a2
    App t1 u1 == App t2 u2 = t1 == t2 && u1 == u2
    Case b1 i1 us1 qs1 ys1 p1 t1 bs1 == Case b2 i2 us2 qs2 ys2 p2 t2 bs2 = b1 == b2 && i1 == i2 && us1 == us2 && qs1 == qs2 && length ys1 == length ys2 && p1 == p2 && t1 == t2 && map (length . fst) bs1 == map (length . fst) bs2 && map snd bs1 == map snd bs2
    Fix k1 fs1 == Fix k2 fs2 = k1 == k2 && fs1 == fs2
    Hole n1 == Hole n2 = n1 == n2
    _ == _ = False

instance Eq Function where
    Function _ n1 a1 t1 == Function _ n2 a2 t2 = n1 == n2 && a1 == a2 && t1 == t2

apps :: Term -> [Term] -> Term
apps = foldl App

fromGlobal :: Global -> Term
fromGlobal = fromGlobalAt []

fromGlobalAt :: UniverseInstance -> Global -> Term
fromGlobalAt universes global
    = case global of
        GlobalCst c -> Cst c universes
        GlobalInd b i -> Ind b i universes
        GlobalCon b i j -> Con b i j universes
        GlobalProj b j -> PField b j universes

-- `lift cutoff amount t`: the indices of `t` that `cutoff` binders do not bind grow by `amount`.
lift :: Int -> Int -> Term -> Term
lift cutoff amount term
    = case term of
        Var i
            | i >= cutoff -> Var (i + amount)
        Proj b j t -> Proj b j (lift cutoff amount t)
        Pi x a b -> Pi x (lift cutoff amount a) (lift (cutoff + 1) amount b)
        Lam x a t -> Lam x (lift cutoff amount a) (lift (cutoff + 1) amount t)
        Let x t a u -> Let x (lift cutoff amount t) (lift cutoff amount a) (lift (cutoff + 1) amount u)
        Cast t a -> Cast (lift cutoff amount t) (lift cutoff amount a)
        App t u -> App (lift cutoff amount t) (lift cutoff amount u)
        Case b i us qs ys p t bs -> Case b i us (map (lift cutoff amount) qs) ys (lift (cutoff + length ys) amount p) (lift cutoff amount t) [(zs, lift (cutoff + length zs) amount body) | (zs, body) <- bs]
        Fix k fs -> Fix k [f { functionType = lift cutoff amount (functionType f), functionBody = lift (cutoff + length fs) amount (functionBody f) } | f <- fs]
        _ -> term

-- The declarations that a term mentions: constants and inductive blocks.
levelOwners :: Level -> Set.Set ConstId
levelOwners level = case level of
    DefaultLevel owner _ -> Set.singleton owner
    Successor inner -> levelOwners inner
    Maximum l r -> Set.union (levelOwners l) (levelOwners r)
    _ -> Set.empty

constraintOwners :: UniverseContext -> Set.Set ConstId
constraintOwners context = Set.unions (map owners (universeConstraints context)) where
    owners (UniverseLe l r) = Set.union (levelOwners l) (levelOwners r)
    owners (UniverseEq l r) = Set.union (levelOwners l) (levelOwners r)

constantsOf :: Term -> Set.Set ConstId
constantsOf = constantsWith levelOwners

-- A universe name needs its owner to load a declaration. For Print Assumptions
-- it names a level and contributes no logical axiom.
constantsWith :: (Level -> Set.Set ConstId) -> Term -> Set.Set ConstId
constantsWith owners = visit where
    visit term
        = case term of
            Type level -> owners level
            Cst c us -> Set.insert c (Set.unions (map owners us))
            Ind b _ us -> Set.insert b (Set.unions (map owners us))
            Con b _ _ us -> Set.insert b (Set.unions (map owners us))
            PField b _ us -> Set.insert b (Set.unions (map owners us))
            Proj b _ r -> Set.insert b (visit r)
            Pi _ a b -> Set.union (visit a) (visit b)
            Lam _ a t -> Set.union (visit a) (visit t)
            Let _ t a u -> Set.unions [visit t, visit a, visit u]
            Cast t a -> Set.union (visit t) (visit a)
            App t u -> Set.union (visit t) (visit u)
            Case b _ us qs _ p t bs -> Set.unions (Set.insert b (Set.unions (map owners us)) : visit p : visit t : map visit qs ++ map (visit . snd) bs)
            Fix _ fs -> Set.unions (concat [[visit (functionType f), visit (functionBody f)] | f <- fs])
            _ -> Set.empty

-- `hinted written elaborated`: the elaborated term with the names of the
-- written one, as far as the two have the same shape. Names are display
-- hints, and the kernel does not keep them when it elaborates a term. A
-- cast that the elaborated term no longer has (a normal form has none) is
-- passed.
hinted :: Term -> Term -> Term
hinted written elaborated
    = case (written, elaborated) of
        (Proj b j r, Proj c k s)
            | b == c && j == k -> Proj b j (hinted r s)
        (Pi x a b, Pi _ a' b') -> Pi x (hinted a a') (hinted b b')
        (Lam x a t, Lam _ a' t') -> Lam x (hinted a a') (hinted t t')
        (Let x t a u, Let _ t' a' u') -> Let x (hinted t t') (hinted a a') (hinted u u')
        (Cast t a, Cast t' a') -> Cast (hinted t t') (hinted a a')
        (Cast t _, _) -> hinted t elaborated
        (App t u, App t' u') -> App (hinted t t') (hinted u u')
        (Case b i _ qs ys p t bs, Case c j us qs' ys' p' t' bs')
            | b == c && i == j && length qs == length qs' && length ys == length ys' && map (length . fst) bs == map (length . fst) bs' -> Case c j us (zipWith hinted qs qs') ys (hinted p p') (hinted t t') [(zs, hinted body body') | ((zs, body), (_, body')) <- zip bs bs']
        (Fix _ fs, Fix k fs')
            | length fs == length fs' -> Fix k [g' { functionName = functionName g, functionType = hinted (functionType g) (functionType g'), functionBody = hinted (functionBody g) (functionBody g') } | (g, g') <- zip fs fs']
        _ -> elaborated

-- Whether a term has a match: such a term is elaborated.
hasMatch :: Term -> Bool
hasMatch term
    = case term of
        Case {} -> True
        _ -> getAny (getConst (descend (\_ part -> Const (Any (hasMatch part))) 0 term))

-- Whether a term has a `let`: the host asks the kernel which types of them it shows (LoL.Env.visible).
hasLet :: Term -> Bool
hasLet term
    = case term of
        Let {} -> True
        _ -> getAny (getConst (descend (\_ part -> Const (Any (hasLet part))) 0 term))

-- `wellScoped depth t`: every index of `t` is bound by `t` or by one of `depth` enclosing binders, and no number of `t` is negative.
wellScoped :: Int -> Term -> Bool
wellScoped = wellScopedUniverses 0

wellScopedLevel :: Int -> Level -> Bool
wellScopedLevel count level
    = case level of
        Closed n -> n >= 0
        DefaultLevel owner slot -> owner >= 0 && slot >= 0
        Parameter n -> n >= 0 && n < count
        Successor value -> wellScopedLevel count value
        Maximum left right -> wellScopedLevel count left && wellScopedLevel count right

-- A level of an instance is any level in scope. A term that is written
-- names a level there, and so does one that Rocq could print; the term of a
-- proof may have an expression, the least level of a universe that only the
-- proof used (Rocq keeps such a universe private to the proof).
wellScopedInstance :: Int -> UniverseInstance -> Bool
wellScopedInstance count = all (wellScopedLevel count)

wellScopedUniverses :: Int -> Int -> Term -> Bool
wellScopedUniverses count depth term
    = case term of
        Type l -> wellScopedLevel count l
        Cst c us -> c >= 0 && wellScopedInstance count us
        Ind b i us -> b >= 0 && i >= 0 && wellScopedInstance count us
        Con b i j us -> b >= 0 && i >= 0 && j >= 0 && wellScopedInstance count us
        PField b j us -> b >= 0 && j >= 0 && wellScopedInstance count us
        Proj b j t -> b >= 0 && j >= 0 && scoped depth t
        Var i -> 0 <= i && i < depth
        Pi _ a b -> scoped depth a && scoped (depth + 1) b
        Lam _ a t -> scoped depth a && scoped (depth + 1) t
        Let _ t a u -> scoped depth t && scoped depth a && scoped (depth + 1) u
        Cast t a -> scoped depth t && scoped depth a
        App t u -> scoped depth t && scoped depth u
        Case b i us qs ys p t bs -> b >= 0 && i >= 0 && wellScopedInstance count us && all (scoped depth) qs && scoped (depth + length ys) p && scoped depth t && and [scoped (depth + length zs) body | (zs, body) <- bs]
        Fix k fs -> k >= 0 && k < length fs && and [functionArgN f >= 0 && scoped depth (functionType f) && scoped (depth + length fs) (functionBody f) | f <- fs]
        Hole n -> n >= 0
        Prop -> True
    where
        scoped = wellScopedUniverses count

-- Universe substitution is structural. Arithmetic and entailment stay in Hol.
substituteLevel :: UniverseInstance -> Level -> Either String Level
substituteLevel instance_ level
    = case level of
        DefaultLevel {} -> Right level
        Closed n -> Right (Closed n)
        Parameter n
            | n >= 0, value : _ <- drop n instance_ -> Right value
            | otherwise -> Left "Universe parameter is outside its declaration context"
        Successor value -> Successor <$> substituteLevel instance_ value
        Maximum left right -> Maximum <$> substituteLevel instance_ left <*> substituteLevel instance_ right

substituteUniverses :: UniverseInstance -> Term -> Either String Term
substituteUniverses instance_ = traverseTermLevels (substituteLevel instance_)

traverseTermLevels :: Applicative f => (Level -> f Level) -> Term -> f Term
traverseTermLevels visit = replace where
    levels = traverse visit
    replace term = case term of
        Type level -> Type <$> visit level
        PField b j us -> PField b j <$> levels us
        Cst c us -> Cst c <$> levels us
        Ind b i us -> Ind b i <$> levels us
        Con b i j us -> Con b i j <$> levels us
        Case b i us qs ys p t bs -> Case b i <$> levels us <*> traverse replace qs <*> pure ys <*> replace p <*> replace t <*> traverse (\(zs, body) -> (,) zs <$> replace body) bs
        _ -> descend (\_ -> replace) 0 term

levelParameters :: Level -> Set.Set Int
levelParameters level = case level of
    Closed _ -> Set.empty
    DefaultLevel {} -> Set.empty
    Parameter i -> Set.singleton i
    Successor a -> levelParameters a
    Maximum a b -> Set.union (levelParameters a) (levelParameters b)

termParameters :: Term -> Set.Set Int
termParameters = getConst . traverseTermLevels (Const . levelParameters)

-- The levels that `particular` has where `general` has its universe
-- parameters, when the second term is the first with levels for them.
instanceOf :: Term -> Term -> Maybe [(Int, Level)]
instanceOf general particular = terms general particular [] where
    level left right found = case (left, right) of
        (Parameter index, _) -> case lookup index found of
            Nothing -> Just ((index, right) : found)
            Just value -> if value == right then Just found else Nothing
        (DefaultLevel {}, DefaultLevel {}) | left == right -> Just found
        (Closed n, Closed m) -> if n == m then Just found else Nothing
        (Successor inner, Successor other) -> level inner other found
        (Successor inner, Closed m) -> if m > 0 then level inner (Closed (m - 1)) found else Nothing
        (Maximum a b, Maximum c d) -> level a c found >>= level b d
        _ -> Nothing
    levels left right found = if length left == length right then foldr (\(a, b) rest -> rest >>= level a b) (Just found) (zip left right) else Nothing
    many left right found = if length left == length right then foldr (\(a, b) rest -> rest >>= terms a b) (Just found) (zip left right) else Nothing
    terms left right found = case (left, right) of
        (Prop, Prop) -> Just found
        (Type l, Type m) -> level l m found
        (Cst c us, Cst d vs) -> if c == d then levels us vs found else Nothing
        (Ind b i us, Ind c j vs) -> if b == c && i == j then levels us vs found else Nothing
        (Con b i j us, Con c k l vs) -> if b == c && i == k && j == l then levels us vs found else Nothing
        (PField b j us, PField c k vs) -> if b == c && j == k then levels us vs found else Nothing
        (Proj b j r, Proj c k s) -> if b == c && j == k then terms r s found else Nothing
        (Var i, Var j) -> if i == j then Just found else Nothing
        (Pi _ a b, Pi _ c d) -> terms a c found >>= terms b d
        (Lam _ a b, Lam _ c d) -> terms a c found >>= terms b d
        (Let _ t a u, Let _ s c v) -> terms t s found >>= terms a c >>= terms u v
        (Cast t a, Cast s c) -> terms t s found >>= terms a c
        (App t u, App s v) -> terms t s found >>= terms u v
        (Case b i us qs ys p t bs, Case c j vs rs zs q s cs) ->
            if b == c && i == j && length ys == length zs && map (length . fst) bs == map (length . fst) cs
                then levels us vs found >>= many qs rs >>= terms p q >>= terms t s >>= many (map snd bs) (map snd cs)
                else Nothing
        (Fix k fs, Fix l gs) ->
            if k == l && map functionArgN fs == map functionArgN gs
                then many (map functionType fs) (map functionType gs) found >>= many (map functionBody fs) (map functionBody gs)
                else Nothing
        (Hole n, Hole m) -> if n == m then Just found else Nothing
        _ -> Nothing

-- `descend f depth t`: the parts of `t`, each one replaced by what `f` gives
-- for it and for `depth` plus the number of binders of `t` around it.
descend :: Applicative m => (Int -> Term -> m Term) -> Int -> Term -> m Term
descend f depth term
    = case term of
        Proj b j t -> Proj b j <$> f depth t
        Pi x a b -> Pi x <$> f depth a <*> f (depth + 1) b
        Lam x a t -> Lam x <$> f depth a <*> f (depth + 1) t
        Let x t a u -> Let x <$> f depth t <*> f depth a <*> f (depth + 1) u
        Cast t a -> Cast <$> f depth t <*> f depth a
        App t u -> App <$> f depth t <*> f depth u
        Case b i us qs ys p t bs -> Case b i us <$> traverse (f depth) qs <*> pure ys <*> f (depth + length ys) p <*> f depth t <*> traverse (\(zs, body) -> (,) zs <$> f (depth + length zs) body) bs
        Fix k fs -> Fix k <$> traverse (\g -> (\a t -> g { functionType = a, functionBody = t }) <$> f depth (functionType g) <*> f (depth + length fs) (functionBody g)) fs
        _ -> pure term
