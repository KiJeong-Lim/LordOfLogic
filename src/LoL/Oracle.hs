module LoL.Oracle (World (..), Failure (..), Judge, refuse, reduced, halted, spine, substitute, occurs, instantiate, exposed, abstractCons, familyOf, positive) where

import Control.Monad
import Control.Monad.Trans.Except
import Data.Functor.Const (Const (..))
import Data.Functor.Identity (runIdentity)
import qualified Data.Set as Set
import LoL.Core
import LoL.Oracle.Tree

-- The oracle. The kernel hands it two judgments:
-- [I-Pos] for an inductive block, here, and the guard condition of a block of
-- functions, in LoL.Oracle.Guard. Both are judged as kernel/indtypes.ml and
-- kernel/inductive.ml of Rocq 9.0 judge them, with the soundness repairs to
-- the guard condition that LoL.Oracle.Guard names.
--
-- Nothing is reduced here. Where Rocq reduces a term to weak head normal form,
-- the oracle asks the kernel for that form (worldHead), or for the form that
-- keeps a `let` at its head (worldHalt). It knows of the environment what it
-- kept of each block that it judged (worldSpec) and the bodies of the
-- constants that reduce (worldBody).
data World
    = World
        { worldHead :: [Maybe Term] -> Term -> IO (Either Failure Term)
        , worldHalt :: [Maybe Term] -> Term -> IO (Either Failure Term)
        , worldSpec :: ConstId -> UniverseInstance -> Maybe Spec
        , worldFixp :: ConstId -> Int -> Bool
        , worldBody :: ConstId -> UniverseInstance -> Maybe Term
        }
    deriving ()

-- A failed reduction is not evidence against the judgment: it is
-- `Unavailable`, not `Refuted`.
data Failure
    = Refuted String
    | Unavailable String
    deriving (Eq, Show)

type Judge = ExceptT Failure IO

refuse :: String -> Judge a
refuse = throwE . Refuted

-- A context has the innermost variable first, each with its body when it is a
-- local definition.

-- The weak head normal form of a term (`whd_all` of Rocq), from the kernel. A
-- term that is in that form as it is written is not asked about.
reduced :: World -> [Maybe Term] -> Term -> Judge Term
reduced world context term = if settled world False context term then return term else ExceptT (worldHead world context term)

-- The same, but a `let` at the head of the term stays (`whd_allnolet`).
halted :: World -> [Maybe Term] -> Term -> Judge Term
halted world context term = if settled world True context term then return term else ExceptT (worldHalt world context term)

-- Whether a term is in weak head normal form as it is written.
settled :: World -> Bool -> [Maybe Term] -> Term -> Bool
settled world halting context term
    = case spine term of
        (Var i, _) -> case drop i context of
            Just _ : _ -> False
            _ -> True
        (Cst c us, _) -> maybe True (const False) (worldBody world c us)
        (Lam {}, arguments) -> null arguments
        (Fix {}, arguments) -> null arguments
        (Let {}, _) -> halting
        (Proj {}, _) -> False
        (PField {}, _) -> False
        (Cast {}, _) -> False
        (Case {}, _) -> False
        _ -> True

-- A term as a function and its arguments; the function is not an application.
spine :: Term -> (Term, [Term])
spine = gather [] where
    gather arguments term = case term of
        App function argument -> gather (argument : arguments) function
        _ -> (term, arguments)

-- `substitute vs t`: variable `k` of `t` is `vs !! k` when it is that near,
-- and another variable is as many places nearer as `vs` has terms.
substitute :: [Term] -> Term -> Term
substitute values = runIdentity . replace 0 where
    count = length values
    replace depth term = case term of
        Var i
            | i < depth -> pure term
            | i - depth < count -> pure (lift 0 depth (values !! (i - depth)))
            | otherwise -> pure (Var (i - count))
        _ -> descend replace depth term

-- Whether one of the `count` variables from `first` on occurs in the term.
occurs :: Int -> Int -> Term -> Bool
occurs first count = any (\i -> first <= i && i < first + count) . variables 0 where
    variables depth term = case term of
        Var i -> [i - depth | i >= depth]
        _ -> getConst (descend (\below part -> Const (variables below part)) depth term)

-- A product type applied to arguments (`hnf_prod_applist` of Rocq).
instantiate :: World -> [Maybe Term] -> Term -> [Term] -> Judge Term
instantiate world context = foldM apply where
    apply product argument = do
        found <- reduced world context product
        case found of
            Pi _ _ body -> return (substitute [argument] body)
            _ -> refuse "a type has fewer products than it is given arguments"

-- `exposed world n t`: `t` begins with `n` products, the parameters. What
-- follows them is reduced as far as each product, as Rocq reduces the arity of
-- a family and the type of a constructor: the number of those products, and
-- the type with them written out.
exposed :: World -> Int -> Term -> Judge (Int, Term)
exposed world = under [] where
    under context left term
        | left > (0 :: Int) = case term of
            Pi x a b -> fmap (Pi x a) <$> under (Nothing : context) (left - 1) b
            _ -> refuse "a type does not begin with the parameters"
        | otherwise = walk context term
    walk context term = do
        found <- reduced world context term
        case found of
            Pi x a b -> (\(count, rest) -> (count + 1, Pi x a rest)) <$> walk (Nothing : context) b
            _ -> return (0, found)

-- The type of a constructor of the block `container`, with each family of
-- that block, applied to its first `parameters` parameters, replaced by a
-- variable: family `i` is variable `families - 1 - i` of the context around
-- the type (`abstract_mind_lc` of Rocq).
abstractCons :: Int -> Int -> ConstId -> Term -> Term
abstractCons families parameters container = runIdentity . replace 0 where
    replace depth term = case spine term of
        (Ind found i _, arguments)
            | found == container -> skip depth i parameters arguments
        _ -> descend replace depth term
    skip depth i left arguments = case arguments of
        _ : rest
            | left > (0 :: Int) -> skip depth i (left - 1) rest
        _ -> do
            inner <- mapM (replace (left + depth)) arguments
            return (iterate (Lam "" Prop) (apps (Var (families + left + depth - i - 1)) inner) !! left)

-- A family that the oracle has judged, with what it kept of its block.
familyOf :: World -> Term -> Maybe ((ConstId, Int, UniverseInstance), Spec, Packet)
familyOf world term
    = case term of
        Ind block i us
            | Just spec <- worldSpec world block us, packet : _ <- drop i (specFams spec) -> Just ((block, i, us), spec, packet)
        _ -> Nothing

-- [I-Pos] for the block `block`, which has `parameters` parameters and the
-- given families, each with its type and the types of its constructors: as
-- `check_positivity` of Rocq judges it, with nested occurrences. The answer is
-- what the oracle keeps of the block.
--
-- A family of the block stays the constant that it is, where Rocq has a
-- variable for it: `fams` has the tree of each one. `ras` has, for each
-- variable of the context, whether it stands for an inductive family, and its
-- tree.
positive :: World -> ConstId -> Int -> [(Term, [Term])] -> IO (Either Failure Spec)
positive world block parameters families = runExceptT $ do
    results <- mapM family (zip [0 ..] families)
    shapes <- forM families $ \(arity, constructors) -> (,) <$> exposed world parameters arity <*> mapM (exposed world parameters) constructors
    return Spec
        { specParN = parameters
        , specRecN = minimum (parameters : map fst results)
        , specFams = [Packet { packetIdxN = indices, packetType = arity, packetCons = constructors, packetTree = tree } | (((indices, arity), constructors), tree) <- zip shapes (makeRec (map snd results))]
        }
    where
        start = (replicate parameters Nothing, replicate parameters (Norec, norec), recCalls (length families))
        within = Set.member block . constantsOf
        negative = "a family of the block occurs where it is not strictly positive"
        push (context, ras, fams) = (Nothing : context, (Norec, norec) : ras, fams)
        family (i, (_, constructors)) = do
            results <- forM constructors $ \signature -> do
                body <- strip parameters signature
                arguments start (Just i) parameters body
            return (minimum (parameters : map fst results), Node (Mrec block i) (map snd results))
        strip left term
            | left <= (0 :: Int) = return term
            | otherwise = case term of
                Pi _ _ rest -> strip (left - 1) rest
                _ -> refuse "the type of a constructor does not begin with the parameters"
        -- `check_constructors`: the arguments of a constructor, and its
        -- conclusion when `headed` names the family of the constructor.
        -- `left` counts the parameters that every recursive occurrence so
        -- far has kept.
        arguments ienv headed = walk ienv [] where
            walk now@(context, _, _) found left term = do
                (function, items) <- spine <$> reduced world context term
                case function of
                    Pi _ domain rest -> do
                        (next, tree) <- strictly now left domain
                        walk (push now) (tree : found) next rest
                    _ -> do
                        case headed of
                            Just i
                                | Ind found j _ <- function, found == block, i == j -> conclusion context items
                                | otherwise -> refuse "the type of a constructor does not end in its family"
                            Nothing -> when (any within items) (refuse negative)
                        return (left, reverse found)
        -- `check_correct_par`
        conclusion context items = do
            when (length items < parameters) (refuse "the family of a constructor is not applied to the parameters")
            forM_ (zip [0 ..] (take parameters items)) $ \(k, item) -> do
                found <- reduced world context item
                unless (found == Var (length context - 1 - k)) (refuse "the family of a constructor is not applied to the parameters")
            when (any within (drop parameters items)) (refuse negative)
        -- `check_strict_positivity`: the type of one argument
        strictly now@(context, ras, fams) left term = do
            (function, items) <- spine <$> reduced world context term
            case function of
                Pi _ domain rest -> do
                    clear <- if within domain then not . within <$> reduced world context domain else return True
                    unless clear (refuse negative)
                    strictly (push now) left rest
                Ind found j us
                    | found == block -> do
                        heads <- mapM (reduced world context) items
                        when (left > 0 && length heads < left) (refuse negative)
                        when (any within heads) (refuse negative)
                        return (length (takeWhile id [item == Var (length context - 1 - k) | (k, item) <- zip [0 ..] (take left heads)]), fams !! j)
                    | any within items -> nested now left found j us items
                    | otherwise -> return (left, norec)
                Var k
                    | (_, tree) : _ <- drop k ras -> do
                        heads <- mapM (reduced world context) items
                        when (any within heads) (refuse negative)
                        return (left, tree)
                    | otherwise -> return (left, norec)
                _
                    | within function || any within items -> refuse negative
                    | otherwise -> return (left, norec)
        -- `check_positivity_nested`: a family of the block in a parameter of
        -- another inductive family
        nested (context, ras, fams) left container j us items = do
            spec <- maybe (refuse "a nested occurrence in a block that the oracle has not judged") return (worldSpec world container us)
            let fixed = specRecN spec
                (kept, others) = splitAt fixed items
                inside = (Nothing : context, (Mrec container j, Param 0 0) : [(mark, liftTree 1 tree) | (mark, tree) <- ras], map (liftTree 1) fams)
            when (length items < fixed || any within others || length (specFams spec) /= 1) (refuse negative)
            results <- forM (concatMap packetCons (take 1 (drop j (specFams spec)))) $ \(_, signature) -> do
                applied <- instantiate world (Nothing : context) (abstractCons 1 fixed container signature) (map (lift 0 1) kept)
                (deeper, body) <- skip inside (specParN spec - fixed) applied
                arguments deeper Nothing left body
            return (minimum (left : map fst results), Rec 0 [Node (Mrec container j) (map snd results)])
        -- `ienv_decompose_prod`
        skip now@(context, _, _) left term
            | left <= (0 :: Int) = return (now, term)
            | otherwise = do
                found <- reduced world context term
                case found of
                    Pi _ _ rest -> skip (push now) (left - 1) rest
                    _ -> refuse "a type has fewer products than its family has parameters"
