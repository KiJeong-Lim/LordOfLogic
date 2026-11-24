module LoL.Oracle.Tree where

import Control.Monad (zipWithM)
import LoL.Core (ConstId, Term)

-- Regular trees, as kernel/rtree.ml of Rocq 9.0 has them. `Param i j` is tree
-- `j` of the `Rec` that `i` other ones separate from the occurrence, and
-- `Rec j ts` is tree `j` of the trees `ts`, each of which may refer to all of
-- them: a tree is read with its `Rec` unfolded as often as needed.
data Tree a
    = Param Int Int
    | Node a [[Tree a]]
    | Rec Int [Tree a]
    deriving (Eq, Show)

-- Whether a subterm is one of an inductive family, and of which one
-- (`recarg` of Rocq).
data Recarg
    = Norec
    | Mrec ConstId Int
    deriving (Eq, Show)

-- For a family: a node `Mrec` with, for each constructor, a tree for each of
-- its arguments (`wf_paths` of Rocq).
type Paths = Tree Recarg

-- What the oracle keeps of an inductive block that it has judged, as Rocq
-- keeps it: the number of parameters, how many of them are the same in every
-- recursive occurrence, and for each family its packet.
data Spec
    = Spec
        { specParN :: Int
        , specRecN :: Int
        , specFams :: [Packet]
        }
    deriving (Eq, Show)

-- The number of indices of a family, its type with the products of the
-- parameters and of the indices written out, each constructor with the number
-- of its arguments and its type with the products written out, and the tree
-- of the family.
data Packet
    = Packet
        { packetIdxN :: Int
        , packetType :: Term
        , packetCons :: [(Int, Term)]
        , packetTree :: Paths
        }
    deriving (Eq, Show)

norec :: Paths
norec = Node Norec []

recCalls :: Int -> [Tree a]
recCalls count = [Param 0 j | j <- [0 .. count - 1]]

makeRec :: [Tree a] -> [Tree a]
makeRec trees = [Rec j trees | j <- [0 .. length trees - 1]]

liftTree :: Int -> Tree a -> Tree a
liftTree amount = shift 0 where
    shift depth tree = case tree of
        Param i j
            | i < depth -> tree
            | otherwise -> Param (i + amount) j
        Node label sons -> Node label (map (map (shift depth)) sons)
        Rec j trees -> Rec j (map (shift (depth + 1)) trees)

-- The tree with a node or a parameter at its root.
expand :: Tree a -> Tree a
expand tree
    = case tree of
        Rec j trees -> expand (unfold 0 trees (trees !! j))
        _ -> tree
    where
        unfold depth trees body = case body of
            Param i j
                | i < depth -> body
                | i == depth -> liftTree depth (Rec j trees)
                | otherwise -> Param (i - 1) j
            Node label sons -> Node label (map (map (unfold depth trees)) sons)
            Rec j inner -> Rec j (map (unfold (depth + 1) trees) inner)

-- The label and the sons of the root, when the root is a node.
rootOf :: Tree a -> Maybe (a, [[Tree a]])
rootOf tree
    = case expand tree of
        Node label sons -> Just (label, sons)
        _ -> Nothing

isNorec :: Paths -> Bool
isNorec tree = fmap fst (rootOf tree) == Just Norec

-- The same tree, written the same way or not.
sameTree :: Eq a => Tree a -> Tree a -> Bool
sameTree left right = left == right || alike [] left right where
    alike seen t u = (t, u) `elem` seen || case (expand t, expand u) of
        (Node x v, Node y w) -> x == y && length v == length w && and (zipWith (\a b -> length a == length b && and (zipWith (alike ((t, u) : seen)) a b)) v w)
        _ -> False

-- The tree of what both trees have; `none` labels a node where they differ.
-- An inconsistent parameter or arity is an internal error, not an empty
-- intersection. Rocq asserts these invariants in `Rtree.inter`.
meetTree :: Eq a => a -> Tree a -> Tree a -> Either String (Tree a)
meetTree none = meet (0 :: Int) [] where
    meet depth seen t u
        | invalid t || invalid u = Left "a recursive tree has an invalid root index"
        | otherwise = case lookup (t, u) seen of
            Just (i, j) -> Right (Param (depth - i - 1) j)
            Nothing -> case (t, u) of
                (Param i j, Param k l)
                    | i == k && j == l -> Right t
                    | otherwise -> Left "intersected tree parameters differ"
                (Node x a, Node y b)
                    | x /= y -> Right (Node none [])
                    | map length a /= map length b -> Left "intersected tree arities differ"
                    | otherwise -> Node x <$> zipWithM (zipWithM (meet depth seen)) a b
                (Rec i v, Rec j w)
                    | i == j && length v == length w -> Rec i <$> zipWithM (meet (depth + 1) (((t, u), (depth, i)) : seen)) v w
                    | otherwise -> Rec 0 . pure <$> meet (depth + 1) (((t, u), (depth, 0)) : seen) (expand t) (expand u)
                (Rec _ _, _) -> meet depth seen (expand t) u
                (_, Rec _ _) -> meet depth seen t (expand u)
                _ -> Left "intersected tree roots have incompatible shapes"
    invalid tree = case tree of
        Param i j -> i < 0 || j < 0
        Rec j trees -> j < 0 || j >= length trees
        _ -> False

-- Whether the first tree has no more than the second.
withinTree :: Eq a => a -> Tree a -> Tree a -> Either String Bool
withinTree none t u = sameTree t <$> meetTree none t u
