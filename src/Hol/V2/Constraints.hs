module Hol.V2.Constraints
    ( Store
    , empty
    , fromConstraints
    , prepend
    , constraints
    , roots
    , addedRoots
    , affected
    , zeroWitness
    , rowZeroWitness
    ) where

import qualified Calc.Presburger.Internal as P
import Control.Monad (guard, liftM2)
import qualified Data.List as List
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Hol.BETA.Arith (ArithStore)
import Hol.BETA.Constant
import Hol.BETA.Header
import Hol.BETA.HOPU
import Hol.BETA.Runtime (Constraint (..), arithStoreTerms)
import Hol.BETA.TermNode

-- An immutable conjunction. Occurrences, including duplicate definedness
-- obligations, retain their order. Snapshots share this value without an
-- invalidation protocol. The dependency set answers whether a new binding
-- requires the complete reference settlement path.
data Store
    = Store
        { storedConstraints :: [Constraint]
        , storedRoots       :: !(Set.Set LogicVar)
        , storedAdded       :: !(Set.Set LogicVar)
        , storedUnknown     :: !Int
        }
    deriving ()

empty :: Store
empty = Store [] Set.empty Set.empty 0

fromConstraints :: Labeling -> VarBinding -> [Constraint] -> Store
fromConstraints labeling binding values = prepend labeling binding values empty

prepend :: Labeling -> VarBinding -> [Constraint] -> Store -> Store
prepend labeling binding values before
    = previous `seq` indexed { storedConstraints = values ++ previous }
    where
        -- Do not retain the previous Store through a lazy record selection in
        -- the list tail: its persistent dependency roots are no longer needed.
        previous = storedConstraints before
        indexed = List.foldl' insert (before { storedAdded = Set.empty }) values
        insert store value = store
            { storedRoots   = Set.union variables (storedRoots store)
            , storedAdded   = Set.union (Set.difference variables (storedRoots store)) (storedAdded store)
            , storedUnknown = storedUnknown store + if rowZeroWitness labeling binding value then 0 else 1
            }
            where
                variables = Set.union (getLVars (terms value)) (getLVars (map (bindVars binding) (terms value)))

constraints :: Store -> [Constraint]
constraints = storedConstraints

roots :: Store -> Set.Set LogicVar
roots = storedRoots

addedRoots :: Store -> Set.Set LogicVar
addedRoots = storedAdded

affected :: Set.Set LogicVar -> Store -> Bool
affected changed store = not (Set.disjoint changed (storedRoots store))

-- True is a sufficient satisfiability certificate, never a decision of
-- validity or unsatisfiability. Every supported free atom is an existential
-- natural and the SAME assignment (all zero) satisfies every guarded row.
-- False includes unknown and must use the unchanged complete-store solver.
zeroWitness :: Store -> Bool
zeroWitness = (== 0) . storedUnknown

rowZeroWitness :: Labeling -> VarBinding -> Constraint -> Bool
rowZeroWitness labeling binding value = certified == Just True where
    bound = rewrite NF . bindVars binding
    natural term = case bound term of
        LVar variable
            | lookupLVarType variable labeling == Just mkTyNat -> Just 0
        NCon (DC (DC_NatL number)) _
            | number >= 0 -> Just number
        NApp (NCon (DC DC_Succ) _) argument _ -> (+ 1) <$> natural argument
        NApp (NApp (NCon (DC DC_plus) _) left _) right _ -> liftM2 (+) (natural left) (natural right)
        NApp (NApp (NCon (DC DC_mul) _) left _) right _ -> do
            -- Nonlinear atoms are universally abstracted by the reference
            -- translation. A zero valuation of those atoms is not evidence.
            guard (closed left || closed right)
            liftM2 (*) (natural left) (natural right)
        _ -> Nothing
    closed term = Set.null (getLVars (bound term))
    comparison term = case unfoldlNApp (bound term) of
        (NCon (DC DC_eq) _, [NCon (TC (TC_Named "nat")) _, left, right]) -> liftM2 (==) (natural left) (natural right)
        (NCon (DC DC_lt) _, [left, right]) -> liftM2 (<) (natural left) (natural right)
        (NCon (DC DC_le) _, [left, right]) -> liftM2 (<=) (natural left) (natural right)
        (NCon (DC DC_gt) _, [left, right]) -> liftM2 (>) (natural left) (natural right)
        (NCon (DC DC_ge) _, [left, right]) -> liftM2 (>=) (natural left) (natural right)
        _ -> Nothing
    termRep free term = case term of
        P.IVar variable -> Map.lookup variable free >>= natural
        P.Zero -> Just 0
        P.Succ argument -> (+ 1) <$> termRep free argument
        P.Plus left right -> liftM2 (+) (termRep free left) (termRep free right)
    formula free expression = case expression of
        P.ValF value -> Just value
        P.EqnF left right -> relation (==) left right
        P.LtnF left right -> relation (<) left right
        P.LeqF left right -> relation (<=) left right
        P.GtnF left right -> relation (>) left right
        P.ModF left modulus right -> do
            guard (modulus > 0)
            relation (\a b -> a `mod` modulus == b `mod` modulus) left right
        P.NegF operand -> not <$> formula free operand
        P.DisF left right -> boolean (||) left right
        P.ConF left right -> boolean (&&) left right
        P.ImpF left right -> boolean (\a b -> not a || b) left right
        P.IffF left right -> boolean (==) left right
        P.AllF {} -> Nothing
        P.ExsF {} -> Nothing
        where
            relation operator left right = liftM2 operator (termRep free left) (termRep free right)
            boolean operator left right = liftM2 operator (formula free left) (formula free right)
    store (comparisons, formulas) = do
        compared <- mapM comparison comparisons
        formulated <- mapM (\(expression, free) -> formula free expression) formulas
        return (and compared && and formulated)
    certified = case value of
        EvalutionConstraint left right -> liftM2 (==) (natural left) (natural right)
        ArithmeticConstraint premises obligation -> liftM2 (\a b -> not a || b) (store premises) (comparison obligation)
        PresburgerConstraint premises expression free -> liftM2 (\a b -> not a || b) (store premises) (formula free expression)
        DisagreementConstraint {} -> Nothing

terms :: Constraint -> [TermNode]
terms value = case value of
    DisagreementConstraint (left :=?=: right) -> [left, right]
    EvalutionConstraint left right -> [left, right]
    ArithmeticConstraint premises term -> term : arithStoreTerms premises
    PresburgerConstraint premises _ free -> arithStoreTerms premises ++ Map.elems free
