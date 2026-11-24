module Hol.BETA.Answer (renderAnswer, renderQuestion, renderQuestionWithNames, questionNames, extendQuestionNames) where

import Hol.BETA.Arith (arithEntails, liftConstraint, presburgerGuardedStoreSat, presburgerGuardedValid)
import Hol.BETA.Constant
import Hol.BETA.Debugger
import Hol.BETA.Header
import Hol.BETA.HOPU
import Hol.BETA.Notation (NotationDB)
import Hol.BETA.Runtime
import Hol.BETA.TermNode
import Data.Maybe
import qualified Data.List as List
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set

-- Nothing suppresses an inconsistent answer; an empty list is a plain success.
-- Keep the projection and presentation shared by the REPL and saved bytecode.
renderAnswer :: NotationDB -> NameCache -> TermNode -> Context -> Maybe [String]
renderAnswer notationDB cache query ctx
    | isShort && isClear = Just []
    | isClear && List.null theAnswerSubst = Just []
    | isClear = Just ("The answer substitution is:" : existentialScope ++ substitutionLines)
    | hasGroundContradiction = Nothing
    | otherwise = Just ("The remaining constraints are:" : existentialScope ++ constraintLines ++ ["The binding is:"] ++ bindingLines)
    where
        pp = prettyTerm notationDB cache
        existentialScope = ["exists " ++ List.intercalate ", " displayNames ++ "." | not (null displayNames)]
        substitutionLines = [v ++ " := " ++ pp (bindVars displayRenaming t) "." | (v, t) <- theAnswerSubst]
        constraintLines = [shows (zonkLVar displayRenaming constraint) "" | constraint <- _LeftConstraints final_ctx]
        bindingLines = [pp (bindVars displayRenaming (mkLVar v)) (" := " ++ pp (bindVars displayRenaming t) ".") | (v, t) <- Map.toList (unVarBinding (_TotalVarBinding final_ctx))]
        -- Treat substitutions and surviving residual constraints
        -- as variable-connectivity hyperedges.  A generated
        -- variable is part of the observable answer whenever it
        -- is connected (possibly transitively) to a named query
        -- variable through either kind of edge.  Looking only at
        -- substitution RHSs would miss, for example, the shared
        -- @Y@ in @X > Y@ and @presburger "Y = 5"@.
        answerRelevantVars :: Set.Set LogicVar
        answerRelevantVars = closeRelevance namedQueryVars where
            closeRelevance known
                | known' == known = known
                | otherwise = closeRelevance known'
                where
                    connected = Set.unions
                        [ edge
                        | edge <- relevanceEdges
                        , not (Set.disjoint known edge)
                        ]
                    known' = known `Set.union` connected
        namedQueryVars :: Set.Set LogicVar
        namedQueryVars = Set.filter isNamedLVar (getLVars query)
        relevanceEdges :: [Set.Set LogicVar]
        relevanceEdges = substitutionEdges ++ map constraintVars universallyDropped
        substitutionEdges =
            [ Set.insert lv (getLVars term)
            | (lv, term) <- Map.toList (unVarBinding (_TotalVarBinding ctx))
            ]
        constraintVars :: Constraint -> Set.Set LogicVar
        constraintVars (DisagreementConstraint (lhs :=?=: rhs)) = getLVars lhs `Set.union` getLVars rhs
        constraintVars (EvalutionConstraint lhs rhs) = getLVars lhs `Set.union` getLVars rhs
        constraintVars (ArithmeticConstraint premises term) = Set.unions (getLVars term : map getLVars (arithStoreTerms premises))
        constraintVars (PresburgerConstraint premises _ freeOf) = Set.unions (map getLVars (arithStoreTerms premises ++ Map.elems freeOf))
        isNamedLVar :: LogicVar -> Bool
        isNamedLVar (LV_Named _) = True
        isNamedLVar _ = False
        -- Keep the long-standing answer-substitution projection
        -- directed: internal bindings that merely point back into
        -- a relevant component are not themselves user-visible.
        visibleSubstitutionVars :: Set.Set LogicVar
        visibleSubstitutionVars = namedBindingVars `Set.union` Set.unions [ transCl dependOn lv | lv <- Set.toList namedBindingVars ]
        namedBindingVars = Set.filter isNamedLVar (Map.keysSet (unVarBinding (_TotalVarBinding ctx)))
        dependOn lv = maybe Set.empty getLVars (Map.lookup lv (unVarBinding (_TotalVarBinding ctx)))
        transCl rel start = dfs (rel start) Set.empty where
            dfs current visited
                | Set.null current = visited
                | otherwise = dfs next visited'
                where
                    news = current `Set.difference` visited
                    visited' = visited `Set.union` news
                    next = Set.unions [ rel x | x <- Set.toList news ]
        final_ctx :: Context
        final_ctx = Context
            { _TotalVarBinding = VarBinding (unVarBinding (_TotalVarBinding ctx) `Map.restrictKeys` visibleSubstitutionVars)
            , _CurrentLabeling = _CurrentLabeling ctx
            , _LeftConstraints = prunedConstraints
            , _ContextThreadId = _ContextThreadId ctx
            , _debuggindModeOn = _debuggindModeOn ctx
            }
        universallyDropped :: [Constraint]
        universallyDropped = do
            it <- _LeftConstraints ctx
            case it of
                ArithmeticConstraint _ _
                    | guardedUniversallyValid it -> []
                    | otherwise -> pure it
                EvalutionConstraint lhs rhs
                    | evaluationConstraintUniversallyValid lhs rhs -> []
                    | otherwise -> pure it
                PresburgerConstraint _ _ _
                    | guardedUniversallyValid it -> []
                    | otherwise -> pure it
                it -> pure it
        existentiallyProjected :: [Constraint]
        existentiallyProjected =
            [ constraint
            | (index, constraint) <- indexedResiduals
            , index `Set.notMember` projectedIndices
            ]
        -- Generated wildcard/sigma variables are existential.
        -- Projection is all-or-nothing for each variable-sharing
        -- component.  Otherwise deleting a complete neighbour
        -- such as @Y > 5@ can weaken an unsupported residual
        -- such as @0 is 1 / Y@ that depends on the same witness.
        indexedResiduals :: [(Int, Constraint)]
        indexedResiduals = zip [0 ..] universallyDropped
        projectedIndices :: Set.Set Int
        projectedIndices = Set.fromList
            [ index
            | component <- residualComponents indexedResiduals
            , componentProjectable component
            , (index, _) <- component
            ]
        residualComponents :: [(Int, Constraint)] -> [[(Int, Constraint)]]
        residualComponents [] = []
        residualComponents (seed : rest) = component : residualComponents remaining
            where
                (component, remaining) = grow [seed] (constraintVars (snd seed)) rest
                grow members variables pending
                    | null touching = (members, separate)
                    | otherwise = grow
                        (members ++ touching)
                        (variables `Set.union` Set.unions (map (constraintVars . snd) touching))
                        separate
                    where
                        (touching, separate) = List.partition
                            (not . Set.disjoint variables . constraintVars . snd)
                            pending
        componentProjectable :: [(Int, Constraint)] -> Bool
        componentProjectable component
            = Set.disjoint componentVariables answerRelevantVars
                && all (constraintArithmeticComplete . snd) component
                && componentSatisfiable component
            where
                componentVariables = Set.unions (map (constraintVars . snd) component)
        componentSatisfiable :: [(Int, Constraint)] -> Bool
        componentSatisfiable component = case traverse
            (guardedConstraintStore (_TotalVarBinding ctx) . snd)
            component of
                Nothing -> False
                Just guarded -> presburgerGuardedStoreSat guarded
        constraintArithmeticComplete (EvalutionConstraint lhs rhs)
            = isJust (completeEvaluationObligation lhs rhs)
        constraintArithmeticComplete (ArithmeticConstraint premises term)
            = arithStoreComplete premises && comparisonComplete term
        constraintArithmeticComplete (PresburgerConstraint premises _ freeOf)
            = arithStoreComplete premises && all linearNatTerm (Map.elems freeOf)
        constraintArithmeticComplete _ = False
        arithStoreComplete (comparisons, formulas)
            = all comparisonComplete comparisons
                && all (all linearNatTerm . Map.elems . snd) formulas
        comparisonComplete term = case evaluateB term of
            Right _ -> True
            Left "ill" -> True
            _ -> isJust (liftConstraint term)
        linearNatTerm term = case evaluateA term of
            Right _ -> True
            Left "ill" -> True
            _ -> isJust (liftConstraint (mkNatEquality term (mkNCon (DC_NatL 0))))
        guardedUniversallyValid :: Constraint -> Bool
        guardedUniversallyValid constraint = case guardedConstraintStore (_TotalVarBinding ctx) constraint of
            Nothing -> False
            Just guarded -> presburgerGuardedValid [guarded]
        entailmentDropped :: [Constraint]
        entailmentDropped = go [] existentiallyProjected where
            go kept [] = reverse kept
            go kept (c : rest) = case c of
                ArithmeticConstraint premises t
                    | nullArithStore premises
                    , arithEntails (otherArith kept rest) t -> go kept rest
                _ -> go (c : kept) rest
            otherArith :: [Constraint] -> [Constraint] -> [TermNode]
            otherArith kept rest =
                [ t | ArithmeticConstraint premises t <- kept ++ rest, nullArithStore premises ]
        prunedConstraints :: [Constraint]
        prunedConstraints = List.sortOn (\c -> shows c "") entailmentDropped
        theAnswerSubst :: [(LargeId, TermNode)]
        theAnswerSubst = [ (v, bindVars (_TotalVarBinding final_ctx) t) | (LV_Named v, t) <- Map.toList (unVarBinding (eraseTrivialBinding (_TotalVarBinding final_ctx))) ]
        isShort :: Bool
        isShort = Set.null (getLVars query)
        isClear :: Bool
        isClear = List.null (_LeftConstraints final_ctx)
        displayExistentialVars :: [LogicVar]
        displayExistentialVars = firstVariables (Set.filter (not . isNamedLVar) observableVars) displayTerms
        displayTerms
            | isClear = map snd theAnswerSubst
            | otherwise = concatMap constraintTerms (_LeftConstraints final_ctx) ++ concat [[mkLVar variable, value] | (variable, value) <- Map.toAscList (unVarBinding (_TotalVarBinding final_ctx))]
        observableVars :: Set.Set LogicVar
        observableVars = Set.unions $
            Map.keysSet (unVarBinding (_TotalVarBinding final_ctx))
                : map constraintVars (_LeftConstraints final_ctx)
                ++ map (getLVars . snd) theAnswerSubst
        displayNames :: [String]
        displayNames = take (length displayExistentialVars)
            [ candidate
            | i <- [1 :: Int ..]
            , let candidate = "E_" ++ show i
            , candidate `Set.notMember` usedDisplayNames
            ]
        -- Generated answer names must be valid large identifiers
        -- when pasted back into Hol.  Skip names already present
        -- anywhere in the rendered query or observable answer to
        -- avoid capture.  In particular, a rigid @pi@ constant or
        -- lambda hint named @E_1@ is not a logic variable, but it
        -- is still visible next to a generated existential.
        usedDisplayNames :: Set.Set String
        usedDisplayNames = Set.unions (map (termPresentationNames cache) presentationTerms)
        presentationTerms :: [TermNode]
        presentationTerms =
            query
                : map mkLVar (Map.keys finalBinding)
                ++ Map.elems finalBinding
                ++ concatMap constraintTerms (_LeftConstraints final_ctx)
            where
                finalBinding = unVarBinding (_TotalVarBinding final_ctx)
        displayRenaming :: VarBinding
        displayRenaming = VarBinding $ Map.fromList
            [ (variable, mkLVar (LV_Named name))
            | (variable, name) <- zip displayExistentialVars displayNames
            ]
        hasGroundContradiction :: Bool
        hasGroundContradiction = any contradicts (_LeftConstraints final_ctx)
        contradicts :: Constraint -> Bool
        contradicts constraint@(ArithmeticConstraint _ _)
            = maybe False (not . presburgerGuardedStoreSat . pure) (guardedConstraintStore (_TotalVarBinding ctx) constraint)
        contradicts (EvalutionConstraint lhs rhs)
            = not (evaluationConstraintPossible lhs rhs)
        contradicts constraint@(PresburgerConstraint _ _ _)
            = maybe False (not . presburgerGuardedStoreSat . pure) (guardedConstraintStore (_TotalVarBinding ctx) constraint)
        contradicts _ = False

-- Answer names follow the displayed terms, not unifier allocation order.
firstVariables :: Set.Set LogicVar -> [TermNode] -> [LogicVar]
firstVariables wanted terms = reverse found ++ Set.toAscList (wanted `Set.difference` seen) where
    (seen, found) = List.foldl' visit (Set.empty, []) terms
    visit known@(seen, found) term = case term of
        LVar variable
            | variable `Set.member` wanted && variable `Set.notMember` seen -> (Set.insert variable seen, variable : found)
        NApp function argument _ -> visit (visit known function) argument
        NLam _ _ body _ -> visit known body
        Susp {} -> visit known (rewrite WHNF term)
        NPresburgerCheck _ variables _ -> List.foldl' visit known (Map.elems variables)
        _ -> known

-- The names that the display of a term may show: generated names avoid them.
termPresentationNames :: NameCache -> TermNode -> Set.Set String
termPresentationNames cache term = assertNonnegativeIndices term `seq` go term where
    go (LVar lv) = logicVarPresentationNames lv
    go (NCon constant _) = constantPresentationNames constant
    go (NIdx i)
        | i >= 0 = Set.empty
        | otherwise = undefined
    go (NApp lhs rhs _) = go lhs `Set.union` go rhs
    go (NLam mhint _ body _) = maybe Set.empty Set.singleton mhint `Set.union` go body
    go (Susp body _ _ env) = Set.unions (go body : map suspItemNames env)
    go (NPresburgerCheck _ freeOf _) = Set.unions (map go (Map.elems freeOf))
    suspItemNames (Dummy _) = Set.empty
    suspItemNames (Binds body _) = go body
    logicVarPresentationNames :: LogicVar -> Set.Set String
    logicVarPresentationNames lv = Set.fromList (catMaybes [sourceHint, viewerLookup cache lv]) where
        sourceHint = case lv of
            LV_Named name -> Just name
            LV_Unique _ (DispHint mhint) -> mhint
            LV_ty_var _ -> Nothing
    constantPresentationNames :: Constant -> Set.Set String
    constantPresentationNames constant = case constant of
        DC (DC_Named name) -> Set.singleton name
        DC (DC_Unique _ (DispHint mhint)) -> maybe Set.empty Set.singleton mhint
        TC (TC_Named name) -> Set.singleton name
        _ -> Set.empty

-- What the REPL shows for a question of `oracle`: the
-- lines before the prompt, and the prompt. A question with a variable begins
-- with the scopes: `forall` for the constants that `pi` made and `exists` for
-- the variables, in the order of their levels, so that a variable may have
-- the constants before it. Then each hypothesis of the goal is on a line
-- `given H`, the latest first, and each constraint on a line `where C`. A
-- variable that the query does not name is shown as `E_n`, numbered in the
-- order of `_QuestionVars`.
renderQuestion :: NotationDB -> NameCache -> Question -> ([String], String)
renderQuestion notationDB cache question = renderQuestionWithNames notationDB cache (questionNames cache question) question

renderQuestionWithNames :: NotationDB -> NameCache -> [(LogicVar, SmallId)] -> Question -> ([String], String)
renderQuestionWithNames notationDB cache names question = (scopes ++ givens ++ wheres, pp (questionGoal question) "> ") where
    pp term = prettyTerm notationDB cache (bindVars renaming term)
    renaming = VarBinding (Map.fromList [(variable, mkLVar (LV_Named name)) | (variable, name) <- names])
    givens = ["given " ++ pp hypothesis "" | hypothesis <- _QuestionHyps question]
    wheres = ["where " ++ shows (zonkLVar renaming constraint) "" | constraint <- _QuestionLeft question]
    -- A constant of level n is before the variables of scope n, which may
    -- have it, and after those of scope n - 1, which may not.
    places = List.sortOn fst ([(2 * level, (True, pp (mkNCon constant) "")) | (constant, level) <- _QuestionCons question] ++ [(2 * level + 1, (False, pp (mkLVar variable) "")) | (variable, level) <- _QuestionVars question])
    scopes = [unwords [(if universal then "forall " else "exists ") ++ List.intercalate ", " (map snd members) ++ "." | members@((universal, _) : _) <- List.groupBy (\left right -> fst left == fst right) (map snd places)] | not (null (_QuestionVars question))]

-- The prompt and the assignment parser share the question's local names.
questionNames :: NameCache -> Question -> [(LogicVar, SmallId)]
questionNames cache = extendQuestionNames cache (const True) []

-- Editing retains names after their variables are bound, so neither the
-- display nor `:show` can reuse an earlier name for a different variable.
extendQuestionNames :: NameCache -> (SmallId -> Bool) -> [(LogicVar, SmallId)] -> Question -> [(LogicVar, SmallId)]
extendQuestionNames cache available names question = names ++ zip hidden [candidate | i <- [1 :: Int ..], let candidate = "E_" ++ show i, candidate `Set.notMember` used, available candidate] where
    hidden = [variable | (variable, _) <- _QuestionVars question, not (named variable), variable `Set.notMember` known]
    known = Set.fromList (map fst names)
    named variable = case variable of
        LV_Named _ -> True
        _ -> False
    shown = _QuestionTerm question : _QuestionHyps question ++ concatMap constraintTerms (_QuestionLeft question)
    used = Set.fromList (map snd names) `Set.union` Set.unions (map (termPresentationNames cache) shown)
