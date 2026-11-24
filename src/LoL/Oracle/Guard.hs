module LoL.Oracle.Guard (guarded) where

import Control.Monad
import Control.Monad.IO.Class (liftIO)
import Control.Monad.Trans.Except
import Data.IORef
import qualified Data.IntSet as IntSet
import LoL.Core
import LoL.Oracle
import LoL.Oracle.Tree

-- A structural guard condition for CIC, based on `check_fix` of
-- kernel/inductive.ml of Rocq 9.0 with the soundness repairs named below.
-- Rocq compatibility does not decide admission.
-- A variable is counted from 1 where that file counts it so: `renvMin`
-- and the places of `renvGen` are such.

data Size
    = Large
    | Strict
    deriving (Eq)

-- What is known of the size of a term (`subterm_spec`).
data Shape
    = Subterm IntSet.IntSet Size Paths
    | DeadCode
    | NotSubterm
    | Bound IntSet.IntSet
    deriving ()

-- A value that is computed when it is first needed, and once.
type Late a = IORef (Either (Judge a) a)

late :: Judge a -> Judge (Late a)
late = liftIO . newIORef . Left

now :: a -> Judge (Late a)
now = liftIO . newIORef . Right

force :: Late a -> Judge a
force cell = do
    state <- liftIO (readIORef cell)
    case state of
        Right value -> return value
        Left action -> do
            value <- action
            liftIO (writeIORef cell (Right value))
            return value

-- `guard_env`: the context, the variable of the last function of the block,
-- and the shape of each variable, the innermost first.
data Renv
    = Renv
        { renvCtx :: [Maybe Term]
        , renvMin :: Int
        , renvGen :: [Late Shape]
        }
    deriving ()

-- `fix_check_result`
data Need
    = NoNeed
    | Need String
    deriving ()

-- `stack_element`
data Item
    = Closure Need Renv Int Term
    | Given (Late Shape)
    deriving ()

orElse :: Need -> Need -> Need
orElse first second
    = case first of
        Need _ -> first
        NoNeed -> second

needOf :: [Item] -> Need
needOf = foldr step NoNeed where
    step item rest = case item of
        Closure need _ _ _ -> orElse need rest
        Given _ -> rest

liftItems :: Int -> [Item] -> [Item]
liftItems amount = map $ \item -> case item of
    Closure need renv count term -> Closure need renv (count + amount) term
    Given _ -> item

closures :: Renv -> [Term] -> [Item] -> [Item]
closures renv items stack = map (Closure NoNeed renv 0) items ++ stack

pushVar :: Renv -> Late Shape -> Renv
pushVar renv shape = Renv { renvCtx = Nothing : renvCtx renv, renvMin = renvMin renv + 1, renvGen = shape : renvGen renv }

pushLet :: Renv -> Term -> Late Shape -> Renv
pushLet renv body shape = Renv { renvCtx = Just body : renvCtx renv, renvMin = renvMin renv + 1, renvGen = shape : renvGen renv }

-- `push_var_renv`
pushBound :: Renv -> Int -> Judge Renv
pushBound renv level = pushVar renv <$> now (if level >= 1 then Bound (IntSet.singleton level) else NotSubterm)

-- `push_ctxt_renv` and `push_fix_renv`: variables of which nothing is known
pushPlain :: Renv -> Int -> Judge Renv
pushPlain renv count = do
    shapes <- replicateM count (now NotSubterm)
    return Renv { renvCtx = replicate count Nothing ++ renvCtx renv, renvMin = renvMin renv + count, renvGen = shapes ++ renvGen renv }

-- `assign_var_spec`
assign :: Renv -> Int -> Late Shape -> Renv
assign renv place shape = renv { renvGen = take (place - 1) (renvGen renv) ++ shape : drop place (renvGen renv) }

-- `spec_of_tree`
shapeOf :: IntSet.IntSet -> Paths -> Shape
shapeOf levels tree = if isNorec tree then NotSubterm else Subterm levels Strict tree

-- `inter_spec` and `subterm_spec_glb`
meet :: [Shape] -> Judge Shape
meet = foldM both DeadCode where
    both first second = case (first, second) of
        (_, DeadCode) -> return first
        (DeadCode, _) -> return second
        (NotSubterm, _) -> return first
        (_, NotSubterm) -> return second
        (Bound left, Bound right) -> return (Bound (IntSet.union left right))
        (Subterm left size tree, Bound right) -> return (Subterm (IntSet.union left right) size tree)
        (Bound left, Subterm right size tree) -> return (Subterm (IntSet.union left right) size tree)
        (Subterm left size1 tree1, Subterm right size2 tree2) -> Subterm (IntSet.union left right) (if size1 == Strict && size2 == Strict then Strict else Large) <$> checkedTree (meetTree Norec tree1 tree2)

checkedTree :: Either String a -> Judge a
checkedTree = either (throwE . Unavailable) return

-- `set_iota_specif`
iota :: Int -> Late Shape -> Judge (Late Shape)
iota level shape = late $ do
    found <- force shape
    return $ case found of
        NotSubterm
            | level >= 1 -> Bound (IntSet.singleton level)
        _ -> found

-- `set_need_reduce_one`: the redex that is `level` from the bottom needs to
-- be reduced.
needAt :: Int -> String -> [Need] -> [Need]
needAt level reason needs = take place needs ++ Need reason : drop (place + 1) needs where
    place = length needs - level

-- The return clause of a match with its binders as abstractions, and each
-- branch likewise (`expand_case`). The types of the binders are those of the
-- family and of its constructors at the parameters that the match keeps.
expanded :: Packet -> ConstId -> Int -> UniverseInstance -> [Term] -> [Hint] -> Term -> [([Hint], Term)] -> (Term, [Term])
expanded packet block i us kept hints clause branches = (abstract (hints `zip` (domains (length hints - 1) (packetType packet) ++ [self])) clause, [abstract (zip names (domains (length names) signature)) body | ((names, body), (_, signature)) <- zip branches (packetCons packet)]) where
    count = length hints - 1
    self = apps (Ind block i us) (map (lift 0 count) kept ++ [Var k | k <- reverse [0 .. count - 1]])
    abstract binders body = foldr (\(hint, domain) rest -> Lam hint domain rest) body binders
    -- the first `wanted` domains of a type, after its parameters
    domains wanted signature = take wanted (walk (applied (length kept) kept signature))
    applied left values term = case term of
        Pi _ _ rest
            | left > (0 :: Int) -> applied (left - 1) (drop 1 values) (substitute (take 1 values) rest)
        _ -> term
    walk term = case term of
        Pi _ domain rest -> domain : walk rest
        _ -> []

guarded :: World -> [Maybe Term] -> Term -> IO (Either Failure ())
guarded world outer term
    = case term of
        Fix _ functions -> runExceptT (block functions)
        _ -> return (Left (Refuted "the term is not a block of functions"))
    where
        ask = reduced world
        halt = halted world
        -- `check_fix`, with `inductive_of_mutfix`
        block functions = do
            let total = length functions
                positions = map functionArgN functions
            found <- forM functions $ \function -> argument total (replicate total Nothing ++ outer) 1 (functionArgN function) (functionBody function)
            forM_ (zip found positions) $ \((tree, (context, body)), position) -> do
                first <- now (Subterm IntSet.empty Large tree)
                oneFix total positions (map fst found) (Renv { renvCtx = context, renvMin = position + 2, renvGen = [first] }) body
        -- `check_occur`: the struct argument of a body, the tree of its
        -- family, and the body under its first abstractions
        argument total context place position body = do
            found <- ask context body
            case found of
                Lam _ domain rest
                    | occurs (place - 1) total domain -> refuse "a function of the block occurs in the type of an argument before its struct argument"
                    | place == position + 1 -> do
                        family <- spine <$> ask context domain
                        case familyOf world (fst family) of
                            Just ((owner, index, _), _, packet)
                                | worldFixp world owner index -> return (packetTree packet, (Nothing : context, rest))
                                | otherwise -> refuse "a nonrecursive primitive Record cannot be the struct argument of a fixpoint"
                            Nothing -> refuse "the struct argument of a function is not of an inductive family"
                    | otherwise -> argument total (Nothing : context) (place + 1 :: Int) position rest
                _ -> refuse "the body of a function has fewer abstractions than its struct argument needs"
        -- `subterm_var`
        shapeOfVar renv place = case drop (place - 1) (renvGen renv) of
            shape : _ -> force shape
            [] -> return NotSubterm
        -- `stack_element_specif`
        shapeOfItem item = case item of
            Closure _ renv _ body -> late (subterm renv [] body)
            Given shape -> return shape
        -- `branches_specif`: the shapes of the arguments of each constructor
        -- of the family, from the shape of the scrutinee
        sameFamily block i (found, j, _) = block == found && i == j
        branchShapes family packet scrutinee = forM (zip [0 ..] (map fst (packetCons packet))) $ \(place, arity) -> do
            row <- late $ do
                found <- force scrutinee
                return $ case found of
                    Subterm levels _ tree
                        | Just (Mrec block i, sons) <- rootOf tree, sameFamily block i family -> map (shapeOf levels) (take arity (concat (take 1 (drop place sons)) ++ repeat norec))
                    DeadCode -> replicate arity DeadCode
                    Bound levels -> replicate arity (Bound levels)
                    _ -> replicate arity NotSubterm
            forM [0 .. arity - 1] (\k -> late ((!! k) <$> force row))
        -- `whd_decompose_prod_decls`: the products of a type, reduced. A
        -- `let` that the reduction meets on the way joins the context.
        products context term' = do
            found <- halt context term'
            case found of
                Pi _ _ rest -> products (Nothing : context) rest
                Let _ value _ rest -> products (Just value : context) rest
                _ -> do
                    further <- ask context found
                    if further == found then return (context, found) else products context further
        -- `whd_decompose_lambda_decls`, for a return clause that has `count`
        -- binders around it: the context, the number of its variables that
        -- are binders of the clause or come from a `let` of it, and the rest
        lambdas context count term' = do
            found <- halt context term'
            case found of
                Lam _ _ rest -> lambdas (Nothing : context) (count + 1 :: Int) rest
                Let _ value _ rest -> lambdas (Just value : context) (count + 1) rest
                _ -> do
                    further <- ask context found
                    if further == found then return (context, count, found) else lambdas context count further
        -- `get_recargs_approx`: the tree of the family `family` at the
        -- arguments `items`, as far as the tree `tree` lets it go
        approximate context tree family items = nestedTree (context, []) tree family items
        build ienv@(context, ras) tree term' = do
            (function, items) <- spine <$> ask context term'
            case function of
                Pi _ _ rest -> build (Nothing : context, (Norec, norec) : ras) tree rest
                Var k -> return (maybe norec snd (lookupAt k ras))
                _ -> case (familyOf world function, rootOf tree) of
                    (Just (family, _, _), Just (Mrec block i, _))
                        | sameFamily block i family -> nestedTree ienv tree family items
                    _ -> return norec
        nestedTree (context, ras) tree (block, i, us) items
            | isNorec tree = return tree
            | otherwise = do
                spec <- maybe (refuse "a family that the oracle has not judged") return (worldSpec world block us)
                let fixed = specRecN spec
                    families = length (specFams spec)
                    inside = replicate families Nothing ++ context
                    marks = reverse [(Mrec block j, Param 0 j) | j <- [0 .. families - 1]] ++ [(mark, liftTree families path) | (mark, path) <- ras]
                    kept = map (lift 0 families) (take fixed items)
                    given j = if families == 1 then maybe [] snd (rootOf tree) else maybe [] snd (rootOf (packetTree (specFams spec !! j)))
                nodes <- forM (zip [0 ..] (specFams spec)) $ \(j, packet) -> do
                    rows <- forM (zip (packetCons packet) (given j ++ repeat [])) $ \((_, signature), trees) -> do
                        applied <- instantiate world inside (abstractCons families fixed block signature) kept
                        skipped <- skip (inside, marks) (specParN spec - fixed) applied
                        uncurry constructor skipped trees
                    return (Node (Mrec block j) rows)
                return (makeRec nodes !! i)
        skip ienv@(context, ras) left term'
            | left <= (0 :: Int) = return (ienv, term')
            | otherwise = do
                found <- ask context term'
                case found of
                    Pi _ _ rest -> skip (Nothing : context, (Norec, norec) : ras) (left - 1) rest
                    _ -> refuse "a type has fewer products than its family has parameters"
        constructor ienv@(context, ras) term' trees = do
            (function, _) <- spine <$> ask context term'
            case (function, trees) of
                (Pi _ domain rest, tree : others) -> (:) <$> build ienv tree domain <*> constructor (Nothing : context, (Norec, norec) : ras) rest others
                _ -> return []
        lookupAt k items = case drop k items of
            item : _ -> Just item
            [] -> Nothing
        -- `restrict_spec`: what of a shape may pass a match whose return
        -- clause, under its `binders` binders, is `clause`
        restrict context shape binders clause = case shape of
            NotSubterm -> return shape
            Bound _ -> return shape
            _ -> do
                (inside, count, arity) <- lambdas (replicate binders Nothing ++ context) binders clause
                if not (occurs 0 count arity) then return shape else do
                    (deeper, sort) <- products inside arity
                    (function, items) <- spine <$> ask deeper sort
                    case (familyOf world function, shape) of
                        (Just (family, _, _), Subterm levels size tree) -> do
                            found <- approximate deeper tree family items
                            Subterm levels size <$> checkedTree (meetTree Norec tree found)
                        (Just _, _) -> return shape
                        (Nothing, _) -> return NotSubterm
        -- `subterm_specif`
        subterm renv stack term' = do
            (function, items) <- spine <$> ask (renvCtx renv) term'
            case function of
                Var k -> shapeOfVar renv (k + 1)
                Proj block field receiver -> do
                    shape <- subterm renv [] receiver
                    return $ case shape of
                        Subterm levels _ tree
                            | Just (Mrec owner 0, [fields]) <- rootOf tree, owner == block, path : _ <- drop field fields -> shapeOf levels path
                        Bound levels -> Bound levels
                        DeadCode -> DeadCode
                        _ -> NotSubterm
                Case block i us kept hints clause scrutinee branches
                    | Just (family, _, packet) <- familyOf world (Ind block i us) -> do
                        shape <- late (subterm renv [] scrutinee)
                        rows <- branchShapes family packet shape
                        stack' <- filterStack (renvCtx renv) 0 (length hints) clause (closures renv items stack)
                        shapes <- forM (zip rows (snd (expanded packet block i us kept hints clause branches))) $ \(row, branch) -> subterm renv (map Given row ++ stack') branch
                        shape' <- meet shapes
                        restrict (renvCtx renv) shape' (length hints) clause
                Fix chosen functions
                    | function' : _ <- drop chosen functions -> do
                        let total = length functions
                            position = functionArgN function'
                        (context, conclusion) <- products (renvCtx renv) (functionType function')
                        family <- spine <$> ask context conclusion
                        case familyOf world (fst family) of
                            Nothing -> return NotSubterm
                            Just (_, _, packet) -> do
                                inside <- pushPlain renv total
                                strict <- now (Subterm IntSet.empty Strict (packetTree packet))
                                (body, opened) <- abstractions (assign inside (total - chosen) strict) (position + 1) (functionBody function')
                                let stack' = closures renv items stack
                                final <- if length stack' < position + 1 then return opened else (\shape -> assign opened 1 shape) <$> shapeOfItem (stack' !! position)
                                subterm final [] body
                Lam _ _ body -> do
                    (shape, rest) <- case stack of
                        [] -> (\shape -> (shape, [])) <$> now NotSubterm
                        item : others -> (\shape -> (shape, others)) <$> shapeOfItem item
                    subterm (pushVar renv shape) rest body
                _ -> return NotSubterm
        -- `whd_decompose_lambda_n_assum`: the body under its first
        -- abstractions, of which nothing is known
        abstractions renv left body
            | left <= (0 :: Int) = return (body, renv)
            | otherwise = do
                found <- ask (renvCtx renv) body
                case found of
                    Lam _ _ rest -> pushPlain renv 1 >>= \inside -> abstractions inside (left - 1) rest
                    _ -> refuse "the body of a function has fewer abstractions than its struct argument needs"
        -- `filter_stack_domain`: what of the shapes on the stack may pass a
        -- match with that return clause. The clause is taken as it is written
        -- (`Term.decompose_lambda_decls`): a `let` at its head joins the
        -- context, and its variable counts as a binder of the clause; a cast
        -- at its head is passed.
        filterStack context level binders clause stack
            | not (occurs 0 count written) = return stack
            | otherwise = domain opened written stack
            where
                (opened, count, written) = strip (replicate binders Nothing ++ context) binders clause
                strip found known term' = case term' of
                    Lam _ _ rest -> strip (Nothing : found) (known + 1 :: Int) rest
                    Let _ value _ rest -> strip (Just value : found) (known + 1) rest
                    Cast inner _ -> strip found known inner
                    _ -> (found, known, term')
                domain inside arity items = case items of
                    [] -> return []
                    item : rest -> do
                        found <- ask inside arity
                        case found of
                            Pi _ argument' body -> do
                                (deeper, conclusion) <- products inside argument'
                                (function, values) <- spine <$> ask deeper conclusion
                                kept <- case familyOf world function of
                                    Just (family, _, _) -> do
                                        shape <- shapeOfItem item
                                        late $ do
                                            known <- force shape
                                            case known of
                                                Subterm levels size tree -> do
                                                    tree' <- approximate deeper tree family values
                                                    Subterm levels size <$> checkedTree (meetTree Norec tree tree')
                                                _ -> return known
                                    Nothing -> now NotSubterm >>= iota level
                                -- Only this argument enters the remaining codomain;
                                -- the products inside its type do not (#22763).
                                (Given kept :) <$> domain (Nothing : inside) body rest
                            _ -> mapM (\_ -> Given <$> (now NotSubterm >>= iota level)) items
        -- `find_uniform_parameters`, with the soundness repairs of Rocq
        -- #21684, #21798 and #22384. Count the actual lambda arguments in
        -- the context of the whole nested block (#22645).
        uniform context positions arguments' bodies
            = foldM body (minimum (arguments' : positions)) (zip positions bodies)
            where
                total = length bodies
                body found (position, term') = do
                    rest <- prefix context (position + 1) term'
                    return (scan (position + 1) found rest)
                prefix inside left term'
                    | left == (0 :: Int) = return term'
                    | otherwise = do
                        found <- ask inside term'
                        case found of
                            Lam _ _ rest -> prefix (Nothing : inside) (left - 1) rest
                            _ -> refuse "the body of a function has fewer abstractions than its struct argument needs"
                scan depth found term' = case spine term' of
                    (Var k, items)
                        | depth <= k && k < depth + total -> min scanned (length (takeWhile id [item == Var (depth - j - 1) | (j, item) <- zip [0 ..] items]))
                        | otherwise -> scanned
                        where
                            scanned = foldl (scan depth) found items
                    (function, items)
                        | not (null items) -> foldl (scan depth) found (function : items)
                        | otherwise -> parts scan depth found function
        -- Strip that prefix from every call of the mutual block, including
        -- calls inside arguments of ordinary variables and recursive calls.
        dropUniform found bodies = map (cut (0 :: Int)) bodies where
            total = length bodies
            cut depth body = case spine body of
                (Var k, items)
                    | depth <= k && k < depth + total -> apps (Var k) (drop found (map (cut depth) items))
                    | otherwise -> apps (Var k) (map (cut depth) items)
                (function, items)
                    | not (null items) -> apps (cut depth function) (map (cut depth) items)
                    | otherwise -> rebuilt cut depth function
        -- `pop_argument`
        pop need renv item stack body = case (need, item) of
            (NoNeed, Closure NoNeed _ lifted value) -> do
                shape <- shapeOfItem item
                return (pushLet renv (lift 0 lifted value) shape, liftItems 1 stack, body)
            (_, Closure _ _ lifted value) -> return (renv, stack, substitute [lift 0 lifted value] body)
            (_, Given shape) -> return (pushVar renv shape, liftItems 1 stack, body)
        -- `check_one_fix`: `needs` is the stack of the redexes that have been
        -- passed and not reduced
        oneFix total positions trees start body = do
            (need, _) <- call start [] body
            case need of
                Need reason -> refuse reason
                NoNeed -> return ()
            where
                -- What is refused: which function of the block is called (the
                -- first is 1) and which of its arguments is its struct argument.
                called which position = " (the call is of function " ++ show (which + 1) ++ " of the block, whose struct argument is argument " ++ show (position + 1) ++ ")"
                illegal which position = "a recursive call is not on a term that is smaller than the struct argument" ++ called which position
                short which position = "a recursive call has fewer arguments than its struct argument needs" ++ called which position
                -- `check_rec_call_stack`
                walk renv stack needs term' = case term' of
                    App _ _ -> do
                        let (function, items) = spine term'
                        (needs', stack') <- foldM (\(found, pushed) item -> (\(need, rest) -> (rest, Closure need renv 0 item : pushed)) <$> call renv found item) (needs, stack) (reverse items)
                        walk renv stack' needs' function
                    Var k -> do
                        needs' <- if renvMin renv <= k + 1 && k + 1 < renvMin renv + total then do
                            let which = renvMin renv + total - 1 - (k + 1)
                                position = positions !! which
                            if length stack <= position then return (needAt (length needs) (short which position) needs) else do
                                shape <- shapeOfItem (stack !! position) >>= force
                                case shape of
                                    Subterm levels Strict tree -> do
                                        smaller <- checkedTree (withinTree Norec (trees !! which) tree)
                                        if smaller then return (IntSet.foldr (\level -> needAt level (illegal which position)) needs levels) else refuse (illegal which position)
                                    DeadCode -> return needs
                                    Bound levels -> return (IntSet.foldr (\level -> needAt level (illegal which position)) needs levels)
                                    _ -> refuse (illegal which position)
                            else return needs
                        -- Recursive heads must also check the other arguments
                        -- for pending recursive calls (#20413).
                        state renv NoNeed stack needs' $ return $ case drop k (renvCtx renv) of
                            Just value : _ -> Just (lift 0 (k + 1) value, [])
                            _ -> Nothing
                    Case block i us kept hints clause scrutinee branches
                        | Just (family, spec, packet) <- familyOf world (Ind block i us) -> do
                            let (clause', branches') = expanded packet block i us kept hints clause branches
                            (needScrutinee, needs1) <- call renv needs scrutinee
                            needs2 <- inert renv needs1 clause'
                            let level = length needs2 + 1
                            shape <- late (subterm renv [] scrutinee) >>= iota level
                            rows <- branchShapes family packet shape
                            stack' <- filterStack (renvCtx renv) level (length hints) clause stack
                            needs3 <- foldM (\found (row, branch) -> walk renv (map Given row ++ stack') found branch) (NoNeed : needs2) (zip rows branches')
                            state renv (orElse (head needs3) needScrutinee) stack (tail needs3) $ do
                                (function, items) <- spine <$> ask (renvCtx renv) scrutinee
                                return $ case function of
                                    Con _ _ j _
                                        | (_, branch) : _ <- drop j branches -> Just (substitute (reverse (drop (specParN spec) items)) branch, [])
                                    _ -> Nothing
                    Case {} -> refuse "a match on a family that the oracle has not judged"
                    Fix chosen functions
                        | function' : _ <- drop chosen functions -> do
                            let position = functionArgN function'
                                inner = length functions
                                places = map functionArgN functions
                            needs1 <- foldM (inert renv) (NoNeed : needs) (map functionType functions)
                            inside <- pushPlain renv inner
                            found <- uniform (renvCtx inside) places (length stack) (map functionBody functions)
                            let bodies = dropUniform found (map functionBody functions)
                            filtered <- forM (zip3 [0 ..] (map (< found) [0 ..]) stack) $ \(place, kept, item) -> if kept then return item else if place == position then Given <$> shapeOfItem item else Given <$> (now NotSubterm >>= iota (length needs))
                            let passed = if length stack > position then take (position + 1) filtered else filtered
                                this = liftItems inner passed
                                others = liftItems inner (take found passed)
                            needs2 <- foldM (\known (j, place, body') -> nestedBody inside (place + 1) (if j == chosen then this else others) known body') needs1 (zip3 [0 ..] places bodies)
                            state renv (head needs2) (drop found stack) (tail needs2) $
                                if length stack <= position then return Nothing else case stack !! position of
                                    Given _ -> return Nothing
                                    Closure _ _ lifted value -> do
                                        (function, _) <- spine <$> ask (renvCtx renv) (lift 0 lifted value)
                                        return $ case function of
                                            Con {} -> Just (substitute [Fix j functions | j <- reverse [0 .. inner - 1]] (functionBody function'), take found stack)
                                            _ -> Nothing
                    Proj _ _ receiver -> do
                        (need, needs') <- call renv needs receiver
                        state renv need stack needs' (reduceProjection renv term')
                    PField {} -> state renv NoNeed stack needs (reduceProjection renv term')
                    Cst c us -> state renv NoNeed stack needs (return (fmap (\value -> (value, [])) (worldBody world c us)))
                    Lam _ domain rest -> do
                        (need, needs') <- call renv needs domain
                        case stack of
                            item : others -> do
                                (renv', stack', rest') <- pop need renv item others rest
                                walk renv' stack' needs' rest'
                            [] -> pushBound renv (length needs') >>= \inside -> walk inside [] needs' rest
                    Pi _ domain rest -> do
                        needs' <- inert renv needs domain
                        pushBound renv (length needs') >>= \inside -> walk inside [] needs' rest
                    Let _ value annotation rest -> do
                        (needValue, needs1) <- call renv needs value
                        (needType, needs2) <- call renv needs1 annotation
                        case orElse (needOf stack) (orElse needValue needType) of
                            NoNeed -> do
                                shape <- late (subterm renv [] value)
                                walk (pushLet renv value shape) (liftItems 1 stack) needs2 rest
                            Need _ -> walk renv stack needs2 (substitute [value] rest)
                    -- a cast: its type is checked by itself, and its term
                    -- takes the stack
                    Cast value annotation -> do
                        needs' <- inert renv needs annotation
                        walk renv stack needs' value
                    Ind _ _ _ -> state renv NoNeed stack needs (return Nothing)
                    Con {} -> state renv NoNeed stack needs (return Nothing)
                    _ -> return needs
                -- `check_nested_fix_body`
                nestedBody renv left stack needs body'
                    | left <= (0 :: Int) = inert renv needs body'
                    | otherwise = do
                        found <- ask (renvCtx renv) body'
                        case found of
                            Lam _ domain rest -> do
                                needs' <- inert renv needs domain
                                case stack of
                                    item : others -> do
                                        (renv', stack', rest') <- pop NoNeed renv item others rest
                                        nestedBody renv' (left - 1) stack' needs' rest'
                                    [] -> pushBound renv (length needs') >>= \inside -> nestedBody inside (left - 1) [] needs' rest
                            _ -> refuse "the body of a function has fewer abstractions than its struct argument needs"
                reduceProjection renv value = do
                    reduced <- ask (renvCtx renv) value
                    return (if reduced == value then Nothing else Just (reduced, []))
                -- `check_rec_call_state`
                state renv need stack needs expand' = case orElse need (needOf stack) of
                    NoNeed -> return needs
                    reason -> do
                        unfolded <- expand'
                        case unfolded of
                            Nothing -> return (reason : drop 1 needs)
                            Just (value, items) -> walk renv (items ++ stack) needs value
                -- `check_inert_subterm_rec_call`
                inert renv needs term' = do
                    (need, needs') <- call renv needs term'
                    state renv need [] needs' (return Nothing)
                -- `check_rec_call`
                call renv needs term' = (\found -> (head found, tail found)) <$> walk renv [] (NoNeed : needs) term'

-- `fold_constr_with_binders`: over the parts of a term
parts :: (Int -> a -> Term -> a) -> Int -> a -> Term -> a
parts f depth start term
    = case term of
        Pi _ a b -> f (depth + 1) (f depth start a) b
        Lam _ a t -> f (depth + 1) (f depth start a) t
        Let _ t a u -> f (depth + 1) (f depth (f depth start t) a) u
        Cast t a -> f depth (f depth start t) a
        Proj _ _ receiver -> f depth start receiver
        App t u -> f depth (f depth start t) u
        Case _ _ _ qs ys p t bs -> foldl (\found (zs, body) -> f (depth + length zs) found body) (f depth (f (depth + length ys) (foldl (f depth) start qs) p) t) bs
        Fix _ fs -> foldl (\found g -> f (depth + length fs) (f depth found (functionType g)) (functionBody g)) start fs
        _ -> start

-- `map_with_binders`: the term with its parts replaced
rebuilt :: (Int -> Term -> Term) -> Int -> Term -> Term
rebuilt f depth term
    = case term of
        Pi x a b -> Pi x (f depth a) (f (depth + 1) b)
        Lam x a t -> Lam x (f depth a) (f (depth + 1) t)
        Let x t a u -> Let x (f depth t) (f depth a) (f (depth + 1) u)
        Cast t a -> Cast (f depth t) (f depth a)
        Proj b field receiver -> Proj b field (f depth receiver)
        App t u -> App (f depth t) (f depth u)
        Case b i us qs ys p t bs -> Case b i us (map (f depth) qs) ys (f (depth + length ys) p) (f depth t) [(zs, f (depth + length zs) body) | (zs, body) <- bs]
        Fix k fs -> Fix k [g { functionType = f depth (functionType g), functionBody = f (depth + length fs) (functionBody g) } | g <- fs]
        _ -> term
