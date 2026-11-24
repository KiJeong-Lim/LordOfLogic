{-# LANGUAGE ScopedTypeVariables #-}
module Hol.BETA.Runtime where

import Calc.Presburger.Internal
import Hol.BETA.Arith
import Hol.BETA.Debugger
import Hol.BETA.Notation (NotationDB)
import qualified Hol.BETA.Notation as Notation
import Hol.BETA.TermNode
import Hol.BETA.HOPU
import Hol.BETA.Constant
import Hol.BETA.Header
import Control.Concurrent (ThreadId, myThreadId)
import Control.Exception (bracket, evaluate, finally, mask, mask_, throwIO)
import Control.Monad
import Control.Monad.IO.Class
import Control.Monad.Trans.Class
import Control.Monad.Trans.Except
import Control.Monad.Trans.Reader
import Control.Monad.Trans.State.Strict
import Data.IORef
import Data.Int (Int64)
import Data.Maybe
import Data.Word (Word64)
import qualified Data.IntMap.Strict as IntMap
import qualified Data.IntSet as IntSet
import qualified Data.List as List
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Z.Utils

type Fact = TermNode

type Goal = TermNode

type Stack = [(Context, [Cell])]

type Satisfied = Bool

type RunMore = Bool

type CallId = Unique

type Debugging = Bool

data KernelErr
    = BadGoalGiven TermNode
    | BadFactGiven TermNode
    | UnsupportedArithmeticConstraint TermNode
    | BackendError String
    deriving ()

data Constraint
    = DisagreementConstraint Disagreement
    | EvalutionConstraint TermNode TermNode
    | ArithmeticConstraint !ArithStore !TermNode
    | PresburgerConstraint !ArithStore !MyPresburgerFormulaRep !(Map.Map MyVar TermNode)
    deriving ()

data Cell
    = Cell
        { _GivenFacts         :: Map.Map Constant [Fact]
        , _GivenHypos         :: [Fact]
        , _GivenArithPremises :: ArithStore
        , _ScopeLevel         :: ScopeLevel
        , _WantedGoal         :: Goal
        , _CellCallId         :: CallId
        }
    deriving ()

emptyArithStore :: ArithStore
emptyArithStore = ([], [])

appendArithStore :: ArithStore -> ArithStore -> ArithStore
appendArithStore (leftComparisons, leftFormulas) (rightComparisons, rightFormulas)
    = (leftComparisons ++ rightComparisons, leftFormulas ++ rightFormulas)

nullArithStore :: ArithStore -> Bool
nullArithStore (comparisons, formulas) = null comparisons && null formulas

-- A comparison with a ground truth value needs no solver while no premise is
-- in scope: a true one is entailed by every store, a false one by no
-- consistent store. The solver represents a literal by that many successors.
groundComparison :: ArithStore -> Either ErrMsg Bool -> Maybe Bool
groundComparison premises result = case result of
    Right True -> Just True
    Right False
        | nullArithStore premises -> Just False
    _ -> Nothing

bindArithStore :: VarBinding -> ArithStore -> ArithStore
bindArithStore theta store@(comparisons, formulas)
    = assertVarBinding theta `seq`
        assertArithStore store `seq`
        ( bindVars theta comparisons
        , [ (rep, Map.map (bindVars theta) freeOf) | (rep, freeOf) <- formulas ]
        )

arithStoreTerms :: ArithStore -> [TermNode]
arithStoreTerms (comparisons, formulas)
    = comparisons ++ concatMap (Map.elems . snd) formulas

assertArithStore :: ArithStore -> ()
assertArithStore = assertNonnegativeTerms . arithStoreTerms

assertConstraint :: Constraint -> ()
assertConstraint constraint = case constraint of
    DisagreementConstraint (lhs :=?=: rhs) ->
        assertNonnegativeIndices lhs `seq` assertNonnegativeIndices rhs
    EvalutionConstraint lhs rhs ->
        assertNonnegativeIndices lhs `seq` assertNonnegativeIndices rhs
    ArithmeticConstraint premises term ->
        assertArithStore premises `seq` assertNonnegativeIndices term
    PresburgerConstraint premises _ freeOf ->
        assertArithStore premises `seq` assertNonnegativeTerms (Map.elems freeOf)

assertConstraints :: [Constraint] -> ()
assertConstraints [] = ()
assertConstraints (constraint : rest) = assertConstraint constraint `seq` assertConstraints rest

instance Eq Constraint where
    lhs == rhs
        = assertConstraint lhs `seq`
            assertConstraint rhs `seq`
            case (lhs, rhs) of
                (DisagreementConstraint d1, DisagreementConstraint d2) -> d1 == d2
                (EvalutionConstraint l1 r1, EvalutionConstraint l2 r2) -> l1 == l2 && r1 == r2
                (ArithmeticConstraint p1 t1, ArithmeticConstraint p2 t2) -> p1 == p2 && t1 == t2
                (PresburgerConstraint p1 f1 m1, PresburgerConstraint p2 f2 m2) -> p1 == p2 && f1 == f2 && m1 == m2
                _ -> False

instance Ord Constraint where
    compare lhs rhs
        = assertConstraint lhs `seq`
            assertConstraint rhs `seq`
            case (lhs, rhs) of
                (DisagreementConstraint d1, DisagreementConstraint d2) -> compare d1 d2
                (EvalutionConstraint l1 r1, EvalutionConstraint l2 r2) -> compare l1 l2 <> compare r1 r2
                (ArithmeticConstraint p1 t1, ArithmeticConstraint p2 t2) -> compare p1 p2 <> compare t1 t2
                (PresburgerConstraint p1 f1 m1, PresburgerConstraint p2 f2 m2) -> compare p1 p2 <> compare f1 f2 <> compare m1 m2
                _ -> compare (constraintTag lhs) (constraintTag rhs)
        where
            constraintTag (DisagreementConstraint _) = 0 :: Int
            constraintTag (EvalutionConstraint _ _) = 1
            constraintTag (ArithmeticConstraint _ _) = 2
            constraintTag (PresburgerConstraint _ _ _) = 3

assertEvaluationTerms :: [(TermNode, TermNode)] -> ()
assertEvaluationTerms [] = ()
assertEvaluationTerms ((lhs, rhs) : rest)
    = assertNonnegativeIndices lhs `seq`
        assertNonnegativeIndices rhs `seq`
        assertEvaluationTerms rest

data Context
    = Context
        { _TotalVarBinding :: VarBinding
        , _CurrentLabeling :: Labeling
        , _LeftConstraints :: [Constraint]
        , _ContextThreadId :: CallId
        , _debuggindModeOn :: IORef Debugging
        }
    deriving ()

assertCell :: Cell -> ()
assertCell cell
    | _ScopeLevel cell < 0 = undefined
    | otherwise =
        assertNonnegativeTerms (concat (Map.elems (_GivenFacts cell))) `seq`
        assertNonnegativeTerms [ NCon constant Nothing | constant <- Map.keys (_GivenFacts cell) ] `seq`
        assertNonnegativeTerms (_GivenHypos cell) `seq`
        assertArithStore (_GivenArithPremises cell) `seq`
        assertNonnegativeIndices (_WantedGoal cell)

assertContext :: Context -> ()
assertContext ctx
    = assertVarBinding (_TotalVarBinding ctx) `seq`
        assertLabelingDomain (_CurrentLabeling ctx) `seq`
        assertConstraints (_LeftConstraints ctx)

assertLabelingDomain :: Labeling -> ()
assertLabelingDomain labeling
    = assertScopeMap (_ConLabel labeling) `seq`
        assertScopeMap (_VarLabel labeling) `seq`
        assertKeyMap (_ConTypes labeling) `seq`
        assertKeyMap (_VarTypes labeling) `seq`
        assertKeyMap (_TyVarKeys labeling)
    where
        assertScopeMap values = IntMap.foldrWithKey
            (\key level rest -> if key < 0 || level < 0 then undefined else rest)
            () values
        assertKeyMap values = IntMap.foldrWithKey
            (\key _ rest -> if key < 0 then undefined else rest)
            () values

assertStack :: Stack -> ()
assertStack [] = ()
assertStack ((ctx, cells) : rest)
    = assertContext ctx `seq` assertCells cells `seq` assertStack rest
    where
        assertCells [] = ()
        assertCells (cell : more) = assertCell cell `seq` assertCells more

-- What a goal `oracle Name Term` hands to the host: the
-- name, the type at which the goal uses `oracle`, the term, and where the goal
-- stands: the hypotheses that `=>` has given it, the latest first, and the
-- number of `pi` around it. The name has no variable. The term, the type and
-- the hypotheses are as the bindings of the call leave them, and may have
-- variables. `_QuestionLeft` has the constraints that the search has left on
-- the variables of the term and of the hypotheses, and on the variables that
-- those constraints connect with them. `_QuestionCons` has each constant that
-- a `pi` made, with its level, and `_QuestionVars` each variable, with its
-- scope: the level of the innermost such constant that its value may have.
-- Both are in the order in which the term, then the hypotheses and then the
-- constraints first have them; a type variable is in neither.
data Question
    = Question
        { _QuestionName       :: String
        , _QuestionType       :: TermNode
        , _QuestionTerm       :: TermNode
        , _QuestionHyps       :: [TermNode]
        , _QuestionNest       :: ScopeLevel
        , _QuestionCons       :: [(Constant, ScopeLevel)]
        , _QuestionVars       :: [(LogicVar, ScopeLevel)]
        , _QuestionLeft       :: [Constraint]
        , _QuestionEdit       :: Maybe (IO Context)
        , _QuestionCheckpoint :: Maybe (IO OracleCheckpoint)
        }
    deriving ()

-- The question of the goal `oracle` applied to `args`, which are the type
-- instance, the name and the term, in the context `ctx` and with the
-- hypotheses `hyps`. Nothing when the name is not a string without a variable.
askedQuestion :: Context -> [TermNode] -> ScopeLevel -> [TermNode] -> Maybe Question
askedQuestion ctx hyps level args
    = case args of
        [typ, name, term]
            | Just text <- groundString (bound name) -> Just (asked text (rewrite NF (bound typ)) (rewrite NF (bound term)))
        _ -> Nothing
    where
        bound = bindVars (_TotalVarBinding ctx)
        labeling = _CurrentLabeling ctx
        asked text typ term = Question { _QuestionName = text, _QuestionType = typ, _QuestionTerm = term, _QuestionHyps = given, _QuestionNest = level, _QuestionCons = [(constant, lookupLabel constant labeling) | constant <- constants], _QuestionVars = [(variable, lookupLabel variable labeling) | variable <- variables], _QuestionLeft = left, _QuestionEdit = Nothing, _QuestionCheckpoint = Nothing } where
            given = map (rewrite NF . bound) hyps
            direct = snd (occurrences (term : given))
            directSet = Set.fromList direct
            -- The order of the constraints does not depend on the engine: it
            -- is that of their texts, with the variables that only they have
            -- shown alike.
            alike = VarBinding (Map.fromList [(variable, mkLVar (LV_Named ("_" ++ show place))) | (place, variable) <- zip [0 :: Int ..] direct])
            blank constraint = VarBinding (Map.fromList [(variable, mkLVar (LV_Named "_")) | variable <- Set.toList (Set.unions (map getLVars (constraintTerms constraint)) `Set.difference` directSet)])
            left = List.sortOn (\constraint -> shows (zonkLVar (blank constraint) (zonkLVar alike constraint)) "") (connected directSet (zonkLVar (_TotalVarBinding ctx) (_LeftConstraints ctx)))
            (constants, variables) = occurrences (term : given ++ concatMap constraintTerms left)

-- The terms of a constraint.
constraintTerms :: Constraint -> [TermNode]
constraintTerms (DisagreementConstraint (lhs :=?=: rhs)) = [lhs, rhs]
constraintTerms (EvalutionConstraint lhs rhs) = [lhs, rhs]
constraintTerms (ArithmeticConstraint premises term) = term : arithStoreTerms premises
constraintTerms (PresburgerConstraint premises _ freeOf) = arithStoreTerms premises ++ Map.elems freeOf

-- The constraints that have one of the variables `known`, or a variable of a
-- constraint that does.
connected :: Set.Set LogicVar -> [Constraint] -> [Constraint]
connected known constraints = visit known known IntSet.empty where
    rows = IntMap.fromDistinctAscList [(place, (constraint, Set.unions (map getLVars (constraintTerms constraint)))) | (place, constraint) <- zip [0 ..] constraints]
    links = IntMap.foldlWithKey' (\found place (_, variables) -> Set.foldl' (\table variable -> Map.insertWith IntSet.union variable (IntSet.singleton place) table) found variables) Map.empty rows
    -- A breadth-first layer keeps the original constraint order, including
    -- ties in the caller's stable sort, without rescanning untouched rows.
    visit seen frontier taken
        | IntSet.null touching = []
        | otherwise = map fst selected ++ visit (Set.union seen reached) (Set.difference reached seen) (IntSet.union taken touching)
        where
            touching = Set.foldl' (\found variable -> IntSet.union found (Map.findWithDefault IntSet.empty variable links)) IntSet.empty frontier `IntSet.difference` taken
            selected = map (rows IntMap.!) (IntSet.toAscList touching)
            reached = Set.unions (map snd selected)

-- The constants that `pi` made and the variables, other than type variables,
-- of the terms, each once and in the order in which the terms first have them.
occurrences :: [TermNode] -> ([Constant], [LogicVar])
occurrences = (\(_, _, constants, variables) -> (reverse constants, reverse variables)) . List.foldl' walk (Set.empty, Set.empty, [], []) where
    walk found@(seenConstants, seenVariables, constants, variables) term = case term of
        LVar (LV_ty_var _) -> found
        LVar variable -> if variable `Set.member` seenVariables then found else (seenConstants, Set.insert variable seenVariables, constants, variable : variables)
        NCon constant@(DC (DC_Unique _ _)) _ -> if constant `Set.member` seenConstants then found else (Set.insert constant seenConstants, seenVariables, constant : constants, variables)
        NApp function argument _ -> walk (walk found function) argument
        NLam _ _ body _ -> walk found body
        Susp {} -> walk found (rewrite NF term)
        NPresburgerCheck _ freeOf _ -> List.foldl' walk found (Map.elems freeOf)
        _ -> found

-- The goal that a question came from, without the type instance: `oracle Name Term`.
questionGoal :: Question -> TermNode
questionGoal question = foldlNApp (mkNCon (DC_Named "oracle")) [name, _QuestionTerm question] where
    character = mkNCon (TC_Named "char")
    name = foldr (\ch rest -> foldlNApp (mkNCon DC_Cons) [character, mkNCon (DC_ChrL ch), rest]) (mkNApp (mkNCon DC_Nil) character) (_QuestionName question)

-- The characters of a string that has no variable.
groundString :: TermNode -> Maybe String
groundString term
    = case unfoldlNApp (rewrite NF term) of
        (NCon (DC DC_Nil) _, _) -> Just ""
        (NCon (DC DC_Cons) _, args)
            | [NCon (DC (DC_ChrL chr)) _, rest] <- drop (length args - 2) args -> (chr :) <$> groundString rest
        _ -> Nothing

-- What the callback of `oracle` sees of a run: the
-- context of the question, not that of the run. The terms of a question have
-- the values of their variables in them, so this context has no value of a
-- variable. It has the constraints of the question, and the labels and types
-- of its constants and variables. It is made of the question alone, so it
-- does not depend on the engine. The edit capability reaches the run itself.
questionContext :: RuntimeEnv -> Context -> Question -> Context
questionContext env context question = context { _TotalVarBinding = mempty, _CurrentLabeling = selected, _LeftConstraints = _QuestionLeft question } where
    labeling = questionTyped env question (_CurrentLabeling (refineContext env context))
    constants = IntSet.fromList [unUnique unique | (DC (DC_Unique unique _), _) <- _QuestionCons question]
    variables = IntSet.fromList [lvKey variable | (variable, _) <- _QuestionVars question, keyed variable]
    names = Set.fromList [name | (LV_Named name, _) <- _QuestionVars question]
    keyed variable = case variable of
        LV_Named _ -> False
        _ -> True
    -- The types are as the run has them by now, because this context has no
    -- value of a type variable either. The type variables that it knows are
    -- those of these types.
    current = specializeType (_ProgramKindEnv env) (_TotalVarBinding context)
    constantTypes = IntMap.map current (IntMap.restrictKeys (_ConTypes labeling) constants)
    variableTypes = IntMap.map current (IntMap.restrictKeys (_VarTypes labeling) variables)
    namedTypes = Map.map current (Map.restrictKeys (_NamedTypes labeling) names)
    typeVariables = IntSet.fromList (concatMap undecided (IntMap.elems constantTypes ++ IntMap.elems variableTypes ++ Map.elems namedTypes))
    undecided typ = case typ of
        TyApp function argument -> undecided function ++ undecided argument
        _ -> maybe [] (\unique -> [unUnique unique]) (runtimeTypeVariable typ)
    selected = labeling { _ConLabel = IntMap.restrictKeys (_ConLabel labeling) constants, _VarLabel = IntMap.restrictKeys (_VarLabel labeling) variables, _ConTypes = constantTypes, _VarTypes = variableTypes, _NamedTypes = namedTypes, _TyVarKeys = IntMap.fromSet (const ()) typeVariables }

-- The term of a question has the type of the question. When the term is a
-- variable that the run made, that type replaces a recorded one that has a
-- guessed instance (guessedType), or none.
questionTyped :: RuntimeEnv -> Question -> Labeling -> Labeling
questionTyped env question labeling = case (_QuestionTerm question, primitiveTypeArgumentWithKinds (_ProgramKindEnv env) (_QuestionType question)) of
    (LVar variable@(LV_Unique unique _), Just typ)
        | maybe True guessedType (lookupLVarType variable labeling) -> labeling { _VarTypes = IntMap.insert (unUnique unique) typ (_VarTypes labeling) }
    _ -> labeling

-- The exposed action retains only this cell after the callback ends.
oracleEdit :: IORef (Maybe (ThreadId, IO Context)) -> IO Context
oracleEdit capability = do
    caller <- myThreadId
    granted <- readIORef capability
    case granted of
        Just (owner, edit)
            | caller == owner -> edit
        _ -> ioError (userError "oracle edit capability is outside its callback")

newtype OracleCheckpoint
    = OracleCheckpoint { checkpointRestore :: IORef (Maybe (ThreadId, IO ())) }
    deriving ()

restoreOracleCheckpoint :: OracleCheckpoint -> IO (Either ErrMsg ())
restoreOracleCheckpoint checkpoint = do
    caller <- myThreadId
    granted <- readIORef (checkpointRestore checkpoint)
    case granted of
        Just (owner, action)
            | caller == owner -> Right <$> mask_ action
        _ -> return (Left "oracle checkpoint is outside its callback")

-- Editing is local to this call. Retained capabilities release their captured
-- states on exit, and a deferred exception in the Bool is forced before exit.
answerOracle :: RuntimeEnv -> Context -> Question -> IO Stack -> IO (Bool, Context, VarBinding)
answerOracle env context question inspect = mask $ \restoreAction -> do
    owner <- myThreadId
    current <- newIORef context
    entered <- newIORef False
    alive <- newIORef True
    checkpoints <- newIORef []
    stack <- readIORef (_StackRef env)
    pending <- readIORef (_PendingSubst env)
    names <- readIORef (_NameCacheRef env)
    let edit = do
            seen <- readIORef entered
            unless seen $ do
                inspected <- inspect
                case inspected of
                    (shown, cells) : older -> do
                        let refined = refineContext env shown
                            ctx = refined { _CurrentLabeling = questionTyped env question (_CurrentLabeling refined) }
                            frames = (ctx, cells) : older
                        writeIORef (_StackRef env) frames
                        modifyIORef' (_NameCacheRef env) (recordVisibleLVarHints frames)
                        writeIORef current ctx
                        writeIORef entered True
                    _ -> ioError (userError "oracle has no active goal to edit")
            readIORef current
        checkpoint = do
            caller <- myThreadId
            active <- readIORef alive
            unless (active && caller == owner) (ioError (userError "oracle checkpoint is outside its callback"))
            frames <- readIORef (_StackRef env)
            changed <- readIORef (_PendingSubst env)
            cache <- readIORef (_NameCacheRef env)
            ctx <- readIORef current
            editing <- readIORef entered
            handle <- newIORef (Just (owner, do
                writeIORef (_StackRef env) frames
                writeIORef (_PendingSubst env) changed
                writeIORef (_NameCacheRef env) cache
                writeIORef current ctx
                writeIORef entered editing))
            modifyIORef' checkpoints (handle :)
            return (OracleCheckpoint handle)
    capability <- newIORef (Just (owner, edit))
    checkpointCapability <- newIORef (Just checkpoint)
    let takeCheckpoint = do
            granted <- readIORef checkpointCapability
            maybe (ioError (userError "oracle checkpoint is outside its callback")) id granted
        cleanup = do
            writeIORef alive False
            writeIORef capability Nothing
            writeIORef checkpointCapability Nothing
            readIORef checkpoints >>= mapM_ (\handle -> writeIORef handle Nothing)
            writeIORef checkpoints []
            writeIORef (_StackRef env) stack
            writeIORef (_PendingSubst env) pending
            writeIORef (_NameCacheRef env) names
        scope = OracleScope owner alive entered stack pending names
    writeIORef (_StackRef env) []
    writeIORef (_PendingSubst env) mempty
    withRuntimePhase env (RuntimeOracle scope) (restoreAction (do
        answer <- _OraclePrimitive env (questionContext env context question) question { _QuestionEdit = Just (oracleEdit capability), _QuestionCheckpoint = Just takeCheckpoint } >>= evaluate
        changed <- readIORef (_PendingSubst env)
        editing <- readIORef entered
        unless (editing || Map.null (unVarBinding changed)) (ioError (userError "oracle assignments require its edit capability"))
        (,,) answer <$> readIORef current <*> pure changed)) `finally` cleanup

newtype StepId = StepId Word64 deriving (Eq, Ord, Show)

data DebugReason
    = DebugGoal TermNode
    | DebugTrace
    | StepFailed StepId
    deriving ()

data DebugEvent
    = DebugEvent
        { debugReason  :: DebugReason
        , debugContext :: Context
        , debugStack   :: Stack
        , debugText    :: String
        }
    deriving ()

data OracleScope
    = OracleScope ThreadId (IORef Bool) (IORef Bool) Stack VarBinding NameCache
    deriving ()

data RuntimePhase
    = RuntimeHost
    | RuntimeRunning
    | RuntimeDebugger
    | RuntimeStepFailure
    | RuntimeService
    | RuntimeOracle OracleScope
    deriving ()

data StepBoundary
    = StepBoundary
        { stepIdentity     :: StepId
        , stepOlder        :: Int
        , stepStart        :: DebugEvent
        , stepStartPending :: VarBinding
        , stepFailed       :: Bool
        , stepStarted      :: Bool
        , stepNotified     :: Bool
        }
    deriving ()

data RuntimeControl
    = RuntimeControl
        { runtimePhase       :: RuntimePhase
        , runtimeNextStep    :: Word64
        , runtimeStep        :: Maybe StepBoundary
        , runtimeLabel       :: Maybe TermNode
        , runtimeRestores    :: Integer
        , runtimeQuit        :: Bool
        , runtimeOwner       :: Maybe ThreadId
        , runtimeLease       :: Maybe RuntimeLease
        , runtimeInterrupted :: Bool
        , runtimeTypeSupply  :: Maybe (IO (Maybe Unique))
        , runtimeReplayStop  :: Bool
        }
    deriving ()

newtype RuntimeLease = RuntimeLease (IORef ()) deriving (Eq)

newRuntimeControl :: IO (IORef RuntimeControl)
newRuntimeControl = newIORef (RuntimeControl RuntimeHost 1 Nothing Nothing 0 False Nothing Nothing False Nothing False)

-- The lease does not start a run: the mark of an interrupted run stays until
-- `startRun` has dropped what that run left.
claimRuntime :: RuntimeEnv -> IO RuntimeLease
claimRuntime env = do
    caller <- myThreadId
    lease <- RuntimeLease <$> newIORef ()
    claimed <- atomicModifyIORef' (_RuntimeControl env) $ \control -> case runtimePhase control of
        RuntimeHost
            | isNothing (runtimeLease control) && maybe True (== caller) (runtimeOwner control) ->
                (control { runtimeLease = Just lease }, Right lease)
        _ -> (control, Left "runtime environment already belongs to an active run or session")
    either (ioError . userError) return claimed

-- The start of a run in an environment, whichever engine runs it. The
-- pending assignments of an interrupted run are dropped with it: a host
-- cannot assign after an interruption, so what is pending then is of that
-- run. Assignments that a host made between runs are for this run and stay.
-- The exposed stack is emptied and the controls of a run are reset.
startRun :: RuntimeEnv -> IO ()
startRun env = do
    interrupted <- runtimeInterrupted <$> readIORef (_RuntimeControl env)
    when interrupted (writeIORef (_PendingSubst env) mempty)
    writeIORef (_StackRef env) []
    modifyIORef' (_RuntimeControl env) (\control -> control { runtimeQuit = False, runtimeStep = Nothing, runtimeLabel = Nothing, runtimeInterrupted = False, runtimeReplayStop = False })

releaseRuntime :: RuntimeEnv -> RuntimeLease -> IO ()
releaseRuntime env lease = atomicModifyIORef' (_RuntimeControl env) $ \control ->
    (if runtimeLease control == Just lease then control { runtimeLease = Nothing } else control, ())

-- A callback can call the ordinary host commands on its own thread. A second
-- thread cannot inspect or change the exposed state while that scope is live.
withRuntimeAccess :: MonadRuntime m => RuntimeEnv -> m a -> m a
withRuntimeAccess env action = runtimeBracket enter leave (const action) where
    enter = do
        caller <- myThreadId
        claimed <- atomicModifyIORef' (_RuntimeControl env) $ \control ->
            if maybe True (== caller) (runtimeOwner control) then
                (control { runtimeOwner = Just caller }, Right (runtimeOwner control))
            else
                (control, Left "runtime state belongs to another active thread")
        either (ioError . userError) return claimed
    leave previous = modifyIORef' (_RuntimeControl env) (\control -> control { runtimeOwner = previous })

-- The whole run, including monadic decoding and unique allocation, owns the
-- environment. Acquisition is masked by runtimeBracket; exception cleanup
-- leaves Undo available but does not silently resume a partly consumed state.
withRuntimeExecution :: UniqueM m => RuntimeEnv -> Maybe RuntimeLease -> m a -> m a
withRuntimeExecution env lease action = runtimeBracketOutcome enter leave run where
    enter = do
        caller <- myThreadId
        claimed <- atomicModifyIORef' (_RuntimeControl env) $ \control -> case runtimePhase control of
            RuntimeHost
                | runtimeLease control == lease && maybe True (== caller) (runtimeOwner control) ->
                    (control { runtimePhase = RuntimeRunning, runtimeOwner = Just caller }, Right (runtimeOwner control))
            _ -> (control, Left "runtime environment already belongs to an active run or session")
        either (ioError . userError) return claimed
    run _ = do
        supply <- getUniqueAllocator
        liftIO (modifyIORef' (_RuntimeControl env) (\control -> control { runtimeTypeSupply = supply }))
        action
    leave previous finished = do
        modifyIORef' (_RuntimeControl env) (\control -> control { runtimePhase = RuntimeHost, runtimeOwner = previous, runtimeInterrupted = runtimeInterrupted control || not finished })

markRuntimeInterrupted :: RuntimeEnv -> IO ()
markRuntimeInterrupted env = modifyIORef' (_RuntimeControl env) (\control -> control { runtimeInterrupted = True })

withRuntimePhase :: RuntimeEnv -> RuntimePhase -> IO a -> IO a
withRuntimePhase env phase action = withRuntimeAccess env (bracket enter leave (const action)) where
    enter = do
        previous <- runtimePhase <$> readIORef (_RuntimeControl env)
        modifyIORef' (_RuntimeControl env) (\control -> control { runtimePhase = phase })
        return previous
    leave previous = modifyIORef' (_RuntimeControl env) (\control -> control { runtimePhase = previous })

nextStepId :: RuntimeEnv -> IO (Either ErrMsg StepId)
nextStepId env = atomicModifyIORef' (_RuntimeControl env) $ \control ->
    if runtimeNextStep control == 0 || runtimeNextStep control > fromIntegral (maxBound :: Int64) then
        (control, Left "step identifiers are exhausted")
    else
        (control { runtimeNextStep = runtimeNextStep control + 1 }, Right (StepId (runtimeNextStep control)))

runtimeCanControl :: RuntimeEnv -> IO (Either ErrMsg ())
runtimeCanControl env = do
    caller <- myThreadId
    control <- readIORef (_RuntimeControl env)
    return $ if maybe False (/= caller) (runtimeOwner control) then
        Left "runtime state belongs to another active thread"
    else case runtimePhase control of
            RuntimeHost -> Right ()
            RuntimeDebugger -> Right ()
            RuntimeStepFailure -> Right ()
            _ -> Left "execution state can be controlled only between runs or at a debugger stop"

runtimeCanResume :: RuntimeEnv -> IO (Either ErrMsg ())
runtimeCanResume env = do
    caller <- myThreadId
    control <- readIORef (_RuntimeControl env)
    return $ if maybe False (/= caller) (runtimeOwner control) then
        Left "runtime state belongs to another active thread"
    else if runtimeInterrupted control then
        Left "runtime was interrupted; restore a saved state or start a new run"
    else Right ()

runtimeCanSnapshot :: RuntimeEnv -> IO (Either ErrMsg ())
runtimeCanSnapshot env = do
    usable <- runtimeCanResume env
    phase <- runtimePhase <$> readIORef (_RuntimeControl env)
    return $ usable >> case phase of
        RuntimeRunning -> Left "execution state is not exposed while search is running"
        _ -> Right ()

runtimeCanInterpret :: RuntimeEnv -> IO (Either ErrMsg ())
runtimeCanInterpret env = do
    lease <- runtimeLease <$> readIORef (_RuntimeControl env)
    return $ case lease of
        Nothing -> Right ()
        Just _ -> Left "native sessions require the Hol.V1.FullRuntime snapshot and step APIs"

runtimeCanAssign :: RuntimeEnv -> IO (Either ErrMsg ())
runtimeCanAssign env = do
    usable <- runtimeCanResume env
    control <- readIORef (_RuntimeControl env)
    case usable of
        Left message -> return (Left message)
        Right () -> allowed control
    where
        allowed control = case runtimePhase control of
            RuntimeHost
                | maybe False stepFailed (runtimeStep control) -> return (Left "restore or end the failed step before assigning")
                | otherwise -> return (Right ())
            RuntimeDebugger -> return (Right ())
            RuntimeOracle (OracleScope owner alive entered _ _ _) -> do
                caller <- myThreadId
                active <- readIORef alive
                editing <- readIORef entered
                return (if caller == owner && active && editing then Right () else Left "oracle assignments require its active edit capability")
            _ -> return (Left "debugger assignment is not allowed in this callback")

runtimeView :: RuntimeEnv -> IO (Stack, VarBinding)
runtimeView env = withRuntimeAccess env $ do
    control <- readIORef (_RuntimeControl env)
    case (runtimePhase control, runtimeStep control) of
        (RuntimeStepFailure, Just boundary) -> return (debugStack (stepStart boundary), stepStartPending boundary)
        (RuntimeHost, Just boundary)
            | stepFailed boundary -> return (debugStack (stepStart boundary), stepStartPending boundary)
        _ -> (,) <$> readIORef (_StackRef env) <*> readIORef (_PendingSubst env)

beginStep :: Runtime (Either ErrMsg StepId)
beginStep = do
    env <- askRuntimeEnv
    liftIO $ do
        allowed <- (\control usable interpreted -> control >> usable >> interpreted) <$> runtimeCanControl env <*> runtimeCanResume env <*> runtimeCanInterpret env
        control <- readIORef (_RuntimeControl env)
        frames <- readIORef (_StackRef env)
        case (allowed, runtimeStep control, frames) of
            (Left message, _, _) -> return (Left message)
            _
                | RuntimeStepFailure <- runtimePhase control -> return (Left "restore the failed proof state before beginning a step")
            (_, Just _, _) -> return (Left "a step is already active")
            (_, _, []) -> return (Left "no active goal")
            (_, Nothing, (ctx, cells) : older) -> do
                identifier <- nextStepId env
                case identifier of
                    Left message -> return (Left message)
                    Right key -> do
                        verbose <- readIORef (_VerboseTyping env)
                        pending <- readIORef (_PendingSubst env)
                        let viewed = map (\(context, goals) -> (zonkLVar pending context, map (zonkLVar pending) goals)) frames
                            shown = zonkLVar pending ctx
                            text = showsCurrentState (_NotationDB env) (_ProgramKindEnv env) verbose (Map.keysSet (_TypeInfo env)) (_TypeInfo env) shown (map (zonkLVar pending) cells) older ""
                            event = DebugEvent DebugTrace shown viewed text
                        modifyIORef' (_RuntimeControl env) (\state -> state { runtimeStep = Just (StepBoundary key (length older) event pending False False False) })
                        return (Right key)

endStep :: StepId -> Runtime (Either ErrMsg ())
endStep identifier = do
    env <- askRuntimeEnv
    liftIO $ do
        allowed <- (\control usable interpreted -> control >> usable >> interpreted) <$> runtimeCanControl env <*> runtimeCanResume env <*> runtimeCanInterpret env
        case allowed of
            Left message -> return (Left message)
            Right () -> atomicModifyIORef' (_RuntimeControl env) $ \control -> case runtimeStep control of
                Just boundary
                    | stepIdentity boundary == identifier -> (control { runtimeStep = Nothing }, Right ())
                _ -> (control, Left "step identifier is not active")

data RuntimeEnv
    = RuntimeEnv
        { _Debugger        :: RuntimeEnv -> DebugEvent -> IO ()
        , _RuntimeControl  :: IORef RuntimeControl
        , _Answer          :: Context -> IO RunMore
        , _PrintPrimitive  :: Context -> TermNode -> IO ()
        , _ReadPrimitive   :: Context -> TermNode -> IO (Maybe TermNode)
        , _OraclePrimitive :: Context -> Question -> IO Bool
        , _TypeInfo        :: Map.Map LogicVar (MonoType Int)
        , _PendingSubst    :: IORef LogicVarSubst
        , _ProgramKindEnv  :: KindEnv
        , _ProgramTypeEnv  :: TypeEnv
        , _VerboseTyping   :: IORef Bool
        , _StackRef        :: IORef Stack
        , _NameCacheRef    :: IORef NameCache
        , _DebuggingRef    :: IORef Debugging
        , _NotationDB      :: NotationDB
        , _ModuleName      :: String
        , _QueryCallId     :: Maybe CallId
        }
    deriving ()

newtype Runtime a
    = Runtime { unRuntime :: ReaderT RuntimeEnv IO a }
    deriving ()

instance Functor Runtime where
    fmap f (Runtime m) = Runtime (fmap f m)

instance Applicative Runtime where
    pure = Runtime . pure
    Runtime f <*> Runtime x = Runtime (f <*> x)

instance Monad Runtime where
    return = pure
    Runtime m >>= k = Runtime (m >>= unRuntime . k)

instance MonadIO Runtime where
    liftIO = Runtime . liftIO

instance MonadRuntime Runtime where
    runtimeBracket acquire release action = Runtime (runtimeBracket acquire release (unRuntime . action))
    runtimeBracketOutcome acquire release action = Runtime (runtimeBracketOutcome acquire release (unRuntime . action))

runRuntime :: Runtime a -> RuntimeEnv -> IO a
runRuntime (Runtime m) env = withRuntimeAccess env (runReaderT m env)

askRuntimeEnv :: Runtime RuntimeEnv
askRuntimeEnv = Runtime ask

data Snapshot
    = Snapshot
        { _SnapOwner          :: IORef Stack
        , _SnapPendingOwner   :: IORef LogicVarSubst
        , _SnapNameCacheOwner :: IORef NameCache
        , _SnapStack          :: Stack
        , _SnapPendingSubst   :: LogicVarSubst
        , _SnapNameCache      :: NameCache
        , _SnapStep           :: Maybe StepBoundary
        , _SnapLabel          :: Maybe TermNode
        , _SnapDebugStop      :: Bool
        }
    deriving ()

snapshot :: Runtime Snapshot
snapshot = do
    env <- askRuntimeEnv
    liftIO $ do
        permitted <- (>>) <$> runtimeCanSnapshot env <*> runtimeCanInterpret env
        either (ioError . userError) return permitted
        control <- readIORef (_RuntimeControl env)
        (st, ps, nc) <- case runtimePhase control of
            RuntimeOracle (OracleScope _ _ _ beforeStack beforePending beforeNames) -> return (beforeStack, beforePending, beforeNames)
            _ -> (,,) <$> readIORef (_StackRef env) <*> readIORef (_PendingSubst env) <*> readIORef (_NameCacheRef env)
        assertStack st `seq` assertVarBinding ps `seq` return Snapshot
            { _SnapOwner = _StackRef env
            , _SnapPendingOwner = _PendingSubst env
            , _SnapNameCacheOwner = _NameCacheRef env
            , _SnapStack = st
            , _SnapPendingSubst = ps
            , _SnapNameCache = nc
            , _SnapStep = runtimeStep control
            , _SnapLabel = runtimeLabel control
            , _SnapDebugStop = case runtimePhase control of
                RuntimeDebugger -> True
                _ -> runtimeReplayStop control
            }

-- A snapshot is meaningful only for the runtime whose choice stack it
-- captured.  In particular, a query/reload creates a fresh stack ref, so an
-- old debugger snapshot cannot time-travel into the new runtime.
restore :: Snapshot -> Runtime (Either ErrMsg ())
restore snap
    = assertStack (_SnapStack snap) `seq`
        assertVarBinding (_SnapPendingSubst snap) `seq` do
    env <- askRuntimeEnv
    allowed <- liftIO ((>>) <$> runtimeCanControl env <*> runtimeCanInterpret env)
    case allowed of
        Left message -> return (Left message)
        Right ()
            | _SnapOwner snap /= _StackRef env
                || _SnapPendingOwner snap /= _PendingSubst env
                || _SnapNameCacheOwner snap /= _NameCacheRef env -> return (Left "snapshot belongs to a different runtime")
            | otherwise -> liftIO $ mask_ $ do
                writeIORef (_StackRef env) (_SnapStack snap)
                writeIORef (_PendingSubst env) (_SnapPendingSubst snap)
                currentCache <- readIORef (_NameCacheRef env)
                writeIORef (_NameCacheRef env) (mergeKeepingNewEntries (_SnapNameCache snap) currentCache)
                -- beginStep skips the state which its caller already saw.
                -- Restoring exposes that state again, including its label.
                modifyIORef' (_RuntimeControl env) (\control -> control
                    { runtimeStep = fmap (\boundary -> boundary { stepStarted = True }) (_SnapStep snap)
                    , runtimeLabel = _SnapLabel snap
                    , runtimeReplayStop = _SnapDebugStop snap
                    , runtimeRestores = runtimeRestores control + 1
                    , runtimeQuit = False
                    , runtimeInterrupted = False
                    , runtimePhase = case runtimePhase control of
                        RuntimeStepFailure -> RuntimeDebugger
                        phase -> phase
                    })
                return (Right ())

cmdDebugToggle :: Runtime ()
cmdDebugToggle = do
    env <- askRuntimeEnv
    liftIO $ modifyIORef (_DebuggingRef env) not

cmdQuit :: Runtime ()
cmdQuit = do
    env <- askRuntimeEnv
    allowed <- liftIO (runtimeCanControl env)
    case allowed of
        Left message -> liftIO (ioError (userError message))
        Right () -> liftIO $ mask_ $ do
            writeIORef (_StackRef env) []
            writeIORef (_PendingSubst env) (VarBinding Map.empty)
            modifyIORef' (_RuntimeControl env) (\control -> control { runtimeStep = Nothing, runtimeLabel = Nothing, runtimeQuit = True, runtimeReplayStop = False })

cmdShow :: SmallId -> Runtime String
cmdShow name
    = do
        env <- askRuntimeEnv
        liftIO $ do
            (st, pending) <- runtimeView env
            cache <- readIORef (_NameCacheRef env)
            let resolved = case fromDisplay name cache of
                    Just lv -> Just lv
                    Nothing -> parseAnonymousLV name `mplus` Just (LV_Named name)
            case (st, resolved) of
                (_, Nothing) -> return ("unknown variable '?" ++ name ++ "'")
                ([], _) -> return "no active goal"
                ((ctx, cells) : _, Just lv)
                    | not (assignmentTargetIsKnown env ctx cells pending lv) ->
                        return ("unknown variable '?" ++ name ++ "'")
                    | otherwise ->
                        let composed = pending <> _TotalVarBinding ctx
                            value = bindVars composed (mkLVar lv)
                        in if value == mkLVar lv
                            then return "unbound"
                            else return (prettyTerm (_NotationDB env) cache value "")

scopeEscaping :: Labeling -> ScopeLevel -> LogicVar -> TermNode -> ([Constant], [LogicVar])
scopeEscaping labeling targetScope targetLV term = assertNonnegativeIndices term `seq` walk term where
    walk :: TermNode -> ([Constant], [LogicVar])
    walk (LVar v)
        | v == targetLV = ([], [])
        | lookupLabel v labeling > targetScope = ([], [v])
        | otherwise = ([], [])
    walk (NCon c _)
        | lookupLabel c labeling > targetScope = ([c], [])
        | otherwise = ([], [])
    walk (NApp t1 t2 _) = combine (walk t1) (walk t2)
    walk (NLam _ _ t _) = walk t
    -- A suspension denotes its body after applying the environment and level
    -- shift.  Walking the raw body can hide a rigid constant or variable that
    -- is substituted for a de Bruijn index.
    walk suspended@Susp {} = walk (rewrite NF suspended)
    walk (NPresburgerCheck _ freeOf _) = foldr (combine . walk) ([], []) (Map.elems freeOf)
    walk _ = ([], [])
    combine (a1, b1) (a2, b2) = (a1 ++ a2, b1 ++ b2)

-- Evidence that can be recovered defensively from values returned by the
-- primitive-read callback.  Unknown/custom terms intentionally carry no
-- evidence so existing embedders are not rejected; literals and proper
-- literal lists have an unambiguous ground type.  The empty list is kept
-- separate because its element type is polymorphic.
data PrimitiveTypeEvidence
    = PrimitiveExactType (MonoType Int)
    | PrimitiveEmptyList
    | PrimitiveInvalidValue
    deriving (Eq)

primitiveBindingTypeOkay :: Labeling -> LogicVar -> TermNode -> Bool
primitiveBindingTypeOkay = primitiveBindingTypeOkayWithKinds primitiveBuiltinKindEnv

primitiveBindingTypeOkayWithKinds :: KindEnv -> Labeling -> LogicVar -> TermNode -> Bool
primitiveBindingTypeOkayWithKinds kindEnv labeling target value
    | assignmentTypeVariable labeling target = isJust (primitiveTypeArgumentWithKinds kindEnv value)
    | otherwise = isJust $ do
        prepared <- evalStateT (renameHostValue temporary value) (Just (-1), Map.empty)
        valueTypeBinding kindEnv mempty labeling (maybeToList (lookupLVarType target labeling)) prepared
    where
        -- This Boolean compatibility API installs no binding. Its private
        -- names are disjoint from the state, including guessed negative IDs.
        reserved = IntSet.unions (map identities (IntMap.elems (_ConTypes labeling) ++ IntMap.elems (_VarTypes labeling) ++ Map.elems (_NamedTypes labeling)))
        identities typ = case typ of
            TyApp function argument -> identities function `IntSet.union` identities argument
            _ -> maybe IntSet.empty (IntSet.singleton . unUnique) (runtimeTypeVariable typ)
        available index
            | index `IntSet.notMember` reserved = Just index
            | index == minBound = Nothing
            | otherwise = available (index - 1)
        temporary key = do
            (next, names) <- get
            case Map.lookup key names of
                Just unique -> return unique
                Nothing -> do
                    index <- lift (next >>= available)
                    let unique = Unique index
                    put (if index == minBound then Nothing else Just (index - 1), Map.insert key unique names)
                    return unique

-- An annotation supplied by the host was checked outside this run. Its
-- numbers can coincide with live type variables, so rename it before any
-- live substitution. The installed term keeps these same fresh identities.
-- A nominal constant, in contrast, gets its type from the current labeling.
prepareHostValue :: RuntimeEnv -> TermNode -> IO (Either ErrMsg (TermNode, Set.Set LogicVar))
prepareHostValue env value = assertNonnegativeIndices value `seq` runExceptT action
    where
        action = do
            (prepared, names) <- runStateT prepare Map.empty
            return (prepared, Set.fromList (map LV_ty_var (Map.elems names)))
        prepare = do
            prepared <- renameHostValue fresh value
            case prepared of
                NCon (DC DC_Nil) location -> do
                    element <- fresh (Left (-1))
                    return (mkNAppLoc location prepared (mkLVar (LV_ty_var element)))
                _ -> return prepared
        fresh key = do
            names <- get
            case Map.lookup key names of
                Just unique -> return unique
                Nothing -> do
                    supply <- liftIO (runtimeTypeSupply <$> readIORef (_RuntimeControl env))
                    allocate <- maybe (lift (throwE "the runtime has no callback type-variable allocator")) return supply
                    unique <- liftIO allocate >>= maybe (liftIO (throwIO UniqueExhausted)) return
                    modify (Map.insert key unique)
                    return unique

renameHostValue :: Monad m => (Either Int Unique -> m Unique) -> TermNode -> m TermNode
renameHostValue fresh = term
    where
        typ value = case value of
            TyVar index -> named (Left index)
            TyMTV unique -> named (Right unique)
            TyCon (TCon (TC_Unique unique) _) -> named (Right unique)
            TyApp function argument -> TyApp <$> typ function <*> typ argument
            _ -> return value
        named key = (\unique -> TyCon (TCon (TC_Unique unique) Star)) <$> fresh key
        term value = case value of
            LVar (LV_ty_var unique) -> mkLVar . LV_ty_var <$> fresh (Right unique)
            NApp function argument location -> NApp <$> term function <*> term argument <*> pure location
            NLam hint (LamType annotation) body location -> NLam hint <$> (LamType <$> traverse typ annotation) <*> term body <*> pure location
            Susp {} -> term (rewrite NF value)
            NPresburgerCheck formula free location -> NPresburgerCheck formula <$> traverse term free <*> pure location
            _ -> return value

-- Types of closed values at a host boundary. Elaborated polymorphic
-- constants carry their type arguments before their ordinary arguments;
-- those arguments instantiate the declaration's scheme. Keep the equations
-- of applications, including those involving in-run nominal constants.
runtimeValueType :: KindEnv -> VarBinding -> Labeling -> TermNode -> Maybe (MonoType Int, IntMap.IntMap (MonoType Int))
runtimeValueType kinds binding labeling value = runStateT (go [] (rewrite NF value)) IntMap.empty
    where
        current = specializeType kinds binding
        go local value = case unfoldlNApp value of
            (NCon (DC constructor) _, arguments)
                | Just (Forall variables body) <- Map.lookup constructor (_TypeEnv labeling) -> do
                    let (types, terms) = splitAt (length variables) arguments
                    guard (length types == length variables)
                    instances <- lift (mapM (primitiveTypeArgumentWithKinds kinds) types)
                    instantiated <- lift (instantiate instances body)
                    foldM (apply local) instantiated terms
            (function, arguments)
                | not (null arguments) -> go local function >>= \typ -> foldM (apply local) typ arguments
            _ -> case value of
                LVar variable -> lift (current <$> lookupLVarType variable labeling)
                NCon constructor _ -> lift (current <$> lookupConType constructor labeling)
                NIdx index -> lift (if index >= 0 && index < length local then Just (local !! index) else Nothing)
                NLam _ (LamType (Just domain)) body _ -> do
                    void (lift (typeTerm domain >>= primitiveTypeArgumentWithKinds kinds))
                    mkTyArrow domain <$> go (domain : local) body
                Susp {} -> go local (rewrite NF value)
                NPresburgerCheck {} -> return mkTyO
                _ -> lift Nothing
        instantiate types typ = case typ of
            TyVar index -> if index >= 0 && index < length types then Just (types !! index) else Nothing
            TyApp function argument -> TyApp <$> instantiate types function <*> instantiate types argument
            _ -> Just typ
        apply local function argument = do
            actual <- go local argument
            solved <- get
            case closeRuntimeType solved function of
                TyApp (TyApp (TyCon (TCon TC_Arrow _)) domain) result -> do
                    next <- lift (unifyRuntimeTypes solved domain actual)
                    put next
                    return (closeRuntimeType next result)
                _ -> lift Nothing

-- The values that the type variables of a run get when `value` is given to a
-- variable that has every type of `expected`, in a state whose binding is
-- `binding`; Nothing when the value cannot have those types. The expected
-- types are as `specializeType` leaves them. A term of a host from which no
-- type can be read is admitted when no type is expected. The checked entry
-- points first use prepareHostValue to give external annotations fresh
-- identities. runtimeValueType preserves the current identities of nominal
-- constants, and keeps partial type structure and application equations.
valueTypeBinding :: KindEnv -> VarBinding -> Labeling -> [MonoType Int] -> TermNode -> Maybe (IntMap.IntMap (MonoType Int))
valueTypeBinding = valueTypeBindingWithFresh Set.empty

valueTypeBindingWithFresh :: Set.Set LogicVar -> KindEnv -> VarBinding -> Labeling -> [MonoType Int] -> TermNode -> Maybe (IntMap.IntMap (MonoType Int))
valueTypeBindingWithFresh fresh kindEnv binding labeling expected value
    | not (Set.null (getLVars value `Set.difference` fresh)) = Nothing
    | otherwise = case primitiveTypeEvidenceWithFresh fresh kindEnv value of
        Just PrimitiveInvalidValue -> Nothing
        Just (PrimitiveExactType actual) -> agree IntMap.empty actual
        Just PrimitiveEmptyList -> if all typeCouldBeList expected then Just IntMap.empty else Nothing
        Nothing
            | null expected -> Just IntMap.empty
            | otherwise -> runtimeValueType kindEnv binding labeling value >>= \(actual, solved) -> agree solved actual
    where
        agree initial actual = foldM (\solved typ -> unifyRuntimeTypes solved typ actual) initial expected

-- Compatibility helper for callers describing a type with non-run IDs.
-- Checked values use prepareHostValue instead: a partial type needs real
-- fresh variables in the run, while an existing nominal keeps its identity.
foreignTypes :: MonoType Int -> MonoType Int
foreignTypes typ = case typ of
    TyApp function argument -> TyApp (foreignTypes function) (foreignTypes argument)
    _ -> maybe typ (TyMTV . foreignTypeVariable) (runtimeTypeVariable typ)

-- An identity that no type variable of a run has, made of one that a run may
-- have. A type variable with it decides nothing and is decided by nothing.
-- Untyped legacy metadata and foreign annotations use it when they have no
-- link to a live instance. Typed native nodes carry that link separately.
foreignTypeVariable :: Unique -> Unique
foreignTypeVariable unique
    | unUnique unique < 0 = unique
    | otherwise = Unique (negate (unUnique unique) - 1)

-- Whether a type has a type variable of no run: it is then no evidence
-- where that variable stands.
guessedType :: MonoType Int -> Bool
guessedType typ = case typ of
    TyApp function argument -> guessedType function || guessedType argument
    _ -> maybe False ((< 0) . unUnique) (runtimeTypeVariable typ)

-- The identity of a type variable in the type of a variable or of a
-- constant. For a type variable of the run it is the identity of that logic
-- variable (LV_ty_var): TC_Unique in the types that the interpreter records
-- and in the annotations of a query, TyMTV in the types that the checker
-- gives the variables of a query. A negative one is of no run.
runtimeTypeVariable :: MonoType Int -> Maybe Unique
runtimeTypeVariable typ = case typ of
    TyMTV unique -> Just unique
    TyCon (TCon (TC_Unique unique) _) -> Just unique
    _ -> Nothing

-- A type as a state has it by now: a type variable that the binding of the
-- state has a value for is replaced by that value. A type variable that is
-- left has no value yet.
specializeType :: KindEnv -> VarBinding -> MonoType Int -> MonoType Int
specializeType kindEnv binding = go IntSet.empty where
    go seen typ = case typ of
        TyApp function argument -> TyApp (go seen function) (go seen argument)
        _ -> case runtimeTypeVariable typ of
            Just unique
                | unUnique unique `IntSet.notMember` seen
                , Just value <- Map.lookup (LV_ty_var unique) (unVarBinding binding)
                , Just known <- primitiveTypeArgumentWithKinds kindEnv (bindVars binding value) -> go (IntSet.insert (unUnique unique) seen) known
            _ -> typ

-- The type of a variable in a state: the type that the run recorded for it,
-- or the type of the query for it (`queryTypes`), as the state has that type
-- by now.
stateVariableType :: KindEnv -> Map.Map LogicVar (MonoType Int) -> Context -> LogicVar -> Maybe (MonoType Int)
stateVariableType kindEnv queryTypes ctx variable = specializeType kindEnv (_TotalVarBinding ctx) <$> (lookupLVarType variable (_CurrentLabeling ctx) `mplus` Map.lookup variable queryTypes)

variableType :: RuntimeEnv -> Context -> LogicVar -> Maybe (MonoType Int)
variableType env = stateVariableType (_ProgramKindEnv env) (_TypeInfo env)

-- Recover types only at host boundaries, not on every search step.
refineContext :: RuntimeEnv -> Context -> Context
refineContext env ctx = ctx { _CurrentLabeling = refineBindingTypes env (_TotalVarBinding ctx) (_CurrentLabeling ctx) }

-- Unification-generated variables have no source annotation. Recover their
-- types from the typed variables whose values contain them, without copying
-- display hints or guessing a type for a missing application argument. The
-- type of a typed variable is as the state has it by now. A type that is
-- found this way replaces a recorded one that has a guessed instance
-- (instantiateMetadataType): the place of a variable in a value is evidence.
refineBindingTypes :: RuntimeEnv -> VarBinding -> Labeling -> Labeling
refineBindingTypes env (VarBinding binding) = improve . labelingWithRuntimeTypes env where
    improve labeling
        | _VarTypes next == _VarTypes labeling = next
        | otherwise = improve next
        where
            inferred = concat
                [ collect labeling [] (specializeType (_ProgramKindEnv env) (VarBinding binding) typ) value
                | (variable, value) <- Map.toList binding
                , Just typ <- [lookupLVarType variable labeling]
                ]
            next = labeling { _VarTypes = foldl insert (_VarTypes labeling) inferred }
            insert types (LV_Named _, _) = types
            insert types (variable, typ) = IntMap.insertWith (\found old -> if guessedType old && not (guessedType found) then found else old) (lvKey variable) typ types
    collect labeling bound expected value = case value of
        LVar variable -> [(variable, expected)]
        NLam _ _ body _ -> case splitArrowsHOPU 1 expected of
            Just ([domain], result) -> collect labeling (domain : bound) result body
            _ -> []
        _ -> case unfoldlNApp value of
            (LVar variable, arguments) -> case mapM (typeOfTerm labeling bound) arguments of
                Just domains -> [(variable, foldr mkTyArrow expected domains)]
                Nothing -> []
            (NCon (DC constructor) _, arguments) -> case Map.lookup constructor (_ProgramTypeEnv env) of
                Just (Forall parameters body) ->
                    let (typeArguments, values) = splitAt (length parameters) arguments
                    in case mapM (primitiveTypeArgumentWithKinds (_ProgramKindEnv env)) typeArguments of
                        Just replacements
                            | length replacements == length parameters -> case substitute replacements body >>= splitArrowsHOPU (length values) of
                                Just (domains, _) -> concat (zipWith (collect labeling bound) domains values)
                                Nothing -> []
                        _ -> []
                Nothing -> []
            _ -> []
    substitute replacements typ = case typ of
        TyVar index
            | index >= 0 && index < length replacements -> Just (replacements !! index)
            | otherwise -> Nothing
        TyApp left right -> TyApp <$> substitute replacements left <*> substitute replacements right
        _ -> Just typ


-- Two types as one type: the values of the type variables of a run that make
-- them equal, added to `solved`. An index of a declared type scheme matches
-- any type, as it did before type variables were solved here.
unifyRuntimeTypes :: IntMap.IntMap (MonoType Int) -> MonoType Int -> MonoType Int -> Maybe (IntMap.IntMap (MonoType Int))
unifyRuntimeTypes solved lhs rhs = case (walk lhs, walk rhs) of
    (TyVar _, _) -> Just solved
    (_, TyVar _) -> Just solved
    (left, right)
        | Just unique <- runtimeTypeVariable left -> bind (unUnique unique) right
        | Just unique <- runtimeTypeVariable right -> bind (unUnique unique) left
    (TyCon left, TyCon right) -> if left == right then Just solved else Nothing
    (TyApp function1 argument1, TyApp function2 argument2) -> unifyRuntimeTypes solved function1 function2 >>= \next -> unifyRuntimeTypes next argument1 argument2
    _ -> Nothing
    where
        walk typ = case runtimeTypeVariable typ >>= \unique -> IntMap.lookup (unUnique unique) solved of
            Just known -> walk known
            Nothing -> typ
        bind key typ
            | fmap unUnique (runtimeTypeVariable typ) == Just key = Just solved
            | occurs key typ = Nothing
            | otherwise = Just (IntMap.insert key typ solved)
        occurs key typ = case walk typ of
            TyApp function argument -> occurs key function || occurs key argument
            other -> fmap unUnique (runtimeTypeVariable other) == Just key

closeRuntimeType :: IntMap.IntMap (MonoType Int) -> MonoType Int -> MonoType Int
closeRuntimeType solved typ = case typ of
    TyApp function argument -> TyApp (closeRuntimeType solved function) (closeRuntimeType solved argument)
    _ -> case runtimeTypeVariable typ >>= \unique -> IntMap.lookup (unUnique unique) solved of
        Just found -> closeRuntimeType solved found
        Nothing -> typ

labelingTypeVariables :: Labeling -> Set.Set LogicVar
labelingTypeVariables labeling = Set.unions (map variables (IntMap.elems (_ConTypes labeling) ++ IntMap.elems (_VarTypes labeling) ++ Map.elems (_NamedTypes labeling))) where
    variables typ = case typ of
        TyApp function argument -> variables function `Set.union` variables argument
        _ -> maybe Set.empty (\unique -> if unUnique unique >= 0 then Set.singleton (LV_ty_var unique) else Set.empty) (runtimeTypeVariable typ)

-- The term of a type, for the binding of a type variable; Nothing for a type
-- that has an index of a type scheme.
typeTerm :: MonoType Int -> Maybe TermNode
typeTerm typ = case typ of
    TyVar _ -> Nothing
    TyMTV unique -> Just (mkLVar (LV_ty_var unique))
    TyCon (TCon (TC_Unique unique) _) -> Just (mkLVar (LV_ty_var unique))
    TyCon (TCon constructor _) -> Just (mkNCon constructor)
    TyApp function argument -> mkNApp <$> typeTerm function <*> typeTerm argument

-- What giving `value` to the variable `target` binds in a state: the
-- variable, and the type variables among `known` that the type of the value
-- decides. `types` are terms of types that the variable has besides its
-- recorded type. Nothing when the value cannot have the types of the
-- variable. A type variable that is not of the run, such as one of the text
-- of an assigned term, is not bound.
typedBinding :: RuntimeEnv -> Context -> Set.Set LogicVar -> [TermNode] -> LogicVar -> TermNode -> Maybe VarBinding
typedBinding = typedBindingWithFresh Set.empty

typedBindingWithFresh :: Set.Set LogicVar -> RuntimeEnv -> Context -> Set.Set LogicVar -> [TermNode] -> LogicVar -> TermNode -> Maybe VarBinding
typedBindingWithFresh fresh env ctx known types target value
    | assignmentTypeVariable (_CurrentLabeling ctx) target = do
        _ <- primitiveTypeArgumentWithKinds (_ProgramKindEnv env) value
        return (VarBinding (Map.singleton target value))
    | otherwise = typedValueBindingWithFresh fresh env ctx known types target value

typedValueBindingWithFresh :: Set.Set LogicVar -> RuntimeEnv -> Context -> Set.Set LogicVar -> [TermNode] -> LogicVar -> TermNode -> Maybe VarBinding
typedValueBindingWithFresh fresh env ctx known types target value = do
    instances <- mapM (primitiveTypeArgumentWithKinds kindEnv . bindVars binding) types
    solved <- valueTypeBindingWithFresh fresh kindEnv binding (_CurrentLabeling ctx) (map (specializeType kindEnv binding) (instances ++ maybeToList (variableType env ctx target))) value
    let live = known `Set.union` labelingTypeVariables (_CurrentLabeling ctx)
    return (VarBinding (Map.fromList ((target, closeValue solved value) : [(variable, term) | (key, typ) <- IntMap.toList solved, let variable = LV_ty_var (Unique key), variable `Set.member` live, variable `Set.notMember` fresh, let closed = closeRuntimeType solved typ, ofTheRun closed, Just term <- [typeTerm closed]])))
    where
        kindEnv = _ProgramKindEnv env
        binding = _TotalVarBinding ctx
        closeValue solved value = case value of
            LVar variable@(LV_ty_var unique)
                | variable `Set.member` fresh -> fromMaybe value (typeTerm (closeRuntimeType solved (TyMTV unique)))
            NApp function argument location -> NApp (closeValue solved function) (closeValue solved argument) location
            NLam hint (LamType annotation) body location -> NLam hint (LamType (closeRuntimeType solved <$> annotation)) (closeValue solved body) location
            Susp {} -> closeValue solved (rewrite NF value)
            NPresburgerCheck formula free location -> NPresburgerCheck formula (Map.map (closeValue solved) free) location
            _ -> value
        ofTheRun typ = case typ of
            TyApp function argument -> ofTheRun function && ofTheRun argument
            _ -> maybe True ((>= 0) . unUnique) (runtimeTypeVariable typ)

-- What a goal `read` with the arguments `args` binds when the host gives
-- `value` for its variable `target`; Nothing when the variable cannot have
-- the value. The type instance of the goal is a type of the variable.
readBinding :: RuntimeEnv -> Context -> [TermNode] -> LogicVar -> TermNode -> Maybe VarBinding
readBinding = readBindingWithKnown Set.empty

readBindingWithKnown :: Set.Set LogicVar -> RuntimeEnv -> Context -> [TermNode] -> LogicVar -> TermNode -> Maybe VarBinding
readBindingWithKnown fresh env ctx args target value
    | target `Set.member` getLVars value = Nothing
    | not (null badConstants && all (`Set.member` fresh) badVariables) = Nothing
    | otherwise = typedBindingWithFresh fresh env ctx (Set.unions (map (getLVars . bindVars (_TotalVarBinding ctx)) types)) types target value
    where
        types = take (length args - 1) args
        (badConstants, badVariables) = scopeEscaping (_CurrentLabeling ctx) (lookupLabel target (_CurrentLabeling ctx)) target value

readHostBinding :: RuntimeEnv -> Context -> [TermNode] -> LogicVar -> TermNode -> IO (Either ErrMsg (Maybe VarBinding))
readHostBinding env ctx args target value
    | not (Set.null (hostTypeArguments value)) = return (Right Nothing)
    | otherwise = fmap (\(prepared, fresh) -> readBindingWithKnown fresh env (refineContext env ctx) args target prepared) <$> prepareHostValue env value

-- Open type arguments supplied by a caller remain outside the accepted
-- value domain. Only the empty-list witness made above is admitted here.
hostTypeArguments :: TermNode -> Set.Set LogicVar
hostTypeArguments = Set.filter isType . getLVars where
    isType (LV_ty_var _) = True
    isType _ = False

monoTypesCouldMatch :: MonoType Int -> MonoType Int -> Bool
monoTypesCouldMatch expected actual = isJust (unifyRuntimeTypes IntMap.empty expected actual)

typeCouldBeList :: MonoType Int -> Bool
typeCouldBeList (TyVar _) = True
typeCouldBeList (TyMTV _) = True
typeCouldBeList (TyCon (TCon (TC_Unique _) _)) = True
typeCouldBeList (TyApp (TyCon (TCon (TC_Named "list") _)) _) = True
typeCouldBeList _ = False

primitiveTypeEvidence :: TermNode -> Maybe PrimitiveTypeEvidence
primitiveTypeEvidence = primitiveTypeEvidenceWithKinds primitiveBuiltinKindEnv

primitiveTypeEvidenceWithKinds :: KindEnv -> TermNode -> Maybe PrimitiveTypeEvidence
primitiveTypeEvidenceWithKinds = primitiveTypeEvidenceWithFresh Set.empty

primitiveTypeEvidenceWithFresh :: Set.Set LogicVar -> KindEnv -> TermNode -> Maybe PrimitiveTypeEvidence
primitiveTypeEvidenceWithFresh fresh kindEnv value
    | not (Set.null (getLVars value `Set.difference` fresh)) = Just PrimitiveInvalidValue
    | otherwise = case rewrite NF value of
        NCon (DC (DC_NatL _)) _ -> Just (PrimitiveExactType mkTyNat)
        NCon (DC (DC_ChrL _)) _ -> Just (PrimitiveExactType mkTyChr)
        value' -> case primitiveListEvidenceWithKinds kindEnv value' of
            Just evidence -> Just evidence
            Nothing
                | looksLikePrimitiveList value' -> Just PrimitiveInvalidValue
                | otherwise -> Nothing

-- Preserve and validate elaborated list type arguments.  Dropping them would
-- let a forged `(::) nat 'a' ([] nat)' masquerade as `list char' at the
-- primitive/debugger API boundary.
primitiveListEvidence :: TermNode -> Maybe PrimitiveTypeEvidence
primitiveListEvidence = primitiveListEvidenceWithKinds primitiveBuiltinKindEnv

primitiveListEvidenceWithKinds :: KindEnv -> TermNode -> Maybe PrimitiveTypeEvidence
primitiveListEvidenceWithKinds kindEnv value = case primitiveListView (rewrite NF value) of
    Just (PrimitiveNilView Nothing) -> Just PrimitiveEmptyList
    Just (PrimitiveNilView (Just typeArg)) ->
        Just $ maybe PrimitiveInvalidValue
            (PrimitiveExactType . mkTyList) (primitiveTypeArgumentWithKinds kindEnv typeArg)
    Just (PrimitiveConsView maybeTypeArg item rest) -> Just $
        case (primitiveExactTypeWithKinds kindEnv item, primitiveListEvidenceWithKinds kindEnv rest) of
            (Just itemType, Just restEvidence)
                | explicitTypeMatches maybeTypeArg itemType
                , restMatches itemType restEvidence ->
                    PrimitiveExactType (mkTyList itemType)
            _ -> PrimitiveInvalidValue
    Nothing -> Nothing
    where
        explicitTypeMatches Nothing _ = True
        explicitTypeMatches (Just typeArg) itemType =
            maybe False (`monoTypesCouldMatch` itemType) (primitiveTypeArgumentWithKinds kindEnv typeArg)

        restMatches _ PrimitiveEmptyList = True
        restMatches itemType (PrimitiveExactType (TyApp (TyCon (TCon (TC_Named "list") _)) tailType)) =
            monoTypesCouldMatch itemType tailType
        restMatches _ _ = False

primitiveTypeArgument :: TermNode -> Maybe (MonoType Int)
primitiveTypeArgument = primitiveTypeArgumentWithKinds primitiveBuiltinKindEnv

-- Recover a type argument together with its real constructor kinds.  Merely
-- building a 'TyApp' tree is insufficient: for example, @nat nat@ is not in
-- the type domain even though both leaves individually denote types.
primitiveTypeArgumentWithKinds :: KindEnv -> TermNode -> Maybe (MonoType Int)
primitiveTypeArgumentWithKinds kindEnv term = do
    (typ, kind) <- go (rewrite NF term)
    guard (kind == Star)
    return typ
    where
        go :: TermNode -> Maybe (MonoType Int, KindExpr)
        go (LVar (LV_ty_var mtv)) = Just (TyMTV mtv, Star)
        go (NCon (TC typeConstructor) _) = do
            kind <- typeConstructorKind typeConstructor
            return (TyCon (TCon typeConstructor kind), kind)
        go (NApp lhs rhs _) = do
            (lhsType, lhsKind) <- go lhs
            (rhsType, rhsKind) <- go rhs
            case lhsKind of
                KArr argumentKind resultKind
                    | argumentKind == rhsKind ->
                        Just (TyApp lhsType rhsType, resultKind)
                _ -> Nothing
        go _ = Nothing

        typeConstructorKind (TC_Unique _) = Just Star
        typeConstructorKind typeConstructor =
            Map.lookup typeConstructor kindEnv
                `mplus` Map.lookup typeConstructor primitiveBuiltinKindEnv

primitiveBuiltinKindEnv :: KindEnv
primitiveBuiltinKindEnv = Map.fromList
    [ (TC_Arrow, KArr Star (KArr Star Star))
    , (TC_Named "list", KArr Star Star)
    , (TC_Named "o", Star)
    , (TC_Named "char", Star)
    , (TC_Named "nat", Star)
    , (TC_Named "string", Star)
    ]

primitiveExactType :: TermNode -> Maybe (MonoType Int)
primitiveExactType = primitiveExactTypeWithKinds primitiveBuiltinKindEnv

primitiveExactTypeWithKinds :: KindEnv -> TermNode -> Maybe (MonoType Int)
primitiveExactTypeWithKinds kindEnv value
    = case primitiveTypeEvidenceWithKinds kindEnv value of
        Just (PrimitiveExactType ty) -> Just ty
        _ -> Nothing

data PrimitiveListView
    = PrimitiveNilView (Maybe TermNode)
    | PrimitiveConsView (Maybe TermNode) TermNode TermNode

-- Runtime values occur both with explicit type arguments (after elaboration)
-- and without them (the default REPL callback constructs the latter).
primitiveListView :: TermNode -> Maybe PrimitiveListView
primitiveListView value
    = assertNonnegativeIndices value `seq` case unfoldPrimitiveApps value of
        (NCon (DC DC_Nil) _, []) -> Just (PrimitiveNilView Nothing)
        (NCon (DC DC_Nil) _, [typeArg]) -> Just (PrimitiveNilView (Just typeArg))
        (NCon (DC DC_Cons) _, [item, rest]) -> Just (PrimitiveConsView Nothing item rest)
        (NCon (DC DC_Cons) _, [typeArg, item, rest]) -> Just (PrimitiveConsView (Just typeArg) item rest)
        _ -> Nothing
    where
        unfoldPrimitiveApps = flip go []
        go (NApp fun arg _) args = go fun (arg : args)
        go term args = (term, args)

looksLikePrimitiveList :: TermNode -> Bool
looksLikePrimitiveList value = assertNonnegativeIndices value `seq` case fst (unfold value []) of
    NCon (DC DC_Nil) _ -> True
    NCon (DC DC_Cons) _ -> True
    _ -> False
    where
        unfold (NApp fun arg _) args = unfold fun (arg : args)
        unfold term args = (term, args)

-- Keep the debugger's display-name map tied to the generated variables that
-- are actually visible in the current proof state.  A source hint is used
-- when available; collisions retain the established owner and give the newer
-- variable a deterministic V_<unique> fallback.
recordVisibleLVarHints :: Stack -> NameCache -> NameCache
recordVisibleLVarHints stack0 cache0 = List.foldl' hintedFrame cache0 stack0 where
    register cache lv@(LV_Unique uni (DispHint (Just preferred)))
        | isJust (toDisplay lv cache) = cache
        | otherwise = recordRename lv (availableName preferred uni cache) cache
    register cache _ = cache

    availableName preferred uni cache
        | available preferred = preferred
        | otherwise = firstAvailable 0
        where
            available candidate = case fromDisplay candidate cache of
                Nothing -> True
                Just owner -> owner == LV_Unique uni noHint
            stem = "V_" ++ show (unUnique uni)
            firstAvailable n
                | available candidate = candidate
                | otherwise = firstAvailable (n + 1)
                where
                    candidate = if n == (0 :: Int) then stem else stem ++ "_" ++ show n

    hintedFrame cache (ctx, cells) = List.foldl' hintedCell (hintedContext cache ctx) cells
    hintedContext cache ctx =
        List.foldl' hintedConstraint
            (List.foldl' hintedTerm (List.foldl' register cache (Map.keys binding)) (Map.elems binding))
            (_LeftConstraints ctx)
        where
            binding = unVarBinding (_TotalVarBinding ctx)
    hintedCell cache cell = hintedTerm
        (List.foldl' hintedTerm (List.foldl' hintedTerm cache (_GivenHypos cell)) (arithStoreTerms (_GivenArithPremises cell)))
        (_WantedGoal cell)

    hintedConstraint cache (DisagreementConstraint (lhs :=?=: rhs)) = hintedTerm (hintedTerm cache lhs) rhs
    hintedConstraint cache (EvalutionConstraint lhs rhs) = hintedTerm (hintedTerm cache lhs) rhs
    hintedConstraint cache (ArithmeticConstraint premises term) = hintedTerm (List.foldl' hintedTerm cache (arithStoreTerms premises)) term
    hintedConstraint cache (PresburgerConstraint premises _ freeOf) = List.foldl' hintedTerm (List.foldl' hintedTerm cache (arithStoreTerms premises)) (Map.elems freeOf)

    -- Force each prefix before visiting the next child. The occurrence order
    -- decides collision ownership, but no occurrence list needs to survive.
    hintedTerm cache term = cache `seq` case term of
        LVar variable -> register cache variable
        NCon _ _ -> cache
        NIdx i
            | i >= 0 -> cache
            | otherwise -> undefined
        NApp t1 t2 _ -> hintedTerm (hintedTerm cache t1) t2
        NLam _ _ body _ -> hintedTerm cache body
        Susp body _ _ suspEnv -> List.foldl' hintedSuspItem (hintedTerm cache body) suspEnv
        NPresburgerCheck _ freeOf _ -> List.foldl' hintedTerm cache (Map.elems freeOf)
    hintedSuspItem cache (Dummy _) = cache
    hintedSuspItem cache (Binds term _) = hintedTerm cache term

-- Machine-readable rejections are decided at the failing check. The terminal
-- wrappers retain their existing text, without making that text an API tag.
data AssignmentReason
    = AssignmentUnavailable
    | AssignmentUnknownVariable
    | AssignmentAlreadyBound
    | AssignmentOccursCheck
    | AssignmentScopeEscape
    | AssignmentTypeMismatch
    | AssignmentKindMismatch
    | AssignmentConstraintConflict
    | AssignmentPreparationFailed
    deriving (Eq, Ord, Show)

data AssignmentFailure
    = AssignmentFailure
        { assignmentReason  :: AssignmentReason
        , assignmentMessage :: ErrMsg
        }
    deriving (Eq, Show)

assignmentTypeVariable :: Labeling -> LogicVar -> Bool
assignmentTypeVariable labeling variable = case variable of
    LV_ty_var _ -> True
    LV_Unique unique _ -> IntMap.member (unUnique unique) (_TyVarKeys labeling)
    LV_Named _ -> False

cmdAssign :: SmallId -> TermNode -> Runtime (Either ErrMsg ())
cmdAssign name term
    = assertNonnegativeIndices term `seq` do
        env <- askRuntimeEnv
        targetLV <- liftIO $ do
            cache <- readIORef (_NameCacheRef env)
            return $ case fromDisplay name cache of
                Just lv -> lv
                Nothing -> fromMaybe (LV_Named name) (parseAnonymousLV name)
        cmdAssignTargetWithAnchor False name targetLV term

-- | Assign a target that the caller has already resolved in the current
-- debugger state.  In particular, do not reinterpret a generated variable's
-- display hint as an unrelated 'LV_Named'.
cmdAssignVar :: LogicVar -> TermNode -> Runtime (Either ErrMsg ())
cmdAssignVar variable term = assertNonnegativeIndices term `seq` fmap (either (Left . assignmentMessage) Right) (cmdAssignVarChecked variable term)

cmdAssignVarChecked :: LogicVar -> TermNode -> Runtime (Either AssignmentFailure ())
cmdAssignVarChecked targetLV term = assertNonnegativeIndices term `seq` do
    env <- askRuntimeEnv
    cache <- liftIO (readIORef (_NameCacheRef env))
    cmdAssignTargetChecked True (fromMaybe (assignmentTargetName targetLV) (toDisplay targetLV cache)) targetLV term

-- The legacy terminal names a displayed witness. Its edit belongs to that
-- witness's branch; the embedding API instead anchors the requested identity.
cmdAssignTerminalVar :: LogicVar -> TermNode -> Runtime (Either ErrMsg ())
cmdAssignTerminalVar = cmdAssignVarWithAnchor False

cmdAssignVarWithAnchor :: Bool -> LogicVar -> TermNode -> Runtime (Either ErrMsg ())
cmdAssignVarWithAnchor anchor targetLV term = assertNonnegativeIndices term `seq` do
    env <- askRuntimeEnv
    cache <- liftIO (readIORef (_NameCacheRef env))
    cmdAssignTargetWithAnchor anchor (fromMaybe (assignmentTargetName targetLV) (toDisplay targetLV cache)) targetLV term

assignmentTargetName :: LogicVar -> SmallId
assignmentTargetName (LV_Named name) = name
assignmentTargetName (LV_Unique uni (DispHint mhint)) = fromMaybe ("V_" ++ show (unUnique uni)) mhint
assignmentTargetName (LV_ty_var uni) = "TV_" ++ show (unUnique uni)

-- Do not let callers of the public debugger API manufacture a fresh pending
-- binding merely by naming an arbitrary LogicVar.  Generated variables are
-- registered in the current labeling; named variables normally have type
-- information, but the frame scan also covers deliberately untyped embedders.
assignmentTargetIsKnown :: RuntimeEnv -> Context -> [Cell] -> LogicVarSubst -> LogicVar -> Bool
assignmentTargetIsKnown env ctx cells pending target
    = namedQueryVariable env ctx target || stateHasVariable target ctx cells pending

-- A type-map key alone does not establish active membership or the variable
-- constructor. Generated identities must occur in the current state; named
-- query variables may also be known solely from their type environment while
-- still unbound. Display hints do not distinguish identities: DispHint Eq/Ord
-- deliberately ignore them.
namedQueryVariable :: RuntimeEnv -> Context -> LogicVar -> Bool
namedQueryVariable env ctx target = case target of
    LV_Named _ -> isJust (lookupLVarType target (_CurrentLabeling ctx)) || Map.member target (_TypeInfo env)
    _ -> False

-- Membership needs only the first occurrence. In a proof state the newest
-- hypothesis usually contains the command variable; constructing the set of
-- every frame's variables would repeatedly expand shared hypotheses. Keep
-- LogicVar's identity equality and the same roots as stateVariables.
stateHasVariable :: LogicVar -> Context -> [Cell] -> LogicVarSubst -> Bool
stateHasVariable target ctx cells pending
    = binding (_TotalVarBinding ctx) || binding pending || any constraint (_LeftConstraints ctx) || any cell cells
    where
        binding (VarBinding values) = Map.member target values || any term (Map.elems values)
        constraint (DisagreementConstraint (lhs :=?=: rhs)) = term lhs || term rhs
        constraint (EvalutionConstraint lhs rhs) = term lhs || term rhs
        constraint (ArithmeticConstraint premises value) = any term (value : arithStoreTerms premises)
        constraint (PresburgerConstraint premises _ freeOf) = any term (arithStoreTerms premises ++ Map.elems freeOf)
        cell value = any term (_WantedGoal value : _GivenHypos value ++ arithStoreTerms (_GivenArithPremises value))
        term value = assertNonnegativeIndices value `seq` walk value
        walk (LVar variable) = target == variable
        walk (NApp function argument _) = walk function || walk argument
        walk (NLam _ _ body _) = walk body
        walk (Susp body _ _ environment) = walk body || any item environment
        walk (NPresburgerCheck _ freeOf _) = any walk (Map.elems freeOf)
        walk _ = False
        item (Dummy _) = False
        item (Binds value _) = walk value

-- The variables that a frame has: those of its binding and of the pending
-- assignments, of its constraints and of its goals.
stateVariables :: Context -> [Cell] -> LogicVarSubst -> Set.Set LogicVar
stateVariables ctx cells pending
    = bindingVars (_TotalVarBinding ctx) `Set.union` bindingVars pending `Set.union` Set.unions (map constraintVars (_LeftConstraints ctx) ++ map cellVars cells)
    where
        bindingVars (VarBinding binding) = Map.keysSet binding `Set.union` Set.unions (map getLVars (Map.elems binding))
        constraintVars (DisagreementConstraint (lhs :=?=: rhs)) = getLVars lhs `Set.union` getLVars rhs
        constraintVars (EvalutionConstraint lhs rhs) = getLVars lhs `Set.union` getLVars rhs
        constraintVars (ArithmeticConstraint premises term) = Set.unions (getLVars term : map getLVars (arithStoreTerms premises))
        constraintVars (PresburgerConstraint premises _ freeOf) = Set.unions (map getLVars (arithStoreTerms premises ++ Map.elems freeOf))
        cellVars cell = Set.unions (getLVars (_WantedGoal cell) : map getLVars (_GivenHypos cell ++ arithStoreTerms (_GivenArithPremises cell)))

-- Query declarations supply missing evidence. A current exact type may
-- already include a runtime instantiation absent from a reduced binding view.
labelingWithRuntimeTypes :: RuntimeEnv -> Labeling -> Labeling
labelingWithRuntimeTypes env labeling0
    = Map.foldlWithKey' insertType labeling0 (_TypeInfo env)
    where
        insertType labeling variable typ = case variable of
            LV_Named name -> labeling
                { _NamedTypes = Map.insertWith keepCurrent name typ (_NamedTypes labeling) }
            LV_Unique unique _ -> labeling
                { _VarTypes = IntMap.insertWith keepCurrent (unUnique unique) typ (_VarTypes labeling) }
            LV_ty_var unique -> labeling
                { _VarTypes = IntMap.insertWith keepCurrent (unUnique unique) typ (_VarTypes labeling) }
        keepCurrent supplied recorded
            | guessedType recorded = supplied
            | otherwise = recorded

initialQueryLabeling :: RuntimeEnv -> TermNode -> Labeling -> Labeling
initialQueryLabeling env query labeling = Set.foldl' enroll typed variables where
    enroll known variable = case variable of
        LV_ty_var unique -> (enrollLabel variable 0 known) { _TyVarKeys = IntMap.insert (unUnique unique) () (_TyVarKeys known) }
        _ -> enrollLabel variable 0 known
    typed = (labelingWithRuntimeTypes env labeling) { _QueryOrder = Map.fromList (zip ordered [0 ..]) }
    direct = collect Set.empty query
    variables = direct `Set.union` Set.unions [typeVariables Set.empty typ | (variable, typ) <- Map.toList (_TypeInfo env), variable `Set.member` direct]
    ordered = Set.toAscList direct ++ Set.toAscList (variables `Set.difference` direct)
    collect bound term = case term of
        LVar variable -> Set.singleton variable
        NApp (NCon (DC (DC_LO LO_ty_pi)) _) (NLam _ (LamType (Just (TyMTV variable))) body _) _ -> collect (Set.insert variable bound) body
        NApp function argument _ -> collect bound function `Set.union` collect bound argument
        NLam _ marker body _ -> maybe Set.empty (typeVariables bound) (unLamType marker) `Set.union` collect bound body
        NPresburgerCheck _ free _ -> Set.unions (map (collect bound) (Map.elems free))
        suspended@Susp {} -> collect bound (rewrite NF suspended)
        _ -> Set.empty
    typeVariables bound typ = case typ of
        TyApp function argument -> typeVariables bound function `Set.union` typeVariables bound argument
        _ -> case runtimeTypeVariable typ of
            Just unique
                | unique `Set.notMember` bound -> Set.singleton (LV_ty_var unique)
            _ -> Set.empty

-- Why the variable `target` cannot have `value` in a state whose binding is
-- `binding`; Nothing when it can. The type of the variable is as that binding
-- has it by now.
assignmentTypeError :: RuntimeEnv -> VarBinding -> Labeling -> LogicVar -> TermNode -> Maybe ErrMsg
assignmentTypeError = assignmentTypeErrorWithFresh Set.empty

assignmentTypeErrorWithFresh :: Set.Set LogicVar -> RuntimeEnv -> VarBinding -> Labeling -> LogicVar -> TermNode -> Maybe ErrMsg
assignmentTypeErrorWithFresh fresh env binding originalLabeling target value
    | assignmentTypeVariable labeling target = if isJust (primitiveTypeArgumentWithKinds (_ProgramKindEnv env) value) then Nothing else Just "kind mismatch for debugger assignment: expected a type of kind *."
    | otherwise = case specializeType (_ProgramKindEnv env) binding <$> lookupLVarType target labeling of
        Nothing -> case primitiveTypeEvidenceWithFresh fresh (_ProgramKindEnv env) value of
            Just PrimitiveInvalidValue -> Just "type mismatch for debugger assignment: the assigned term is not well-typed in the active context."
            _ -> Nothing
        Just expected -> case primitiveTypeEvidenceWithFresh fresh (_ProgramKindEnv env) value of
            Just (PrimitiveExactType actual)
                | monoTypesCouldMatch expected actual -> Nothing
                | otherwise -> Just (mismatch expected (Just actual))
            Just PrimitiveEmptyList
                | typeCouldBeList expected -> Nothing
                | otherwise -> Just (mismatch expected Nothing)
            Just PrimitiveInvalidValue -> Just (mismatch expected Nothing)
            Nothing -> case runtimeValueType (_ProgramKindEnv env) binding labeling value of
                Just (actual, solved)
                    | isJust (unifyRuntimeTypes solved expected actual) -> Nothing
                    | otherwise -> Just (mismatch expected (Just (closeRuntimeType solved actual)))
                Nothing -> Just (mismatch expected Nothing)
    where
        labeling = labelingWithRuntimeTypes env originalLabeling
        renderType = showsMonoType (_NotationDB env) 0
        mismatch expected actual =
            "type mismatch for debugger assignment: expected `"
                ++ renderType expected "' but "
                ++ case actual of
                    Just typ -> "the assigned term has type `" ++ renderType typ "'."
                    Nothing -> "the assigned term is not well-typed in the active context."

cmdAssignTarget :: SmallId -> LogicVar -> TermNode -> Runtime (Either ErrMsg ())
cmdAssignTarget = cmdAssignTargetWithAnchor True

cmdAssignTargetWithAnchor :: Bool -> SmallId -> LogicVar -> TermNode -> Runtime (Either ErrMsg ())
cmdAssignTargetWithAnchor anchor name target term = assertNonnegativeIndices term `seq` fmap (either (Left . assignmentMessage) Right) (cmdAssignTargetChecked anchor name target term)

cmdAssignTargetChecked :: Bool -> SmallId -> LogicVar -> TermNode -> Runtime (Either AssignmentFailure ())
cmdAssignTargetChecked anchor name target term = assertNonnegativeIndices term `seq` do
    env <- askRuntimeEnv
    allowed <- liftIO (runtimeCanAssign env)
    case allowed of
        Left message -> return (Left (AssignmentFailure AssignmentUnavailable message))
        Right ()
            | not (Set.null (hostTypeArguments term)) -> return (Left (AssignmentFailure AssignmentScopeEscape ("scope violation for '" ++ name ++ "' — out-of-scope: " ++ List.intercalate ", " (map (show . mkLVar) (Set.toList (hostTypeArguments term))))))
        Right () -> do
            prepared <- liftIO (prepareHostValue env term)
            case prepared of
                Left message -> return (Left (AssignmentFailure AssignmentPreparationFailed message))
                Right (value, fresh) -> assignThrough fresh [] target value
    where
        -- `types` are the types of the variables through which the
        -- assignment came to `targetLV`: it is their value, so it has their
        -- types too.
        assignThrough fresh types targetLV term = assertNonnegativeIndices term `seq` do
            env <- askRuntimeEnv
            allowed <- liftIO (runtimeCanAssign env)
            case allowed of
                Left message -> return (Left (AssignmentFailure AssignmentUnavailable message))
                Right () -> assign env fresh types targetLV term
        assign env fresh types targetLV term = do
            outcome <- liftIO $ do
                st <- readIORef (_StackRef env)
                case st of
                    [] -> return (Left (AssignmentFailure AssignmentUnavailable "no active goal"))
                    (storedContext, activeCells) : _ -> do
                        existingPending <- readIORef (_PendingSubst env)
                        let composed_subst = existingPending <> _TotalVarBinding storedContext
                            ctx = refineContext env (storedContext { _TotalVarBinding = composed_subst })
                            targetKnown = assignmentTargetIsKnown env ctx activeCells existingPending targetLV
                            current_target = bindVars composed_subst (mkLVar targetLV)
                            t_zonked = bindVars composed_subst term
                            isTypeTarget = assignmentTypeVariable (_CurrentLabeling ctx) target || assignmentTypeVariable (_CurrentLabeling ctx) targetLV
                            maybeTypeErr = if isTypeTarget then Nothing else assignmentTypeErrorWithFresh fresh env composed_subst (_CurrentLabeling ctx) targetLV t_zonked
                        if not targetKnown then
                            return (Left (AssignmentFailure AssignmentUnknownVariable ("unknown or inactive variable '?" ++ name ++ "'")))
                        else if isTypeTarget && isNothing (primitiveTypeArgumentWithKinds (_ProgramKindEnv env) t_zonked) then
                            return (Left (AssignmentFailure AssignmentKindMismatch "kind mismatch for debugger assignment: expected a type of kind *."))
                        else if current_target /= mkLVar targetLV then
                            if assignedTermsAgree current_target t_zonked then
                                return (Right Nothing)
                            else case etaReduce (rewrite NF current_target) of
                                -- bound to a variable that has no value: that
                                -- variable is the one to assign, and it has
                                -- the type of this one too
                                LVar other
                                    | other /= targetLV -> return (maybe (Right (Just (other, maybeToList (variableType env ctx { _TotalVarBinding = composed_subst } targetLV >>= typeTerm) ++ types))) (Left . AssignmentFailure AssignmentTypeMismatch) maybeTypeErr)
                                _ -> return (Left (AssignmentFailure AssignmentAlreadyBound ("variable '?" ++ name ++ "' is already bound to an incompatible value")))
                        else if targetLV `Set.member` getLVars t_zonked then
                            return (Left (AssignmentFailure AssignmentOccursCheck ("occurs check failed for '" ++ name ++ "'")))
                        else do
                            let labeling = _CurrentLabeling ctx
                                scope_target = min (lookupLabel target labeling) (lookupLabel targetLV labeling)
                                (escapedCons, escapedVars) = scopeEscaping labeling scope_target targetLV t_zonked
                            if not (null escapedCons) || any (`Set.notMember` fresh) escapedVars then do
                                let renderCon c = shows c ""
                                    renderVar v = case v of
                                        LV_Unique _ (DispHint (Just s)) -> s
                                        LV_Unique u (DispHint Nothing) -> "?V_" ++ show (unUnique u)
                                        LV_ty_var u -> "?TV_" ++ show (unUnique u)
                                        LV_Named n -> n
                                    items = map renderCon escapedCons ++ map renderVar escapedVars
                                return (Left (AssignmentFailure AssignmentScopeEscape ("scope violation for '" ++ name ++ "' — out-of-scope: " ++ List.intercalate ", " items)))
                            else if isJust maybeTypeErr then
                                return (Left (AssignmentFailure AssignmentTypeMismatch (fromMaybe "debugger assignment type check failed" maybeTypeErr)))
                            else case (if isTypeTarget then Just (VarBinding (Map.singleton targetLV t_zonked)) else typedBindingWithFresh fresh env ctx { _TotalVarBinding = composed_subst } (stateVariables ctx activeCells existingPending) types targetLV t_zonked) of
                                Nothing -> return (Left (AssignmentFailure AssignmentTypeMismatch "type mismatch for debugger assignment: the types of the target and its aliases do not agree"))
                                Just resolved_binding -> do
                                    -- Keep the value and its type equations
                                    -- together. The caller's target anchors
                                    -- persistence; its current representative
                                    -- also needs the value for immediate reads.
                                    let new_binding = if anchor then VarBinding (Map.insert target (bindVars resolved_binding (mkLVar targetLV)) (unVarBinding resolved_binding)) else resolved_binding
                                        composedAfter = new_binding <> composed_subst
                                        constraintsAfter = zonkLVar composedAfter (_LeftConstraints ctx)
                                        contextAfter = ctx
                                            { _TotalVarBinding = composedAfter
                                            , _LeftConstraints = constraintsAfter
                                            }
                                        evaluationTermsAfter =
                                            [ (lhs, rhs)
                                            | EvalutionConstraint lhs rhs <- constraintsAfter
                                            ]
                                        inconsistentStore =
                                            isNothing (recheckEvaluationConstraints evaluationTermsAfter)
                                                || not (storeSatisfiable contextAfter)
                                    if inconsistentStore then
                                        return (Left (AssignmentFailure AssignmentConstraintConflict ("inconsistent with arithmetic constraints for '" ++ name ++ "'")))
                                    else do
                                        writeIORef (_PendingSubst env) (new_binding <> existingPending)
                                        return (Right Nothing)
            case outcome of
                Left err -> return (Left err)
                Right (Just (other, known)) -> assignThrough fresh known other term
                Right Nothing -> return (Right ())

assignedTermsAgree :: TermNode -> TermNode -> Bool
assignedTermsAgree lhs rhs
    = assertNonnegativeIndices lhs `seq`
        assertNonnegativeIndices rhs `seq`
        (etaReduce (rewrite NF lhs) == etaReduce (rewrite NF rhs)
            || case arithmeticEquality lhs rhs of
                ArithEqTrue -> evaluationConstraintUniversallyValid lhs rhs
                _ -> False)

instance ZonkLVar Context where
    zonkLVar theta ctx
        = assertVarBinding theta `seq`
            assertVarBinding (_TotalVarBinding ctx) `seq`
            assertConstraints (_LeftConstraints ctx) `seq`
            Context
        { _TotalVarBinding = theta <> _TotalVarBinding ctx
        , _CurrentLabeling = zonkLVar theta (_CurrentLabeling ctx)
        , _LeftConstraints = zonkLVar theta (_LeftConstraints ctx)
        , _ContextThreadId = _ContextThreadId ctx
        , _debuggindModeOn = _debuggindModeOn ctx
        }

instance ZonkLVar Constraint where
    zonkLVar theta constraint
        = assertVarBinding theta `seq`
            assertConstraint constraint `seq`
            go constraint
        where
            go (DisagreementConstraint eqn)
                = DisagreementConstraint (bindVars theta eqn)
            go (EvalutionConstraint lhs rhs)
                = EvalutionConstraint (bindVars theta lhs) (bindVars theta rhs)
            go (ArithmeticConstraint premises arith)
                = ArithmeticConstraint (bindArithStore theta premises) (bindVars theta arith)
            go (PresburgerConstraint premises rep freeOf)
                = PresburgerConstraint (bindArithStore theta premises) rep (Map.map (bindVars theta) freeOf)

instance ZonkLVar Cell where
    zonkLVar theta (Cell facts hyps premises level goal call_id)
        = assertVarBinding theta `seq`
            assertNonnegativeTerms (concat (Map.elems facts)) `seq`
            assertNonnegativeTerms hyps `seq`
            assertArithStore premises `seq`
            assertNonnegativeIndices goal `seq`
            mkCell facts (bindVars theta hyps) (bindArithStore theta premises) level (bindVars theta goal) call_id

instance Show Constraint where
    showsPrec prec (DisagreementConstraint eqn) = showsPrec prec eqn
    showsPrec prec (EvalutionConstraint lhs rhs) = showsPrec prec lhs . strstr " is " . showsPrec prec rhs
    showsPrec prec (ArithmeticConstraint premises arith) = showsGuarded prec premises (showsPrec 0 arith)
    showsPrec prec (PresburgerConstraint premises rep freeOf) = showsGuarded prec premises (showsPrec 0 (NPresburgerCheck rep freeOf Nothing))

showsGuarded :: Int -> ArithStore -> ShowS -> ShowS
showsGuarded prec premises consequent
    | null premiseTerms = consequent
    | otherwise = parensIf (prec > 3) (strstr "(" . sepBy (strstr " & ") (map (showsPrec 0) premiseTerms) . strstr ") => " . consequent)
    where
        premiseTerms = fst premises ++ [ NPresburgerCheck rep freeOf Nothing | (rep, freeOf) <- snd premises ]
        sepBy _ [] = id
        sepBy _ [item] = item
        sepBy separator (item : items) = item . separator . sepBy separator items

mkCell :: Map.Map Constant [Fact] -> [Fact] -> ArithStore -> ScopeLevel -> Goal -> CallId -> Cell
mkCell facts hyps premises level goal call_id = goal `seq` Cell { _GivenFacts = facts, _GivenHypos = hyps, _GivenArithPremises = premises, _ScopeLevel = level, _WantedGoal = goal, _CellCallId = call_id }

showsvdash :: Show goal => Indentation -> [Fact] -> goal -> ShowS
showsvdash space [] goal = strstr "|- " . shows goal
showsvdash space [hyp] goal = shows hyp . strstr " |- " . shows goal
showsvdash space (hyp : hyps) goal = shows hyp . strstr ", " . showsvdash space hyps goal

parensIf :: Bool -> ShowS -> ShowS
parensIf True inner = strstr "(" . inner . strstr ")"
parensIf False inner = inner

showsMonoType :: NotationDB -> Int -> MonoType Int -> ShowS
showsMonoType db prec t
    = case Notation.tryFoldType db t of
        Just (name, []) -> strstr name
        Just (name, args) -> parensIf (prec > 6) inner where
            inner = strstr name . List.foldr (.) id [ strstr " " . showsMonoType db 7 a | a <- args ]
        Nothing -> showsMonoTypeRaw db prec t

showsMonoTypeRaw :: NotationDB -> Int -> MonoType Int -> ShowS
showsMonoTypeRaw _ _ (TyVar i)
    = strstr "a_" . shows i
showsMonoTypeRaw _ _ (TyMTV mtv)
    = strstr "?TV_" . shows (if unUnique mtv < 0 then negate (unUnique mtv) - 1 else unUnique mtv)
showsMonoTypeRaw _ _ (TyCon (TCon (TC_Unique uni) _))
    = strstr "?TV_" . shows (unUnique uni)
showsMonoTypeRaw _ _ (TyCon (TCon tc _))
    = shows tc
showsMonoTypeRaw db prec (TyApp (TyApp (TyCon (TCon TC_Arrow _)) t1) t2)
    = parensIf (prec > 4) inner where
        inner = showsMonoType db 5 t1 . strstr " -> " . showsMonoType db 4 t2
showsMonoTypeRaw db prec (TyApp t1 t2)
    = parensIf (prec > 6) inner where
        inner = showsMonoType db 6 t1 . strstr " " . showsMonoType db 7 t2

showLVarVN :: LogicVar -> ShowS
showLVarVN (LV_ty_var uni) = strstr "?TV_" . shows (unUnique uni)
showLVarVN (LV_Unique uni (DispHint (Just s))) = strstr s
showLVarVN (LV_Unique uni (DispHint Nothing)) = strstr "?V_" . shows (unUnique uni)
showLVarVN (LV_Named name) = strstr name

showsMonoTypeIn :: NotationDB -> Bool -> Labeling -> LogicVar -> Maybe (MonoType Int) -> ShowS
showsMonoTypeIn db False _ _ mtyp
    = case mtyp of
        Just t -> showsMonoType db 0 t
        Nothing -> strstr "?"
showsMonoTypeIn db True labeling lv mtyp
    = render lv mtyp where
    render :: LogicVar -> Maybe (MonoType Int) -> ShowS
    render lv' mtyp' = prefix . strstr "|- " . renderedTy . strstr ")" where
        (scope_v, myK) = case lv' of
            LV_Named _ -> (-1, -1)
            _ -> (lookupLabel lv' labeling, lvKey lv')
        cons =
            [ renderCon uni cTyp
            | (uni, cTyp) <- IntMap.toAscList (_ConTypes labeling)
            , IntMap.findWithDefault maxBound uni (_ConLabel labeling) <= scope_v
            ]
        vars =
            [ renderVar uni
            | (uni, scp) <- IntMap.toAscList (_VarLabel labeling)
            , uni < myK
            , scp <= scope_v
            ]
        entries = cons ++ vars
        prefix = case entries of
            [] -> strstr "("
            _ -> strstr "(" . sepBy (strstr ", ") entries . strstr " "
        renderedTy = case mtyp' of
            Just t -> showsMonoType db 0 t
            Nothing -> strstr "?"
    renderCon :: Int -> MonoType Int -> ShowS
    renderCon uni cTyp = strstr "c_" . shows uni . strstr " : " . showsMonoType db 0 cTyp
    renderVar :: Int -> ShowS
    renderVar uni
        | IntMap.member uni (_TyVarKeys labeling) = strstr "?TV_" . shows uni
        | otherwise = strstr "?V_" . shows uni . strstr " : " . render innerLV mInnerTy
        where
            innerLV = LV_Unique (Unique uni) noHint
            mInnerTy = IntMap.lookup uni (_VarTypes labeling)
    sepBy :: ShowS -> [ShowS] -> ShowS
    sepBy _ [] = id
    sepBy _ [x] = x
    sepBy sep (x : xs) = x . sep . sepBy sep xs

-- The types of `_typing` are as the frame has them by now (specializeType).
showStackItem :: NotationDB -> KindEnv -> Bool -> Set.Set LogicVar -> Map.Map LogicVar (MonoType Int) -> Indentation -> (Context, [Cell]) -> ShowS
showStackItem db kindEnv verbose fvs typeMap space (ctx, cells)
    = strcat
        [ pindent space . strstr "+ progressings = " . plist (space + 4) [ strstr "?- [ " . showsvdash (space + 8) hyps goal . strstr " ] # call_id = " . shows call_id | Cell facts hyps premises level goal call_id <- cells ] . nl
        , pindent space . strstr "+ context = Context" . nl
        , pindent (space + 4) . strstr "{ " . strstr "_substitution = " . plist (space + 8) [ shows (LVar v) . strstr " := " . shows t | (v, t) <- Map.toList (unVarBinding (_TotalVarBinding ctx)), v `Set.member` fvs ] . nl
        , pindent (space + 4) . strstr ", " . strstr "_constraints = " . plist (space + 8) [ shows constraint | constraint <- _LeftConstraints ctx, debugConstraintVisible constraint ] . nl
        , pindent (space + 4) . strstr ", " . strstr "_typing = " . plist (space + 8) typings . nl
        , pindent (space + 4) . strstr ", " . strstr "_thread_id = " . shows (_ContextThreadId ctx) . nl
        , pindent (space + 4) . strstr "}" . nl
        ]
    where
        debugConstraintVisible (EvalutionConstraint lhs rhs) = not (evaluationConstraintUniversallyValid lhs rhs)
        debugConstraintVisible _ = True

        typings = namedTypings ++ generatedTypings

        current = specializeType kindEnv (_TotalVarBinding ctx)
        labeling = (_CurrentLabeling ctx) { _ConTypes = IntMap.map current (_ConTypes (_CurrentLabeling ctx)), _VarTypes = IntMap.map current (_VarTypes (_CurrentLabeling ctx)) }

        namedTypings =
            [ showLVarVN v . strstr " : " . showsMonoTypeIn db verbose labeling v (Just (current typ))
            | (v, typ) <- Map.toList typeMap, v `Set.member` fvs
            ]

        generatedTypings =
            [ showLVarVN v . strstr " : " . showsMonoTypeIn db verbose labeling v (lookupLVarType v labeling)
            | (uni, _) <- IntMap.toList (_VarLabel (_CurrentLabeling ctx))
            , not (IntMap.member uni (_TyVarKeys (_CurrentLabeling ctx)))
            , let v = LV_Unique (Unique uni) noHint
            ]

showsCurrentState :: NotationDB -> KindEnv -> Bool -> Set.Set LogicVar -> Map.Map LogicVar (MonoType Int) -> Context -> [Cell] -> Stack -> ShowS
showsCurrentState db kindEnv verbose fvs typeMap ctx cells stack = strcat
    [ strstr "--------------------------------" . nl
    , strstr "* The top of the current stack is:" . nl
    , showStackItem db kindEnv verbose fvs typeMap 4 (ctx, cells) . nl
    , strstr "* The rest of the current stack is:" . nl
    , strcat
        [ strcat
            [ pindent 0 . strstr "- (#" . shows i . strstr ")" . nl
            , showStackItem db kindEnv verbose fvs typeMap 4 item . nl
            ]
        | (i, item) <- zip [1, 2 .. length stack] stack
        ]
    , strstr "--------------------------------" . nl
    ]

instantiateFact :: UniqueM m => Fact -> ScopeLevel -> StateT Labeling (ExceptT KernelErr m) (TermNode, TermNode)
instantiateFact fact level
    = case unfoldlNApp (rewrite HNF fact) of
        (NCon (DC (DC_LO LO_ty_pi)) _, [fact1]) -> do
            uni <- getUnique
            let var = LV_ty_var uni
                mtvKey = case rewrite HNF fact1 of
                    NLam _ (LamType (Just (TyMTV mtv))) _ _ -> Just mtv
                    _ -> Nothing
                fact1' = case mtvKey of
                    Just mtv -> substTyMTV mtv uni fact1
                    Nothing -> fact1
            modify (enrollLabel var level)
            modify (\lbl -> lbl { _TyVarKeys = IntMap.insert (unUnique uni) () (_TyVarKeys lbl) })
            instantiateFact (rewrite HNF (mkNApp fact1' (mkLVar var))) level
        (NCon (DC (DC_LO LO_pi)) _, [fact1]) -> do
            uni <- getUnique
            let (mhint, mty) = case rewrite HNF fact1 of
                    NLam h ty _ _ -> (h, unLamType ty)
                    _ -> (Nothing, Nothing)
                var = LV_Unique uni (mkHint mhint)
            modify (enrollLabel var level)
            case mty of
                Just ty -> modify (\lbl -> lbl { _VarTypes = IntMap.insert (unUnique uni) ty (_VarTypes lbl) })
                Nothing -> return ()
            instantiateFact (rewrite HNF (mkNApp fact1 (mkLVar var))) level
        (NCon (DC (DC_LO LO_if)) _, [conclusion, premise]) -> return (conclusion, premise)
        (NCon (DC (DC_LO logical_operator)) _, args) -> lift (throwE (BadFactGiven (foldlNApp (mkNCon logical_operator) args)))
        (t, ts) -> return (foldlNApp t ts, mkNCon LO_true)

runLogicalOperator :: UniqueM m => LogicalOperator -> [TermNode] -> Context -> Map.Map Constant [Fact] -> [Fact] -> ArithStore -> ScopeLevel -> CallId -> [Cell] -> Stack -> ExceptT KernelErr m Stack
runLogicalOperator logicalOperator args ctx facts hyps premises level callId cells stack
    = assertNonnegativeTerms args `seq`
        runLogicalOperatorUnchecked logicalOperator args ctx facts hyps premises level callId cells stack

runLogicalOperatorUnchecked :: UniqueM m => LogicalOperator -> [TermNode] -> Context -> Map.Map Constant [Fact] -> [Fact] -> ArithStore -> ScopeLevel -> CallId -> [Cell] -> Stack -> ExceptT KernelErr m Stack
runLogicalOperatorUnchecked LO_true [] ctx facts hyps premises level call_id cells stack
    = return ((ctx, cells) : stack)
runLogicalOperatorUnchecked LO_fail [] ctx facts hyps premises level call_id cells stack
    = return stack
runLogicalOperatorUnchecked LO_debug [loc_str] ctx facts hyps premises level call_id cells stack
    = runDebugger loc_str ctx facts hyps level call_id cells stack
runLogicalOperatorUnchecked LO_cut [] ctx facts hyps premises level call_id cells stack
    = return ((ctx, cells) : [ (ctx', cells') | (ctx', cells') <- stack, _ContextThreadId ctx' < call_id ])
runLogicalOperatorUnchecked LO_and [goal1, goal2] ctx facts hyps premises level call_id cells stack
    = return ((ctx, mkCell facts hyps premises level goal1 call_id : mkCell facts hyps premises level goal2 call_id : cells) : stack)
runLogicalOperatorUnchecked LO_or [goal1, goal2] ctx facts hyps premises level call_id cells stack
    = return ((ctx, mkCell facts hyps premises level goal1 call_id : cells) : (ctx, mkCell facts hyps premises level goal2 call_id : cells) : stack)
runLogicalOperatorUnchecked LO_imply [fact1, goal2] ctx facts hyps premises level call_id cells stack
    = do
        localPremises <- instantiateArithPremises fact1
        let premises' = appendArithStore premises localPremises
        return ((ctx, mkCell facts (expandAssumptions fact1 ++ hyps) premises' level goal2 call_id : cells) : stack)
runLogicalOperatorUnchecked LO_sigma [goal1] ctx facts hyps premises level call_id cells stack
    = do
        uni <- getUnique
        let (mhint, mty) = case rewrite HNF goal1 of
                NLam h ty _ _ -> (h, unLamType ty)
                _ -> (Nothing, Nothing)
            var = LV_Unique uni (mkHint mhint)
            labeling0 = enrollLabel var level (_CurrentLabeling ctx)
            labeling1 = case mty of
                Just ty -> labeling0 { _VarTypes = IntMap.insert (unUnique uni) ty (_VarTypes labeling0) }
                Nothing -> labeling0
            goal' = rewrite HNF (mkNApp goal1 (mkLVar var))
        return ((ctx { _CurrentLabeling = labeling1 }, mkCell facts hyps premises level goal' call_id : cells) : stack)
runLogicalOperatorUnchecked LO_pi [goal1] ctx facts hyps premises level call_id cells stack
    = do
        uni <- getUnique
        let (mhint, mty) = case rewrite HNF goal1 of
                NLam h ty _ _ -> (h, unLamType ty)
                _ -> (Nothing, Nothing)
            con = DC (DC_Unique uni (mkHint mhint))
            labeling0 = enrollLabel con (level + 1) (_CurrentLabeling ctx)
            labeling1 = case mty of
                Just ty -> labeling0 { _ConTypes = IntMap.insert (unUnique uni) ty (_ConTypes labeling0) }
                Nothing -> labeling0
            goal' = rewrite HNF (mkNApp goal1 (mkNCon con))
        return ((ctx { _CurrentLabeling = labeling1 }, mkCell facts hyps premises (level + 1) goal' call_id : cells) : stack)
runLogicalOperatorUnchecked LO_is [lhs, rhs] ctx facts hyps premises level call_id cells stack
    | Left "ill" == rhsValue
    = return stack
    | LVar x <- rewrite NF lhs
    , Right v <- rhsValue
    = bindIs ctx x (mkNCon (DC (DC_NatL v)))
    | Right v <- rhsValue
    , Right lhs_v <- lhsValue
    = if lhs_v == v then return ((ctx, cells) : stack) else return stack
    | LVar x <- lhs'
    , Just rhs_s <- simplifyArithmetic rhs'
    , canBindIs x rhs_s
    = case addDefinitionConstraints [rhs'] ctx of
        Nothing -> return stack
        Just ctx' -> bindIs ctx' x rhs_s
    | ArithEqTrue <- arithmeticEquality lhs' rhs'
    = case addDefinitionConstraints [lhs', rhs'] ctx of
        Nothing -> return stack
        Just ctx' -> return ((ctx', cells) : stack)
    | ArithEqFalse <- arithmeticEquality lhs' rhs'
    = return stack
    | not arithmeticMode
    = unifyNonArithmetic
    | otherwise
    = case settleEvaluationConstraints
        (ctx { _LeftConstraints = EvalutionConstraint lhs' rhs' : _LeftConstraints ctx })
        cells of
        Nothing -> return stack
        Just (ctx', cells') -> return ((ctx', cells') : stack)
    where
        lhs' = rewrite NF lhs
        rhs' = rewrite NF rhs
        lhsValue = evaluateA lhs'
        rhsValue = evaluateA rhs'
        arithmeticMode = isNatTerm lhs' || isNatTerm rhs' || mentionsArithmetic lhs' || mentionsArithmetic rhs'
        isNatTerm t = case rewrite NF t of
            NCon (DC (DC_NatL _)) _ -> True
            _ -> typeOfTerm (_CurrentLabeling ctx) [] t == Just mkTyNat
        bindIs ctx0 x rhs_s = execIs hyps (zonkLVar theta ctx0) (map (zonkLVar theta) cells) stack where
            theta = VarBinding (Map.singleton x rhs_s)
        canBindIs x t = x `Set.notMember` getLVars t && null badCons && null badVars where
                targetScope = lookupLabel x (_CurrentLabeling ctx)
                (badCons, badVars) = scopeEscaping (_CurrentLabeling ctx) targetScope x t
        unifyNonArithmetic = do
            let priorDisagreements =
                    [ eqn
                    | DisagreementConstraint eqn <- _LeftConstraints ctx
                    ]
                otherConstraints =
                    [ constraint
                    | constraint <- _LeftConstraints ctx
                    , case constraint of
                        DisagreementConstraint _ -> False
                        _ -> True
                    ]
            output <- lift (runHOPU (_CurrentLabeling ctx) ((lhs' :=?=: rhs') : priorDisagreements))
            case output of
                Nothing -> return stack
                Just (newDisagreements, HopuSol newLabeling subst) -> do
                    let ctx' = (zonkLVar subst ctx)
                            { _CurrentLabeling = newLabeling
                            , _LeftConstraints =
                                map DisagreementConstraint newDisagreements
                                    ++ zonkLVar subst otherConstraints
                            }
                    execIs hyps ctx' (zonkLVar subst cells) stack
runLogicalOperatorUnchecked logical_operator args ctx facts hyps premises level call_id cells stack
    = throwE (BadGoalGiven (foldlNApp (mkNCon logical_operator) args))

-- Retain one self-evaluation per arithmetic term whose value is not known yet.
-- These constraints are deliberately not discharged merely because a
-- Presburger normalization proves the surrounding formula: HOPU may later
-- replace a typed variable by a partial expression such as @1 / 0@.
-- A pi-bound natural is immutable and ranges only over natural values. Its
-- exact runtime type and live scope entry justify total arithmetic built
-- from successor, addition and multiplication. Flexible cells, applications
-- of unknown heads and partial operators still need delayed definedness.
rigidNaturalDefined :: Labeling -> TermNode -> Bool
rigidNaturalDefined labeling term = case term of
    NCon (DC (DC_NatL number)) _ -> number >= 0
    NCon constant@(DC (DC_Unique identity _)) _ ->
        IntMap.member (unUnique identity) (_ConLabel labeling)
            && lookupConType constant labeling == Just mkTyNat
    NApp (NCon (DC DC_Succ) _) value _ -> rigidNaturalDefined labeling value
    NApp (NApp (NCon (DC operator) _) left _) right _
        | operator == DC_plus || operator == DC_mul -> rigidNaturalDefined labeling left && rigidNaturalDefined labeling right
    _ -> False

-- This also discharges an old self-obligation after HOPU has replaced its
-- flexible cell by an immutable natural. A proper equation is never dropped.
rigidDefinition :: Labeling -> (TermNode, TermNode) -> Bool
rigidDefinition labeling (left, right) = left == right && rigidNaturalDefined labeling left

addDefinitionConstraints :: [TermNode] -> Context -> Maybe Context
addDefinitionConstraints terms ctx
    = do
        pending <- filter (not . rigidDefinition (_CurrentLabeling ctx)) <$> recheckEvaluationConstraints evaluationTerms
        let nonEvaluations =
                [ constraint
                | constraint <- constraints0
                , case constraint of
                    EvalutionConstraint _ _ -> False
                    _ -> True
                ]
            ctx' = ctx
                { _LeftConstraints = map (uncurry EvalutionConstraint) pending ++ nonEvaluations
                }
        if storeSatisfiable ctx' then Just ctx' else Nothing
    where
        normalized = List.nub (map (rewrite NF) terms)
        newDefinitions =
            [ EvalutionConstraint term term
            | term <- normalized
            , not (rigidNaturalDefined (_CurrentLabeling ctx) term)
            , case evaluateA term of
                Right _ -> False
                _ -> True
            ]
        constraints0 = newDefinitions ++ _LeftConstraints ctx
        evaluationTerms =
            [ (lhs, rhs)
            | EvalutionConstraint lhs rhs <- constraints0
            ]

expandAssumptions :: Fact -> [Fact]
expandAssumptions fact
    = case exposed of
        NApp (NApp (NCon (DC (DC_LO LO_and)) _) fact1 _) fact2 _ -> expandAssumptions fact1 ++ expandAssumptions fact2
        NApp (NApp head@(NCon (DC (DC_LO LO_if)) _) conclusion headLoc) premise outerLoc ->
            [ mkNAppLoc outerLoc (mkNAppLoc headLoc head conclusion') premise
            | conclusion' <- expandAssumptions conclusion
            ]
        NApp head@(NCon (DC (DC_LO operator)) _) (NLam mhint lam_ty body loc) outerLoc
            | operator == LO_pi || operator == LO_ty_pi ->
                [ mkNAppLoc outerLoc head (NLam mhint lam_ty body' loc)
                | body' <- expandAssumptions body
                ]
        _ -> [fact]
    where
        -- A rigid source clause needs no reduction to expose its outer form.
        -- Rebuilding it with unlocated constructors loses cached diagnostics.
        exposed = case fst (unfoldlNApp fact) of
            NCon {} -> fact
            _ -> rewrite HNF fact

-- | Extract only the arithmetic role of a local antecedent.  Searchable local
-- clauses continue to live in '_GivenHypos'; this separate store prevents
-- comparisons and Presburger formulas from becoming predicate alternatives.
-- A @pi@ inside the antecedent is represented as an actual formula quantifier,
-- rather than as a free eigenconstant outside the implication.  Thus
-- @(pi C\ A C) => G@ means @(forall C. A C) => G@, not
-- @forall C. (A C => G)@.
instantiateArithPremises :: MonadUnique m => Fact -> m ArithStore
instantiateArithPremises = collect [] . rewrite HNF where
    collect binders fact = case unfoldlNApp (rewrite HNF fact) of
        (NCon (DC (DC_LO LO_and)) _, [fact1, fact2]) ->
            appendArithStore <$> collect binders fact1 <*> collect binders fact2
        (NCon (DC (DC_LO LO_pi)) _, [fact1]) -> do
            uni <- getUnique
            let mhint = case rewrite HNF fact1 of
                    NLam hint _ _ _ -> hint
                    _ -> Nothing
                marker = LV_Unique uni (mkHint mhint)
                fact1' = rewrite HNF (mkNApp fact1 (mkLVar marker))
            collect (binders ++ [marker]) fact1'
        (NCon (DC (DC_LO LO_ty_pi)) _, [fact1]) -> do
            uni <- getUnique
            let var = LV_ty_var uni
                mtvKey = case rewrite HNF fact1 of
                    NLam _ (LamType (Just (TyMTV mtv))) _ _ -> Just mtv
                    _ -> Nothing
                fact1' = case mtvKey of
                    Just mtv -> substTyMTV mtv uni fact1
                    Nothing -> fact1
            collect binders (rewrite HNF (mkNApp fact1' (mkLVar var)))
        (NPresburgerCheck rep freeOf _, []) ->
            let (rep', freeOf') = quantifyBinders binders rep freeOf
            in return ([], [(rep', freeOf')])
        (NCon (DC (DC_LO _)) _, _) -> return emptyArithStore
        (headTerm, args) ->
            let term = foldlNApp headTerm args
            in case liftConstraint term of
                Nothing -> return emptyArithStore
                Just lifted
                    | null binders -> return ([term], [])
                    | otherwise ->
                        let (rep', freeOf') = quantifyBinders binders (_liftedFormula lifted) (_freeOfLifted lifted)
                        in return ([], [(rep', freeOf')])

    quantifyBinders binders rep freeOf = (foldr AllF rep boundVars, freeOf') where
        (boundVars, freeOf') = List.foldl' detach ([], freeOf) binders
        detach (vars, remaining) binder =
            let (owned, unowned) = Map.partition (sameBinder binder) remaining
            in (vars ++ Map.keys owned, unowned)
        sameBinder binder term = rewrite NF term == mkLVar binder

execIs :: MonadUnique m => [Fact] -> Context -> [Cell] -> Stack -> m Stack
execIs hyps ctx cells stack
    = assertNonnegativeTerms hyps `seq`
        assertConstraints (_LeftConstraints ctx) `seq`
        case settleEvaluationConstraints ctx cells of
            Nothing -> return stack
            Just (ctx', cells') -> return ((ctx', cells') : stack)

-- Apply bindings produced by delayed @is@ constraints, normalize every other
-- arithmetic residual under those bindings, and validate the complete joint
-- store.  This is shared by direct @is@ execution and HOPU clause matching.
settleEvaluationConstraints :: Context -> [Cell] -> Maybe (Context, [Cell])
settleEvaluationConstraints ctx cells = do
    let storedBinding = _TotalVarBinding ctx
        ctx0 = ctx
            { _LeftConstraints = zonkLVar storedBinding (_LeftConstraints ctx)
            }
        cells0 = zonkLVar storedBinding cells
        evaluationTerms =
            [ (rewrite NF lhs, rewrite NF rhs)
            | EvalutionConstraint lhs rhs <- _LeftConstraints ctx0
            ]
    (evaluationBinding, pendingEvaluations) <- solveEvaluationConstraints evaluationTerms
    let ctx1 = zonkLVar evaluationBinding ctx0
        cells1 = zonkLVar evaluationBinding cells0
        newDisagreements = [ eqn | DisagreementConstraint eqn <- _LeftConstraints ctx1 ]
        newArithmeticConstraints =
            [ (premises, rewrite NF arith)
            | ArithmeticConstraint premises arith <- _LeftConstraints ctx1
            ]
        newPresburgerConstraints =
            [ PresburgerConstraint premises rep freeOf
            | PresburgerConstraint premises rep freeOf <- _LeftConstraints ctx1
            ]
        ctx2 = ctx1
            { _LeftConstraints =
                map DisagreementConstraint newDisagreements
                    ++ map (uncurry EvalutionConstraint) (filter (not . rigidDefinition (_CurrentLabeling ctx1)) pendingEvaluations)
                    ++ [ ArithmeticConstraint premises arith
                        | (premises, arith) <- newArithmeticConstraints
                        , evaluateB arith /= Right True
                        ]
                    ++ newPresburgerConstraints
            }
    if storeSatisfiable ctx2 then Just (ctx2, cells1) else Nothing

evaluateA :: TermNode -> Either ErrMsg Integer
evaluateA term = assertNonnegativeIndices term `seq` go term where
    go (NApp (NCon (DC DC_Succ) _) t1 _)
        = succ <$> go t1
    go (NApp (NApp (NCon (DC DC_plus) _) t1 _) t2 _)
        = strictBinary (+) (go t1) (go t2)
    go (NApp (NApp (NCon (DC DC_minus) _) t1 _) t2 _)
        = case strictPair (go t1) (go t2) of
            Right (v1, v2)
                | v1 >= v2 -> Right (v1 - v2)
                | otherwise -> Left "ill"
            Left err -> Left err
    go (NApp (NApp (NCon (DC DC_mul) _) t1 _) t2 _)
        = strictBinary (*) (go t1) (go t2)
    go (NApp (NApp (NCon (DC DC_div) _) t1 _) t2 _)
        = case (go t1, go t2) of
            (_, Right 0) -> Left "ill"
            (Left "ill", _) -> Left "ill"
            (_, Left "ill") -> Left "ill"
            (Right v1, Right v2) -> Right (v1 `div` v2)
            _ -> Left "non"
    go t
        = case reads (shows t "") of
            [(v, "")] -> return v
            _ -> Left "non"

    -- Natural arithmetic is strict in both operands.  In particular, an
    -- ill-defined operand is not hidden by a still-unknown sibling (or by
    -- multiplication with zero).
    strictPair :: Either ErrMsg Integer -> Either ErrMsg Integer -> Either ErrMsg (Integer, Integer)
    strictPair lhs rhs = case (lhs, rhs) of
        (Left "ill", _) -> Left "ill"
        (_, Left "ill") -> Left "ill"
        (Right x, Right y) -> Right (x, y)
        _ -> Left "non"

    strictBinary :: (Integer -> Integer -> Integer) -> Either ErrMsg Integer -> Either ErrMsg Integer -> Either ErrMsg Integer
    strictBinary op lhs rhs = uncurry op <$> strictPair lhs rhs

-- Re-evaluate delayed `is` constraints after each substitution.  A ground
-- equality that is true is discharged, a ground mismatch or an ill-defined
-- arithmetic expression kills the branch, and genuinely non-ground pairs
-- remain in source order for the next substitution.
recheckEvaluationConstraints :: [(TermNode, TermNode)] -> Maybe [(TermNode, TermNode)]
recheckEvaluationConstraints constraints
    = assertEvaluationTerms constraints `seq`
        foldr step (Just []) constraints
    where
        step (lhs, rhs) checked
            = case (evaluateA lhs', evaluateA rhs') of
                (Right lhsValue, Right rhsValue)
                    | lhsValue == rhsValue -> checked
                    | otherwise -> Nothing
                (Left "ill", _) -> Nothing
                (_, Left "ill") -> Nothing
                _
                    | evaluationConstraintPossible lhs' rhs' -> ((lhs', rhs') :) <$> checked
                    | otherwise -> Nothing
            where
                lhs' = rewrite NF lhs
                rhs' = rewrite NF rhs

-- Resolve every delayed @L is R@ whose right-hand side has become a concrete
-- natural.  Bindings are accumulated and fed back through the whole set until
-- a fixed point is reached, so the outcome is independent of constraint
-- order.  The public consistency-only checker above intentionally does not
-- discard such a binding; runtime transition boundaries use this solver.
solveEvaluationConstraints :: [(TermNode, TermNode)] -> Maybe (VarBinding, [(TermNode, TermNode)])
solveEvaluationConstraints constraints
    = assertEvaluationTerms constraints `seq` loop mempty
    where
        loop theta =
            let current =
                    [ (rewrite NF (bindVars theta lhs), rewrite NF (bindVars theta rhs))
                    | (lhs, rhs) <- constraints
                    ]
            in case firstGroundBinding current of
                Just (variable, value) ->
                    let binding = VarBinding (Map.singleton variable (mkNCon (DC_NatL value)))
                    in loop (binding <> theta)
                Nothing -> do
                    pending <- recheckEvaluationConstraints current
                    return (theta, pending)

        firstGroundBinding [] = Nothing
        firstGroundBinding ((lhs, rhs) : rest) = case (rewrite NF lhs, evaluateA rhs) of
            (LVar variable, Right value) -> Just (variable, value)
            _ -> firstGroundBinding rest

-- A delayed arithmetic evaluation requires every arithmetic subexpression to
-- be defined.  Subtraction and division add the only non-structural domain
-- conditions; addition, multiplication and successor are strict and recurse
-- into all operands.  Bare typed variables are values for the current solver
-- valuation, but the enclosing evaluation constraint is retained so a later
-- HOPU substitution is checked again.
definednessConditions :: TermNode -> [TermNode]
definednessConditions = go . rewrite NF where
    go (NApp (NCon (DC DC_Succ) _) t1 _) = go t1
    go (NApp (NApp (NCon (DC DC_plus) _) t1 _) t2 _) = go t1 ++ go t2
    go (NApp (NApp (NCon (DC DC_mul) _) t1 _) t2 _) = go t1 ++ go t2
    go (NApp (NApp (NCon (DC DC_minus) _) t1 _) t2 _)
        = go t1 ++ go t2 ++ [mkComparison DC_ge t1 t2]
    go (NApp (NApp (NCon (DC DC_div) _) t1 _) t2 _)
        = go t1 ++ go t2 ++ [mkComparison DC_gt t2 (mkNCon (DC_NatL 0))]
    go _ = []

mkComparison :: DataConstructor -> TermNode -> TermNode -> TermNode
mkComparison predicate lhs rhs = mkNApp (mkNApp (mkNCon predicate) lhs) rhs

mkNatEquality :: TermNode -> TermNode -> TermNode
mkNatEquality lhs rhs
    = mkNApp
        (mkNApp
            (mkNApp (mkNCon DC_eq) (mkNCon (TC_Named "nat")))
            lhs)
        rhs

-- Keep feasibility pruning conservative: only formulae accepted by the
-- linear lifting boundary are handed to Presburger.  Unsupported domain
-- conditions remain represented by the delayed evaluation constraint and are
-- reconsidered after each substitution.
supportedDefinitionConditions :: [TermNode] -> [TermNode]
supportedDefinitionConditions = filter (isJust . liftConstraint)

evaluationObligation :: TermNode -> TermNode -> ArithStore
evaluationObligation lhs rhs = (conditions ++ equality, []) where
    conditions = supportedDefinitionConditions (definednessConditions lhs ++ definednessConditions rhs)
    equalityTerm = mkNatEquality lhs rhs
    equality
        | rewrite NF lhs == rewrite NF rhs = []
        | isJust (liftConstraint equalityTerm) = [equalityTerm]
        | otherwise = []

completeEvaluationObligation :: TermNode -> TermNode -> Maybe ArithStore
completeEvaluationObligation lhs rhs
    | length supportedConditions /= length allConditions = Nothing
    | lhs' == rhs' = Just (supportedConditions, [])
    | isJust (liftConstraint equalityTerm) = Just (supportedConditions ++ [equalityTerm], [])
    | otherwise = Nothing
    where
        lhs' = rewrite NF lhs
        rhs' = rewrite NF rhs
        allConditions = definednessConditions lhs' ++ definednessConditions rhs'
        supportedConditions = supportedDefinitionConditions allConditions
        equalityTerm = mkNatEquality lhs' rhs'

evaluationConstraintPossible :: TermNode -> TermNode -> Bool
evaluationConstraintPossible lhs rhs
    = assertNonnegativeIndices lhs `seq`
        assertNonnegativeIndices rhs `seq`
        case (evaluateA lhs', evaluateA rhs') of
            (Right x, Right y) -> x == y
            (Left "ill", _) -> False
            (_, Left "ill") -> False
            _ -> presburgerStoreSat emptyArithStore (evaluationObligation lhs' rhs')
    where
        lhs' = rewrite NF lhs
        rhs' = rewrite NF rhs

-- Universal validity is used only when pruning a residual at answer time or
-- comparing already-assigned debugger values.  Unlike feasibility, every
-- generated condition must be linear; otherwise retaining the constraint is
-- the safe result.
evaluationConstraintUniversallyValid :: TermNode -> TermNode -> Bool
evaluationConstraintUniversallyValid lhs rhs
    = assertNonnegativeIndices lhs `seq`
        assertNonnegativeIndices rhs `seq`
        case (evaluateA lhs', evaluateA rhs') of
            (Right x, Right y) -> x == y
            (Left "ill", _) -> False
            (_, Left "ill") -> False
            _ -> case completeEvaluationObligation lhs' rhs' of
                Nothing -> False
                Just obligation -> presburgerGuardedValid [(emptyArithStore, obligation)]
    where
        lhs' = rewrite NF lhs
        rhs' = rewrite NF rhs

evaluateB :: TermNode -> Either ErrMsg Bool
evaluateB term = assertNonnegativeIndices term `seq` go term where
    go (NApp (NApp (NApp (NCon (DC DC_eq) _) (NCon (TC (TC_Named "nat")) _) _) t1 _) t2 _)
        = compareStrict (==) t1 t2
    go (NApp (NApp (NCon (DC DC_le) _) t1 _) t2 _)
        = compareStrict (<=) t1 t2
    go (NApp (NApp (NCon (DC DC_lt) _) t1 _) t2 _)
        = compareStrict (<) t1 t2
    go (NApp (NApp (NCon (DC DC_ge) _) t1 _) t2 _)
        = compareStrict (>=) t1 t2
    go (NApp (NApp (NCon (DC DC_gt) _) t1 _) t2 _)
        = compareStrict (>) t1 t2
    go _
        = Left "non"

    -- Boolean arithmetic is strict for the same reason as value arithmetic:
    -- a flexible sibling must not hide a definitely partial operand.
    compareStrict op lhs rhs = case (evaluateA lhs, evaluateA rhs) of
        (Left "ill", _) -> Left "ill"
        (_, Left "ill") -> Left "ill"
        (Right lhsValue, Right rhsValue) -> Right (op lhsValue rhsValue)
        _ -> Left "non"

data ArithmeticEquality
    = ArithEqTrue
    | ArithEqFalse
    | ArithEqUnknown
    deriving ()

arithmeticEquality :: TermNode -> TermNode -> ArithmeticEquality
arithmeticEquality t1 t2
    = assertNonnegativeIndices t1 `seq`
        assertNonnegativeIndices t2 `seq`
        case (evaluateA t1', evaluateA t2') of
            (Right v1, Right v2) -> if v1 == v2 then ArithEqTrue else ArithEqFalse
            (Left "ill", _) -> ArithEqFalse
            (_, Left "ill") -> ArithEqFalse
            _
                | t1' == t2' -> ArithEqTrue
                | otherwise -> case (simplifyArithmetic t1', simplifyArithmetic t2') of
                    (Just s1, Just s2)
                        | rewrite NF s1 == rewrite NF s2 -> ArithEqTrue
                    _ -> ArithEqUnknown
    where
        t1' = rewrite NF t1
        t2' = rewrite NF t2

mentionsArithmetic :: TermNode -> Bool
mentionsArithmetic t = case rewrite HNF t of
    NCon (DC (DC_NatL _)) _ -> False
    NCon (DC DC_Succ) _ -> True
    NCon (DC DC_plus) _ -> True
    NCon (DC DC_minus) _ -> True
    NCon (DC DC_mul) _ -> True
    NCon (DC DC_div) _ -> True
    NApp t1 t2 _ -> mentionsArithmetic t1 || mentionsArithmetic t2
    NLam _ _ body _ -> mentionsArithmetic body
    Susp body _ _ env -> mentionsArithmetic body || any mentionsSuspItem env
    _ -> False
    where
        mentionsSuspItem (Dummy _) = False
        mentionsSuspItem (Binds body _) = mentionsArithmetic body

simplifyArithmetic :: TermNode -> Maybe TermNode
simplifyArithmetic t
    = do
        (sawArithmetic, poly) <- Just (polyOf (rewrite NF t))
        if sawArithmetic then renderPoly (combinePoly poly) else Nothing
    where
        polyOf :: TermNode -> (Bool, [([TermNode], Integer)])
        polyOf (NCon (DC (DC_NatL n)) _) = (True, [([], n)])
        polyOf (NApp (NApp (NCon (DC DC_plus) _) t1 _) t2 _) = (saw1 || saw2 || True, p1 ++ p2) where
            (saw1, p1) = polyOf t1
            (saw2, p2) = polyOf t2
        polyOf (NApp (NApp (NCon (DC DC_mul) _) t1 _) t2 _) = (saw1 || saw2 || True, multiplyPoly p1 p2) where
            (saw1, p1) = polyOf t1
            (saw2, p2) = polyOf t2
        polyOf atom = (False, [([atom], 1)])

        multiplyPoly p1 p2 =
            [ (List.sort (factors1 ++ factors2), coeff1 * coeff2)
            | (factors1, coeff1) <- p1
            , (factors2, coeff2) <- p2
            ]

        -- Both multiplication and addition are commutative in this fragment.
        -- Keying by sorted factor lists combines like terms and Map's ascending
        -- traversal gives every polynomial a canonical monomial order,
        -- independent of the source addition tree.
        combinePoly = Map.toAscList . Map.fromListWith (+) . map canonicalTerm where
            canonicalTerm (factors, coeff) = (List.sort factors, coeff)

        renderPoly poly0
            = case filter ((/= 0) . snd) poly0 of
                [] -> Just (mkNCon (DC_NatL 0))
                terms
                    | all ((>= 0) . snd) terms -> Just (foldl1 add (map renderTerm terms))
                    | otherwise -> Nothing

        renderTerm (factors, coeff)
            = case (coeff, factors) of
                (0, _) -> mkNCon (DC_NatL 0)
                (1, []) -> mkNCon (DC_NatL 1)
                (1, factor : rest) -> foldl mul factor rest
                (_, []) -> mkNCon (DC_NatL coeff)
                (_, _) -> foldl mul (mkNCon (DC_NatL coeff)) factors

        add t1 t2 = mkNApp (mkNApp (mkNCon DC_plus) t1) t2
        mul t1 t2 = mkNApp (mkNApp (mkNCon DC_mul) t1) t2

runDebugger :: UniqueM m => TermNode -> Context -> Map.Map Constant [Fact] -> [Fact] -> ScopeLevel -> CallId -> [Cell] -> Stack -> ExceptT KernelErr m Stack
runDebugger loc_str ctx facts hyps level call_id cells stack = assertNonnegativeIndices loc_str `seq` do
    liftIO $ writeIORef (_debuggindModeOn ctx) True
    return ((ctx, cells) : stack)

-- | A @presburger phi@ goal retains @phi@ as a deferred constraint and succeeds
--   iff the whole store (existing constraints conjoined with @phi@) stays
--   satisfiable under the arithmetic assumptions in scope (left-hand sides of
--   enclosing @=>@). The retained constraint is carried along, re-checked as
--   bindings accumulate, and reported as a residual at query success.
runPresburger :: MyPresburgerFormulaRep -> Map.Map MyVar TermNode -> ArithStore -> Context -> [Cell] -> Stack -> Stack
runPresburger rep freeOf premises ctx cells stack
    = assertNonnegativeTerms (Map.elems freeOf) `seq`
        assertArithStore premises `seq`
        assertVarBinding (_TotalVarBinding ctx) `seq`
        dispatch
    where
        dispatch
            = case addDefinitionConstraints (Map.elems freeOfBound) ctx of
                Nothing -> stack
                Just definedCtx
                    | not (storeSatisfiable (retainedCtx definedCtx)) -> stack
                    | presburgerEntails (arithAssumptions premises definedCtx) (rep, freeOfBound)
                    -> (definedCtx, cells) : stack
                    | otherwise -> (retainedCtx definedCtx, cells) : stack
        retainedCtx definedCtx = definedCtx
            { _LeftConstraints = PresburgerConstraint premises rep freeOf : _LeftConstraints definedCtx
            }
        -- For the entailment test, resolve the goal's free terms under the
        -- current binding (the store-sat path zonks internally via the store).
        freeOfBound :: Map.Map MyVar TermNode
        freeOfBound = Map.map (bindVars (_TotalVarBinding ctx)) freeOf

-- | The arithmetic assumptions in scope: the comparison/presburger facts among
--   the hypotheses introduced by enclosing @=>@. Non-arithmetic hypotheses are
--   ignored (comparisons are filtered downstream by 'leafFormula').
arithAssumptions :: ArithStore -> Context -> ArithStore
arithAssumptions premises ctx = bindArithStore (_TotalVarBinding ctx) premises

-- | Validity of the lia-style implication from in-scope assumptions to the
--   retained comparison/Presburger obligations under the current binding.
storeSatisfiable :: Context -> Bool
storeSatisfiable ctx
    = assertVarBinding theta `seq`
        assertConstraints (_LeftConstraints ctx) `seq`
        isJust (recheckEvaluationConstraints evaluations)
            && presburgerGuardedStoreSat guarded
    where
        theta = _TotalVarBinding ctx
        evaluations =
            [ (bindVars theta lhs, bindVars theta rhs)
            | EvalutionConstraint lhs rhs <- _LeftConstraints ctx
            ]
        guarded :: GuardedArithStore
        guarded = mapMaybe (guardedConstraintStore theta) (_LeftConstraints ctx)

guardedConstraintStore :: VarBinding -> Constraint -> Maybe (ArithStore, ArithStore)
guardedConstraintStore theta constraint
    = assertVarBinding theta `seq`
        assertConstraint constraint `seq`
        go constraint
    where
        go (EvalutionConstraint lhs rhs) =
            Just (emptyArithStore, evaluationObligation (bindVars theta lhs) (bindVars theta rhs))
        go (ArithmeticConstraint premises term) =
            Just (bindArithStore theta premises, arithmeticObligation (bindVars theta term))
        go (PresburgerConstraint premises rep freeOf) =
            Just (bindArithStore theta premises, ([], [(rep, Map.map (bindVars theta) freeOf)]))
        go _ = Nothing

-- Ground false/ill comparison consequents must stay false under their captured
-- guard.  Treating an ill term as an opaque arithmetic atom would incorrectly
-- make it satisfiable; an explicitly false Presburger obligation preserves the
-- conditional semantics (and still lets an impossible premise discharge it).
arithmeticObligation :: TermNode -> ArithStore
arithmeticObligation term = assertNonnegativeIndices term `seq` case evaluateB term of
    Right True -> emptyArithStore
    Right False -> ([], [(ValF False, Map.empty)])
    Left "ill" -> ([], [(ValF False, Map.empty)])
    _ -> ([term], [])

isInconsistent :: [TermNode] -> Bool
isInconsistent arithTerms
    = assertNonnegativeTerms arithTerms `seq`
        if cheapKill then True else entails compiledHyps (ValF False)
    where
        cheapKill :: Bool
        cheapKill = List.any (\t -> evaluateB t == Right False || evaluateB t == Left "ill") arithTerms

        liftedResults :: [LiftResult]
        liftedResults = mapMaybe liftConstraint arithTerms

        allFreeTerms :: [TermNode]
        allFreeTerms = Set.toAscList $ Set.unions [ Set.fromList (map (rewrite NF) (Map.elems (_freeOfLifted lr))) | lr <- liftedResults ]

        shared :: Map.Map TermNode MyVar
        shared = Map.fromAscList (zip allFreeTerms [theMinNumOfMyVar ..])

        hypReps :: [MyPresburgerFormulaRep]
        hypReps =
            [ renumberFormula shared (_freeOfLifted lr) (_liftedFormula lr)
            | lr <- liftedResults
            ]

        compiledHyps :: [MyPresburgerFormula]
        compiledHyps = map (fmap compilePresburgerTerm) hypReps

runTransition :: forall m. UniqueM m => RuntimeEnv -> Set.Set LogicVar -> Stack -> ExceptT KernelErr m Satisfied
runTransition env free_lvars stack = withRuntimeExecution env Nothing $ do
    liftIO (runtimeCanResume env) >>= either (throwE . BackendError) return
    runTransitionActive env free_lvars stack

runTransitionActive :: forall m. UniqueM m => RuntimeEnv -> Set.Set LogicVar -> Stack -> ExceptT KernelErr m Satisfied
runTransitionActive env free_lvars stack = catchE (assertStack stack `seq` go stack) (\failure -> liftIO (markRuntimeInterrupted env) >> throwE failure) where
    failure :: ExceptT KernelErr m Stack
    failure = return []
    success :: (Context, [Cell]) -> ExceptT KernelErr m Stack
    success with = return [with]
    -- The stack and HOPU substitution are validated; program clauses stay shared.
    zonkMatchedCells :: VarBinding -> [Cell] -> [Cell]
    zonkMatchedCells subst cells
        | Map.null (unVarBinding subst) = cells
        | otherwise = map go cells
        where
            go (Cell facts hyps premises level goal call_id) = mkCell facts (map (bindVarsUnchecked subst) hyps) (if nullArithStore premises then premises else bindArithStore subst premises) level (bindVarsUnchecked subst goal) call_id
    arithOpCheck :: CallId -> CallId -> ArithStore -> Context -> [Cell] -> Constant -> [TermNode] -> (Integer -> Integer -> Bool) -> ExceptT KernelErr m Stack
    arithOpCheck source_call_id call_id premises ctx cells predicate args@[_, _] op
        = case addDefinitionConstraints boundArgs ctx of
            Nothing -> failure
            Just definedCtx
                | Just okay <- groundComparison premises groundResult -> if okay then success (definedCtx, cells) else failure
            Just definedCtx -> case liftConstraint candidate of
                Nothing -> case groundResult of
                    Right okay -> if okay then success (definedCtx, cells) else failure
                    Left "ill" -> failure
                    _ -> throwE (UnsupportedArithmeticConstraint candidate)
                Just lifted
                    | presburgerEntails (activePremises definedCtx) (_liftedFormula lifted, _freeOfLifted lifted)
                    -> success (definedCtx, cells)
                    | Right False <- groundResult
                    , nullArithStore premises
                    -> failure
                    | Left "ill" <- groundResult
                    -> failure
                    | not (storeSatisfiable (newCtx definedCtx))
                    -> failure
                    | otherwise
                    -> success (newCtx definedCtx, cells)
        where
            boundArgs = map (rewrite NF . bindVars (_TotalVarBinding ctx)) args
            candidate = arithmeticConstraintCandidate (_QueryCallId env) source_call_id predicate args boundArgs
            groundResult = case boundArgs of
                [lhs', rhs'] -> liftM2 op (evaluateA lhs') (evaluateA rhs')
                _ -> Left "non"
            activePremises definedCtx = arithAssumptions premises definedCtx
            newCtx definedCtx = definedCtx
                { _LeftConstraints = ArithmeticConstraint premises candidate : _LeftConstraints definedCtx
                , _ContextThreadId = call_id
                }
    arithOpCheck _ _ _ _ _ predicate args _
        = throwE (BadGoalGiven (foldlNApp (mkNCon predicate) args))
    eqOpCheck :: Context -> [Cell] -> [TermNode] -> Maybe (ExceptT KernelErr m Stack)
    eqOpCheck ctx cells [typeArg, lhs, rhs]
        | isNatTypeArg typeArg || mentionsArithmetic lhs || mentionsArithmetic rhs = case arithmeticEquality (bindVars (_TotalVarBinding ctx) lhs) (bindVars (_TotalVarBinding ctx) rhs) of
            ArithEqTrue -> Just (success (ctx, cells))
            ArithEqFalse -> Just failure
            ArithEqUnknown -> Nothing
    eqOpCheck _ _ _ = Nothing
    isNatTypeArg typeArg = case rewrite NF typeArg of
        NCon (TC (TC_Named "nat")) _ -> True
        _ -> False
    addEqualityDefinitions :: [TermNode] -> Context -> Maybe Context
    addEqualityDefinitions [typeArg, lhs, rhs] ctx
        | isNatTypeArg typeArg || mentionsArithmetic lhs || mentionsArithmetic rhs
        = addDefinitionConstraints
            [ bindVars (_TotalVarBinding ctx) lhs
            , bindVars (_TotalVarBinding ctx) rhs
            ]
            ctx
        | otherwise = Just ctx
    addEqualityDefinitions _ ctx = Just ctx
    primitivePrint :: Context -> [TermNode] -> [Cell] -> Stack -> ExceptT KernelErr m Stack
    primitivePrint ctx args cells stack
        | Just arg <- onePrimitiveArg args
        = do
            liftIO (withRuntimePhase env RuntimeService (_PrintPrimitive env (refineContext env ctx) (bindVars (_TotalVarBinding ctx) arg)))
            return ((ctx, cells) : stack)
    primitivePrint _ args _ _ = throwE (BadGoalGiven (foldlNApp (mkNCon (DC_Named "print")) args))
    primitiveFlex :: Context -> [TermNode] -> [Cell] -> Stack -> ExceptT KernelErr m Stack
    primitiveFlex ctx args cells stack
        | Just arg <- onePrimitiveArg args
        = return (if hasFlexibleHead (bindVars (_TotalVarBinding ctx) arg) then (ctx, cells) : stack else stack)
    primitiveFlex _ args _ _ = throwE (BadGoalGiven (foldlNApp (mkNCon (DC_Named "flex")) args))
    primitiveSame :: Context -> [TermNode] -> [Cell] -> Stack -> ExceptT KernelErr m Stack
    primitiveSame ctx [_, lhs, rhs] cells stack
        = return (if etaReduce (bindVars (_TotalVarBinding ctx) lhs) == etaReduce (bindVars (_TotalVarBinding ctx) rhs) then (ctx, cells) : stack else stack)
    primitiveSame _ args _ _ = throwE (BadGoalGiven (foldlNApp (mkNCon (DC_Named "==")) args))
    primitiveRead :: [Fact] -> Context -> [TermNode] -> [Cell] -> Stack -> ExceptT KernelErr m Stack
    primitiveRead hyps ctx args cells stack
        | Just arg <- onePrimitiveArg args
        = do
            mvalue <- liftIO (withRuntimePhase env RuntimeService (_ReadPrimitive env (refineContext env ctx) arg))
            case mvalue of
                Nothing -> return stack
                Just value -> case rewrite NF (bindVars (_TotalVarBinding ctx) arg) of
                    LVar x -> do
                        checked <- liftIO (readHostBinding env ctx args x value) >>= either (throwE . BackendError) return
                        maybe (return stack) bindPrimitive checked
                    arg'
                        | rewrite NF arg' == rewrite NF value -> return ((ctx, cells) : stack)
                    _ -> return stack
        where
            -- the value wakes the delayed equations that it instantiates,
            -- as a debugger assignment does
            bindPrimitive binding = assigned binding (ctx, cells) >>= maybe (return stack) (\(next, rest) -> execIs hyps next rest stack)
    primitiveRead _ _ args _ _ = throwE (BadGoalGiven (foldlNApp (mkNCon (DC_Named "read")) args))
    primitiveOracle :: [Fact] -> ScopeLevel -> Context -> [TermNode] -> [Cell] -> Stack -> ExceptT KernelErr m Stack
    primitiveOracle hyps level ctx args cells stack
        | Just question <- askedQuestion ctx hyps level args
        = do
            frames <- liftIO (readIORef (_StackRef env))
            (answer, context, pending) <- liftIO (answerOracle env ctx question (return frames))
            if not answer then
                return stack
            else if Map.null (unVarBinding pending) then
                return ((context, cells) : stack)
            else do
                let equations = [mkLVar variable :=?=: value | (variable, value) <- Map.toList (unVarBinding pending)]
                    previous = [equation | DisagreementConstraint equation <- _LeftConstraints context]
                solved <- lift (runHOPU (_CurrentLabeling context) (equations ++ previous))
                case solved of
                    Nothing -> return stack
                    Just (remaining, HopuSol labeling binding) -> do
                        let constraints =
                                [ constraint
                                | constraint <- zonkLVar binding (_LeftConstraints context)
                                , case constraint of
                                    DisagreementConstraint _ -> False
                                    _ -> True
                                ]
                            next = context { _TotalVarBinding = binding <> _TotalVarBinding context, _CurrentLabeling = labeling, _LeftConstraints = map DisagreementConstraint remaining ++ constraints }
                        execIs hyps next (map (zonkLVar binding) cells) stack
    primitiveOracle _ _ _ args _ _ = throwE (BadGoalGiven (foldlNApp (mkNCon (DC_Named "oracle")) args))
    onePrimitiveArg :: [TermNode] -> Maybe TermNode
    onePrimitiveArg [arg] = Just arg
    onePrimitiveArg [_typeArg, arg] = Just arg
    onePrimitiveArg _ = Nothing
    search :: Map.Map Constant [Fact] -> [Fact] -> ArithStore -> ScopeLevel -> Constant -> [TermNode] -> CallId -> Context -> [Cell] -> ExceptT KernelErr m Stack
    search facts hyps premises level predicate args source_call_id ctx cells
        = do
            call_id <- getUnique
            let arithOpCheck' = arithOpCheck source_call_id call_id premises ctx cells predicate args
            case predicate of
                DC DC_eq -> do
                    -- A bare equality antecedent keeps its ordinary local
                    -- hypothesis role.  A nonempty local match block has strict
                    -- precedence; only an empty block falls through to the
                    -- arithmetic/program built-in.  In particular,
                    -- @((1 = 2) => (1 = 2))@ succeeds by assumption without a
                    -- duplicate built-in answer.  Strict natural definedness
                    -- is independent of that dispatch precedence, so both the
                    -- local block and the fallback share the same enriched
                    -- context.
                    case addEqualityDefinitions args ctx of
                        Nothing -> failure
                        Just equalityCtx -> do
                            localAnswers <- searchHypsWith equalityCtx call_id
                            if null localAnswers then do
                                arithmeticAnswer <- sequence (eqOpCheck equalityCtx cells args)
                                case arithmeticAnswer of
                                    Just answer -> return answer
                                    Nothing -> searchProgramWith equalityCtx call_id
                            else
                                return localAnswers
                DC DC_ge -> arithOpCheck' (>=)
                DC DC_gt -> arithOpCheck' (>)
                DC DC_le -> arithOpCheck' (<=)
                DC DC_lt -> arithOpCheck' (<)
                _ -> searchFacts call_id
        where
            searchFacts call_id = do
                ans2 <- searchProgram call_id
                ans3 <- searchHyps call_id
                return (ans2 ++ ans3)

            searchProgram call_id = searchProgramWith ctx call_id
            searchProgramWith activeCtx call_id = fmap concat (forM (Map.findWithDefault [] predicate facts) (matchFact activeCtx call_id))
            searchHyps call_id = searchHypsWith ctx call_id
            searchHypsWith activeCtx call_id = fmap concat (forM hyps (matchFact activeCtx call_id))

            matchFact activeCtx call_id fact = do
                ((goal', new_goal), labeling) <- runStateT (instantiateFact fact level) (_CurrentLabeling activeCtx)
                case unfoldlNApp (rewrite HNF goal') of
                    (NCon predicate' _, args')
                        | predicate == predicate' -> do
                            hopu_output <- if length args == length args' then lift (runHOPU labeling (zipWith (:=?=:) args args' ++ [ eqn | DisagreementConstraint eqn <- _LeftConstraints activeCtx ])) else throwE (BadFactGiven goal')
                            let new_level = level
                                new_hyps = hyps
                            case hopu_output of
                                Nothing -> failure
                                Just (new_disagreements, HopuSol new_labeling subst) -> do
                                    let zonkedConstraints = zonkLVar subst (_LeftConstraints activeCtx)
                                        otherConstraints =
                                            [ constraint
                                            | constraint <- zonkedConstraints
                                            , case constraint of
                                                DisagreementConstraint _ -> False
                                                _ -> True
                                            ]
                                        baseCtx = activeCtx
                                            { _TotalVarBinding = subst <> _TotalVarBinding activeCtx
                                            , _CurrentLabeling = new_labeling
                                            , _LeftConstraints = map DisagreementConstraint new_disagreements ++ otherConstraints
                                            , _ContextThreadId = call_id
                                            }
                                        baseCells = zonkMatchedCells subst (mkCell facts new_hyps premises new_level new_goal call_id : cells)
                                    if null (_LeftConstraints baseCtx) then
                                        success (baseCtx, baseCells)
                                    else case settleEvaluationConstraints baseCtx baseCells of
                                        Nothing -> failure
                                        Just settled -> success settled
                    _ -> failure
    dispatch :: Context -> Map.Map Constant [Fact] -> [Fact] -> ArithStore -> ScopeLevel -> (TermNode, [TermNode]) -> CallId -> [Cell] -> Stack -> ExceptT KernelErr m Satisfied
    dispatch ctx facts hyps premises level (NCon predicate _, args) call_id cells stack
        | DC (DC_LO logical_operator) <- predicate
        = do
            liftIO $ case (logical_operator, args) of
                (LO_debug, [label]) -> modifyIORef' (_RuntimeControl env) (\control -> control { runtimeLabel = Just label })
                (LO_cut, []) -> modifyIORef' (_RuntimeControl env) $ \control -> case runtimeStep control of
                    Nothing -> control
                    Just boundary -> control { runtimeStep = Just boundary { stepOlder = length [() | (older, _) <- drop (length stack - stepOlder boundary) stack, _ContextThreadId older < call_id] } }
                _ -> return ()
            stack' <- runLogicalOperator logical_operator args ctx facts hyps premises level call_id cells stack
            go stack'
        | predicate == DC (DC_Named "print")
        = do
            stack' <- primitivePrint ctx args cells stack
            go stack'
        | predicate == DC (DC_Named "read")
        = do
            stack' <- primitiveRead hyps ctx args cells stack
            go stack'
        | predicate == DC (DC_Named "flex")
        = do
            stack' <- primitiveFlex ctx args cells stack
            go stack'
        | predicate == DC (DC_Named "==")
        = do
            stack' <- primitiveSame ctx args cells stack
            go stack'
        | predicate == DC (DC_Named "oracle")
        = do
            stack' <- primitiveOracle hyps level ctx args cells stack
            go stack'
        | otherwise
        = do
            stack' <- search facts hyps premises level predicate args call_id ctx cells
            go (stack' ++ stack)
    dispatch ctx _facts _hyps premises _level (NPresburgerCheck rep freeOf _, []) _call_id cells stack
        = go (runPresburger rep freeOf premises ctx cells stack)
    dispatch ctx facts hyps premises level (t, ts) call_id cells stack
        = throwE (BadGoalGiven (foldlNApp t ts))
    applyPending :: Stack -> ExceptT KernelErr m Stack
    applyPending = fmap fst . applyPendingWithHead
    applyPendingWithHead :: Stack -> ExceptT KernelErr m (Stack, Bool)
    applyPendingWithHead [] = return ([], False)
    applyPendingWithHead st = do
        pending <- liftIO (readIORef (_PendingSubst env))
        if Map.null (unVarBinding pending) then
            return (st, True)
        else do
            liftIO (writeIORef (_PendingSubst env) (VarBinding Map.empty))
            changed <- mapM (\frame -> assigned (activePending pending frame) frame) st
            liftIO $ modifyIORef' (_RuntimeControl env) $ \control -> case runtimeStep control of
                Nothing -> control
                Just boundary -> control { runtimeStep = Just boundary { stepOlder = length (catMaybes (drop (length st - stepOlder boundary) changed)) } }
            return (catMaybes changed, maybe False (const True) (head changed))
    -- An edit of a local variable has no target in alternatives predating
    -- that variable. Query identities and type dependencies remain roots.
    activePending pending (ctx, cells) = VarBinding (Map.filterWithKey (\variable _ -> live variable) (unVarBinding pending)) where
        labeling = _CurrentLabeling ctx
        known = free_lvars `Set.union` stateVariables ctx cells mempty `Set.union` labelingTypeVariables labeling
        live variable = variable `Set.member` known || case variable of
            LV_Named _ -> True
            _ -> IntMap.member (lvKey variable) (_VarLabel labeling)
    -- A value that the host gives to a variable: a debugger assignment, which
    -- goes into every frame, or what `read` binds in its own frame. In a
    -- frame it wakes the delayed equations that it instantiates: they are
    -- solved again, and a frame whose equations have no solution any more is
    -- gone, as the branch of the V1 engine is.
    assigned :: LogicVarSubst -> (Context, [Cell]) -> ExceptT KernelErr m (Maybe (Context, [Cell]))
    assigned pending (ctx, cells)
        | before == [(lhs, rhs) | lhs :=?=: rhs <- after]
        = return (if null (_LeftConstraints ctx') then Just (ctx', cells') else settleEvaluationConstraints ctx' cells')
        | otherwise = do
            solved <- lift (runHOPU (_CurrentLabeling ctx') after)
            return $ do
                (remaining, HopuSol labeling binding) <- solved
                let others = [constraint | constraint <- zonkLVar binding (_LeftConstraints ctx'), not (delayed constraint)]
                    next = (zonkLVar binding ctx') { _CurrentLabeling = labeling, _LeftConstraints = map DisagreementConstraint remaining ++ others }
                if null (_LeftConstraints next) then Just (next, map (zonkLVar binding) cells') else settleEvaluationConstraints next (map (zonkLVar binding) cells')
        where
            ctx' = zonkLVar pending ctx
            cells' = map (zonkLVar pending) cells
            before = [(lhs, rhs) | DisagreementConstraint (lhs :=?=: rhs) <- _LeftConstraints ctx]
            -- A substitution composes existing bindings; it does not check
            -- that an older alternative agrees with a persistent edit. In
            -- particular, an old X := a would otherwise hide the new X := b.
            -- Solve those overlaps before retaining this alternative.
            after = overlaps ++ [equation | DisagreementConstraint equation <- _LeftConstraints ctx']
            overlaps =
                [ bindVars (_TotalVarBinding ctx) (mkLVar variable) :=?=: bindVars (_TotalVarBinding ctx) value
                | (variable, value) <- Map.toList (unVarBinding pending)
                , Map.member variable (unVarBinding (_TotalVarBinding ctx))
                ]
            delayed constraint = case constraint of
                DisagreementConstraint _ -> True
                _ -> False
    go :: Stack -> ExceptT KernelErr m Satisfied
    go raw_stack = do
        stack0 <- applyPending raw_stack
        control <- liftIO (readIORef (_RuntimeControl env))
        if runtimeQuit control then return False else case runtimeStep control of
            Just active
                | stepFailed active || null (drop (stepOlder active) stack0) -> stepFailure active stack0
            _ -> progress stack0
    stepFailure :: StepBoundary -> Stack -> ExceptT KernelErr m Satisfied
    stepFailure boundary remaining
        | stepFailed boundary && stepNotified boundary = return False
        | otherwise = do
            generation <- liftIO $ do
                writeIORef (_StackRef env) remaining
                modifyIORef' (_RuntimeControl env) (\control -> control { runtimeStep = Just boundary { stepFailed = True, stepNotified = False } })
                runtimeRestores <$> readIORef (_RuntimeControl env)
            liftIO $ withRuntimePhase env RuntimeStepFailure (_Debugger env env (stepStart boundary) { debugReason = StepFailed (stepIdentity boundary) })
            control <- liftIO (readIORef (_RuntimeControl env))
            case runtimeStep control of
                Just current
                    | runtimeRestores control == generation && stepIdentity current == stepIdentity boundary && stepFailed current -> do
                        liftIO $ modifyIORef' (_RuntimeControl env) (\state -> state { runtimeStep = Just current { stepNotified = True } })
                        return False
                _ -> liftIO (readIORef (_StackRef env)) >>= go
    progress :: Stack -> ExceptT KernelErr m Satisfied
    progress stack0 = case stack0 of
        [] -> liftIO (writeIORef (_StackRef env) []) >> return False
        (ctx, cells) : stack -> do
            liftIO $ writeIORef (_StackRef env) ((ctx, cells) : stack)
            generation <- liftIO (runtimeRestores <$> readIORef (_RuntimeControl env))
            debugged <- liftIO $ do
                enabled <- readIORef (_debuggindModeOn ctx)
                current <- readIORef (_RuntimeControl env)
                let dbg = runtimeReplayStop current || enabled && maybe True stepStarted (runtimeStep current)
                verbose <- readIORef (_VerboseTyping env)
                when dbg $ do
                    let shown = refineContext env ctx
                        frames = (shown, cells) : stack
                    writeIORef (_StackRef env) frames
                    modifyIORef' (_NameCacheRef env) (recordVisibleLVarHints frames)
                    control <- readIORef (_RuntimeControl env)
                    let reason = maybe DebugTrace DebugGoal (runtimeLabel control)
                        event = DebugEvent reason shown frames (showsCurrentState (_NotationDB env) (_ProgramKindEnv env) verbose free_lvars (_TypeInfo env) shown cells stack "")
                    withRuntimePhase env RuntimeDebugger (_Debugger env env event)
                -- The label describes this state, even if tracing is disabled.
                -- Advancing past it must not label a later, unrelated trace.
                modifyIORef' (_RuntimeControl env) (\state -> if runtimeRestores state == generation then state { runtimeLabel = Nothing, runtimeReplayStop = False } else state)
                return dbg
            stackAfterCb <- liftIO $ do
                updatedStack <- readIORef (_StackRef env)
                -- The debugger callback may replace the public stack ref.
                -- Re-establish the same domain invariant enforced at the
                -- runTransition entry point before inspecting any frame.
                if debugged
                    then assertStack updatedStack `seq` return updatedStack
                    else return updatedStack
            restored <- liftIO ((/= generation) . runtimeRestores <$> readIORef (_RuntimeControl env))
            if restored then go stackAfterCb else do
                (stack1, currentSurvived) <- applyPendingWithHead stackAfterCb
                boundary <- liftIO (runtimeStep <$> readIORef (_RuntimeControl env))
                if not currentSurvived then go stack1 else case boundary of
                    Just active
                        | stepFailed active || null (drop (stepOlder active) stack1) -> stepFailure active stack1
                    _ -> do
                        case boundary of
                            Just active
                                | not (stepStarted active) -> liftIO $ modifyIORef' (_RuntimeControl env) (\control -> control { runtimeStep = fmap (\current -> current { stepStarted = True }) (runtimeStep control) })
                            _ -> return ()
                        -- The answer callback reads the retained alternatives
                        -- from this reference. Publish persistent assignments
                        -- before it removes the current answer frame.
                        liftIO (writeIORef (_StackRef env) stack1)
                        advance stack1
    advance :: Stack -> ExceptT KernelErr m Satisfied
    advance stack1 = case stack1 of
        [] -> return False
        (ctx', cells') : stack' -> case cells' of
            [] -> case settleEvaluationConstraints ctx' [] of
                Nothing -> go stack'
                Just (answerCtx, [])
                    | storeSatisfiable answerCtx -> do
                        want_more <- liftIO (withRuntimePhase env RuntimeService (_Answer env (refineContext env answerCtx)))
                        if want_more then go stack' else return True
                    | otherwise -> go stack'
                Just (_, _ : _) -> go stack'
            Cell facts hyps premises level goal call_id : rest_cells -> dispatch ctx' facts hyps premises level (unfoldlNApp (rewrite HNF goal)) call_id rest_cells stack'

-- Runtime facts and imported clause bodies carry source coordinates from a
-- different file than the active query.  Only the root query call-id is
-- therefore allowed to contribute a location to a query diagnostic; direct
-- embedders (Nothing) and clause calls remain truly locationless.
arithmeticConstraintCandidate :: Maybe CallId -> CallId -> Constant -> [TermNode] -> [TermNode] -> TermNode
arithmeticConstraintCandidate queryCallId callId predicate sourceArgs boundArgs
    = List.foldl' (mkNAppLoc candidateLoc) (mkNConLoc candidateLoc predicate) boundArgs
    where
        candidateLoc
            | queryCallId == Just callId = case mapMaybe getNodeSLoc sourceArgs of
                [] -> Nothing
                firstLoc : restLocs -> Just (List.foldl' (<>) firstLoc restLocs)
            | otherwise = Nothing

eraseTrivialBinding :: LogicVarSubst -> LogicVarSubst
eraseTrivialBinding = VarBinding . loop . unVarBinding where
    hasName :: LogicVar -> Bool
    hasName (LV_Named _) = True
    hasName _ = False
    loop :: Map.Map LogicVar TermNode -> Map.Map LogicVar TermNode
    loop = foldr go <*> Map.toAscList
    go :: (LogicVar, TermNode) -> Map.Map LogicVar TermNode -> Map.Map LogicVar TermNode
    go (v, t) = maybe id (dispatch v) (tryMatchLVar t)
    dispatch :: LogicVar -> LogicVar -> Map.Map LogicVar TermNode -> Map.Map LogicVar TermNode
    dispatch v1 v2
        | v1 == v2 = loop . Map.delete v1
        | not (hasName v1) = loop . Map.map (flatten (VarBinding { unVarBinding = Map.singleton v1 (LVar v2) })) . Map.delete v1
        | otherwise = id
    tryMatchLVar :: TermNode -> Maybe LogicVar
    tryMatchLVar t
        = case viewNestedNLam (rewrite NF t) of
            (n, t') -> case unfoldlNApp t' of
                (LVar v, ts) -> if ts == map mkNIdx [n - 1, n - 2 .. 0] then Just v else Nothing
                _ -> Nothing
