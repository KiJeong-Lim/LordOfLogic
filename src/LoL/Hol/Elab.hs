module LoL.Hol.Elab where

import Control.Applicative ((<|>))
import Control.Exception (evaluate)
import Control.Monad (foldM, replicateM, zipWithM)
import Control.Monad.Trans.Class (lift)
import Control.Monad.Trans.State.Strict
import Data.List (elemIndex, elemIndices, find, foldl', nub)
import Data.Maybe (fromMaybe, isJust, isNothing)
import System.Timeout (timeout)
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import qualified LoL.Core as Core
import LoL.Diagnostic
import qualified LoL.Env as Env
import qualified LoL.Pretty as Pretty
import LoL.Front.Syntax
import LoL.Hol.Embed
import LoL.Hol.Session
import Hol.V2.Embedding (LogicalOperator (..))
import Hol.V2.Embedding

-- This module transports syntax. All typing, reduction and solving occurs
-- in elab.hol, followed by the ordinary independent ground admission path.
data Encoded
    = Encoded
        { encodedTerm  :: TermNode
        , encodedSpans :: Map.Map Integer Span
        , encodedHoles :: [LogicVar]
        }
    deriving ()

-- All three components come back as closed Hol data. The proposal is still
-- untrusted: Env checks the complete scheme in the independent kernel before
-- publishing it. Declaration-local parameter indices are not runtime UIDs.
-- proposedMarks say of a term that is read without a body (e_u_query of
-- elab.hol) where each universe marker ended: its kind and its level in
-- proposedUniverses. A marker of kind 1 or of kind 6 and above is a universe
-- that nothing settles; the parameter of another one is a cell that was
-- left, which the proof of a theorem may settle.
data UniverseProposal
    = UniverseProposal
        { proposedTerm      :: Core.Term
        , proposedType      :: Core.Term
        , proposedUniverses :: Core.UniverseContext
        , proposedRefresh   :: Refresh
        , proposedMarks     :: [(Integer, Core.Level)]
        }
    deriving (Eq, Show)

-- The source nodes whose type is the value of an implicit argument and gets
-- a universe of its own there (e_refresh of elab.hol, Rocq's
-- refresh_universes): where each is written, and for which name of its
-- binder groups it is read.
type Refresh = Set.Set (Span, [Int])

-- What the proof program is given of the statement of a theorem
-- (p_universe_statement of proof.hol): the number of its parameters, the
-- kinds of its markers, its constraints and its mode, as an elaboration
-- gets them, and the statement as it is written.
data Statement
    = Statement
        { statementPrefix :: [TermNode]
        , statementRaw    :: TermNode
        , statementSpans  :: Map.Map Integer Span
        , statementNames  :: [Core.Hint]
        , statementHints  :: TermNode
        , statementCore   :: Maybe Core.Term
        , statementMode   :: Integer
        }
    deriving ()

-- The universes that a declaration writes. Its names are all the universes
-- that it has. With a constraint clause, `@{u v | ...}`, its constraints are
-- all of them too (closed). Without the clause, `@{u v}`, the elaborator adds
-- the constraints that the declaration needs (open), as Rocq reads `@{u v}`.
data UniverseRequest
    = ClosedUniverses Core.UniverseContext
    | OpenUniverses Core.UniverseContext
    deriving (Eq, Show)

requestedUniverses :: UniverseRequest -> Core.UniverseContext
requestedUniverses request = case request of
    ClosedUniverses context -> context
    OpenUniverses context -> context

universeRequest :: Env.Env -> UniverseDecl -> Either Diagnostic UniverseRequest
universeRequest environment declaration = (if universeOpen declaration then OpenUniverses else ClosedUniverses) <$> universeContext environment (Just declaration)

-- The mode that the elaborator is given: 0 infers the parameters and the
-- constraints, 1 checks under the written context, 2 keeps the written
-- parameters and completes the constraints.
requestMode :: Maybe UniverseRequest -> (Integer, Core.UniverseContext)
requestMode request = case request of
    Nothing -> (0, Core.emptyUniverses)
    Just (ClosedUniverses context) -> (1, context)
    Just (OpenUniverses context) -> (2, context)

-- Surface universe syntax is transported to declaration-local indices. This
-- neither solves constraints nor establishes that the context is consistent.
universeContext :: Env.Env -> Maybe UniverseDecl -> Either Diagnostic Core.UniverseContext
universeContext _ Nothing = Right Core.emptyUniverses
universeContext env (Just declaration) = do
    case find (\name -> length (filter ((== nameText name) . nameText) names) > 1) names of
        Just duplicate -> Left (universeError (nameSpan duplicate) ("duplicate universe parameter '" ++ nameText duplicate ++ "'"))
        Nothing -> return ()
    relations <- mapM relation (universeRelations declaration)
    return (Core.UniverseContext (map nameText names) relations)
    where
        names = universeBinders declaration
        parameters = universeScope env (map nameText names)
        relation (left, operator, right) = do
            lhs <- stepsAbove left
            rhs <- atomicUniverseLevel parameters right
            case nameText operator of
                "<=" -> return (Core.UniverseLe lhs rhs)
                "<" -> return (Core.UniverseLe (Core.Successor lhs) rhs)
                "=" -> return (Core.UniverseEq lhs rhs)
                ">=" -> return (Core.UniverseLe rhs lhs)
                ">" -> return (Core.UniverseLe (Core.Successor rhs) lhs)
                _ -> Left (universeError (nameSpan operator) "expected a universe comparison")
        -- The left side may be some steps above an atomic level, `u+1 < v`.
        stepsAbove syntax = case levelForm syntax of
            LOffset inner sign _
                | nameText sign == "+" -> atomicUniverseLevel parameters inner >> universeLevel parameters syntax
            _ -> atomicUniverseLevel parameters syntax

universeError :: Span -> String -> Diagnostic
universeError at message = Diagnostic at "LoL-UniverseError" "E-Universe" message []

-- The right side of a written constraint is an atomic level, and so is what
-- the steps of its left side are above. Sorts and instances may write an
-- expression (universeLevel).
atomicUniverseLevel :: (String -> Maybe Core.Level) -> LevelSyntax -> Either Diagnostic Core.Level
atomicUniverseLevel parameters syntax = case levelForm syntax of
    LNumber _ -> universeLevel parameters syntax
    LName _ -> universeLevel parameters syntax
    _ -> Left (universeError (levelSpan syntax) "expected a closed level or a declared universe parameter")

-- A default belongs to its family across module aliases and object reloads.
universeScope :: Env.Env -> [String] -> String -> Maybe Core.Level
universeScope env locals = resolve where
    local = Map.fromList (zip locals (map Core.Parameter [0 ..]))
    resolve name = Map.lookup name local <|> qualified (break (== '.') (reverse name))
    qualified (reversedHint, '.' : reversedOwner) = do
        Core.GlobalInd b 0 <- Map.lookup (reverse reversedOwner) (Env.envNames env)
        entry <- Map.lookup b (Env.envDecls env)
        Env.Inductive _ families <- Just (Env.entryDecl entry)
        if any Env.familyTemplate families then Core.DefaultLevel b <$> elemIndex (reverse reversedHint) (Pretty.templateHints Pretty.Surface (Core.universeNames (Env.entryUniverses entry))) else Nothing
    qualified _ = Nothing

universeLevel :: (String -> Maybe Core.Level) -> LevelSyntax -> Either Diagnostic Core.Level
universeLevel parameters syntax = case levelForm syntax of
    LNumber number
        | number >= 0 -> Right (Core.Closed number)
        | otherwise -> Left (universeError (levelSpan syntax) "a universe level cannot be negative")
    LName name -> case parameters (nameText name) of
        Just value -> Right value
        Nothing -> Left (universeError (nameSpan name) ("unknown universe parameter '" ++ nameText name ++ "'"))
    LHole -> Left (universeError (levelSpan syntax) "an explicit universe constraint cannot contain a level hole")
    LOffset inner operator amount
        | nameText operator == "+" && amount >= 0 -> do
            level <- universeLevel parameters inner
            return (successors amount level)
        | otherwise -> Left (universeError (levelSpan syntax) "expected a nonnegative universe offset")
    LMaximum operator left right
        | nameText operator == "max" -> Core.Maximum <$> universeLevel parameters left <*> universeLevel parameters right
        | otherwise -> Left (universeError (nameSpan operator) "expected the universe maximum operator")
    where
        successors count level
            | count <= 0 = level
            | otherwise = Core.Successor (successors (count - 1) level)

-- The next source-node number, the spans of the nodes, the output variables,
-- the block and parameter count of a constructor type and whether that type
-- has a `fix`, whether a wildcard template is being read, and the holes of
-- block parameters that were made so far, the latest first.
type Build = StateT (Integer, Map.Map Integer Span, [LogicVar], Maybe (Core.ConstId, Int, Bool), Bool, [TermNode], ProofEncoding, Maybe UniverseBuild) (Either Diagnostic)
data ProofEncoding = OrdinaryEncoding | EagerProof | DeferredProof Int (Set.Set String) deriving (Eq)

-- The universes of the declaration that is being read. Every level that the
-- source leaves out gets a marker, and markerKinds are the kinds of the
-- markers, the latest first. The elaborator reads them (e_u_slots):
-- 0, a level that is a hole or an instance that is left out: a cell that an
-- equation or what is below it settles;
-- 1, a `Type` without a level in a declaration that names no universe: a
-- universe of its own, as Rocq makes one of it;
-- 2 and 3, the conclusion of the arity of an inductive type that is a `Type`
-- without a level (buildingConclusion is where that one is written and
-- whether its family has two constructors or more, while the arity is read):
-- its level is found from the constructors;
-- 4, a conclusion that is a hole (`Type@{_}`) of a family with two
-- constructors or more: a cell that is at least Type@{0}.
-- buildingBare is how a `Type` without a level is read anywhere else.
-- The binders of a definition, of a `fix` and of an inductive type are read
-- once by Rocq and more than once here (with the type and with the body,
-- with the arity and with each constructor): bareMarkers gives a level that
-- is left out the marker that it got before, by where it is written, by
-- binderPath, which says for which name of its binder groups it is read
-- (`(A B : Type)` has two universes), and by its place in an instance. The
-- parameters of the families of a block are also read once by Rocq, and each
-- family writes them here: bareTrace is the markers that were given, the
-- latest first, and bareReplay the ones to give next where there is none yet.
-- A node of refreshNodes gets a spare universe, a marker of kind 6 + the
-- number of the node, after the markers of what is below it: Rocq makes that
-- universe when it has read the node. The node that is read again (a
-- binder) carries the number of the first reading (refreshSpares), so that
-- both find the one universe. nodeKeys says of each node number where the
-- node is written, for the report of the elaborator.
data UniverseBuild
    = UniverseBuild
        { buildingContext    :: Core.UniverseContext
        , nextLevelMarker    :: Integer
        , buildingBare       :: BareType
        , buildingConclusion :: Maybe (Span, Bool)
        , markerKinds        :: [Integer]
        , markerPositions    :: [Integer]
        , bareMarkers        :: Map.Map (Span, [Int], Int) Integer
        , binderPath         :: [Int]
        , bareTrace          :: [Integer]
        , bareReplay         :: [Integer]
        , refreshNodes       :: Refresh
        , refreshSpares      :: Map.Map (Span, [Int]) Integer
        , nodeKeys           :: Map.Map Integer (Span, [Int])
        }
    deriving ()

-- A declaration that names its universes leaves out no level of a `Type`
-- that it writes: Rocq makes a universe of such a `Type` that nothing can
-- settle, and refuses it as unbound. One that names none gets a universe
-- for it. A term of a proof command gets a universe of the proof that
-- nothing settles (kind 5).
data BareType
    = BareRefused
    | BareUniverse
    | BareCell
    deriving (Eq)

bareOf :: Integer -> BareType
bareOf explicit = if explicit == 0 then BareUniverse else BareRefused

newUniverseBuild :: Core.UniverseContext -> Integer -> BareType -> UniverseBuild
newUniverseBuild context frontier bare = UniverseBuild context frontier bare Nothing [] [] Map.empty [] [] [] Set.empty Map.empty Map.empty

refreshing :: Refresh -> UniverseBuild -> UniverseBuild
refreshing nodes universe = universe { refreshNodes = nodes }

-- Read the type of one name of a binder group.
withinBinder :: Int -> Build a -> Build a
withinBinder ordinal action = enter (ordinal :) *> action <* enter (drop 1) where
    enter change = modify (\(next, positions, holes, constructor, template, defaults, proof, universes) -> (next, positions, holes, constructor, template, defaults, proof, fmap (\universe -> universe { binderPath = change (binderPath universe) }) universes))

-- What the elaborator is given of the universes of a declaration: the number
-- of its parameters before elaboration (the universes that it names or, when
-- it names none, one for each marker of kind 1), the kinds of its markers,
-- its constraints and its mode. A spare universe (kind 6 and above) is a
-- parameter too.
universePrefix :: Integer -> Core.UniverseContext -> UniverseBuild -> [TermNode]
universePrefix explicit context universe = [natural count, builtList (kindOf "nat") (map natural kinds), embedUniverseConstraints (Core.universeConstraints context), natural explicit] where
    kinds = reverse (markerKinds universe)
    count = if explicit == 0 then toInteger (length (filter (\kind -> kind == 1 || kind >= 6) kinds)) else toInteger (length (Core.universeNames context))

type Scope = [(String, (Maybe Int, [Bool]))]

scopeShape :: Scope -> [Maybe Int]
scopeShape = map (fst . snd)

local :: String -> (String, (Maybe Int, [Bool]))
local name = (name, (Nothing, []))

rawList :: [TermNode] -> TermNode
rawList = embedList (kindOf "raw")

raw :: String -> [TermNode] -> TermNode
raw = foldlNApp . named

-- These helpers only assemble the encoder's generated children. Complete
-- trees are checked at encode and proposeCompleting; the existing raw,
-- rawList and Embed.embedList entry points still check arbitrary input.
-- No Core typing, reduction or elaboration judgment is performed here.
builtApply :: TermNode -> [TermNode] -> TermNode
builtApply = foldl' (mkNAppLocUnchecked Nothing)

builtRaw :: String -> [TermNode] -> TermNode
builtRaw = builtApply . named

builtList :: TermNode -> [TermNode] -> TermNode
builtList kind = foldr (\item rest -> builtApply (mkNCon DC_Cons) [kind, item, rest]) (builtApply (mkNCon DC_Nil) [kind])

builtRawList :: [TermNode] -> TermNode
builtRawList = builtList (kindOf "raw")

builtLambda :: Maybe SmallId -> TermNode -> TermNode
builtLambda hint body = NLam hint noLamType body Nothing

encode :: Env.Env -> Term -> Either Diagnostic Encoded
encode env source = do
    (value, (_, positions, holes, _, _, _, _, _)) <- runStateT (encodeUnder env [] source) (0, Map.empty, [], Nothing, False, [], OrdinaryEncoding, Nothing)
    assertNonnegativeIndices value `seq` return (Encoded value positions holes)

-- Proof inputs are templates: Hol e_fresh creates their scoped cells. The
-- caller supplies a monotonically increasing source-position origin, so holes
-- from distinct commands cannot acquire one another's source locations.
encodeProofTerm :: Env.Env -> Integer -> [(String, TermNode)] -> Term -> Either Diagnostic Encoded
encodeProofTerm env origin locals = encodeProofWith EagerProof env origin locals

-- Names outside this template's lexical binders can be introduced by an
-- earlier component of a compound tactic. Hol resolves them in that context.
-- Display aliases for older shadowed locals remain explicit captured values.
encodeProofDeferred :: Env.Env -> Integer -> [(String, TermNode)] -> Set.Set String -> Term -> Either Diagnostic Encoded
encodeProofDeferred env origin locals aliases = encodeProofWith (DeferredProof (length locals) aliases) env origin locals

encodeProofWith :: ProofEncoding -> Env.Env -> Integer -> [(String, TermNode)] -> Term -> Either Diagnostic Encoded
encodeProofWith mode env origin locals source = (\(encoded, _, _) -> encoded) <$> encodeProofWithUniverses mode env origin locals Nothing 0 source

-- Every raw term in a command shares this marker namespace. The returned
-- frontier is passed to the next operand, so independent type holes cannot
-- alias merely because each syntax fragment was encoded separately. The
-- returned plan lists each marker position followed by its kind, in creation order.
encodeProofWithUniverses :: ProofEncoding -> Env.Env -> Integer -> [(String, TermNode)] -> Maybe Core.UniverseContext -> Integer -> Term -> Either Diagnostic (Encoded, Integer, [Integer])
encodeProofWithUniverses mode env origin locals context frontier source = do
    let universes = (\given -> newUniverseBuild given frontier BareCell) <$> context
    (value, (_, positions, holes, _, _, _, _, final)) <- runStateT (encodeUnder env (map (local . fst) locals) source) (origin, Map.empty, [], Nothing, True, [], mode, universes)
    let decorated = proofNames value
        abstracted = foldr (\_ body -> builtLambda Nothing body) decorated locals
        closed = builtApply abstracted (reverse (map snd locals))
    assertNonnegativeIndices closed `seq` return (Encoded closed positions holes, maybe frontier nextLevelMarker final, maybe [] commandMarkers final)
    where
        commandMarkers universe = concat (zipWith (\position kind -> [position, kind]) (reverse (markerPositions universe)) (reverse (markerKinds universe)))

-- Only raw binder bodies receive names. r_ref contains embedded Core and is
-- deliberately opaque. The outer binder of r_fix is a function-index map,
-- not a tm local; its bodies may still contain ordinary raw binders.
proofNames :: TermNode -> TermNode
proofNames term = case spine term [] of
    (NCon (DC (DC_Named "r_ref")) _, _) -> term
    (NCon (DC (DC_Named "r_fix")) _, [chosen, positions, types, bodies, defaults]) ->
        builtRaw "r_fix" [chosen, positions, proofNames types, fixed bodies, defaults]
    _ -> case term of
        NApp function argument location -> NApp (proofNames function) (proofNames argument) location
        NLam hint typ body location -> NLam hint typ (namedBody hint (proofNames body)) location
        _ -> term
    where
        spine (NApp function argument _) rest = spine function (argument : rest)
        spine head rest = (head, rest)
        fixed (NLam hint typ body location) = NLam hint typ (proofNames body) location
        fixed other = proofNames other
        namedBody hint body = case recoverHint hint of
            "" -> body
            name -> builtRaw "p_named" [embedList (kindOf "char") (map (mkNCon . DC_ChrL) name), mkNIdx 0, body]

positionOf :: Span -> Build Integer
positionOf location = do
    (number, positions, holes, parameters, template, defaults, proof, universes) <- get
    put (number + 1, Map.insert number location positions, holes, parameters, template, defaults, proof, universes)
    return number

failure :: Span -> String -> String -> Build a
failure at code message = lift (Left (Diagnostic at "LoL-ElabError" code message []))

scopeFailure :: Name -> String -> Build a
scopeFailure name message = lift (Left (Diagnostic (nameSpan name) "LoL-ScopeError" "H-Name" message [nameText name]))

resolveGlobal :: Env.Env -> Name -> Build Core.Global
resolveGlobal env name = maybe (scopeFailure name ("unknown name: " ++ nameText name)) return (Map.lookup (nameText name) (Env.envNames env))

reference :: Env.Env -> Scope -> Bool -> Name -> Build TermNode
reference env scope explicit name = do
    (_, _, _, _, _, _, proof, _) <- get
    let index = elemIndex (nameText name) (map fst scope)
        deferred = case proof of
            DeferredProof count _ -> '.' `notElem` nameText name && maybe True (>= length scope - count) index
            _ -> False
        alias = case proof of
            DeferredProof _ aliases -> Set.member (nameText name) aliases
            _ -> False
        label = builtList (kindOf "char") (map (mkNCon . DC_ChrL) (nameText name))
        global = case Map.lookup (nameText name) (Env.envNames env) of
            Just found -> referenceGlobal env scope (nameSpan name) explicit found
            Nothing
                | deferred -> return (builtRaw "p_missing" [label])
                | otherwise -> scopeFailure name ("unknown name: " ++ nameText name)
    case index of
        Just position
            | not deferred || alias -> do
                modes <- referenceModes scope (nameSpan name) Nothing (if explicit then [] else snd (snd (scope !! position)))
                let local = embedUnder (scopeShape scope) (Core.Var position)
                return (if deferred then builtRaw "p_resolve" [label, builtRaw "p_capture" [local]] else builtRaw "r_ref" [local, builtList (kindOf "rmode") modes])
        _ -> do
            fallback <- global
            return (if deferred then builtRaw "p_resolve" [label, fallback] else fallback)

referenceGlobal :: Env.Env -> Scope -> Span -> Bool -> Core.Global -> Build TermNode
referenceGlobal env scope at explicit global = referenceGlobalAt env scope at explicit global Nothing

referenceGlobalAt :: Env.Env -> Scope -> Span -> Bool -> Core.Global -> Maybe [LevelSyntax] -> Build TermNode
referenceGlobalAt env scope at explicit global supplied = do
    modes <- referenceModes scope at (Just global) (if explicit then [] else Map.findWithDefault [] global (Env.envArguments env))
    (_, _, _, currentBlock, _, _, _, universeMode) <- get
    let identifier = globalOwner global
        count = globalUniverseCount env global
        local = case currentBlock of
            Just (block, _, _) -> block == identifier
            _ -> False
        template = case Env.entryDecl <$> Map.lookup identifier (Env.envDecls env) of
            Just (Env.Inductive _ families) -> any Env.familyTemplate families
            _ -> False
        namedLevel level = case levelForm level of
            LName name -> Just (nameText name)
            _ -> Nothing
    instance' <- case supplied of
        Just levels
            | local, Just universe <- universeMode ->
                if traverse namedLevel levels == Just (Core.universeNames (buildingContext universe))
                    then return [named "lb"]
                    else failure at "E-UniverseArity" "a recursive occurrence must use the universes of its block in declaration order"
            | template -> failure at "E-UniverseArity" "a template occurrence infers its universe instance from its arguments"
            | length levels /= count -> failure at "E-UniverseArity" "the reference has the wrong number of universe arguments"
            | otherwise -> mapM (encodeUniverseLevel env False) levels
        Nothing
            | local, Just _ <- universeMode -> return [named "lb"]
            | count == 0 -> return []
            -- Template slots take the least bound of their arguments. Like
            -- an inferred arity, it may be a maximum or a successor.
            | Just _ <- universeMode -> mapM (\place -> freshUniverseAt place (if template then 2 else 0) at) [0 .. count - 1]
            | otherwise -> failure at "E-Universe" "a polymorphic reference requires universe-aware elaboration"
    let arguments = builtList (kindOf "lvl") instance'
        term = case global of
            Core.GlobalCst constant -> builtRaw "cst" [natural constant, arguments]
            Core.GlobalInd block index -> builtRaw "ind" [natural block, natural (toInteger index), arguments]
            Core.GlobalProj block field -> builtRaw "pfield" [natural block, natural (toInteger field), arguments]
            Core.GlobalCon block index constructor -> builtRaw "con" [natural block, natural (toInteger index), natural (toInteger constructor), arguments]
    return (builtRaw "r_ref" [term, builtList (kindOf "rmode") modes])

globalUniverseCount :: Env.Env -> Core.Global -> Int
globalUniverseCount env global = maybe 0 (length . Core.universeNames . Env.entryUniverses) (Map.lookup (globalOwner global) (Env.envDecls env))

globalOwner :: Core.Global -> Core.ConstId
globalOwner global = case global of
    Core.GlobalCst constant -> constant
    Core.GlobalInd block _ -> block
    Core.GlobalCon block _ _ -> block
    Core.GlobalProj block _ -> block

encodeUniverseLevel :: Env.Env -> Bool -> LevelSyntax -> Build TermNode
encodeUniverseLevel env atomic syntax = do
    (_, _, _, _, _, _, _, mode) <- get
    context <- maybe (failure (levelSpan syntax) "E-Universe" "this syntax requires universe-aware elaboration") (return . buildingContext) mode
    let parameters = universeScope env (Core.universeNames context)
        known = lift . fmap embedLevel . universeLevel parameters
    case levelForm syntax of
        LHole -> freshUniverse 0 (levelSpan syntax)
        LNumber _ -> known syntax
        LName _ -> known syntax
        LOffset inner operator amount
            | not atomic && nameText operator == "+" && amount >= 0 -> do
                value <- encodeUniverseLevel env False inner
                return (successors amount value)
        LMaximum operator left right
            | not atomic && nameText operator == "max" -> builtRaw "lm" <$> mapM (encodeUniverseLevel env False) [left, right]
        _ -> failure (levelSpan syntax) "E-Universe" (if atomic then "a universe instance requires atomic levels" else "invalid universe expression")
    where
        successors count value
            | count <= 0 = value
            | otherwise = builtRaw "lu" [successors (count - 1) value]

-- Marker numbers are local to one whole proposal. Hol allocates their cells
-- before entering term binders, so a level cannot capture a term parameter.
freshUniverse :: Integer -> Span -> Build TermNode
freshUniverse = freshUniverseAt 0

freshUniverseAt :: Int -> Integer -> Span -> Build TermNode
freshUniverseAt place kind at = do
    (number, positions, holes, parameters, template, defaults, proof, mode) <- get
    case mode of
        Nothing -> failure at "E-Universe" "a fresh level requires universe-aware elaboration"
        Just universe
            | Just marker <- Map.lookup key (bareMarkers universe) -> given marker universe
            | marker : rest <- bareReplay universe -> given marker universe { bareReplay = rest }
            | otherwise -> given (nextLevelMarker universe) universe { nextLevelMarker = nextLevelMarker universe + 1, markerKinds = kind : markerKinds universe, markerPositions = number : markerPositions universe }
            where
                key = (at, binderPath universe, place)
                given marker from = do
                    put (number, positions, holes, parameters, template, defaults, proof, Just from { bareMarkers = Map.insert key marker (bareMarkers from), bareTrace = marker : bareTrace from })
                    return (builtRaw "lf" [natural marker])

referenceModes :: Scope -> Span -> Maybe Core.Global -> [Bool] -> Build [TermNode]
referenceModes scope at global = mapM mode . zip [0 ..] where
    mode (_, False) = return (named "r_explicit")
    mode (index, True) = do
        (_, _, _, parameters, template, _, _, _) <- get
        case (global, parameters) of
            -- An implicit parameter of a family of the block, in a constructor
            -- type: a hole that unification may solve, and otherwise the
            -- parameter of the block. The mode has
            -- that parameter beside the cell of the hole, and the hole is
            -- recorded for the `fix` nodes that end after it. A template
            -- has no hole of its own: each copy of it gets one, which no
            -- `fix` could be told of, so in a type that has a `fix` the
            -- parameter is given at once there.
            (Just (Core.GlobalInd block _), Just (expected, count, recursive))
                | block == expected && index < count && index < length scope -> if template then return (builtRaw (if recursive then "r_given" else "r_pending_block") [given]) else do
                    cell <- registered "RawImplicit"
                    let closed = foldl (\inner fixed -> builtRaw (if fixed then "rd_fix" else "rd_bind") [builtLambda Nothing inner]) (builtRaw "rd_pair" [cell, given]) (scopeBinders scope)
                    modify (\(next, positions, holes, known, templated, defaults, proof, universes) -> (next, positions, holes, known, templated, closed : defaults, proof, universes))
                    return (builtRaw "r_block" [cell, given])
                where
                    given = embedUnder (scopeShape scope) (Core.Var (length scope - index - 1))
            _
                | template -> return (named "r_pending")
                | otherwise -> builtRaw "r_implicit" . pure <$> registered "RawImplicit"
    registered prefix = do
        (variable, cell) <- scopedCell scope prefix at
        modify (\(next, positions, holes, known, templated, defaults, proof, universes) -> (next, positions, variable : holes, known, templated, defaults, proof, universes))
        return cell

-- The binders of Hol that a scope has, the innermost first: whether each is
-- the one binder of the functions of a `fix`.
scopeBinders :: Scope -> [Bool]
scopeBinders scope = [maybe False (const True) shape | (_, (shape, _)) <- scope, maybe True (== 0) shape]

-- A new output variable applied to the binders of the scope: a cell that the
-- elaborator fills with a value that may mention those binders.
scopedCell :: Scope -> String -> Span -> Build (LogicVar, TermNode)
scopedCell scope prefix at = do
    number <- positionOf at
    let variable = LV_Named (prefix ++ show number)
        width = length (scopeBinders scope)
    return (variable, builtApply (mkLVar variable) [mkNIdx n | n <- reverse [0 .. width - 1]])

encodeUnder :: Env.Env -> Scope -> Term -> Build TermNode
encodeUnder = encodeUnderWith False

-- `command`: the term is the `fix` of a `Fixpoint` command.
-- Visit syntax in Hol's elaboration order, so a `fix` records the earlier
-- block-parameter cells. Only elab.hol decides their types and bindings.
encodeUnderWith :: Bool -> Env.Env -> Scope -> Term -> Build TermNode
encodeUnderWith command env scope source = do
    (frontier, _, _, _, _, _, mode, _) <- get
    let proof = mode /= OrdinaryEncoding
    -- In a proof the hole is a leaf: its next position is also its end.
    -- Other proof nodes need only the end position, after their children.
    number <- if proof then return frontier else positionOf (termSpan source)
    value <- node number
    carrier <- if proof then positionOf (termSpan source) else refreshCarrier number (termSpan source)
    return (builtRaw "r_at" [natural carrier, value])
    where
        at = termSpan source
        descend = encodeUnder env scope
        node number = case termForm source of
            SName name -> reference env scope False name
            SDeclared name -> resolveGlobal env name >>= referenceGlobal env scope at True
            SBound index -> return (builtRaw "r_ref" [embedUnder (scopeShape scope) (Core.Var index), builtList (kindOf "rmode") []])
            SMask prefix count expr -> encodeUnder env (maskLocals (\(_, details) -> ("", details)) prefix count scope) expr
            SWithout name expr -> encodeUnder (Env.withNames (Map.delete (nameText name) (Env.envNames env)) env) scope expr
            SGlobal global -> referenceGlobal env scope at False global
            SExplicit name -> reference env scope True name
            SInstance explicit name levels
                | nameText name `elem` map fst scope -> scopeFailure name "a local term does not take universe arguments"
                | otherwise -> resolveGlobal env name >>= \global -> referenceGlobalAt env scope at explicit global (Just levels)
            SProp -> return (literal Core.Prop)
            SSet -> return (literal (Core.Type (Core.Closed 0)))
            SType level -> return (literal (Core.Type (Core.Closed level)))
            SInferredType -> do
                (_, _, _, _, _, _, _, mode) <- get
                case mode of
                    Nothing -> failure at "E-Universe" "bare Type requires universe inference"
                    Just universe
                        | Just (place, wide) <- buildingConclusion universe, place == at -> inferred (if wide then 3 else 2)
                        | otherwise -> case buildingBare universe of
                            BareRefused -> failure at "E-Universe" "a declaration that names its universes leaves out no level of Type: write the level, as in Type@{u}"
                            BareUniverse -> inferred 1
                            BareCell -> inferred 5
            SUniverse level -> do
                (_, _, _, _, _, _, _, mode) <- get
                encoded <- case (levelForm level, mode >>= buildingConclusion) of
                    (LHole, Just (place, True)) | place == at -> freshUniverse 4 (levelSpan level)
                    _ -> encodeUniverseLevel env False level
                return (builtRaw "r_ref" [builtRaw "typ" [encoded], builtList (kindOf "rmode") []])
            SHole -> do
                (_, _, _, _, template, _, _, _) <- get
                if template then return (builtRaw "r_blank" [natural number]) else do
                    let variable = LV_Named ("RawHole" ++ show number)
                        request = LV_Named ("RawRequest" ++ show number)
                        typ = LV_Named ("RawType" ++ show number)
                        width = length (scopeBinders scope)
                        applied value = builtApply (mkLVar value) [mkNIdx n | n <- reverse [0 .. width - 1]]
                    modify (\(next, positions, holes, parameters, template, defaults, proof, universes) -> (next, positions, variable : request : typ : holes, parameters, template, defaults, proof, universes))
                    return (builtRaw "r_hole" [natural number, applied request, applied variable, applied typ])
            SProjection receiver field -> do
                accessor <- resolveGlobal env field
                case accessor of
                    Core.GlobalProj block index -> do
                        value <- descend receiver
                        return (builtRaw "r_proj" [natural block, natural (toInteger index), value])
                    _ -> scopeFailure field ("expected a primitive projection: " ++ nameText field)
            SApp {} -> do
                let (headTerm, arguments) = applicationSpine source
                function <- descend headTerm
                items <- mapM descend arguments
                return (builtRaw "r_apps" [function, builtRawList items])
            SArrow domain body -> do
                left <- descend domain
                right <- encodeUnder env (local "" : scope) body
                return (builtRaw "r_pi" [left, builtLambda Nothing right])
            SForall binders body -> encodeBinders env "r_pi" scope scope binders body
            SLambda binders body -> encodeBinders env "r_lam" scope scope binders body
            SLet name annotation value body -> do
                written <- traverse descend annotation
                -- A literal sort uses the known sort annotation. For any other
                -- expression Hol finds the algebraic arity first. Its next
                -- reading gets a flexible level after the value's markers.
                asked <- gets (\(_, _, _, _, _, _, _, universes) -> maybe False (\universe -> Set.member (termSpan value, binderPath universe) (refreshNodes universe)) universes)
                levels <- gets (\(_, _, _, _, _, _, _, universes) -> maybe False (const True) universes)
                let flexible = isNothing annotation && levels && (sortFormer value || asked)
                    withheld change = modify (\(next, positions, holes, constructor, template, defaults, proof, universes) -> (next, positions, holes, constructor, template, defaults, proof, fmap (\universe -> universe { refreshNodes = change (termSpan value, binderPath universe) (refreshNodes universe) }) universes))
                term <- if flexible && asked then withheld Set.delete *> descend value <* withheld Set.insert else descend value
                spare <- if flexible then Just <$> freshUniverseAt (-1) 0 (termSpan value) else return Nothing
                rest <- builtLambda (binderHint (nameText name)) <$> encodeUnder env (local (nameText name) : scope) body
                case (written, spare) of
                    (Just typ, _) -> return (builtRaw "r_let" [typ, term, rest])
                    (_, Just level)
                        | sortFormer value -> return (builtRaw "r_let" [builtRaw "r_ref" [builtRaw "typ" [level], builtList (kindOf "rmode") []], term, rest])
                        | otherwise -> return (builtRaw "r_letfresh" [level, term, rest])
                    _ -> return (builtRaw "r_letinfer" [term, rest])
            SParen inner -> descend inner
            SAnnotation value annotation -> do
                typ <- descend annotation
                term <- descend value
                return (builtRaw "r_annot" [term, typ])
            SFix bodies selected -> encodeFix command env scope at bodies selected
            SMatch term alias family clause branches -> encodeMatch env scope at term alias family clause branches
            _ -> failure at "E-Syntax" "notation must be resolved before elaboration"
        literal value = builtRaw "r_ref" [embedTerm value, builtList (kindOf "rmode") []]
        inferred kind = do
            fresh <- freshUniverse kind at
            return (builtRaw "r_ref" [builtRaw "typ" [fresh], builtList (kindOf "rmode") []])

-- Whether the expression itself is a sort.
sortFormer :: Term -> Bool
sortFormer source = case termForm source of
    SParen inner -> sortFormer inner
    SType _ -> True
    SUniverse _ -> True
    form -> form `elem` [SProp, SSet, SInferredType]

-- The number that a node carries: its own, or the number of the earlier
-- reading of the same written node that got its spare universe. A node of
-- refreshNodes that has none yet gets one here, after the markers of what is
-- below it (in a later family of a block, the one of the first family).
refreshCarrier :: Integer -> Span -> Build Integer
refreshCarrier number at = do
    (next, positions, holes, parameters, template, defaults, proof, mode) <- get
    case mode of
        Nothing -> return number
        Just universe -> do
            let key = (at, binderPath universe)
                noted = universe { nodeKeys = Map.insert number key (nodeKeys universe) }
                keep from carrier = put (next, positions, holes, parameters, template, defaults, proof, Just from) >> return carrier
                spared = [marker | marker : _ <- [bareReplay universe], kind : _ <- [drop (fromInteger marker) (reverse (markerKinds universe))], kind >= 6]
            if not (Set.member key (refreshNodes universe)) then keep noted number else case (Map.lookup key (refreshSpares universe), spared) of
                (Just carrier, _) -> keep noted carrier
                (Nothing, marker : _) -> do
                    let carrier = reverse (markerKinds universe) !! fromInteger marker - 6
                    keep noted { bareReplay = drop 1 (bareReplay universe), bareTrace = marker : bareTrace universe, refreshSpares = Map.insert key carrier (refreshSpares universe) } carrier
                (Nothing, []) -> keep noted
                    { nextLevelMarker = nextLevelMarker universe + 1
                    , markerKinds = 6 + number : markerKinds universe
                    , bareTrace = nextLevelMarker universe : bareTrace universe
                    , refreshSpares = Map.insert key number (refreshSpares universe)
                    } number

-- The nodes that a report of the elaborator names, by where they are
-- written, in the order of the report.
refreshedNodes :: Map.Map Integer (Span, [Int]) -> Report -> [(Span, [Int])]
refreshedNodes keys report = [key | Just (ReportTerm _ (Core.Cst number [])) <- reportCore report, Just key <- [Map.lookup number keys]]

type RefreshReading = (Verdict, Map.Map Integer Span, Map.Map Integer (Span, [Int]), Maybe String)

data RefreshStep
    = NeedsRefresh [(Span, [Int])]
    | ReadVerdict Verdict (Map.Map Integer Span) (Maybe String)
    deriving ()

-- One deadline covers encoding, all kernel readings and pruning. A smaller
-- reading can keep the old key only when it stopped with a logical refusal.
-- A declaration that names no universe is read with a list for the nodes
-- that need a universe of their own (e_u_found of elab.hol): the reading
-- gives such a node a universe for the time being, goes on, and stops when
-- the term is read, with every such node on the list. The declaration is
-- then read again with a spare universe for each of them. A declaration
-- that names its universes has no such list: the node is reported, and
-- refused.
readWithRefresh :: Span -> Limits -> Bool -> (Refresh -> IO (Either Diagnostic RefreshReading)) -> (Refresh -> Map.Map Integer Span -> Verdict -> Maybe String -> Either Diagnostic a) -> (a -> Bool) -> IO (Either Diagnostic a)
readWithRefresh at limits namedHeader run answer idle = do
    let readDeclaration = attempt Set.empty >>= evaluate
    if limitMicros limits <= 0 then readDeclaration else do
        outcome <- timeout (limitMicros limits) readDeclaration
        return (fromMaybe (Left (outOfTime at)) outcome)
    where
        readOne refresh = do
            outcome <- run refresh
            return $ do
                (verdict, positions, keys, reason) <- outcome
                case verdict of
                    Rejected (Just report)
                        | reportRule report == "E-Refresh" && namedHeader -> Left (refreshRefused at keys report)
                        | reportRule report `elem` ["E-Refresh", "E-LetRefresh"], found@(_ : _) <- nextRefresh keys refresh report -> Right (NeedsRefresh found)
                        | reportRule report `elem` ["E-Refresh", "E-LetRefresh"] -> Left (Diagnostic at "LoL-ElabError" "E-Unsolved" "the elaborator asked again for a universe that it was given" [])
                    _ -> Right (ReadVerdict verdict positions reason)
        attempt refresh = readOne refresh >>= \outcome -> case outcome of
            Left problem -> return (Left problem)
            Right (NeedsRefresh found) -> attempt (foldr Set.insert refresh found)
            Right (ReadVerdict verdict positions reason) -> prune (Set.toList refresh) refresh (answer refresh positions verdict reason)
        prune candidates refresh result = case (result, candidates) of
            (Right proposal, key : rest)
                | idle proposal -> do
                    let fewer = Set.delete key refresh
                    outcome <- readOne fewer
                    case outcome of
                        Left problem -> return (Left problem)
                        Right (NeedsRefresh _) -> prune rest refresh result
                        Right (ReadVerdict (Rejected _) _ _) -> prune rest refresh result
                        Right (ReadVerdict verdict positions reason) -> prune rest fewer (answer fewer positions verdict reason)
            _ -> return result

-- The goal of a reading that has the list of its refresh nodes for an
-- output, and its verdict: a reading that stopped with nodes on the list
-- says which they are, as a report of the elaborator does.
listing :: Bool -> LogicVar -> TermNode -> TermNode
listing wanted found goal = if wanted then builtApply (mkNCon LO_imply) [builtRaw "e_u_found" [mkLVar found], goal] else goal

listed :: Bool -> Verdict -> Verdict
listed wanted verdict = case verdict of
    Admitted values
        | wanted, Right nodes@(_ : _) <- recoverList (last values) >>= mapM recoverNatural -> Rejected (Just (Report "E-Refresh" [] [Just (ReportTerm [] (Core.Cst (toInteger number) [])) | number <- nodes]))
        | wanted -> Admitted (init values)
    _ -> verdict

outOfTime :: Span -> Diagnostic
outOfTime at = Diagnostic at "LoL-KernelUndecided" "R5" "the time limit was reached while the universes of the declaration were read" []

-- The nodes of a report that have no universe yet.
nextRefresh :: Map.Map Integer (Span, [Int]) -> Refresh -> Report -> [(Span, [Int])]
nextRefresh keys refresh report = filter (not . (`Set.member` refresh)) (refreshedNodes keys report)

-- Whether a universe of a proposal is in none of its terms and constraints.
-- A spare universe that the reading did not use is such a one: it was given
-- for a node that a failed reading reported on its way back.
idleUniverse :: Core.UniverseContext -> [Core.Term] -> Bool
idleUniverse context terms = any (`Set.notMember` used) [0 .. length (Core.universeNames context) - 1] where
    used = Set.unions (map Core.termParameters terms ++ concat [[Core.levelParameters left, Core.levelParameters right] | constraint <- Core.universeConstraints context, (left, right) <- [sides constraint]])
    sides (Core.UniverseLe left right) = (left, right)
    sides (Core.UniverseEq left right) = (left, right)

-- A declaration that names its universes has no universe for the node (an
-- argument whose type is the value of an implicit argument, or the term that
-- a `let` without a type binds): Rocq refuses the one that it makes there as
-- unbound.
refreshRefused :: Span -> Map.Map Integer (Span, [Int]) -> Report -> Diagnostic
refreshRefused fallback keys report = Diagnostic at "LoL-ElabError" "E-Level" "the type of this term is the value of an implicit argument, or the type of a `let` that writes none, and needs a universe of its own there, which a declaration that names its universes does not have: write that argument or that type" [] where
    at = case refreshedNodes keys report of
        (found, _) : _ -> found
        [] -> fallback

-- Inspect source annotations before elaboration erases them.
anyForm :: (TermForm -> Bool) -> Term -> Bool
anyForm matches = visit where
    visit (Term _ form) = matches form || case form of
        SApp left right -> visit left || visit right
        SProjection receiver _ -> visit receiver
        SMask _ _ expr -> visit expr
        SWithout _ expr -> visit expr
        SArrow left right -> visit left || visit right
        SOperators first rest -> visit first || any (visit . snd) rest
        SForall binders body -> any binder binders || visit body
        SLambda binders body -> any binder binders || visit body
        SLet _ annotation value body -> any visit annotation || visit value || visit body
        SParen inner -> visit inner
        SAnnotation value annotation -> visit value || visit annotation
        SMatch value _ _ motive branches -> visit value || any visit motive || or [visit body | Branch _ _ body <- branches]
        SFix functions _ -> or [any binder binders || visit domain || visit body | FixBody _ _ binders _ domain body <- functions]
        _ -> False
    binder = any visit . binderType

writesBareType :: Term -> Bool
writesBareType = anyForm (== SInferredType)

hasFix :: Term -> Bool
hasFix = anyForm isFix where
    isFix SFix {} = True
    isFix _ = False

applicationSpine :: Term -> (Term, [Term])
applicationSpine = go [] where
    go arguments source = case termForm source of
        SApp function argument -> go (argument : arguments) function
        _ -> (source, arguments)

-- A shared annotation is resolved before its group. Anonymous padding shifts
-- its free indices without letting a new binder capture the annotation.
encodeBinders :: Env.Env -> String -> Scope -> Scope -> [Binder] -> Term -> Build TermNode
encodeBinders env = encodeBindersIn env env

-- The annotations are read in `outer` and the body in `inner`: the parameters
-- of an `Inductive` are outside its block, and its constructor types inside.
encodeBindersIn :: Env.Env -> Env.Env -> String -> Scope -> Scope -> [Binder] -> Term -> Build TermNode
encodeBindersIn outer inner constructor domains scope binders body = case binders of
    [] -> encodeUnder inner scope body
    binder : remaining -> group domains domains scope (binderVars binder) where
        group _ following current [] = encodeBindersIn outer inner constructor following current remaining body
        group signature following current (name : names) = do
            annotation <- case binderType binder of
                Just declared -> Just <$> withinBinder (length (binderVars binder) - length names - 1) (encodeUnder outer signature declared)
                Nothing
                    | constructor == "r_lam" -> return Nothing
                    | otherwise -> failure (binderSpan binder) "E-NeedAnnotation" "a product binder needs a type"
            case (names, elemIndex (nameText name) (map fst signature), annotation) of
                (_ : _, Just index, Just term)
                    | rawUses (length (filter (maybe True (== 0) . fst . snd) (take index signature))) 0 term -> lift (Left (Diagnostic (nameSpan name) "LoL-ScopeError" "H-Binders" ("a shared binder annotation depends on the local name that this binder shadows: " ++ nameText name) [nameText name]))
                _ -> return ()
            rest <- group (local "" : signature) (local (hint name) : following) (local (hint name) : current) names
            let bound = builtLambda (binderHint (hint name)) rest
            return (maybe (builtRaw "r_untyped" [bound]) (\domain -> builtRaw constructor [domain, bound]) annotation)
        hint name = if nameText name == "_" then "" else nameText name

-- This inspects only de Bruijn occurrences of the transported raw syntax.
-- A hole's scope arguments are administrative, not source occurrences.
rawUses :: Int -> Int -> TermNode -> Bool
rawUses index depth term
    | rawHead term == named "r_hole" = False
    | otherwise = case term of
        NIdx found -> found == index + depth
        NApp left right _ -> rawUses index depth left || rawUses index depth right
        NLam _ _ body _ -> rawUses index (depth + 1) body
        _ -> False
    where
        rawHead (NApp function _ _) = rawHead function
        rawHead value = value

-- The functions of a `fix` have, in its bodies, the implicit arguments that
-- their binders give them. Those of a `Fixpoint` command have the ones of
-- their written result types too. Both are as in Rocq, which ignores an
-- implicit binder in the result type of a `fix` inside a term.
encodeFix :: Bool -> Env.Env -> Scope -> Span -> [FixBody] -> Maybe Name -> Build TermNode
encodeFix command env scope at functions selected = do
    chosen <- case (selected, functions) of
        (Nothing, [_]) -> return 0
        (Just name, _) -> maybe (scopeFailure name "the selected function is not in this block") return (elemIndex (nameText name) names)
        _ -> failure at "E-Arity" "a mutual fix needs a selected function"
    choices <- mapM choice functions
    types <- mapM (\(FixBody position _ binders _ annotation _) -> encodeUnder env scope (Term position (SForall binders annotation))) functions
    let masks = [binderModes binders ++ (if command then typeModes annotation else []) | FixBody _ _ binders _ annotation _ <- functions]
        siblings = reverse (zip names (zip (map Just [0 .. length functions - 1]) masks))
        hidden = map (\(_, (index, _)) -> ("", (index, []))) siblings
    bodies <- mapM (\(FixBody _ _ binders _ _ body) -> encodeBinders env "r_lam" (hidden ++ scope) (siblings ++ scope) binders body) functions
    -- the holes of block parameters that were made before the end of this `fix`
    (_, _, _, _, _, defaults, proof, _) <- get
    let namedBodies = if proof /= OrdinaryEncoding then map nameFunctions bodies else bodies
    return (builtRaw "r_fix" [natural (toInteger chosen), builtList (kindOf "rposition") choices, builtRawList types, builtLambda (binderHint (concat (take 1 names))) (builtRawList namedBodies), builtList (kindOf "rdefault") (reverse defaults)])
    where
        names = [nameText name | FixBody _ name _ _ _ _ <- functions]
        nameFunctions body = foldr nameFunction body (zip [0 ..] names)
        nameFunction (index, name) body = builtRaw "p_named"
            [ embedList (kindOf "char") (map (mkNCon . DC_ChrL) name)
            , builtApply (mkNIdx 0) [natural index]
            , body
            ]
        binderModes = concatMap (\binder -> replicate (length (binderVars binder)) (binderImpl binder))
        typeModes term = case termForm term of
            SForall binders body -> binderModes binders ++ typeModes body
            SArrow _ body -> False : typeModes body
            SParen body -> typeModes body
            _ -> []
        choice (FixBody location _ binders struct _ _) = case struct of
            Just name -> case elemIndices (nameText name) variables of
                [] -> scopeFailure name "the struct argument is not a binder"
                [found] -> return (builtRaw "r_fixed" [natural (toInteger found)])
                _ -> lift (Left (ambiguousStruct (nameSpan name) (nameText name)))
            Nothing -> return (builtRaw "r_search" [builtList (kindOf "nat") (map (natural . toInteger) [0 .. length variables - 1])])
            where
                variables = concatMap (map nameText . binderVars) binders

encodeMatch :: Env.Env -> Scope -> Span -> Term -> Maybe Name -> Maybe Pattern -> Maybe Term -> [Branch] -> Build TermNode
encodeMatch env scope at scrutinee alias family clause branches = do
    known <- case family of
        Just (Pattern _ _ name _) -> Just <$> patternGlobal name
        Just (WildPattern place) -> failure place "E-Arity" "an in clause needs an inductive family"
        Nothing -> case [name | Branch _ (Pattern _ _ name _) _ <- branches] of
            name : _ -> Just <$> patternGlobal name
            [] -> return Nothing
    case (family, known) of
        (Just _, Just (Core.GlobalInd _ _)) -> return ()
        (Nothing, _) -> return ()
        _ -> failure at "E-Arity" "an in clause must name an inductive family"
    let familyId = case known of
            Just (Core.GlobalInd block index) -> Just (block, index)
            Just (Core.GlobalCon block index _) -> Just (block, index)
            _ -> Nothing
    shape <- case familyId of
        Nothing -> return Nothing
        Just (block, index) -> case Map.lookup block (Env.envDecls env) of
            Just (Env.Entry { Env.entryDecl = Env.Inductive parameters families })
                | index >= 0 && index < length families -> return (Just (block, index, parameters, families !! index))
            _ -> failure at "E-Arity" "the match family is not declared"
    indices <- case (family, shape) of
        (Just (Pattern place explicit name items), Just (block, index, parameters, form)) -> do
            expanded <- patternItems env place explicit (Core.GlobalInd block index) parameters items
            return (map nameText (drop parameters expanded))
        (_, Just _) -> return []
        _ -> return []
    let self = maybe "" (\name -> if nameText name == "_" then "" else nameText name) alias
    term <- encodeUnder env scope scrutinee
    result <- case clause of
        Nothing -> return (named "rr_none")
        Just term -> builtRaw (if maybe True (const False) family then "rr_auto" else "rr_some") . pure <$> abstractRaw env scope (indices ++ [self]) term
    arms <- concat <$> mapM (encodeBranch shape) (zip [0 ..] branches)
    let labels = [(b, i, j) | Branch _ (Pattern _ _ name _) _ <- branches, Just (Core.GlobalCon b i j) <- [Map.lookup (nameText name) (Env.envNames env)]]
    if length labels /= length (nub labels) then failure at "E-Arity" "a constructor branch occurs more than once" else return ()
    let assertion = case familyId of
            Nothing -> named "rf_any"
            Just (block, index) -> case family of
                Nothing -> builtRaw "rf_named" [natural block, natural (toInteger index)]
                Just _ -> builtRaw "rf_pattern" [natural block, natural (toInteger index), natural (toInteger (length indices))]
    return (builtRaw "r_match" [term, assertion, result, builtList (kindOf "rbranch") arms])
    where
        patternGlobal name
            | nameText name `elem` map fst scope = lift (Left (unsupported (nameSpan name) "a pattern head shadowed by a local variable"))
            | otherwise = resolveGlobal env name
        covered = [constructor | Branch _ (Pattern _ _ name _) _ <- branches, Just (Core.GlobalCon _ _ constructor) <- [Map.lookup (nameText name) (Env.envNames env)]]
        encodeBranch shape (place, Branch location pattern body) = case pattern of
            WildPattern _
                | place + 1 /= length branches -> failure location "E-Arity" "a wildcard branch must be last"
                | otherwise -> do
                    (_, _, _, _, _, _, _, mode) <- get
                    case (shape, fmap buildingBare mode) of
                        -- Rocq reads the body of a wildcard branch once for each
                        -- constructor that it covers, and each reading of a `Type`
                        -- without a level makes a universe. The copies that the
                        -- elaborator makes of a template share its markers, so such
                        -- a branch is written out here: the branch of each
                        -- constructor that it covers, with no name for an argument.
                        (Just (block, index, parameters, form), Just BareUniverse)
                            | writesBareType body, missing@(_ : _) <- [(constructor, signature) | (constructor, (_, signature)) <- zip [0 ..] (Env.familyCons form), constructor `notElem` covered] ->
                                mapM (\(constructor, signature) -> do
                                    term <- withinBinder constructor (abstractRaw env scope (replicate (products signature - parameters) "") body)
                                    return (builtRaw "rb_named" [natural block, natural (toInteger index), natural (toInteger constructor), term])) missing
                        _ -> pure <$> wildcard location body
            Pattern _ explicit name items -> do
                global <- patternGlobal name
                (block, index, constructor, parameters, form) <- case (global, shape) of
                    (Core.GlobalCon b i j, Just (expected, familyIndex, n, form))
                        | b == expected && i == familyIndex -> return (b, i, j, n, form)
                    _ -> failure location "E-Arity" "a pattern names a constructor of another family"
                signature <- maybe (failure location "E-Arity" "the constructor index is invalid") (return . snd) (atIndex constructor (Env.familyCons form))
                expanded <- patternItems env location explicit global parameters items
                let bound = map (\item -> if nameText item == "_" then "" else nameText item) (drop parameters expanded)
                    named = filter (not . null) bound
                if length named /= length (nub named) then failure location "E-Arity" "a pattern binds a name more than once" else return ()
                term <- abstractRaw env scope bound body
                return [builtRaw "rb_named" [natural block, natural (toInteger index), natural (toInteger constructor), term]]
        wildcard location body = do
            (_, _, _, _, previous, _, _, _) <- get
            -- The branch has a cell for the copies that the
            -- constructors get of its template. Inside a template
            -- each copy of that template makes the cell.
            copies <- if previous then return (builtRawList []) else do
                (variable, cell) <- scopedCell scope "RawWild" location
                modify (\(next, positions, holes, parameters, templated, defaults, proof, universes) -> (next, positions, variable : holes, parameters, templated, defaults, proof, universes))
                return cell
            modify (\(next, positions, holes, parameters, _, defaults, proof, universes) -> (next, positions, holes, parameters, True, defaults, proof, universes))
            term <- encodeUnder env scope body
            modify (\(next, positions, holes, parameters, _, defaults, proof, universes) -> (next, positions, holes, parameters, previous, defaults, proof, universes))
            return (builtRaw "rb_other" [term, copies])
        products typ = case typ of
            Core.Pi _ _ rest -> 1 + products rest
            _ -> 0 :: Int

abstractRaw :: Env.Env -> Scope -> [String] -> Term -> Build TermNode
abstractRaw env scope names term = case names of
    [] -> encodeUnder env scope term
    name : rest -> builtRaw "r_abs" . pure . builtLambda (binderHint name) <$> abstractRaw env (local name : scope) rest term

patternItems :: Env.Env -> Span -> Bool -> Core.Global -> Int -> [Name] -> Build [Name]
patternItems env at explicit global parameters items = do
    expanded <- fill flags items
    let bound = drop parameters expanded
        names = filter (/= "_") (map nameText bound)
    -- A constructor there would be a pattern inside a pattern.
    case filter (Env.constructorName env . nameText) bound of
        item : _ -> lift (Left (unsupported (nameSpan item) "a pattern inside a pattern"))
        [] -> return ()
    if length names /= length (nub names) then failure at "E-Arity" "a pattern binds a name more than once" else return ()
    if length expanded < parameters || any ((/= "_") . nameText) (take parameters expanded) then failure at "E-Arity" "constructor parameters in a pattern must be _" else return expanded
    where
        flags = if explicit then [] else Map.findWithDefault [] global (Env.envArguments env)
        fill [] names = return names
        fill (True : rest) names = (Name at "_" :) <$> fill rest names
        fill (False : rest) (name : names) = (name :) <$> fill rest names
        fill _ [] = failure at "E-Arity" "not enough pattern arguments"

atIndex :: Int -> [a] -> Maybe a
atIndex index values = case drop index values of
    value : _
        | index >= 0 -> Just value
    _ -> Nothing

-- Only use this path where surface elaboration is required. Explicit scripts
-- keep their rule-labelled ground diagnostics and their existing round trips.
needsUniverses :: Env.Env -> Term -> Bool
needsUniverses = anyForm . universeForm

universeForm :: Env.Env -> TermForm -> Bool
universeForm env form = case form of
    SInferredType -> True
    SUniverse _ -> True
    SInstance {} -> True
    SGlobal global -> globalUniverseCount env global > 0
    SName name -> polymorphic name
    SExplicit name -> polymorphic name
    SDeclared name -> polymorphic name
    SMatch _ _ family _ branches -> any patternUses family || or [patternUses pat | Branch _ pat _ <- branches]
    _ -> False
    where
        polymorphic name = maybe False ((> 0) . globalUniverseCount env) (Map.lookup (nameText name) (Env.envNames env))
        patternUses (Pattern _ _ name _) = polymorphic name
        patternUses WildPattern {} = False

-- A term is read by the elaborator when it has something that is not
-- explicit, and also when it has a cast and an elaborator is loaded: a
-- cast is explicit and is the same term either way, and the elaborator
-- says where it fails. Without one (a replay on the kernel alone) the cast is
-- read as it is written (`Front.Scope`).
neededBy :: Kernel -> Env.Env -> Term -> Bool
neededBy kernel env = anyForm (\form -> universeForm env form || elaborationForm (isJust (kernelElaborator kernel)) env form)

-- Vernac has already ruled out universe elaboration for the whole command.
-- One visit finds both implicit syntax and casts handled by a loaded elaborator.
needsGroundElaborator :: Kernel -> Env.Env -> Term -> Bool
needsGroundElaborator kernel env = anyForm (elaborationForm (isJust (kernelElaborator kernel)) env)

needed :: Env.Env -> Term -> Bool
needed env = anyForm (\form -> universeForm env form || elaborationForm False env form)

elaborationForm :: Bool -> Env.Env -> TermForm -> Bool
elaborationForm casts env = required where
    required form = case form of
        SAnnotation {} -> casts
        SGlobal global -> marked global
        SName name -> namedArgument name
        SHole -> True
        SNumeral {} -> True
        SOperators {} -> True
        SForall binders _ -> any binder binders
        SLambda binders _ -> any binder binders
        SLet _ annotation _ _ -> isNothing annotation
        SMatch _ _ family clause branches -> maybe (null branches || familyAlias branches) patternNeeded family || isNothing clause || or [patternNeeded pat | Branch _ pat _ <- branches] || unordered branches
        SFix functions _ -> or [isNothing struct || any binder binders | FixBody _ _ binders struct _ _ <- functions]
        _ -> False
    marked global = or (Map.findWithDefault [] global (Env.envArguments env))
    namedArgument name = maybe False marked (Map.lookup (nameText name) (Env.envNames env))
    binder value = binderImpl value || isNothing (binderType value)
    patternNeeded WildPattern {} = True
    patternNeeded (Pattern _ explicit name _) = primitivePattern name || not explicit && namedArgument name
    primitivePattern name = case Map.lookup (nameText name) (Env.envNames env) of
        Just (Core.GlobalInd block index) -> primitiveFamily block index
        Just (Core.GlobalCon block index _) -> primitiveFamily block index
        _ -> False
    primitiveFamily block index = case Env.entryDecl <$> Map.lookup block (Env.envDecls env) of
        Just (Env.Inductive _ families) -> isJust (atIndex index families >>= Env.familyRecord)
        _ -> False
    familyAlias arms = case arms of
        Branch _ (Pattern _ _ name _) _ : _ -> case Map.lookup (nameText name) (Env.envNames env) of
            Just (Core.GlobalCon block index _) -> case Map.lookup block (Env.envDecls env) of
                Just (Env.Entry { Env.entryDecl = Env.Inductive _ families }) -> maybe False (not . visibleTelescope . Env.familyType) (atIndex index families)
                _ -> False
            _ -> False
        _ -> False
    visibleTelescope typ = case typ of
        Core.Pi _ _ body -> visibleTelescope body
        Core.Prop -> True
        Core.Type _ -> True
        _ -> False
    unordered arms = or [j /= place | (place, Branch _ (Pattern _ _ name _) _) <- zip [0 ..] arms, Just (Core.GlobalCon _ _ j) <- [Map.lookup (nameText name) (Env.envNames env)]]

propose :: Kernel -> Limits -> Env.Env -> Maybe Term -> Term -> IO (Either Diagnostic (Core.Term, Core.Term))
propose = proposeDisplaying id

proposeDisplaying :: (Env.Env -> Env.Env) -> Kernel -> Limits -> Env.Env -> Maybe Term -> Term -> IO (Either Diagnostic (Core.Term, Core.Term))
proposeDisplaying display = proposeCompleting display False [] Nothing

proposeWith :: [TermNode] -> Kernel -> Limits -> Env.Env -> Maybe Term -> Term -> IO (Either Diagnostic (Core.Term, Core.Term))
proposeWith premises = proposeCompleting id False premises Nothing

proposeUniverses :: Kernel -> Limits -> Env.Env -> Maybe UniverseRequest -> Maybe Term -> Term -> IO (Either Diagnostic UniverseProposal)
proposeUniverses = proposeUniversesDisplaying id

proposeUniversesDisplaying :: (Env.Env -> Env.Env) -> Kernel -> Limits -> Env.Env -> Maybe UniverseRequest -> Maybe Term -> Term -> IO (Either Diagnostic UniverseProposal)
proposeUniversesDisplaying display kernel limits env Nothing annotation source
    | not (needsUniverses env source || maybe False (needsUniverses env) annotation) = fmap (fmap (\(term, typ) -> UniverseProposal term typ Core.emptyUniverses Set.empty [])) (proposeDisplaying display kernel limits env annotation source)
proposeUniversesDisplaying display kernel limits env request annotation source = proposeCompletingMode display False [] Nothing (Just (requestMode request)) kernel limits env annotation source

proposeFixpoint :: Kernel -> Limits -> Env.Env -> Term -> IO (Either Diagnostic (Core.Term, Core.Term))
proposeFixpoint = proposeFixpointDisplaying id

proposeFixpointDisplaying :: (Env.Env -> Env.Env) -> Kernel -> Limits -> Env.Env -> Term -> IO (Either Diagnostic (Core.Term, Core.Term))
proposeFixpointDisplaying display kernel limits env = proposeCompleting display True [] Nothing kernel limits env Nothing

proposeFixpointUniversesDisplaying :: (Env.Env -> Env.Env) -> Kernel -> Limits -> Env.Env -> Maybe UniverseRequest -> Term -> IO (Either Diagnostic UniverseProposal)
proposeFixpointUniversesDisplaying display kernel limits env Nothing source
    | not (needsUniverses env source) = fmap (fmap (\(term, typ) -> UniverseProposal term typ Core.emptyUniverses Set.empty [])) (proposeFixpointDisplaying display kernel limits env source)
proposeFixpointUniversesDisplaying display kernel limits env request source = proposeCompletingMode display True [] Nothing (Just (requestMode request)) kernel limits env Nothing source

-- The type of a constructor, `forall binders, signature`. `outer` is the
-- environment around the block: the binders are the parameters of the block
-- and are read there. `env` has the families of the block too.
proposeConstructor :: [TermNode] -> Core.ConstId -> Int -> Int -> Env.Env -> Kernel -> Limits -> Env.Env -> Term -> IO (Either Diagnostic (Core.Term, Core.Term))
proposeConstructor = proposeConstructorDisplaying id

proposeConstructorDisplaying :: (Env.Env -> Env.Env) -> [TermNode] -> Core.ConstId -> Int -> Int -> Env.Env -> Kernel -> Limits -> Env.Env -> Term -> IO (Either Diagnostic (Core.Term, Core.Term))
proposeConstructorDisplaying display premises block index parameters outer kernel limits env = proposeCompleting display False premises (Just (block, index, parameters, outer)) kernel limits env Nothing

-- A mutual block is one proposal: its arities and constructor types share
-- both the level-marker namespace and the constraint collector. The private
-- [lb] instance marks only references to this as-yet unpublished block.
proposeInductiveUniversesDisplaying :: (Env.Env -> Env.Env) -> Kernel -> Limits -> Env.Env -> Maybe UniverseRequest -> [IndBody] -> IO (Either Diagnostic (Core.UniverseContext, Env.Decl))
proposeInductiveUniversesDisplaying display kernel limits environment requested bodies = readWithRefresh at limits (fst (requestMode requested) /= 0) run (const answer) idle
    where
        idle (universes, declaration) = idleUniverse universes (Env.declTerms declaration)
        run refresh = case build refresh of
            Left failed -> return (Left failed)
            Right (goal, positions, keys) -> do
                (verdict, _, reason) <- Env.run Env.Persistent (fromMaybe kernel (kernelElaborator kernel)) limits environment [] (listing unnamed found goal) ([output, countOutput, constraintsOutput] ++ [found | unnamed])
                return (Right (listed unnamed verdict, positions, keys, reason))
        unnamed = fst (requestMode requested) == 0
        found = LV_Named "ElaboratedRefreshNodes"
        answer positions verdict reason = case verdict of
            Admitted (value : remaining) -> do
                universes <- either (Left . problem "E-Unsolved") Right (recoverProposalUniverses mode remaining)
                (actual, count, families) <- either (Left . problem "E-Unsolved") Right (recoverBlock value)
                if actual /= block || count /= parameters || length families /= length bodies || not (Env.validUniverses universes)
                    then Left (problem "E-Unsolved" "the elaborator returned an invalid inductive block")
                    else do
                        translated <- sequence [family source result | (source, result) <- zip bodies families]
                        let declaration = Env.Inductive parameters translated
                        if all (Core.wellScopedUniverses (length (Core.universeNames universes)) 0) (Env.declTerms declaration)
                            then Right (universes, declaration)
                            else Left (problem "E-Unsolved" "the inductive proposal has an escaping term or universe parameter")
            Rejected (Just report) -> Left (Diagnostic (reportPosition positions report) "LoL-ElabError" (reportRule report) (reportMessage report) (reportedTerms report ++ maybe [] pure reason))
            Rejected Nothing -> Left (problem "E-Unify" "inductive universe elaboration failed")
            Undecided message -> Left (Diagnostic at "LoL-KernelUndecided" "R5" message [])
            _ -> Left (problem "E-Unsolved" "the elaborator returned an incomplete inductive proposal")
        at = case bodies of
            IndBody place _ _ _ _ : _ -> place
            [] -> Span (1, 1) (1, 1)
        initial = snd (requestMode requested)
        mode = Just (requestMode requested)
        block = Env.envFresh environment
        parameters = case bodies of
            IndBody _ _ binders _ _ : _ -> sum (map (length . binderVars) binders)
            [] -> 0
        globals = Map.fromList [(nameText name, Core.GlobalInd block index) | (index, IndBody _ name _ _ _) <- zip [0 ..] bodies]
        syntax = Env.envSyntax environment
        arguments = Map.fromList [(Core.GlobalInd block index, flags binders ++ typeFlags arity) | (index, IndBody _ _ binders arity _) <- zip [0 ..] bodies]
        inner = Env.withSyntax syntax { Env.syntaxArguments = Map.union arguments (Env.syntaxArguments syntax) } (Env.withNames (Map.union globals (Env.envNames environment)) environment)
        flags = concatMap (\binder -> replicate (length (binderVars binder)) (binderImpl binder))
        typeFlags term = case termForm term of
            SForall binders body -> flags binders ++ typeFlags body
            SParen body -> typeFlags body
            _ -> []
        output = LV_Named "ElaboratedBlock"
        countOutput = LV_Named "ElaboratedUniverseCount"
        constraintsOutput = LV_Named "ElaboratedUniverseConstraints"
        problem code message = Diagnostic at "LoL-ElabError" code message []
        build refresh = do
            if null bodies || not (Env.validUniverses initial) then Left (problem "E-Universe" "an inductive proposal requires a nonempty block and a valid declared context") else return ()
            (families, (_, positions, holes, _, _, _, _, universes)) <- runStateT (foldM rawParameters Nothing bodies >> mapM rawSignature bodies >>= \signatures -> zipWithM rawFamily signatures bodies) (0, Map.empty, [], Nothing, True, [], OrdinaryEncoding, Just (refreshing refresh (newUniverseBuild initial 0 (bareOf (fst (requestMode requested))))))
            built <- maybe (Left (problem "E-Universe" "the universe marker context was lost")) Right universes
            if not (null holes) then Left (problem "E-Unsolved" "the block template has an allocated term hole") else return ()
            let goal = builtRaw "e_u_inductive" (universePrefix (fst (requestMode requested)) initial built ++
                    [ natural block, natural (toInteger parameters)
                    , builtList (kindOf "urawfamily") families
                    , mkLVar output, mkLVar countOutput, mkLVar constraintsOutput
                    ])
            assertNonnegativeIndices goal `seq` return (goal, positions, nodeKeys built)
        -- The parameters of a block are read once by Rocq, before its arities:
        -- the universes of the bare `Type`s in the binders of the first family
        -- are those of the binders of the others.
        rawParameters shared (IndBody place _ binders _ _) = do
            replaying (\universe -> universe { bareReplay = fromMaybe [] shared, bareTrace = [] })
            _ <- encodeUnder environment [] (Term place (SForall binders (Term place SProp)))
            (_, _, _, _, _, _, _, universes) <- get
            replaying (\universe -> universe { bareReplay = [] })
            return (Just (fromMaybe (maybe [] (reverse . bareTrace) universes) shared))
        replaying change = modify (\(next, positions, holes, constructor, template, defaults, proof, universes) -> (next, positions, holes, constructor, template, defaults, proof, fmap change universes))
        -- The arities of a block are read before its constructors, as Rocq
        -- reads them: the markers are in the order of its universes.
        rawSignature (IndBody place _ binders arity constructors) = do
            concluding (fmap (\written -> (written, length constructors >= 2)) (arityConclusion arity))
            signature <- encodeUnder environment [] (Term place (SForall binders arity))
            concluding Nothing
            return signature
        rawFamily signature (IndBody _ _ binders _ constructors) = do
            values <- mapM (rawConstructor binders) constructors
            return (builtRaw "u_raw_family" [signature, builtRawList values])
        rawConstructor binders (Constructor place _ signature) = do
            modify (\(next, positions, holes, _, template, defaults, proof, universes) -> (next, positions, holes, Just (block, parameters, hasFix signature), template, defaults, proof, universes))
            number <- positionOf place
            value <- encodeBindersIn environment inner "r_pi" [] [] binders signature
            modify (\(next, positions, holes, _, template, defaults, proof, universes) -> (next, positions, holes, Nothing, template, defaults, proof, universes))
            return (builtRaw "r_at" [natural number, value])
        family (IndBody place name binders arity constructors) (signature, values)
            | length constructors /= length values = Left (problem "E-Unsolved" "the elaborator changed a constructor count")
            | otherwise = Right (Env.Family (nameText name) (withSourceHints environment (Term place (SForall binders arity)) signature)
                [(nameText given, withSourceHints inner (Term location (SForall binders written)) value) | (Constructor location given written, value) <- zip constructors values])
        reportPosition positions report = maybe at (\index -> Map.findWithDefault at index positions) (reportSourceNumber report)
        -- The first term of a report of the elaborator is where it was made.
        reportedTerms report = (if take 2 (reportRule report) == "E-" && maybe False (const True) (reportSourceNumber report) then drop 1 else id) (reportTerms (display environment) report)
        reportMessage report = fromMaybe "inductive universe elaboration failed" (unsettledLevel (reportRule report))
        concluding place = modify (\(next, positions, holes, constructor, template, defaults, proof, universes) -> (next, positions, holes, constructor, template, defaults, proof, fmap (\universe -> universe { buildingConclusion = place }) universes))

-- What the elaborator says of a level that a declaration with named
-- universes left out and that nothing settles.
unsettledLevel :: String -> Maybe String
unsettledLevel rule = case rule of
    "E-Conclusion" -> Just "the constructors give the conclusion Type of an arity no level: write the level, as in Type@{u}"
    "E-Level" -> Just "a level that is left out has no value here: write the level or the universe instance"
    "E-Set" -> Just "a universe of the declaration would have to be below Set: no such universe is made (Rocq: Cannot enforce u <= Set)"
    "E-Algebraic" -> Just "a level has to be below a maximum or a successor, and the constraints of the declaration do not say that it is: write the constraint (Rocq: cannot handle algebraic on the right)"
    _ -> Nothing

-- Where the arity of an inductive type ends in a `Type` without a level or
-- with a hole for one: below its products and its definitions, as Rocq looks
-- for it.
arityConclusion :: Term -> Maybe Span
arityConclusion = conclusion False where
    conclusion cast arity = case termForm arity of
        SForall _ body -> conclusion cast body
        SArrow _ body -> conclusion cast body
        SLet _ _ _ body -> conclusion cast body
        SParen body -> conclusion cast body
        -- A cast prevents a bare Type from becoming a flexible conclusion.
        -- An explicitly flexible Type@{_} still gets the constructors' bound.
        SAnnotation value _ -> conclusion True value
        SInferredType | not cast -> Just (termSpan arity)
        SUniverse level | LHole <- levelForm level -> Just (termSpan arity)
        _ -> Nothing

proposeCompleting :: (Env.Env -> Env.Env) -> Bool -> [TermNode] -> Maybe (Core.ConstId, Int, Int, Env.Env) -> Kernel -> Limits -> Env.Env -> Maybe Term -> Term -> IO (Either Diagnostic (Core.Term, Core.Term))
proposeCompleting display command premises constructor kernel limits env annotation source = do
    result <- proposeCompletingMode display command premises constructor Nothing kernel limits env annotation source
    return $ do
        proposal <- result
        if proposedUniverses proposal == Core.emptyUniverses
            then Right (proposedTerm proposal, proposedType proposal)
            else Left (universeError (termSpan source) "the monomorphic proposal API cannot return a universe scheme")

proposeCompletingMode :: (Env.Env -> Env.Env) -> Bool -> [TermNode] -> Maybe (Core.ConstId, Int, Int, Env.Env) -> Maybe (Integer, Core.UniverseContext) -> Kernel -> Limits -> Env.Env -> Maybe Term -> Term -> IO (Either Diagnostic UniverseProposal)
proposeCompletingMode display command premises constructor universeMode kernel limits env annotation source = readWithRefresh (termSpan source) limits (fmap fst universeMode /= Just 0) run answer idle
    where
        idle proposal = idleUniverse (proposedUniverses proposal) [proposedTerm proposal, proposedType proposal]
        run refresh = case build refresh of
            Left problem -> return (Left problem)
            Right (goal, outputs, positions, keys, _) -> do
                (verdict, _, reason) <- Env.run Env.Persistent (fromMaybe kernel (kernelElaborator kernel)) limits env [] (listing unnamed found goal) (outputs ++ [found | unnamed])
                return (Right (listed unnamed verdict, positions, keys, reason))
        unnamed = fmap fst universeMode == Just 0
        found = LV_Named "ElaboratedRefreshNodes"
        answer refresh positions verdict reason = case verdict of
            Admitted (value : typ : remaining) -> do
                let (scheme, rest) = splitAt 2 remaining
                context <- either (\message -> Left (diagnostic "E-Unsolved" message [])) Right (recoverContext (if maybe False (const True) universeMode then scheme else remaining))
                marks <- case (universeMode, map recoverTerm rest, build refresh) of
                    (Just _, [Right (Core.Cst 0 levels)], Right (_, _, _, _, kinds))
                        | length kinds == length levels && all (Core.wellScopedLevel (length (Core.universeNames context))) levels -> Right (zip kinds levels)
                    (Just _, _ : _, _) -> Left (diagnostic "E-Unsolved" "the elaborator did not say where the universe markers of the term ended" [])
                    _ -> Right []
                case (recoverTerm value, recoverTerm typ) of
                    (Right term, Right signature)
                        | Env.validUniverses context && all (Core.wellScopedUniverses (length (Core.universeNames context)) 0) [term, signature] ->
                            Right (UniverseProposal (withSourceHints env source term) (maybe signature (\written -> withSourceHints env written signature) annotation) context refresh marks)
                    _ -> Left (diagnostic "E-Unsolved" "the elaborator did not return closed Core terms in its universe context" [])
            Admitted _ -> Left (diagnostic "E-Unsolved" "the elaborator returned an incomplete answer" [])
            Rejected (Just report) -> Left (reported positions report reason)
            Rejected Nothing -> Left (diagnostic "E-Unify" "surface elaboration failed" [])
            Undecided message -> Left (Diagnostic (termSpan source) "LoL-KernelUndecided" "R5" message [])
        output = LV_Named "Elaborated"
        typ = LV_Named "ElaboratedType"
        countOutput = LV_Named "ElaboratedUniverseCount"
        constraintsOutput = LV_Named "ElaboratedUniverseConstraints"
        fixedOutput = LV_Named "ElaboratedFixedUniverses"
        build refresh = do
            ((body, declaration), (_, positions, holes, _, _, _, _, builtUniverses)) <- runStateT (if maybe False (const True) universeMode then flip (,) <$> traverse (encodeUnder env []) annotation <*> whole else (,) <$> whole <*> traverse (encodeUnder env []) annotation) (0, Map.empty, [], fmap (\(block, _, count, _) -> (block, count, hasFix source)) constructor, maybe False (const True) universeMode, [], OrdinaryEncoding, fmap (\(explicit, context) -> refreshing refresh (newUniverseBuild context 0 (bareOf explicit))) universeMode)
            let proposal = case constructor of
                    Nothing -> builtRaw "e_query" [body, mkLVar output, mkLVar typ]
                    Just (block, index, parameters, _) -> builtRaw "e_constructor_query" [body, natural (toInteger parameters), natural block, natural (toInteger index), mkLVar output, mkLVar typ]
                ordinaryCommand = maybe proposal (\declared -> builtRaw "e_definition" [declared, body, mkLVar typ, mkLVar output]) declaration
                selectedCommand = case (universeMode, builtUniverses) of
                    (Just (explicit, context), Just universe) ->
                        let prefix = universePrefix explicit context universe
                            suffix = [mkLVar countOutput, mkLVar constraintsOutput]
                        in case declaration of
                            Nothing -> builtRaw "e_u_query" (prefix ++ [body, mkLVar output, mkLVar typ] ++ suffix ++ [mkLVar fixedOutput])
                            Just declared -> builtRaw "e_u_definition" (prefix ++ [declared, body, mkLVar typ, mkLVar output] ++ suffix)
                    _ -> ordinaryCommand
                goal = builtApply (mkNCon LO_imply) [builtRaw "e_at" [natural 0], foldr (\premise rest -> builtApply (mkNCon LO_imply) [premise, rest]) selectedCommand premises]
                outputs = output : typ : case universeMode of
                    Nothing -> holes
                    Just _ -> [countOutput, constraintsOutput] ++ [fixedOutput | Nothing <- [declaration]]
            case universeMode of
                Just (_, context)
                    | not (Env.validUniverses context) -> Left (universeError (termSpan source) "the declared universe context is malformed")
                    | not (null holes) || maybe False (const True) constructor -> Left (universeError (termSpan source) "a universe proposal requires a closed whole-declaration template")
                _ -> return ()
            assertNonnegativeIndices goal `seq` return (goal, outputs, positions, maybe Map.empty nodeKeys builtUniverses, maybe [] (reverse . markerKinds) builtUniverses)
        recoverContext = recoverProposalUniverses universeMode
        whole = case (constructor, termForm source) of
            (Just (_, _, _, outer), SForall binders signature) -> do
                number <- positionOf (termSpan source)
                value <- encodeBindersIn outer env "r_pi" [] [] binders signature
                return (builtRaw "r_at" [natural number, value])
            _ -> encodeUnderWith command env [] source
        diagnostic code message = Diagnostic (termSpan source) "LoL-ElabError" code message
        reported positions report reason = Diagnostic at kind (reportRule report) message (terms ++ oracleReason) where
            oracleReason = if reportRule report `elem` ["F-Guard", "I-Pos"] then maybe [] (pure . ("the oracle says: " ++)) reason else []
            terms = if located then drop 1 (reportTerms (display env) report) else reportTerms (display env) report
            located = take 2 (reportRule report) == "E-" || (reportRule report == "F-Guard" && maybe False (const True) sourceNumber)
            location = if located then sourceNumber else Nothing
            sourceNumber = reportSourceNumber report
            at = maybe (termSpan source) (\number -> Map.findWithDefault (termSpan source) number positions) location
            kind = if take 2 (reportRule report) == "E-" then "LoL-ElabError" else "LoL-KernelError"
            message = if kind == "LoL-ElabError" then fromMaybe "surface elaboration failed" (unsettledLevel (reportRule report)) else "the kernel rejected a component during elaboration"

-- The statement of a theorem as the proof program reads it: with the
-- universes of the nodes that the proposal of its header found.
statementOf :: Env.Env -> Maybe UniverseRequest -> Refresh -> Term -> Either Diagnostic Statement
statementOf env request refresh source = do
    let (explicit, context) = requestMode request
    (body, (_, positions, holes, _, _, _, _, built)) <- runStateT (encodeUnder env [] source) (0, Map.empty, [], Nothing, True, [], OrdinaryEncoding, Just (refreshing refresh (newUniverseBuild context 0 (bareOf explicit))))
    universe <- maybe (Left (universeError (termSpan source) "the universe marker context was lost")) Right built
    if null holes then return () else Left (universeError (termSpan source) "the statement of a theorem has an allocated term hole")
    assertNonnegativeIndices body `seq` return (Statement (universePrefix explicit context universe) body positions (Core.universeNames context) (surfaceHints source) Nothing explicit)

-- A proof hole receives its own binder spellings, including those of the
-- domains of its products. This tree contains no Core terms or logic cells.
surfaceHints :: Term -> TermNode
surfaceHints term = case termForm term of
    SForall binders body -> foldr group (surfaceHints body) binders
    SArrow domain body -> hintNode "" (surfaceHints domain) (surfaceHints body)
    SLet name domain _ body -> hintNode (nameText name) (maybe emptyHints surfaceHints domain) (surfaceHints body)
    SParen body -> surfaceHints body
    SAnnotation body _ -> surfaceHints body
    _ -> emptyHints
    where
        group binder rest = foldr add rest (binderVars binder) where
            add name = hintNode (nameText name) domain
            domain = maybe emptyHints surfaceHints (binderType binder)

emptyHints :: TermNode
emptyHints = named "p_no_hints"

hintNode :: String -> TermNode -> TermNode -> TermNode
hintNode "_" domain rest = hintNode "" domain rest
hintNode "" domain rest
    | domain == emptyHints && rest == emptyHints = emptyHints
hintNode name domain rest = builtRaw "p_binding" [builtList (kindOf "char") (map (mkNCon . DC_ChrL) name), domain, rest]

coreHints :: Core.Term -> TermNode
coreHints term = case term of
    Core.Pi name domain rest -> hintNode name (coreHints domain) (coreHints rest)
    Core.Let name _ domain rest -> hintNode name (coreHints domain) (coreHints rest)
    Core.Cast body _ -> coreHints body
    _ -> emptyHints

-- The proposed context must imply the obligations of the instantiated
-- header. A direct witness can justify additional obligations through the
-- clean elaborator, independently of the tactic program.
proofConstraints :: Kernel -> Limits -> Env.Env -> Span -> [Core.UniverseConstraint] -> Bool -> Core.UniverseContext -> Core.Term -> Core.Term -> IO (Either Diagnostic ())
proofConstraints kernel limits env at original direct proposed typ body
    | null goals = return (Right ())
    | otherwise = do
        (verdict, _, _) <- run (foldr1 both goals)
        return $ case verdict of
            Admitted [] -> Right ()
            Rejected _ -> Left refused
            Undecided reason -> Left (Diagnostic at "LoL-KernelUndecided" "R5" reason [])
            _ -> Left (Diagnostic at "LoL-KernelUndecided" "R5" "Unexpected result from universe constraint verification." [])
    where
        run goal = Env.run Env.Persistent (fromMaybe kernel (kernelElaborator kernel)) limits env [body] goal []
        refused = Diagnostic at "LoL-ProofError" "P-Statement" "The proposed universe constraints do not match the obligations of the theorem." []
        count = natural (toInteger (length (Core.universeNames proposed)))
        claimed = Core.universeConstraints proposed
        given = embedUniverseConstraints claimed
        literal term = builtRaw "r_ref" [embedTerm term, builtList (kindOf "rmode") []]
        both a b = builtApply (mkNCon LO_and) [a, b]
        implies a b = builtRaw "e_u_closed_obligations" [count, a, b]
        goals = [implies given (embedUniverseConstraints original) | any (`notElem` claimed) original] ++ [fromWitness | direct, any (`notElem` original) claimed]
        fromWitness = builtApply (mkNCon LO_imply) [builtRaw "e_at" [natural 0], mkNApp (mkNCon LO_sigma) (mkNLamHint Nothing (both definition (implies (mkNIdx 0) given)))]
        definition = builtRaw "e_u_definition" [count, builtList (kindOf "nat") [], embedUniverseConstraints original, natural 2, literal typ, literal body, embedTerm typ, embedTerm body, count, mkNIdx 0]

-- Source markers are closed Core constants with an empty instance. Read the
-- recovered structure rather than depending on the rendered wire spelling.
reportSourceNumber :: Report -> Maybe Integer
reportSourceNumber report = case reportCore report of
    Just (ReportTerm _ (Core.Cst number [])) : _ | number >= 0 -> Just number
    _ -> Nothing

recoverProposalUniverses :: Maybe (Integer, Core.UniverseContext) -> [TermNode] -> Either String Core.UniverseContext
recoverProposalUniverses universeMode remaining = case universeMode of
    Nothing -> Right Core.emptyUniverses
    Just (explicit, original) -> case remaining of
        [NCon (DC (DC_NatL count)) _, constraints]
            | count >= 0 && count <= toInteger (maxBound :: Int) -> do
                obligations <- recoverUniverseConstraints constraints
                let oldNames = Core.universeNames original
                    wanted = fromInteger count
                if wanted < length oldNames then Left "the elaborator dropped a declared universe parameter" else do
                    let names = oldNames ++ take (wanted - length oldNames) [name | index <- [0 :: Integer ..], let name = "u" ++ show index, name `notElem` oldNames]
                        context = Core.UniverseContext names obligations
                    if explicit == 1 && context /= original then Left "the elaborator changed an explicit universe context"
                    else if explicit == 2 && (names /= oldNames || not (all (`elem` obligations) (Core.universeConstraints original))) then Left "the elaborator changed the parameters or dropped a constraint of an open universe context"
                    else Right context
        _ -> Left "the elaborator did not return a closed universe context"

-- Hints change no Core constructor or index. A written binder keeps its
-- name. Of the binders that the user did not write, as in Rocq: an implicit
-- position of a pattern has the name that the declaration gives it, other
-- than a name written in that pattern; a position that a wildcard branch
-- covers has no name; and the scrutinee of an inferred return clause has the
-- name of the scrutinee when that is a variable. Any other inferred binder
-- retains the name returned by Hol.
withSourceHints :: Env.Env -> Term -> Core.Term -> Core.Term
withSourceHints env source core = case (termForm source, core) of
    (SMask _ _ inner, _) -> again inner core
    (SWithout hidden inner, _) -> withSourceHints (Env.withNames (Map.delete (nameText hidden) (Env.envNames env)) env) inner core
    (SParen inner, _) -> again inner core
    (SAnnotation value annotation, Core.Cast result typ) -> Core.Cast (again value result) (again annotation typ)
    (SForall binders body, _) -> telescope True binders body core
    (SLambda binders body, _) -> telescope False binders body core
    (SArrow domain body, Core.Pi _ typ rest) -> Core.Pi "" (again domain typ) (again body rest)
    (SLet name annotation value body, Core.Let _ result typ rest) -> Core.Let (hint name) (again value result) (maybe typ (\written -> again written typ) annotation) (again body rest)
    (SProjection receiver _, Core.Proj block field value) -> Core.Proj block field (again receiver value)
    (SApp {}, _) -> application source core
    (SFix bodies _, Core.Fix chosen functions)
        | length bodies == length functions -> Core.Fix chosen (zipWith function bodies functions)
    (SMatch term alias family clause branches, Core.Case block index instance_ parameters names motive value arms) -> Core.Case block index instance_ parameters motiveNames (maybe motive (\written -> again written motive) clause) (again term value) (zipWith branch [0 ..] arms) where
        explicitNames = case family of
            Just (Pattern _ explicit name items) -> drop (length parameters) (patternNames explicit (Core.GlobalInd block index) items)
            _ -> []
        self = maybe "" hint alias
        proposed = explicitNames ++ [self]
        motiveNames = case (clause, variable term, value, reverse names) of
            (Just _, _, _, _) -> if length proposed == length names then proposed else names
            (Nothing, Just given, Core.Var _, _ : indices) -> reverse (given : indices)
            _ -> names
        variable written = case termForm written of
            SParen inner -> variable inner
            SName name -> Just (hint name)
            _ -> Nothing
        branch number arm = case [pair | Branch _ pattern body <- branches, pair <- select number pattern body] of
            (bound, body) : _ -> (if length bound == length (fst arm) then bound else fst arm, again body (snd arm))
            [] -> arm
        select number pattern body = case pattern of
            Pattern _ explicit name items
                | Map.lookup (nameText name) (Env.envNames env) == Just (Core.GlobalCon block index number) -> [(drop (length parameters) (patternNames explicit (Core.GlobalCon block index number) items), body)]
            WildPattern _ -> [(map (const "") (fst (arms !! number)), body)]
            _ -> []
    _ -> core
    where
        again = withSourceHints env
        hint name = if nameText name == "_" then "" else nameText name
        telescope product binders body = bind (concatMap (\binder -> [(name, binderType binder) | name <- binderVars binder]) binders) where
            bind [] term = again body term
            bind ((name, annotation) : rest) term = case term of
                Core.Pi _ typ value
                    | product -> Core.Pi (hint name) (maybe typ (\written -> again written typ) annotation) (bind rest value)
                Core.Lam _ typ value
                    | not product -> Core.Lam (hint name) (maybe typ (\written -> again written typ) annotation) (bind rest value)
                _ -> term
        function (FixBody at name binders _ annotation body) value = value
            { Core.functionName = hint name
            , Core.functionType = again (Term at (SForall binders annotation)) (Core.functionType value)
            , Core.functionBody = again (Term at (SLambda binders body)) (Core.functionBody value)
            }
        patternNames explicit global items = fill (if explicit then [] else Map.findWithDefault [] global (Env.envArguments env)) (declared ++ repeat "") written where
            written = map hint items
            declared = products (maybe Core.Prop id (signatureOf global))
            fill [] _ names = names
            fill (True : flags) (given : more) names = fresh given : fill flags more names
            fill (False : flags) (_ : more) (name : names) = name : fill flags more names
            fill _ _ _ = []
            fresh given = if null given then "" else head [candidate | candidate <- given : [given ++ show number | number <- [1 :: Int ..]], candidate `notElem` written]
        signatureOf global = case global of
            Core.GlobalInd b i -> Env.familyType <$> familyOf b i
            Core.GlobalProj {} -> Nothing
            Core.GlobalCon b i j -> familyOf b i >>= fmap snd . atIndex j . Env.familyCons
            _ -> Nothing
        familyOf b i = case Map.lookup b (Env.envDecls env) of
            Just (Env.Entry { Env.entryDecl = Env.Inductive _ families }) -> atIndex i families
            _ -> Nothing
        products typ = case typ of
            Core.Pi given _ rest -> given : products rest
            _ -> []
        application written value = Core.apps (again headSource headTerm) (arguments modes rawArguments coreArguments) where
            (headSource, rawArguments) = writtenSpine [] written
            writtenSpine rest term = case termForm term of
                SApp left right -> writtenSpine (right : rest) left
                SParen inner -> writtenSpine rest inner
                _ -> (term, rest)
            (headTerm, coreArguments) = coreSpine [] value
            coreSpine rest (Core.App left right) = coreSpine (right : rest) left
            coreSpine rest term = (term, rest)
            modes = case termForm headSource of
                SExplicit _ -> []
                SDeclared _ -> []
                _ -> case headTerm of
                    Core.Cst constant _ -> Map.findWithDefault [] (Core.GlobalCst constant) (Env.envArguments env)
                    Core.Ind block index _ -> Map.findWithDefault [] (Core.GlobalInd block index) (Env.envArguments env)
                    Core.Con block index constructor _ -> Map.findWithDefault [] (Core.GlobalCon block index constructor) (Env.envArguments env)
                    _ -> []
            arguments (True : flags) raws (term : terms) = term : arguments flags raws terms
            arguments flags (raw : raws) (term : terms) = again raw term : arguments (drop 1 flags) raws terms
            arguments _ _ terms = terms
