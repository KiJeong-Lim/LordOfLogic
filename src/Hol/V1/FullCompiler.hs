module Hol.V1.FullCompiler (compileFullProgram, PreparedProgram, prepareFullProgram, preparedUniqueFloor, restorePreparedProgram, restoreCheckedProgram, compilePreparedProgram, LoadedTables, loadedUniqueFloor, loadPreparedProgram, extendLoadedProgram, extendLoadedEnvironment, queryLoadedProgram, loadedFragmentUniqueFloor, validateLoadedFragment, fragmentIndices, fragmentMetadataIndices, loadedSourceTerms) where

import Control.Monad
import Control.Monad.Trans.Class
import Control.Monad.Trans.State.Strict
import Data.Char (chr, ord)
import Data.Int
import qualified Data.IntMap.Strict as IntMap
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Hol.BETA.Constant
import Hol.BETA.Header
import Hol.BETA.ModuleLoader (polyTypeEq)
import Hol.BETA.Runtime (expandAssumptions)
import Hol.BETA.TermNode
import Hol.V1.Bytecode (bytecodeMagic)
import Hol.V1.FullBytecode
import Hol.V1.Checked

-- Every field of a template row, including pooled-literal payload references.
data TermKey
    = TermKey !Int64 !Int64 !Int64 !Int64
    | StringKey !Int64 !Int64 !Int64 !Int64 !Int64
    deriving (Eq, Ord)

data Build
    = Build
        { builtTerms    :: IntMap.IntMap [Int64]
        , termCount     :: !Int
        , termKeys      :: Map.Map TermKey Int
        , builtSymbols  :: IntMap.IntMap FullSymbol
        , symbolKeys    :: Map.Map String Int
        , constantKeys  :: Map.Map Constant Int
        , builtMetadata :: IntMap.IntMap NodeMetadata
        , metadataCount :: !Int
        , metadataKeys  :: Map.Map (Maybe String, Maybe StoredType, Maybe ((Int, Int), (Int, Int))) Int
        , digitPayload  :: [Int64]
        , digitCount    :: Int
        , literalKeys   :: Map.Map String (Int, Int)
        , stringKeys    :: Map.Map String (Int, Int)
        , variableSlots :: Map.Map LogicVar Int
        }
    deriving ()

-- Valid artifacts may repeat template or annotation rows. Interning maps
-- deduplicate their keys; row counts must retain the original numbering.
type Compile = StateT Build (Either String)

-- Facts that are compiled already. A query and further facts are compiled on
-- top of them (compilePreparedProgram), so their cost is paid once.
data PreparedProgram
    = PreparedProgram
        { preparedBuild  :: Build
        , preparedFacts  :: [[Int64]]
        , preparedKinds  :: KindEnv
        , preparedTypes  :: TypeEnv
        , preparedLoaded :: Maybe (FullProgram, LoadedTables)
        }
    deriving ()

-- The symbols and annotations of a program that a machine holds. Fragments are
-- compiled against them: they number their own templates, clauses and digits
-- from zero, and add to these two tables only.
data LoadedTables
    = LoadedTables
        { loadedBuild :: Build
        , loadedKinds :: KindEnv
        , loadedTypes :: TypeEnv
        , loadedFloor :: Int
        }
    deriving ()

compileFullProgram :: [TermNode] -> TermNode -> Either String FullProgram
compileFullProgram facts query = assertNonnegativeTerms (query : facts) `seq` do
    let expanded = concatMap expandAssumptions facts
        variables = Set.toAscList (Set.unions (map termVariables (query : expanded)))
    ((slots, root, clauses), built) <- runStateT (internBuiltins >> compileQuery Map.empty variables query expanded) (emptyBuild { variableSlots = Map.fromList (zip variables [0 ..]) })
    let program = assemble 0 built variables slots root clauses
    validateFullBytecode program
    return program

-- The facts have no logic variable. The symbols of the two environments are
-- interned here, as withRuntimeMetadata adds them to a compiled program.
prepareFullProgram :: KindEnv -> TypeEnv -> [TermNode] -> Either String PreparedProgram
prepareFullProgram kinds types facts = assertNonnegativeTerms facts `seq` do
    let expanded = concatMap expandAssumptions facts
    unless (all (Set.null . termVariables) expanded) (Left "a prepared fact has a logic variable")
    (clauses, built) <- runStateT (internBuiltins >> mapM compileFact expanded <* mapM_ (internSymbol . ConstantSymbol) (map TC (Map.keys kinds) ++ map DC (Map.keys types))) emptyBuild
    let prepared = PreparedProgram built clauses kinds types Nothing
    loaded <- loadPreparedProgram prepared
    return prepared { preparedLoaded = Just loaded }

-- Preparation and cache restoration retain the validated load bundle. Reading
-- its identity floor must not revisit an unchanged program for each query.
loadedUniqueFloor :: LoadedTables -> Int
loadedUniqueFloor = loadedFloor

preparedUniqueFloor :: PreparedProgram -> Either String Int
preparedUniqueFloor = fmap (loadedFloor . snd) . loadPreparedProgram

-- Rebuild compiler indices from a validated, closed prepared artifact. The
-- clauses remain wordcode: cache loading does not parse or compile Hol again.
restorePreparedProgram :: FullProgram -> Either String PreparedProgram
restorePreparedProgram program = checkProgram program >>= fmap fst . restoreCheckedProgram

-- The immutable witness lets cache loading reuse validation. It cannot be
-- forged by callers, and the public engine only accepts opaque PreparedProgram.
restoreCheckedProgram :: CheckedProgram -> Either String (PreparedProgram, [TermNode])
restoreCheckedProgram checked = do
    let program = checkedProgram checked
    let (_, slots, _, rows, clauses, payload) = checkedSections checked
    unless (null slots && null (fullVariables program)) (Left "a prepared artifact has query variables")
    let terms = IntMap.fromDistinctAscList (zip [0 ..] rows)
        -- CheckedProgram has already checked the six fields and both reserved operands.
        termIndex = Map.fromList
            [(if tag == 7 then StringKey a b c d meta else TermKey tag a b meta, index)
                | (index, [tag, a, b, c, d, meta]) <- zip [0 ..] rows]
        symbols = fullSymbols program
        metadata = fullMetadata program
        metadataIndex = Map.fromList (zip (checkedMetadata checked) [0 ..])
        payloadTable = IntMap.fromDistinctAscList (zip [0 ..] payload)
        slice offset count = take (fromIntegral count) (IntMap.elems (snd (IntMap.split (fromIntegral offset - 1) payloadTable)))
        naturalEntries = [(map (chr . fromIntegral) (slice offset count), (fromIntegral offset, fromIntegral count)) | [5, offset, count, _, _, _] <- rows]
    stringEntries <- forM [(offset, count) | [7, _, _, offset, count, _] <- rows] $ \(offset, count) -> do
        characters <- traverse (character symbols) (slice offset count)
        return (characters, (fromIntegral offset, fromIntegral count))
    let built = Build
            { builtTerms    = terms
            , termCount     = length rows
            , termKeys      = termIndex
            , builtSymbols  = symbols
            , symbolKeys    = Map.fromList [(symbolIdentity value, index) | (index, value) <- IntMap.toList symbols]
            , constantKeys  = Map.fromList [(constant, index) | (index, ConstantSymbol constant) <- IntMap.toList symbols]
            , builtMetadata = metadata
            , metadataCount = IntMap.size metadata
            , metadataKeys  = metadataIndex
            , digitPayload  = reverse payload
            , digitCount    = length payload
            , literalKeys   = Map.fromList naturalEntries
            , stringKeys    = Map.fromList stringEntries
            , variableSlots = Map.empty
            }
    floor <- fullUniqueFloor program
    (facts, _) <- fragmentSourceTermsFrom program (checkedSections checked)
    let loaded = LoadedTables (withoutTemplates built) (fullKindEnv program) (fullTypeEnv program) floor
    return (PreparedProgram built clauses (fullKindEnv program) (fullTypeEnv program) (Just (program, loaded)), facts)
    where
        character symbols symbol = case IntMap.lookup (fromIntegral symbol) symbols of
            Just (ConstantSymbol (DC (DC_ChrL value))) -> Right value
            _ -> Left "a prepared string has a non-character payload"

-- compilePreparedProgram (prepareFullProgram kinds types facts0) queryTypes facts1 query runs like
-- withRuntimeMetadata kinds types queryTypes applied to compileFullProgram (facts0 ++ facts1) query.
-- The program is not validated here: createSession validates every program it runs.
compilePreparedProgram :: PreparedProgram -> Map.Map LogicVar (MonoType Int) -> [TermNode] -> TermNode -> Either String FullProgram
compilePreparedProgram prepared queryTypes facts query = assertNonnegativeTerms (query : facts) `seq` do
    let expanded = concatMap expandAssumptions facts
        variables = queryVariables queryTypes (query : expanded)
    ((slots, root, clauses), built) <- runStateT (compileQuery queryTypes variables query expanded) ((preparedBuild prepared) { variableSlots = Map.fromList (zip variables [0 ..]) })
    return (assemble 0 built variables slots root (preparedFacts prepared ++ clauses)) { fullKindEnv = preparedKinds prepared, fullTypeEnv = preparedTypes prepared, fullQueryTypes = queryTypes }

-- The whole prepared program with the query `true`, for hol_v2_create, and its
-- tables. A machine created from it has no query variable.
loadPreparedProgram :: PreparedProgram -> Either String (FullProgram, LoadedTables)
loadPreparedProgram prepared = case preparedLoaded prepared of
    Just loaded -> Right loaded
    Nothing -> do
        ((slots, root, clauses), built) <- runStateT (compileQuery Map.empty [] (mkNCon (DC_LO LO_true)) []) (preparedBuild prepared)
        let program = (assemble 0 built [] slots root (preparedFacts prepared ++ clauses)) { fullKindEnv = preparedKinds prepared, fullTypeEnv = preparedTypes prepared }
        validateFullBytecode program
        floor <- fullUniqueFloor program
        return (program, LoadedTables (withoutTemplates built) (preparedKinds prepared) (preparedTypes prepared) floor)

-- A fragment that adds facts without a logic variable, and the tables after it.
extendLoadedProgram :: LoadedTables -> [TermNode] -> Either String (FullProgram, LoadedTables)
extendLoadedProgram tables facts = assertNonnegativeTerms facts `seq` do
    let expanded = concatMap expandAssumptions facts
    unless (all (Set.null . termVariables) expanded) (Left "a loaded fact has a logic variable")
    (clauses, built) <- runStateT (mapM compileFact expanded) (loadedBuild tables)
    let program = (assemble (knownSymbols tables) built [] [] (-1) clauses) { fullKindEnv = loadedKinds tables, fullTypeEnv = loadedTypes tables }
    floor <- loadedFragmentUniqueFloor tables program
    return (program, tables { loadedBuild = withoutTemplates built, loadedFloor = floor })

-- Declarations are deltas, not copies of the old environment. Existing names
-- must agree before any native state is touched. The caller type-checks the
-- module with the ordinary Hol frontend, then commits this staged fragment.
extendLoadedEnvironment :: LoadedTables -> KindEnv -> TypeEnv -> [TermNode] -> Either String (FullProgram, LoadedTables)
extendLoadedEnvironment tables kinds types facts = do
    mapM_ agreeKind (Map.toList kinds)
    mapM_ agreeType (Map.toList types)
    let nextKinds = Map.union kinds (loadedKinds tables)
        nextTypes = Map.union types (loadedTypes tables)
        symbols = map TC (Map.keys kinds) ++ map DC (Map.keys types)
        expanded = concatMap expandAssumptions facts
    assertNonnegativeTerms facts `seq` unless (all (Set.null . termVariables) expanded) (Left "a loaded fact has a logic variable")
    (clauses, built) <- runStateT (mapM_ (internSymbol . ConstantSymbol) symbols >> mapM compileFact expanded) (loadedBuild tables)
    let program = (assemble (knownSymbols tables) built [] [] (-1) clauses) { fullKindEnv = nextKinds, fullTypeEnv = nextTypes }
    floor <- fragmentUniqueFloor tables types program
    return (program, LoadedTables (withoutTemplates built) nextKinds nextTypes floor)
    where
        agreeKind (name, kind) = case Map.lookup name (loadedKinds tables) of
            Just old
                | old /= kind -> Left ("module extension changes the kind of " ++ show name)
            _ -> Right ()
        agreeType (name, typ) = case Map.lookup name (loadedTypes tables) of
            Just old
                | not (polyTypeEq old typ) -> Left ("module extension changes the type of " ++ show name)
            _ -> Right ()

-- A fragment with a query. What it adds to the tables lasts for its run.
queryLoadedProgram :: LoadedTables -> Map.Map LogicVar (MonoType Int) -> TermNode -> Either String FullProgram
queryLoadedProgram tables queryTypes query = assertNonnegativeTerms [query] `seq` do
    let variables = queryVariables queryTypes [query]
    ((slots, root, _), built) <- runStateT (compileQuery queryTypes variables query []) ((loadedBuild tables) { variableSlots = Map.fromList (zip variables [0 ..]) })
    return (assemble (knownSymbols tables) built variables slots root []) { fullKindEnv = loadedKinds tables, fullTypeEnv = loadedTypes tables, fullQueryTypes = queryTypes }

-- A fragment compiled against `tables` is validated against them.
-- Identifier reservation shares the same boundary: a query must not rescan
-- the unchanged program merely to find its already known largest identity.
loadedFragmentUniqueFloor :: LoadedTables -> FullProgram -> Either String Int
loadedFragmentUniqueFloor tables = fragmentUniqueFloor tables Map.empty

fragmentUniqueFloor :: LoadedTables -> TypeEnv -> FullProgram -> Either String Int
fragmentUniqueFloor tables newTypes program = do
    floor <- fullUniqueFloor program
        { fullSymbols = snd (IntMap.split (knownSymbols tables - 1) (fullSymbols program))
        , fullMetadata = snd (IntMap.split (metadataCount (loadedBuild tables) - 1) (fullMetadata program))
        , fullKindEnv = Map.empty
        , fullTypeEnv = newTypes
        }
    return (max floor (loadedFloor tables))

-- A fragment compiled against tables is validated against them.
validateLoadedFragment :: LoadedTables -> FullProgram -> Either String ()
validateLoadedFragment tables = validateFullFragment (`Map.member` symbolKeys (loadedBuild tables)) (knownSymbols tables) (metadataCount (loadedBuild tables))

-- The index of every symbol of a fragment compiled against `tables`, by identity.
fragmentIndices :: LoadedTables -> FullProgram -> Map.Map String Int
fragmentIndices tables program = IntMap.foldlWithKey' (\indices index symbol -> Map.insert (symbolIdentity symbol) index indices) (symbolKeys (loadedBuild tables)) (snd (IntMap.split (knownSymbols tables - 1) (fullSymbols program)))

-- Annotation rows retain their physical numbering, including duplicate keys
-- in restored artifacts. Reuse the old reverse map and inspect only new rows.
fragmentMetadataIndices :: LoadedTables -> FullProgram -> Map.Map (Maybe String, Maybe StoredType, Maybe ((Int, Int), (Int, Int))) Int
fragmentMetadataIndices tables program = IntMap.foldlWithKey' (\indices index info -> Map.insert (storeMetadata info) index indices) (metadataKeys (loadedBuild tables)) (snd (IntMap.split (metadataCount (loadedBuild tables) - 1) (fullMetadata program)))

-- The clauses and the query of a fragment compiled against `tables`.
loadedSourceTerms :: LoadedTables -> FullProgram -> Either String ([TermNode], Maybe TermNode)
loadedSourceTerms tables program = validateLoadedFragment tables program >> fragmentSourceTerms (knownSymbols tables) program

knownSymbols :: LoadedTables -> Int
knownSymbols = Map.size . symbolKeys . loadedBuild

withoutTemplates :: Build -> Build
withoutTemplates built = built { builtTerms = IntMap.empty, termCount = 0, termKeys = Map.empty, digitPayload = [], digitCount = 0, literalKeys = Map.empty, stringKeys = Map.empty, variableSlots = Map.empty }

emptyBuild :: Build
emptyBuild = Build IntMap.empty 0 Map.empty IntMap.empty Map.empty Map.empty IntMap.empty 0 Map.empty [] 0 Map.empty Map.empty Map.empty

-- Natural literal views need the successor symbol even when no explicit
-- successor appears in the source.
internBuiltins :: Compile ()
internBuiltins = mapM_ (internSymbol . ConstantSymbol) (map (DC . DC_LO) logicalOperators ++ builtinConstants ++ [DC (DC_Named "read"), DC (DC_Named "print"), DC (DC_Named "flex"), DC (DC_Named "oracle")])

queryVariables :: Map.Map LogicVar (MonoType Int) -> [TermNode] -> [LogicVar]
queryVariables types terms = Set.toAscList variables ++ Set.toAscList (Set.unions (map typeVariables (Map.elems (Map.restrictKeys types variables))) `Set.difference` variables) where
    variables = Set.unions (map termVariables terms)

compileQuery :: Map.Map LogicVar (MonoType Int) -> [LogicVar] -> TermNode -> [TermNode] -> Compile ([[Int64]], Int, [[Int64]])
compileQuery types variables query expanded = do
    slots <- mapM querySlot variables
    root <- compileTerm query
    clauses <- mapM compileFact expanded
    return (slots, root, clauses)
    where
        querySlot variable = do
            meta <- internMetadata (NodeMetadata (variableHint variable) noLamType Nothing)
            typ <- traverse (compileType 0 Map.empty) (Map.lookup variable types)
            when (isTypeVariable variable && typ /= Nothing) (lift (Left "a query type variable cannot have a term type"))
            return [if isTypeVariable variable then 1 else 0, fromIntegral meta, maybe (-1) fromIntegral typ]
        variableHint (LV_Unique _ (DispHint hint)) = hint
        variableHint _ = Nothing
        isTypeVariable (LV_ty_var _) = True
        isTypeVariable _ = False

-- The symbol section has the roles of the symbols from `known` on.
assemble :: Int -> Build -> [LogicVar] -> [[Int64]] -> Int -> [[Int64]] -> FullProgram
assemble known built variables slots root clauses = FullProgram words (builtSymbols built) variables (builtMetadata built) Map.empty Map.empty Map.empty where
    header = [bytecodeMagic, 6, fromIntegral (termCount built), fromIntegral (Map.size (symbolKeys built)), fromIntegral (length clauses), fromIntegral (length variables), fromIntegral root, fromIntegral (metadataCount built)]
    words = header ++ concat slots ++ map (fromIntegral . symbolRole) (IntMap.elems (snd (IntMap.split (known - 1) (builtSymbols built)))) ++ concat (IntMap.elems (builtTerms built)) ++ concat clauses ++ reverse (digitPayload built)

compileFact :: TermNode -> Compile [Int64]
compileFact fact = do
    root <- compileTerm fact
    predicate <- case factHead fact of
        Just constant -> internSymbol (ConstantSymbol constant)
        Nothing -> return (-1)
    return [fromIntegral predicate, fromIntegral root]
    where
        factHead term = case unfoldlNApp (rewrite HNF term) of
            (NCon (DC (DC_LO operator)) _, [NLam _ _ body _])
                | operator == LO_ty_pi || operator == LO_pi -> factHead body
            (NCon (DC (DC_LO LO_if)) _, [headTerm, _]) -> factHead headTerm
            (NCon constant _, _) -> Just constant
            _ -> Nothing

compileTerm :: TermNode -> Compile Int
compileTerm = compileScoped True 0 Map.empty

compileScoped :: Bool -> Int -> Map.Map MetaTVar Int -> TermNode -> Compile Int
compileScoped pooled depth binders term
    = case term of
        NApp _ _ location
            | pooled, Just (cons, _, _) <- stringCell location term -> case stringContents location term of
                Just (characters, nil) -> do
                    cons' <- compileScoped False depth binders cons
                    nil' <- compileScoped False depth binders nil
                    (offset, count) <- internString characters
                    meta <- sourceMetadata location
                    internRow (StringKey (fromIntegral cons') (fromIntegral nil') (fromIntegral offset) (fromIntegral count) (fromIntegral meta))
                -- Do not rescan every suffix of an open or mixed-location list.
                Nothing -> compileNode False depth binders term
        _ -> compileNode pooled depth binders term

stringCell :: Maybe SLoc -> TermNode -> Maybe (TermNode, Char, TermNode)
stringCell location term
    = case term of
        NApp (NApp cons@(NApp (NCon (DC DC_Cons) consLocation) (NCon (TC (TC_Named "char")) Nothing) typeLocation) (NCon (DC (DC_ChrL character)) charLocation) headLocation) tail outerLocation
            | all (== location) [consLocation, typeLocation, charLocation, headLocation, outerLocation] -> Just (cons, character, tail)
        _ -> Nothing

stringContents :: Maybe SLoc -> TermNode -> Maybe (String, TermNode)
stringContents location = collect [] where
    collect characters term = case term of
        NApp (NCon (DC DC_Nil) nilLocation) (NCon (TC (TC_Named "char")) Nothing) appLocation
            | nilLocation == location && appLocation == location -> Just (reverse characters, term)
        _ -> case stringCell location term of
            Just (_, character, tail) -> collect (character : characters) tail
            Nothing -> Nothing

compileNode :: Bool -> Int -> Map.Map MetaTVar Int -> TermNode -> Compile Int
compileNode pooled depth binders term = case term of
    LVar variable -> do
        slots <- gets variableSlots
        case Map.lookup variable slots of
            Just slot -> internTerm 0 (fromIntegral slot) 0 (-1)
            Nothing -> lift (Left "unregistered full bytecode variable")
    NCon (DC (DC_NatL value)) location -> do
        (offset, count) <- internNatural value
        meta <- sourceMetadata location
        internTerm 5 (fromIntegral offset) (fromIntegral count) (fromIntegral meta)
    NCon (DC DC_wc) location -> do
        meta <- sourceMetadata location
        internTerm 6 0 0 (fromIntegral meta)
    NCon constant location -> do
        symbol <- internSymbol (ConstantSymbol constant)
        meta <- sourceMetadata location
        internTerm 1 (fromIntegral symbol) 0 (fromIntegral meta)
    NIdx index -> internTerm 3 (fromIntegral index) 0 (-1)
    NApp function@(NCon (DC (DC_LO LO_ty_pi)) _) (NLam hint typ body source) location -> do
        function' <- recurse function
        inner <- case unLamType typ of
            Just (TyMTV variable) -> return (Map.insert variable depth binders)
            _ -> return binders
        body' <- compileScoped pooled (depth + 1) inner body
        meta <- internMetadata (NodeMetadata hint typ source)
        argument' <- internTerm 4 (fromIntegral body') 0 (fromIntegral meta)
        sourceMeta <- sourceMetadata location
        internTerm 2 (fromIntegral function') (fromIntegral argument') (fromIntegral sourceMeta)
    NApp function argument location -> do
        function' <- recurse function
        argument' <- recurse argument
        meta <- sourceMetadata location
        internTerm 2 (fromIntegral function') (fromIntegral argument') (fromIntegral meta)
    NLam hint typ body location -> do
        body' <- compileScoped pooled (depth + 1) binders body
        domain <- traverse (compileType depth binders) (unLamType typ)
        meta <- internMetadata (NodeMetadata hint typ location)
        internTerm 4 (fromIntegral body') (maybe 0 ((+ 1) . fromIntegral) domain) (fromIntegral meta)
    suspended@Susp {} -> recurse (rewrite NF suspended)
    NPresburgerCheck formula freeOf location -> do
        symbol <- internSymbol (PresburgerSymbol formula (Map.keys freeOf) location)
        meta <- sourceMetadata location
        headRoot <- internTerm 1 (fromIntegral symbol) 0 (fromIntegral meta)
        foldM (apply meta) headRoot (Map.elems freeOf)
    where
        recurse = compileScoped pooled depth binders
        apply meta function argument = do
            argument' <- recurse argument
            internTerm 2 (fromIntegral function) (fromIntegral argument') (fromIntegral meta)

-- An annotation is outside its own lambda, but inside every enclosing binder.
-- A type binder's annotation names that binder; it is not its domain type.
compileType :: Int -> Map.Map MetaTVar Int -> MonoType Int -> Compile Int
compileType depth binders typ = case typ of
    TyMTV variable -> variableType variable
    TyCon (TCon (TC_Unique variable) _) -> variableType variable
    TyCon (TCon constructor _) -> do
        symbol <- internSymbol (ConstantSymbol (TC constructor))
        internTerm 1 (fromIntegral symbol) 0 (-1)
    TyApp function argument -> do
        function' <- compileType depth binders function
        argument' <- compileType depth binders argument
        internTerm 2 (fromIntegral function') (fromIntegral argument') (-1)
    TyVar _ -> lift (Left "generalized type index in a full bytecode binder")
    where
        variableType variable = case Map.lookup variable binders of
            Just level -> internTerm 3 (fromIntegral (depth - level - 1)) 0 (-1)
            Nothing -> do
                slots <- gets variableSlots
                case Map.lookup (LV_ty_var variable) slots of
                    Just slot -> internTerm 0 (fromIntegral slot) 0 (-1)
                    Nothing -> lift (Left "unbound type variable in a full bytecode binder")

-- Type variables can occur only in annotations, so getLVars is insufficient.
termVariables :: TermNode -> Set.Set LogicVar
termVariables = collect Set.empty where
    collect bound term = case term of
        LVar variable -> Set.singleton variable
        NApp (NCon (DC (DC_LO LO_ty_pi)) _) (NLam _ (LamType (Just (TyMTV variable))) body _) _ -> collect (Set.insert variable bound) body
        NApp function argument _ -> collect bound function `Set.union` collect bound argument
        NLam _ typ body _ -> maybe Set.empty (annotation bound) (unLamType typ) `Set.union` collect bound body
        NPresburgerCheck _ values _ -> Set.unions (map (collect bound) (Map.elems values))
        suspended@Susp {} -> collect bound (rewrite NF suspended)
        _ -> Set.empty
    annotation bound typ = case typ of
        TyMTV variable -> free bound variable
        TyCon (TCon (TC_Unique variable) _) -> free bound variable
        TyApp function argument -> annotation bound function `Set.union` annotation bound argument
        _ -> Set.empty
    free bound variable = if variable `Set.member` bound then Set.empty else Set.singleton (LV_ty_var variable)

sourceMetadata :: Maybe SLoc -> Compile Int
sourceMetadata Nothing = return (-1)
sourceMetadata location = internMetadata (NodeMetadata Nothing noLamType location)

internMetadata :: NodeMetadata -> Compile Int
internMetadata meta = do
    let key = storeMetadata meta
    known <- gets (Map.lookup key . metadataKeys)
    case known of
        Just index -> return index
        Nothing -> do
            index <- gets metadataCount
            modify (\state -> state { builtMetadata = IntMap.insert index meta (builtMetadata state), metadataCount = index + 1, metadataKeys = Map.insert key index (metadataKeys state) })
            return index

-- The identity of a symbol is a string. A constant that was seen before is
-- found without building it again.
internSymbol :: FullSymbol -> Compile Int
internSymbol symbol = case symbol of
    ConstantSymbol constant -> do
        seen <- gets (Map.lookup constant . constantKeys)
        case seen of
            Just index -> return index
            Nothing -> do
                index <- internIdentity symbol
                modify (\state -> state { constantKeys = Map.insert constant index (constantKeys state) })
                return index
    _ -> internIdentity symbol

internIdentity :: FullSymbol -> Compile Int
internIdentity symbol = do
    let key = symbolIdentity symbol
    known <- gets (Map.lookup key . symbolKeys)
    case known of
        Just index -> return index
        Nothing -> do
            index <- gets (Map.size . symbolKeys)
            modify (\state -> state { builtSymbols = IntMap.insert index symbol (builtSymbols state), symbolKeys = Map.insert key index (symbolKeys state) })
            return index

internTerm :: Int64 -> Int64 -> Int64 -> Int64 -> Compile Int
internTerm tag a b meta = internRow (TermKey tag a b meta)

internRow :: TermKey -> Compile Int
internRow key = do
    known <- gets (Map.lookup key . termKeys)
    case known of
        Just index -> return index
        Nothing -> do
            index <- gets termCount
            modify (\state -> state { builtTerms = IntMap.insert index row (builtTerms state), termCount = index + 1, termKeys = Map.insert key index (termKeys state) })
            return index
    where
        row = case key of
            TermKey tag a b meta -> [tag, a, b, 0, 0, meta]
            StringKey a b c d meta -> [7, a, b, c, d, meta]

internString :: String -> Compile (Int, Int)
internString characters = do
    known <- gets (Map.lookup characters . stringKeys)
    case known of
        Just entry -> return entry
        Nothing -> do
            symbols <- mapM (internSymbol . ConstantSymbol . DC . DC_ChrL) characters
            offset <- gets digitCount
            let count = length characters
            when (count > maxBound - offset) (lift (Left "full literal payload size overflow"))
            let entry = (offset, count)
            modify (\state -> state { digitPayload = reverse (map fromIntegral symbols) ++ digitPayload state, digitCount = offset + count, stringKeys = Map.insert characters entry (stringKeys state) })
            return entry

internNatural :: Integer -> Compile (Int, Int)
internNatural value
    | value < 0 = lift (Left "negative natural in full bytecode")
    | otherwise = do
        let digits = show value
        known <- gets (Map.lookup digits . literalKeys)
        case known of
            Just entry -> return entry
            Nothing -> do
                offset <- gets digitCount
                let count = length digits
                    entry = (offset, count)
                modify (\state -> state { digitPayload = reverse (map (fromIntegral . ord) digits) ++ digitPayload state, digitCount = offset + count, literalKeys = Map.insert digits entry (literalKeys state) })
                return entry
