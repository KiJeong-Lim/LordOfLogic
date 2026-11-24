module Hol.V1.FullBytecode where

import qualified Calc.Presburger.Internal as P
import Control.Monad
import Control.Monad.Trans.State.Strict
import qualified Data.Array as Array
import Data.Int
import qualified Data.IntMap.Strict as IntMap
import qualified Data.IntSet as IntSet
import qualified Data.List as List
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Hol.BETA.Constant
import Hol.BETA.Header
import Hol.BETA.TermNode
import qualified Hol.BETA.TypeChecker as TypeChecker
import Hol.V1.Bytecode (ArtifactNumber (..), readBounded, readConstructor)
import Text.Read (Read (..), ReadPrec, pfail, readListPrecDefault, readMaybe, step)
import Z.Utils (Unique (..))

data FullSymbol
    = ConstantSymbol Constant
    | PresburgerSymbol P.MyPresburgerFormulaRep [P.MyVar] (Maybe SLoc)
    deriving ()

data NodeMetadata
    = NodeMetadata
        { nodeHint :: Maybe String
        , nodeType :: LamType
        , nodeLocation :: Maybe SLoc
        }
    deriving ()

data FullProgram
    = FullProgram
        { fullWords :: [Int64]
        , fullSymbols :: IntMap.IntMap FullSymbol
        , fullVariables :: [LogicVar]
        , fullMetadata :: IntMap.IntMap NodeMetadata
        , fullKindEnv :: KindEnv
        , fullTypeEnv :: TypeEnv
        , fullQueryTypes :: Map.Map LogicVar (MonoType Int)
        }
    deriving ()

type FullSections = ([Int64], [[Int64]], [Int64], [[Int64]], [[Int64]], [Int64])

withRuntimeMetadata :: KindEnv -> TypeEnv -> Map.Map LogicVar (MonoType Int) -> FullProgram -> FullProgram
withRuntimeMetadata kinds types variables program = attachQueryTypes (enriched { fullKindEnv = kinds, fullTypeEnv = types, fullQueryTypes = variables }) where
    wanted = map (ConstantSymbol . TC) (Map.keys kinds) ++ map (ConstantSymbol . DC) (Map.keys types) ++ concatMap typeSymbols (Map.elems variables)
    typeSymbols typ = case typ of
        TyCon (TCon (TC_Unique _) _) -> []
        TyCon (TCon constructor _) -> [ConstantSymbol (TC constructor)]
        TyApp function argument -> typeSymbols function ++ typeSymbols argument
        _ -> []
    existing = fullSymbols program
    identities = Set.fromList (map symbolIdentity (IntMap.elems existing))
    (symbols, _) = List.foldl' addSymbol (existing, identities) wanted
    addSymbol (current, seen) symbol
        | identity `Set.member` seen = (current, seen)
        | otherwise = (IntMap.insert (IntMap.size current) symbol current, Set.insert identity seen)
        where
            identity = symbolIdentity symbol
    enriched = case fullSections (fullWords program) of
        Right ([magic, version, terms, _, facts, slots, root, metadata], slotRows, _, termRows, factRows, payload) -> program
            { fullSymbols = symbols
            , fullWords = [magic, version, terms, fromIntegral (IntMap.size symbols), facts, slots, root, metadata] ++ concat slotRows ++ map (fromIntegral . symbolRole) (IntMap.elems symbols) ++ concat termRows ++ concat factRows ++ payload
            }
        _ -> program

typeVariables :: MonoType Int -> Set.Set LogicVar
typeVariables typ = case typ of
    TyMTV variable -> Set.singleton (LV_ty_var variable)
    TyCon (TCon (TC_Unique variable) _) -> Set.singleton (LV_ty_var variable)
    TyApp function argument -> typeVariables function `Set.union` typeVariables argument
    _ -> Set.empty

-- Preserve old query slot numbers when attaching types to legacy wordcode.
-- This also serves the original pure withRuntimeMetadata API. An invalid
-- generalized type produces a rejected descriptor, never a guessed type.
attachQueryTypes :: FullProgram -> FullProgram
attachQueryTypes program = case fullSections (fullWords program) of
    Right ([magic, _, count, symbolCount, factCount, _, root, metadataCount], slots, roles, rows, facts, payload) -> program
        { fullWords = [magic, 6, fromIntegral next, symbolCount, factCount, fromIntegral (length variables), root, metadataCount] ++ concat descriptors ++ roles ++ concat rows ++ concat (reverse added) ++ concat facts ++ payload
        , fullVariables = variables
        }
        where
            originals = fullVariables program
            used = Map.restrictKeys (fullQueryTypes program) (Set.fromList originals)
            extra = Set.toAscList (Set.unions (map typeVariables (Map.elems used)) `Set.difference` Set.fromList originals)
            variables = originals ++ extra
            indices = Map.fromList (zip variables [0 ..])
            symbols = Map.fromList [(constant, fromIntegral index) | (index, ConstantSymbol constant) <- IntMap.toList (fullSymbols program)]
            originalRows = map (take 2) slots ++ replicate (length extra) [1, -1]
            (descriptors, (next, added, _)) = runState (zipWithM descriptor originalRows variables) (fromIntegral count, [], Map.empty)
            descriptor row variable = do
                typ <- maybe (return (-1)) encode (Map.lookup variable used)
                return (row ++ [typ])
            encode :: MonoType Int -> State (Int, [[Int64]], Map.Map StoredType Int64) Int64
            encode typ = do
                let key = storeType typ
                seen <- gets (Map.lookup key . third)
                case seen of
                    Just index -> return index
                    Nothing -> do
                        row <- case typ of
                            TyMTV variable -> return (slot variable)
                            TyCon (TCon (TC_Unique variable) _) -> return (slot variable)
                            TyCon (TCon constructor _) -> return [1, Map.findWithDefault (-1) (TC constructor) symbols, 0, 0, 0, -1]
                            TyApp function argument -> do
                                left <- encode function
                                right <- encode argument
                                return [2, left, right, 0, 0, -1]
                            TyVar _ -> return [-1, 0, 0, 0, 0, -1]
                        (index, values, keys) <- get
                        put (index + 1, row : values, Map.insert key (fromIntegral index) keys)
                        return (fromIntegral index)
            slot variable = [0, Map.findWithDefault (-1) (LV_ty_var variable) indices, 0, 0, 0, -1]
            third (_, _, value) = value
    _ -> program

-- The DTOs preserve identities and kinds; the surface pretty-printers are not
-- parsers for serialized runtime metadata.
data StoredCon
    = SCData String
    | SCType String
    | SCDataUnique Int (Maybe String)
    | SCTypeUnique Int
    | SCBuiltin Int
    | SCLogical Int
    | SCChar Char
    | SCNat Integer
    deriving (Eq, Ord, Show)

instance Read StoredCon where
    readPrec = readConstructor $ \constructor -> case constructor of
        "SCData" -> SCData <$> step readPrec
        "SCType" -> SCType <$> step readPrec
        "SCDataUnique" -> SCDataUnique <$> step readBounded <*> step readPrec
        "SCTypeUnique" -> SCTypeUnique <$> step readBounded
        "SCBuiltin" -> SCBuiltin <$> step readBounded
        "SCLogical" -> SCLogical <$> step readBounded
        "SCChar" -> SCChar <$> step readPrec
        "SCNat" -> SCNat <$> step readPrec
        _ -> pfail
    readListPrec = readListPrecDefault

data StoredKind
    = SKStar
    | SKArrow StoredKind StoredKind
    deriving (Eq, Ord, Read, Show)

data StoredType
    = STVar Int
    | STMeta Int
    | STCon StoredCon StoredKind
    | STApp StoredType StoredType
    deriving (Eq, Ord, Show)

instance Read StoredType where
    readPrec = readConstructor $ \constructor -> case constructor of
        "STVar" -> STVar <$> step readBounded
        "STMeta" -> STMeta <$> step readBounded
        "STCon" -> STCon <$> step readPrec <*> step readPrec
        "STApp" -> STApp <$> step readPrec <*> step readPrec
        _ -> pfail
    readListPrec = readListPrecDefault

data StoredVar
    = SVNamed String
    | SVGenerated Int (Maybe String)
    | SVType Int
    deriving (Eq, Ord, Show)

instance Read StoredVar where
    readPrec = readConstructor $ \constructor -> case constructor of
        "SVNamed" -> SVNamed <$> step readPrec
        "SVGenerated" -> SVGenerated <$> step readBounded <*> step readPrec
        "SVType" -> SVType <$> step readBounded
        _ -> pfail
    readListPrec = readListPrecDefault

data StoredFormula
    = SFTruth Bool
    | SFRelation Int StoredPterm StoredPterm
    | SFModulo StoredPterm Integer StoredPterm
    | SFNot StoredFormula
    | SFConnect Int StoredFormula StoredFormula
    | SFQuant Bool Integer StoredFormula
    deriving (Eq, Ord, Show)

instance Read StoredFormula where
    readPrec = readConstructor $ \constructor -> case constructor of
        "SFTruth" -> SFTruth <$> step readPrec
        "SFRelation" -> SFRelation <$> step readBounded <*> step readPrec <*> step readPrec
        "SFModulo" -> SFModulo <$> step readPrec <*> step readPrec <*> step readPrec
        "SFNot" -> SFNot <$> step readPrec
        "SFConnect" -> SFConnect <$> step readBounded <*> step readPrec <*> step readPrec
        "SFQuant" -> SFQuant <$> step readPrec <*> step readPrec <*> step readPrec
        _ -> pfail
    readListPrec = readListPrecDefault

data StoredPterm
    = SPVar Integer
    | SPZero
    | SPSucc StoredPterm
    | SPPlus StoredPterm StoredPterm
    deriving (Eq, Ord, Read, Show)

data StoredSymbol
    = SSConstant StoredCon
    | SSPresburger StoredFormula [Integer] (Maybe ((Int, Int), (Int, Int)))
    deriving (Show)

instance Read StoredSymbol where
    readPrec = readConstructor $ \constructor -> case constructor of
        "SSConstant" -> SSConstant <$> step readPrec
        "SSPresburger" -> SSPresburger <$> step readPrec <*> step readPrec <*> step readArtifactLocation
        _ -> pfail
    readListPrec = readListPrecDefault

type ArtifactLocation = Maybe ((ArtifactNumber Int, ArtifactNumber Int), (ArtifactNumber Int, ArtifactNumber Int))

artifactLocation :: ArtifactLocation -> Maybe ((Int, Int), (Int, Int))
artifactLocation = fmap (\((line1, column1), (line2, column2)) -> ((unArtifactNumber line1, unArtifactNumber column1), (unArtifactNumber line2, unArtifactNumber column2)))

readArtifactLocation :: ReadPrec (Maybe ((Int, Int), (Int, Int)))
readArtifactLocation = artifactLocation <$> readPrec

data FullArtifact
    = FullArtifact Int [Int64] [StoredSymbol] [StoredVar] [(Maybe String, Maybe StoredType, Maybe ((Int, Int), (Int, Int)))] [(StoredCon, StoredKind)] [(StoredCon, [String], StoredType)] [(StoredVar, StoredType)]
    deriving (Show)

instance Read FullArtifact where
    readPrec = readConstructor $ \constructor -> do
        guard (constructor == "FullArtifact")
        version <- step readBounded
        words <- map unArtifactNumber <$> step readPrec
        symbols <- step readPrec
        variables <- step readPrec
        metadata <- step readPrec
        kinds <- step readPrec
        types <- step readPrec
        queryTypes <- step readPrec
        return (FullArtifact version words symbols variables [(hint, typ, artifactLocation location) | (hint, typ, location) <- metadata] kinds types queryTypes)
    readListPrec = readListPrecDefault

logicalOperators :: [LogicalOperator]
logicalOperators = [LO_ty_pi, LO_if, LO_true, LO_fail, LO_cut, LO_and, LO_or, LO_imply, LO_pi, LO_sigma, LO_debug, LO_is]

builtinConstants :: [Constant]
builtinConstants = map DC [DC_Nil, DC_Cons, DC_Succ, DC_eq, DC_le, DC_lt, DC_ge, DC_gt, DC_plus, DC_minus, DC_mul, DC_div, DC_wc] ++ [TC TC_Arrow]

storeCon :: Constant -> StoredCon
storeCon constant = case constant of
    DC (DC_Named name) -> SCData name
    TC (TC_Named name) -> SCType name
    DC (DC_Unique (Unique key) (DispHint hint)) -> SCDataUnique key hint
    TC (TC_Unique (Unique key)) -> SCTypeUnique key
    DC (DC_ChrL ch) -> SCChar ch
    DC (DC_NatL value) -> SCNat value
    DC (DC_LO operator) -> SCLogical (indexOf operator logicalOperators)
    _ -> SCBuiltin (indexOf constant builtinConstants)
    where
        indexOf value = length . takeWhile (/= value)

restoreCon :: StoredCon -> Either String Constant
restoreCon stored = case stored of
    SCData name -> Right (DC (DC_Named name))
    SCType name -> Right (TC (TC_Named name))
    SCDataUnique key hint -> nonnegative key >> Right (DC (DC_Unique (Unique key) (DispHint hint)))
    SCTypeUnique key -> nonnegative key >> Right (TC (TC_Unique (Unique key)))
    SCChar ch -> Right (DC (DC_ChrL ch))
    SCNat value -> unless (value >= 0) (Left "negative natural constant") >> Right (DC (DC_NatL value))
    SCLogical index -> DC . DC_LO <$> checkedIndex logicalOperators index
    SCBuiltin index -> checkedIndex builtinConstants index
    where
        nonnegative value = unless (value >= 0) (Left "negative constant identifier")

checkedIndex :: [a] -> Int -> Either String a
checkedIndex values index
    | index < 0 = Left "negative metadata index"
    | otherwise = case drop index values of
        value : _ -> Right value
        [] -> Left "unknown metadata index"

storeKind :: KindExpr -> StoredKind
storeKind Star = SKStar
storeKind (KArr lhs rhs) = SKArrow (storeKind lhs) (storeKind rhs)

restoreKind :: StoredKind -> KindExpr
restoreKind SKStar = Star
restoreKind (SKArrow lhs rhs) = KArr (restoreKind lhs) (restoreKind rhs)

storeType :: MonoType Int -> StoredType
storeType typ = case typ of
    TyVar index -> STVar index
    TyMTV (Unique key) -> STMeta key
    TyCon (TCon con kind) -> STCon (storeCon (TC con)) (storeKind kind)
    TyApp lhs rhs -> STApp (storeType lhs) (storeType rhs)

restoreType :: StoredType -> Either String (MonoType Int)
restoreType typ = case typ of
    STVar index -> nonnegative index >> Right (TyVar index)
    STMeta key -> Right (TyMTV (Unique key))
    STCon con kind -> do
        decoded <- restoreCon con
        case decoded of
            TC constructor -> Right (TyCon (TCon constructor (restoreKind kind)))
            _ -> Left "data constructor used as a type constructor"
    STApp lhs rhs -> TyApp <$> restoreType lhs <*> restoreType rhs
    where
        nonnegative value = unless (value >= 0) (Left "negative type identifier")

storeVar :: LogicVar -> StoredVar
storeVar variable = case variable of
    LV_Named name -> SVNamed name
    LV_Unique (Unique key) (DispHint hint) -> SVGenerated key hint
    LV_ty_var (Unique key) -> SVType key

restoreVar :: StoredVar -> Either String LogicVar
restoreVar variable = case variable of
    SVNamed name -> Right (LV_Named name)
    SVGenerated key hint -> nonnegative key >> Right (LV_Unique (Unique key) (DispHint hint))
    SVType key -> nonnegative key >> Right (LV_ty_var (Unique key))
    where
        nonnegative value = unless (value >= 0) (Left "negative variable identifier")

storeLocation :: SLoc -> ((Int, Int), (Int, Int))
storeLocation (SLoc begin end) = (begin, end)

restoreLocation :: ((Int, Int), (Int, Int)) -> Either String SLoc
restoreLocation (begin@(line1, column1), end@(line2, column2)) = do
    unless (all (>= 1) [line1, column1, line2, column2] && begin <= end) (Left "invalid source coordinate")
    return (SLoc begin end)

storeFormula :: P.MyPresburgerFormulaRep -> StoredFormula
storeFormula formula = case formula of
    P.ValF value -> SFTruth value
    P.EqnF lhs rhs -> SFRelation 0 (storePterm lhs) (storePterm rhs)
    P.LtnF lhs rhs -> SFRelation 1 (storePterm lhs) (storePterm rhs)
    P.LeqF lhs rhs -> SFRelation 2 (storePterm lhs) (storePterm rhs)
    P.GtnF lhs rhs -> SFRelation 3 (storePterm lhs) (storePterm rhs)
    P.ModF lhs modulus rhs -> SFModulo (storePterm lhs) modulus (storePterm rhs)
    P.NegF body -> SFNot (storeFormula body)
    P.DisF lhs rhs -> SFConnect 0 (storeFormula lhs) (storeFormula rhs)
    P.ConF lhs rhs -> SFConnect 1 (storeFormula lhs) (storeFormula rhs)
    P.ImpF lhs rhs -> SFConnect 2 (storeFormula lhs) (storeFormula rhs)
    P.IffF lhs rhs -> SFConnect 3 (storeFormula lhs) (storeFormula rhs)
    P.AllF variable body -> SFQuant True variable (storeFormula body)
    P.ExsF variable body -> SFQuant False variable (storeFormula body)

storePterm :: P.PresburgerTermRep -> StoredPterm
storePterm term = case term of
    P.IVar variable -> SPVar variable
    P.Zero -> SPZero
    P.Succ body -> SPSucc (storePterm body)
    P.Plus lhs rhs -> SPPlus (storePterm lhs) (storePterm rhs)

restoreFormula :: StoredFormula -> Either String P.MyPresburgerFormulaRep
restoreFormula formula = case formula of
    SFTruth value -> Right (P.ValF value)
    SFRelation tag lhs rhs -> do
        constructor <- checkedIndex [P.EqnF, P.LtnF, P.LeqF, P.GtnF] tag
        constructor <$> restorePterm lhs <*> restorePterm rhs
    SFModulo lhs modulus rhs -> do
        unless (modulus > 0) (Left "nonpositive Presburger modulus")
        lhs' <- restorePterm lhs
        rhs' <- restorePterm rhs
        return (P.ModF lhs' modulus rhs')
    SFNot body -> P.NegF <$> restoreFormula body
    SFConnect tag lhs rhs -> do
        constructor <- checkedIndex [P.DisF, P.ConF, P.ImpF, P.IffF] tag
        constructor <$> restoreFormula lhs <*> restoreFormula rhs
    SFQuant universal variable body -> do
        unless (variable > 0) (Left "nonpositive Presburger variable")
        (if universal then P.AllF variable else P.ExsF variable) <$> restoreFormula body

restorePterm :: StoredPterm -> Either String P.PresburgerTermRep
restorePterm term = case term of
    SPVar variable -> unless (variable > 0) (Left "nonpositive Presburger variable") >> Right (P.IVar variable)
    SPZero -> Right P.Zero
    SPSucc body -> P.Succ <$> restorePterm body
    SPPlus lhs rhs -> P.Plus <$> restorePterm lhs <*> restorePterm rhs

storeSymbol :: FullSymbol -> StoredSymbol
storeSymbol symbol = case symbol of
    ConstantSymbol constant -> SSConstant (storeCon constant)
    PresburgerSymbol formula variables location -> SSPresburger (storeFormula formula) variables (fmap storeLocation location)

symbolIdentity :: FullSymbol -> String
symbolIdentity symbol = show $ case storeSymbol symbol of
    SSConstant (SCDataUnique key _) -> SSConstant (SCDataUnique key Nothing)
    SSPresburger formula variables _ -> SSPresburger formula variables Nothing
    stored -> stored

restoreSymbol :: StoredSymbol -> Either String FullSymbol
restoreSymbol symbol = case symbol of
    SSConstant constant -> ConstantSymbol <$> restoreCon constant
    SSPresburger formula variables location -> do
        unless (all (> 0) variables && Set.size (Set.fromList variables) == length variables) (Left "invalid Presburger free-variable table")
        decoded <- restoreFormula formula
        unless (P.getFVs decoded `Set.isSubsetOf` Set.fromList variables) (Left "missing Presburger free-variable binding")
        PresburgerSymbol decoded variables <$> traverse restoreLocation location

storeMetadata :: NodeMetadata -> (Maybe String, Maybe StoredType, Maybe ((Int, Int), (Int, Int)))
storeMetadata (NodeMetadata hint (LamType typ) location) = (hint, fmap storeType typ, fmap storeLocation location)

restoreMetadata :: (Maybe String, Maybe StoredType, Maybe ((Int, Int), (Int, Int))) -> Either String NodeMetadata
restoreMetadata (hint, typ, location) = NodeMetadata hint <$> (LamType <$> traverse restoreType typ) <*> traverse restoreLocation location

serializeFullBytecode :: FullProgram -> Either String String
serializeFullBytecode program = do
    validateFullBytecode program
    return (show (storeFullArtifact program) ++ "\n")

storeFullArtifact :: FullProgram -> FullArtifact
storeFullArtifact program = FullArtifact version (fullWords program) symbols variables metadata kinds types queryTypes
    where
        version = fromIntegral (fullWords program !! 1) + 1
        symbols = map storeSymbol (IntMap.elems (fullSymbols program))
        variables = map storeVar (fullVariables program)
        metadata = map storeMetadata (IntMap.elems (fullMetadata program))
        kinds = [(storeCon (TC con), storeKind kind) | (con, kind) <- Map.toList (fullKindEnv program)]
        types = [(storeCon (DC con), names, storeType typ) | (con, Forall names typ) <- Map.toList (fullTypeEnv program)]
        queryTypes = [(storeVar variable, storeType typ) | (variable, typ) <- Map.toList (fullQueryTypes program)]

deserializeFullBytecode :: String -> Either String FullProgram
deserializeFullBytecode text = case readMaybe text of
    Nothing -> Left "invalid full HOL V1 bytecode artifact"
    Just artifact -> restoreFullArtifact artifact

restoreFullArtifact :: FullArtifact -> Either String FullProgram
restoreFullArtifact artifact = do
    program <- restoreFullFields artifact
    validateFullBytecode program
    return program

-- Restore the DTO fields. Structural wordcode validation is a separate step;
-- ordinary .hbc readers call restoreFullArtifact, caches retain its witness.
restoreFullFields :: FullArtifact -> Either String FullProgram
restoreFullFields (FullArtifact version words symbols variables metadata kinds types queryTypes) = do
    -- Version 7 has native wordcode 6, in which every constructor of types
    -- has the role of one (symbolRole). The words of an older file have the
    -- role of an ordinary symbol there: such a file is no damaged file of
    -- this format, and it is compiled again from its source.
    when (version >= 2 && version <= 6) (Left ("full HOL V1 artifact version " ++ show version ++ " is an old format; recompile from source"))
    unless (version == 7) (Left "unsupported full HOL V1 artifact version")
    unless (take 2 words == [0x484f4c31, fromIntegral (version - 1)]) (Left "full HOL V1 artifact/native version mismatch")
    symbols' <- mapM restoreSymbol symbols
    variables' <- mapM restoreVar variables
    metadata' <- mapM restoreMetadata metadata
    kinds' <- mapM restoreKindEntry kinds
    types' <- mapM restoreTypeEntry types
    queryTypes' <- mapM (\(variable, typ) -> (,) <$> restoreVar variable <*> restoreType typ) queryTypes
    unless (distinctKeys kinds' && distinctKeys types' && distinctKeys queryTypes') (Left "duplicate type metadata key")
    let program = FullProgram words (IntMap.fromList (zip [0 ..] symbols')) variables' (IntMap.fromList (zip [0 ..] metadata')) (Map.fromList kinds') (Map.fromList types') (Map.fromList queryTypes')
    return program
    where
        distinctKeys entries = Set.size (Set.fromList (map fst entries)) == length entries
        restoreKindEntry (stored, kind) = do
            constant <- restoreCon stored
            case constant of
                TC con -> Right (con, restoreKind kind)
                _ -> Left "invalid kind environment constructor"
        restoreTypeEntry (stored, names, typ) = do
            constant <- restoreCon stored
            decoded <- restoreType typ
            case constant of
                DC con -> Right (con, Forall names decoded)
                _ -> Left "invalid type environment constructor"

symbolRole :: FullSymbol -> Int
symbolRole (PresburgerSymbol _ _ _) = 20
symbolRole (ConstantSymbol constant) = case constant of
    DC (DC_LO operator) -> 1 + length (takeWhile (/= operator) logicalOperators)
    DC DC_eq -> 13
    DC DC_le -> 14
    DC DC_lt -> 15
    DC DC_ge -> 16
    DC DC_gt -> 17
    DC (DC_Named "read") -> 18
    DC (DC_Named "print") -> 19
    DC DC_Succ -> 21
    DC (DC_Named "flex") -> 22
    DC DC_plus -> 23
    DC DC_minus -> 23
    DC DC_mul -> 23
    DC DC_div -> 23
    TC (TC_Named "nat") -> 24
    DC (DC_Named "oracle") -> 25
    TC TC_Arrow -> 26
    DC (DC_Named "==") -> 27
    -- every other constructor of types: the native store reads the type that
    -- a program wildcard is applied to by these roles
    TC _ -> 28
    _ -> 0

fullSections :: [Int64] -> Either String ([Int64], [[Int64]], [Int64], [[Int64]], [[Int64]], [Int64])
fullSections words = case take 8 words of
    [magic, version, _, _, _, _, entry, _]
        | magic == 0x484f4c31 && (version >= 2 && version <= 6) && entry < 0 -> Left "negative full bytecode count"
    _ -> fragmentSections 0 words

-- A fragment is loaded on a machine that has `known` symbols already: its
-- symbol count is the total after it, and its symbol section has the roles of
-- the new ones. Its templates, clauses and digits are numbered from zero. A
-- fragment that only extends the program has no query slot and the entry -1.
fragmentSections :: Int -> [Int64] -> Either String ([Int64], [[Int64]], [Int64], [[Int64]], [[Int64]], [Int64])
fragmentSections known words = case splitAt 8 words of
    (header@[magic, version, terms, symbols, facts, slots, entry, metadata], rest) -> do
        unless (magic == 0x484f4c31 && (version >= 2 && version <= 6)) (Left "unsupported full bytecode magic or version")
        unless (all (>= 0) [terms, symbols, facts, slots, metadata] && entry >= -1) (Left "negative full bytecode count")
        unless (toInteger known <= toInteger symbols) (Left "a full bytecode fragment has fewer symbols than its program")
        unless (entry >= 0 || slots == 0) (Left "a full bytecode fragment has query slots and no query")
        let slotWidth = if version >= 5 then 3 else 2
            fixed = toInteger slotWidth * toInteger slots + (toInteger symbols - toInteger known) + 6 * toInteger terms + 2 * toInteger facts
        unless (fixed <= toInteger (length rest)) (Left "truncated full bytecode sections")
        unless (entry < terms) (Left "invalid full bytecode query entry")
        let (slotRows, afterSlots) = rows (fromIntegral slots) slotWidth rest
            (roleWords, afterRoles) = splitAt (fromIntegral symbols - known) afterSlots
            (termRows, afterTerms) = rows (fromIntegral terms) 6 afterRoles
            (factRows, payload) = rows (fromIntegral facts) 2 afterTerms
        return (header, slotRows, roleWords, termRows, factRows, payload)
    _ -> Left "truncated full bytecode header"
    where
        rows :: Int -> Int -> [Int64] -> ([[Int64]], [Int64])
        rows 0 _ values = ([], values)
        rows count width values = (row : following, suffix) where
            (row, next) = splitAt width values
            (following, suffix) = rows (count - 1) width next

validateFullBytecode :: FullProgram -> Either String ()
validateFullBytecode program = requireTypedProgram program >> fullSections (fullWords program) >>= validateSections (const False) 0 0 program

requireTypedProgram :: FullProgram -> Either String ()
requireTypedProgram program = case take 2 (fullWords program) of
    [0x484f4c31, 6] -> Right ()
    [0x484f4c31, version]
        | version == 4 || version == 5 -> Left ("full HOL V1 bytecode version " ++ show version ++ " has the symbol roles of an old format; recompile from source")
    _ -> Left "full HOL V1 bytecode needs exact runtime types; recompile from source"

-- The tables of `program` are those of the program its fragment is loaded on,
-- with what the fragment adds. The first `knownSymbols` symbols, which have the
-- identities `known`, and the first `knownMetadata` annotations were validated
-- with an earlier fragment: only the additions are examined.
validateFullFragment :: (String -> Bool) -> Int -> Int -> FullProgram -> Either String ()
validateFullFragment known knownSymbols knownMetadata program = requireTypedProgram program >> fragmentSections knownSymbols (fullWords program) >>= validateSections known knownSymbols knownMetadata program

validateSections :: (String -> Bool) -> Int -> Int -> FullProgram -> ([Int64], [[Int64]], [Int64], [[Int64]], [[Int64]], [Int64]) -> Either String ()
validateSections = validateSectionsWith True

validateSectionsWith :: Bool -> (String -> Bool) -> Int -> Int -> FullProgram -> ([Int64], [[Int64]], [Int64], [[Int64]], [[Int64]], [Int64]) -> Either String ()
validateSectionsWith checkFields known knownSymbols knownMetadata program (header, slots, roles, terms, facts, payload) = do
    let (_, newSymbols) = IntMap.split (knownSymbols - 1) (fullSymbols program)
        (_, newMetadata) = IntMap.split (knownMetadata - 1) (fullMetadata program)
        identities = map symbolIdentity (IntMap.elems newSymbols)
    case header of
        [_, version, termCount, symbolCount, _, slotCount, entry, metadataCount] -> do
            unless (IntMap.keys newSymbols == [knownSymbols .. fromIntegral symbolCount - 1]) (Left "full symbol metadata count mismatch")
            unless (Set.size (Set.fromList identities) == length identities && not (any known identities)) (Left "duplicate full symbol identity")
            unless (IntMap.keys newMetadata == [knownMetadata .. fromIntegral metadataCount - 1]) (Left "full annotation metadata count mismatch")
            unless (toInteger (length (fullVariables program)) == toInteger slotCount) (Left "full query variable count mismatch")
            unless (Set.size (Set.fromList (fullVariables program)) == length (fullVariables program)) (Left "duplicate full query variable")
            unless (roles == map (fromIntegral . symbolRole) (IntMap.elems newSymbols)) (Left "symbol roles do not match metadata")
            unless (IntSet.null (if version == 2 then badDigits else IntSet.intersection badDigits badCharacters)) (Left "invalid full literal payload")
            when checkFields $ do
                mapM_ (restoreSymbol . storeSymbol) (IntMap.elems newSymbols)
                mapM_ (restoreMetadata . storeMetadata) (IntMap.elems newMetadata)
                mapM_ (restoreVar . storeVar) (fullVariables program)
            mapM_ (checkTerm version symbolCount slotCount metadataCount) (zip [0 ..] terms)
            mapM_ (checkSlot version termCount metadataCount) (zip slots (fullVariables program))
            mapM_ (checkFact termCount symbolCount) facts
            -- References are checked above and point strictly backwards. A
            -- dense immutable array therefore memoizes each required depth
            -- once, without constructing an IntMap at every template row.
            let depths = Array.listArray (0, length terms - 1) (map (depthOf depths) terms)
            unless (entry == -1 || depths Array.! fromIntegral entry == 0) (Left "unbound de Bruijn index in full query")
            forM_ facts $ \row -> case row of
                [_, root] -> unless (depths Array.! fromIntegral root == 0) (Left "unbound de Bruijn index in full clause")
                _ -> Left "invalid full clause"
        _ -> Left "invalid full bytecode header"
    where
        termTable = IntMap.fromDistinctAscList (zip [0 ..] terms)
        payloadSize = toInteger (length payload)
        badDigits = IntSet.fromDistinctAscList [offset | (offset, value) <- zip [0 ..] payload, value < 48 || value > 57]
        zeroDigits = IntSet.fromDistinctAscList [offset | (offset, 48) <- zip [0 ..] payload]
        badCharacters = IntSet.fromDistinctAscList [offset | (offset, value) <- zip [0 ..] payload, not (isCharacter value)]
        isCharacter value
            | value < 0 || toInteger value > toInteger (maxBound :: Int) = False
            | otherwise = case IntMap.lookup (fromIntegral value) (fullSymbols program) of
                Just (ConstantSymbol (DC (DC_ChrL _))) -> True
                _ -> False
        checkPayload bad offset count = do
            unless (offset >= 0 && count >= 0 && toInteger offset + toInteger count <= payloadSize) (Left "invalid literal payload reference")
            unless (maybe True (\index -> toInteger index >= toInteger offset + toInteger count) (IntSet.lookupGE (fromIntegral offset) bad)) (Left "invalid literal payload value")
        checkStringHead root constructor = case IntMap.lookup (fromIntegral root) termTable of
            Just [2, function, argument, 0, 0, _] -> do
                checkConstant function (DC constructor)
                checkConstant argument (TC (TC_Named "char"))
            _ -> Left "invalid string constructor template"
        checkConstant root constant = case IntMap.lookup (fromIntegral root) termTable of
            Just [1, symbol, 0, 0, 0, _] -> case IntMap.lookup (fromIntegral symbol) (fullSymbols program) of
                Just (ConstantSymbol found)
                    | found == constant -> Right ()
                _ -> Left "invalid string constructor symbol"
            _ -> Left "invalid string constructor template"
        checkIndex count index = unless (index >= 0 && index < count) (Left "invalid full bytecode reference")
        checkMeta count index = unless (index == -1 || (index >= 0 && index < count)) (Left "invalid annotation reference")
        checkSlot version termCount count (row, variable) = case row of
            [isType, meta]
                | version < 5 -> flags isType meta variable
            [isType, meta, typ]
                | version >= 5 -> do
                    flags isType meta variable
                    unless (isType == 0 || typ == -1) (Left "a query type variable cannot have a term type")
                    case (typ, Map.lookup variable (fullQueryTypes program)) of
                        (-1, Nothing) -> return ()
                        (_, Just expected) -> do
                            checkIndex termCount typ
                            checkQueryKind expected
                            actual <- maybe (Left "invalid query type template") Right (typeRows Array.! fromIntegral typ)
                            unless (actual == canonicalType (storeType expected)) (Left "query type template disagrees with host metadata")
                        _ -> Left "query type template has no host metadata"
            _ -> Left "invalid query slot"
            where
                flags isType meta value = do
                    unless (isType == if isTypeVariable value then 1 else 0) (Left "query type-variable metadata mismatch")
                    checkMeta count meta
        typeRows = Array.listArray (0, length terms - 1) (map typeRow terms)
        variableRows = Array.listArray (0, length (fullVariables program) - 1) (fullVariables program)
        typeRow [0, slot, _, _, _, _] = case variableRows Array.! fromIntegral slot of
            LV_ty_var variable -> Just (storeType (TyMTV variable))
            _ -> Nothing
        typeRow [1, symbol, _, _, _, _] = case IntMap.lookup (fromIntegral symbol) (fullSymbols program) of
            Just (ConstantSymbol (TC constructor)) -> Just (canonicalType (storeType (TyCon (TCon constructor (Map.findWithDefault Star constructor (fullKindEnv program))))))
            _ -> Nothing
        typeRow [2, function, argument, _, _, _] = STApp <$> (typeRows Array.! fromIntegral function) <*> (typeRows Array.! fromIntegral argument)
        typeRow _ = Nothing
        canonicalType typ = case typ of
            STCon (SCTypeUnique variable) _ -> STMeta variable
            STCon constant _ -> STCon constant SKStar
            STApp function argument -> STApp (canonicalType function) (canonicalType argument)
            _ -> typ
        checkQueryKind typ = do
            declaredKinds typ
            case TypeChecker.getKindEither typ of
                Right Star -> Right ()
                _ -> Left "ill-kinded full query type"
        declaredKinds typ = case typ of
            TyCon (TCon (TC_Unique _) kind) -> unless (kind == Star) (Left "a query type variable must have kind *")
            TyCon (TCon constructor kind) -> case Map.lookup constructor (fullKindEnv program) of
                Just expected -> unless (kind == expected) (Left "query type kind disagrees with its declaration")
                Nothing -> Right ()
            TyApp function argument -> declaredKinds function >> declaredKinds argument
            TyVar _ -> Left "generalized variable in a full query type"
            _ -> Right ()
        isTypeVariable (LV_ty_var _) = True
        isTypeVariable _ = False
        checkTerm version symbols slots metadata (index, [tag, a, b, c, d, meta]) = do
            checkMeta metadata meta
            unless (tag == 7 || (c == 0 && d == 0)) (Left "invalid reserved template operand")
            case tag of
                0 -> checkIndex slots a >> zero b
                1 -> checkIndex symbols a >> zero b
                2 -> checkIndex index a >> checkIndex index b
                3 -> unless (a >= 0) (Left "negative de Bruijn index") >> zero b
                4 -> do
                    checkIndex index a
                    if version >= 4 && b > 0 then checkIndex index (b - 1) else zero b
                5 -> do
                    unless (b > 0) (Left "invalid natural payload reference")
                    checkPayload badDigits a b
                    unless (b == 1 || IntSet.notMember (fromIntegral a) zeroDigits) (Left "noncanonical natural literal")
                6 -> zero a >> zero b
                7 -> do
                    unless (version >= 3) (Left "string pool requires full bytecode version 3 or later")
                    checkIndex index a >> checkIndex index b
                    checkStringHead a DC_Cons >> checkStringHead b DC_Nil
                    checkPayload badCharacters c d
                _ -> Left "unknown full bytecode term tag"
        checkTerm _ _ _ _ _ = Left "invalid full bytecode term"
        checkFact terms symbols [predicate, root] = do
            unless (predicate == -1 || (predicate >= 0 && predicate < symbols)) (Left "invalid clause predicate reference")
            checkIndex terms root
        checkFact _ _ _ = Left "invalid full bytecode clause"
        zero operand = unless (operand == 0) (Left "invalid reserved template operand")
        depthOf table row = required where
            required = case row of
                [3, deBruijn, _, _, _, _] -> toInteger deBruijn + 1
                [2, left, right, _, _, _] -> max (child left) (child right)
                [4, body, annotation, _, _, _] -> max (max 0 (child body - 1)) (if annotation == 0 then 0 else child (annotation - 1))
                [7, left, right, _, _, _] -> max (child left) (child right)
                _ -> 0
            child root = table Array.! fromIntegral root

disassembleFull :: FullProgram -> String
disassembleFull program = case fullSections (fullWords program) of
    Left reason -> "Invalid full HOL V1 bytecode: " ++ reason ++ "\n"
    Right (header, slots, roles, terms, facts, _) -> unlines $ concat
        [ ["HOL V1 bytecode version " ++ show (header !! 1), "HEADER " ++ show header]
        , ["SLOT " ++ show index ++ " " ++ show slot | (index, slot) <- zip [0 :: Int ..] slots]
        , ["SYMBOL " ++ show index ++ " role=" ++ show role ++ " " ++ show (storeSymbol symbol) | ((index, symbol), role) <- zip (IntMap.toAscList (fullSymbols program)) roles]
        , ["TERM " ++ show index ++ " " ++ render row | (index, row) <- zip [0 :: Int ..] terms]
        , ["CLAUSE " ++ show index ++ " " ++ show row | (index, row) <- zip [0 :: Int ..] facts]
        , ["EXEC " ++ show (header !! 6)]
        ]
    where
        render [tag, a, b, c, d, meta] = case tag of
            0 -> "VAR " ++ show a
            1 -> "CONST " ++ show a
            2 -> "APP " ++ show a ++ " " ++ show b
            3 -> "INDEX " ++ show a
            4 -> "LAM " ++ show a ++ " metadata=" ++ show meta
            5 -> "NAT offset=" ++ show a ++ " length=" ++ show b
            6 -> "WILDCARD"
            7 -> "STRING cons=" ++ show a ++ " nil=" ++ show b ++ " offset=" ++ show c ++ " length=" ++ show d
            _ -> "UNKNOWN " ++ show tag
        render row = show row

fullUniqueFloor :: FullProgram -> Either String Int
fullUniqueFloor program
    | largest == maxBound = Left "full bytecode has exhausted variable identifiers"
    | otherwise = Right (largest + 1)
    where
        largest = maximum (0 : keys)
        keys = concatMap varKeys (fullVariables program)
            ++ concatMap symbolKeys (IntMap.elems (fullSymbols program))
            ++ concatMap (maybe [] typeKeys . unLamType . nodeType) (IntMap.elems (fullMetadata program))
            ++ concatMap (typeKeys . snd) (Map.toList (fullQueryTypes program))
            ++ concatMap (conKeys . TC) (Map.keys (fullKindEnv program))
            ++ concatMap (conKeys . DC) (Map.keys (fullTypeEnv program))
            ++ concatMap (\(Forall _ typ) -> typeKeys typ) (Map.elems (fullTypeEnv program))
        varKeys (LV_Named _) = []
        varKeys (LV_Unique (Unique key) _) = [key]
        varKeys (LV_ty_var (Unique key)) = [key]
        symbolKeys (ConstantSymbol constant) = conKeys constant
        symbolKeys _ = []
        conKeys (DC (DC_Unique (Unique key) _)) = [key]
        conKeys (TC (TC_Unique (Unique key))) = [key]
        conKeys _ = []
        typeKeys (TyMTV (Unique key)) = [key]
        typeKeys (TyCon (TCon con _)) = conKeys (TC con)
        typeKeys (TyApp lhs rhs) = typeKeys lhs ++ typeKeys rhs
        typeKeys _ = []

data TemplateValue
    = TemplateTerm TermNode
    | TemplateFormula P.MyPresburgerFormulaRep [P.MyVar] [TermNode] (Maybe SLoc)
    deriving ()

-- Reconstruct compiled terms for diagnostics and answer projection only.
-- Execution always uses the native graph and never this presentation view.
fullSourceTerms :: FullProgram -> Either String ([TermNode], TermNode)
fullSourceTerms program = do
    validateFullBytecode program
    (clauses, goal) <- fragmentSourceTerms 0 program
    maybe (Left "missing full query") (\query -> return (clauses, query)) goal

-- The clauses and the query of a validated fragment that is loaded on a program
-- with `known` symbols. A fragment that only extends the program has no query.
fragmentSourceTerms :: Int -> FullProgram -> Either String ([TermNode], Maybe TermNode)
fragmentSourceTerms known program = fragmentSections known (fullWords program) >>= fragmentSourceTermsFrom program

fragmentSourceTermsFrom :: FullProgram -> FullSections -> Either String ([TermNode], Maybe TermNode)
fragmentSourceTermsFrom program (header, _, _, rows, facts, payload) = do
    let payloadTable = IntMap.fromDistinctAscList (zip [0 ..] payload)
        slice offset count = take (fromIntegral count) (IntMap.elems (snd (IntMap.split (fromIntegral offset - 1) payloadTable)))
        table = Array.listArray (0, length rows - 1) (map (decodeTemplate slice table) (zip [0 ..] rows))
    mapM_ void (Array.elems table)
    clauses <- mapM (fact table) facts
    goal <- if header !! 6 < 0 then return Nothing else Just <$> (lookupTerm table (header !! 6) >>= finish)
    return (clauses, goal)
    where
        fact table [_, root] = lookupTerm table root >>= finish
        fact _ _ = Left "invalid full clause record"
        lookupTerm table root
            | root < 0 || toInteger root > toInteger (snd (Array.bounds table)) = Left "missing full template"
            | otherwise = table Array.! fromIntegral root
        finish (TemplateTerm term) = Right term
        finish _ = Left "incomplete Presburger term in bytecode"
        decodeTemplate slice table (index, [tag, a, b, c, d, meta]) = do
            let info = IntMap.findWithDefault (NodeMetadata Nothing noLamType Nothing) (fromIntegral meta) (fullMetadata program)
                location = nodeLocation info
                earlier root
                    | root >= index = Left "missing full template"
                    | otherwise = lookupTerm table root
                child root = earlier root >>= finish
            result <- case tag of
                0 -> TemplateTerm . mkLVar <$> checkedIndex (fullVariables program) (fromIntegral a)
                1 -> case IntMap.lookup (fromIntegral a) (fullSymbols program) of
                    Just (ConstantSymbol constant) -> Right (TemplateTerm (mkNConLoc location constant))
                    Just (PresburgerSymbol formula [] source) -> Right (TemplateTerm (NPresburgerCheck formula Map.empty source))
                    Just (PresburgerSymbol formula variables source) -> Right (TemplateFormula formula variables [] source)
                    Nothing -> Left "unknown full bytecode constant"
                2 -> do
                    function <- earlier a
                    argument <- child b
                    case function of
                        TemplateTerm term -> Right (TemplateTerm (mkNAppLoc location term argument))
                        TemplateFormula formula variables arguments source
                            | length arguments + 1 == length variables -> Right (TemplateTerm (NPresburgerCheck formula (Map.fromList (zip variables (arguments ++ [argument]))) source))
                            | otherwise -> Right (TemplateFormula formula variables (arguments ++ [argument]) source)
                3 -> Right (TemplateTerm (mkNIdx (fromIntegral a)))
                4 -> TemplateTerm . (\body -> NLam (nodeHint info) (nodeType info) body location) <$> child a
                5 -> do
                    let digits = slice a b
                        value = foldl (\number digit -> number * 10 + toInteger (digit - 48)) 0 digits
                    Right (TemplateTerm (mkNConLoc location (DC_NatL value)))
                6 -> Right (TemplateTerm (mkNConLoc location DC_wc))
                7 -> do
                    cons <- child a
                    nil <- child b
                    let symbols = map fromIntegral (slice c d)
                    heads <- IntMap.fromDistinctAscList <$> mapM (literalHead location cons) (IntSet.toAscList (IntSet.fromList symbols))
                    Right (TemplateTerm (foldr (\symbol tail -> mkNAppLoc location (heads IntMap.! symbol) tail) nil symbols))
                _ -> Left "unknown full template tag"
            return result
        decodeTemplate _ _ _ = Left "invalid full template record"
        literalHead location cons symbol = case IntMap.lookup symbol (fullSymbols program) of
            Just (ConstantSymbol (DC (DC_ChrL ch))) -> Right (symbol, mkNAppLoc location cons (mkNConLoc location (DC_ChrL ch)))
            _ -> Left "invalid string payload symbol"

queryFromBytecode :: FullProgram -> Either String TermNode
queryFromBytecode = fmap snd . fullSourceTerms
