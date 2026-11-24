module Hol.BETA.Compiler where

import Hol.BETA.Constant
import Hol.BETA.Diagnostic (diagnosticNoLoc)
import Hol.BETA.Header
import Hol.BETA.TermNode
import Control.Monad
import Control.Monad.Trans.Class
import Control.Monad.Trans.Except
import Control.Monad.Trans.State.Strict
import qualified Data.List as List
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import qualified Z.Doc
import Z.Utils

type ExpectedAs = String

type DeBruijnIndicesEnv = [Unique]

type FreeVariableEnv = Map.Map Unique TermNode

convertVar :: FreeVariableEnv -> DeBruijnIndicesEnv -> IVar -> Either ErrMsg TermNode
convertVar var_name_env env var
    = case var `List.elemIndex` env of
        Nothing -> case Map.lookup var var_name_env of
            Just node -> Right node
            Nothing -> Left (compilerError ("Unbound free variable with unique id " ++ show (unUnique var) ++ "."))
        Just idx -> Right (mkNIdx idx)

convertType :: FreeVariableEnv -> DeBruijnIndicesEnv -> MonoType Int -> Either ErrMsg TermNode
convertType var_name_env env (TyMTV mtv) = convertVar var_name_env env mtv
convertType var_name_env env (TyApp typ1 typ2) =
    mkNApp <$> convertType var_name_env env typ1 <*> convertType var_name_env env typ2
convertType _ _ (TyCon (TCon tc _)) = Right (mkNCon tc)
convertType _ _ (TyVar idx) = Left (compilerError ("Unexpected generalized type variable index " ++ show idx ++ "."))

convertCon :: FreeVariableEnv -> DeBruijnIndicesEnv -> Maybe SLoc -> DataConstructor -> [MonoType Int] -> Either ErrMsg TermNode
convertCon var_name_env env sl con tapps = do
    converted <- mapM (convertType var_name_env env) tapps
    return (List.foldl' (mkNAppLoc sl) (mkNConLoc sl con) converted)

compilerError :: String -> ErrMsg
compilerError msg = diagnosticNoLoc "HolBETA-CompilerError" [Z.Doc.text msg]

-- A wildcard is given its checked type and, when that type has a term here,
-- the term of it.
convertWithWildcards :: Monad m => (SLoc -> MonoType Int -> Maybe TermNode -> m TermNode) -> FreeVariableEnv -> DeBruijnIndicesEnv -> TermExpr (DataConstructor, [MonoType Int]) (SLoc, MonoType Int) -> ExceptT ErrMsg m TermNode
convertWithWildcards wildcard var_name_env env = loop env . reduceTermExpr where
    loop _ (Con (loc, _) (DC_LO logical_operator, _)) = return (mkNConLoc (Just loc) logical_operator)
    loop current (Con (loc, typ) (DC_wc, _)) = lift (wildcard loc typ (either (const Nothing) Just (convertType var_name_env current typ)))
    loop current (Var _ var) = either throwE return (convertVar var_name_env current var)
    loop current (Con (loc, _) (data_constructor, tapps)) = either throwE return (convertCon var_name_env current (Just loc) data_constructor tapps)
    loop current (App (loc, _) term1 term2) = mkNAppLoc (Just loc) <$> loop current term1 <*> loop current term2
    loop current (Lam (loc, lamTy) var1 hint term2) = do
        body <- loop (var1 : current) term2
        return (mkNLamLoc (Just loc) hint domTy body)
        where
            domTy = case lamTy of
                TyApp (TyApp (TyCon (TCon TC_Arrow _)) t1) _ -> LamType (Just t1)
                _ -> noLamType

convertWithoutChecking :: MonadUnique m => FreeVariableEnv -> DeBruijnIndicesEnv -> TermExpr (DataConstructor, [MonoType Int]) (SLoc, MonoType Int) -> ExceptT ErrMsg m TermNode
convertWithoutChecking = convertWithWildcards (\loc _ typ -> return (typedWildcard loc typ))

-- The wildcard of a program is the constant applied to its type, as a
-- polymorphic constant is applied to its type arguments. A run makes a
-- variable of it wherever it meets a value, and that variable has this type
-- whether or not a typed variable still holds the value around it.
typedWildcard :: SLoc -> Maybe TermNode -> TermNode
typedWildcard loc typ = maybe wildcard (mkNAppLoc (Just loc) wildcard) typ where
    wildcard = mkNConLoc (Just loc) DC_wc

convertProgram :: MonadUnique m => Map.Map IVar LargeId -> Map.Map MetaTVar SmallId -> Map.Map IVar (MonoType Int) -> TermExpr (DataConstructor, [MonoType Int]) (SLoc, MonoType Int) -> ExceptT ErrMsg m TermNode
convertProgram nameHints used_mtvs assumptions = fmap makeUniversalClosure . convertWithoutChecking Map.empty initialEnv where
    initialEnv :: DeBruijnIndicesEnv
    initialEnv = Set.toList (Map.keysSet assumptions `Set.union` Map.keysSet used_mtvs)
    makeUniversalClosure :: TermNode -> TermNode
    makeUniversalClosure body = foldr wrapTyVar afterAssumed (Map.toDescList used_mtvs) where
        wrapAssumption (ivar, ty) acc = mkNApp (mkNCon LO_pi) (mkNLamHintTy (Map.lookup ivar nameHints) (mkLamType ty) acc)
        wrapTyVar (mtv, _) acc = mkNApp (mkNCon LO_ty_pi) (mkNLamHintTy Nothing (mkLamType (TyMTV mtv)) acc)
        afterAssumed = foldr wrapAssumption body (Map.toDescList assumptions)

-- A wildcard with its type (typedWildcard) is one wildcard: the type, of
-- whatever shape, goes with it.
replaceWildcards :: MonadUnique m => TermNode -> m TermNode
replaceWildcards (NApp (NCon (DC DC_wc) _) annotation _)
    | typeTerm annotation = fmap (\u -> mkLVar (LV_Unique u noHint)) getUnique
    where
        typeTerm (NCon (TC _) _) = True
        typeTerm (LVar (LV_ty_var _)) = True
        typeTerm (NApp function argument _) = typeTerm function && typeTerm argument
        typeTerm _ = False
replaceWildcards (NCon (DC DC_wc) _) = fmap (\u -> mkLVar (LV_Unique u noHint)) getUnique
replaceWildcards (NApp t1 t2 sl) = liftM2 (mkNAppLoc sl) (replaceWildcards t1) (replaceWildcards t2)
replaceWildcards (NLam h ty t sl) = fmap (mkNLamLoc sl h ty) (replaceWildcards t)
replaceWildcards t = return t

-- A type variable of a query is, in the run, the logic variable of the same
-- identity: the types that the checker gives the variables of the query
-- (`assumptions`) name the type variables that the run binds.
-- Term-only compatibility entry. Executable queries must retain the type
-- map returned by convertQueryWithTypes, including anonymous variables.
convertQuery :: MonadUnique m => Map.Map MetaTVar SmallId -> Map.Map IVar (MonoType Int) -> FreeVariableEnv -> TermExpr (DataConstructor, [MonoType Int]) (SLoc, MonoType Int) -> ExceptT ErrMsg m TermNode
convertQuery used_mtvs assumptions var_name_env = fmap fst . convertQueryWithTypes used_mtvs assumptions var_name_env

-- Query wildcards are allocated after source beta reduction, in the same
-- traversal order as before. Keep their checked types before Con annotations
-- disappear; a wildcard need not occur in the value of any named variable.
convertQueryWithTypes :: MonadUnique m => Map.Map MetaTVar SmallId -> Map.Map IVar (MonoType Int) -> FreeVariableEnv -> TermExpr (DataConstructor, [MonoType Int]) (SLoc, MonoType Int) -> ExceptT ErrMsg m (TermNode, Map.Map LogicVar (MonoType Int))
convertQueryWithTypes used_mtvs assumptions var_name_env query = do
    let var_name_env' = foldr (\mtv env -> Map.insert mtv (LVar (LV_ty_var mtv)) env) var_name_env (Map.keys used_mtvs)
        namedTypes = Map.fromList [(variable, typ) | (ivar, LVar variable) <- Map.toList var_name_env, Just typ <- [Map.lookup ivar assumptions]]
        wildcard _ typ _ = do
            variable <- lift (getUnique >>= \unique -> return (LV_Unique unique noHint))
            modify (Map.insert variable typ)
            return (mkLVar variable)
    (node, wildcardTypes) <- ExceptT $ do
        (result, types) <- runStateT (runExceptT (convertWithWildcards wildcard var_name_env' [] query)) Map.empty
        return (fmap (\term -> (term, types)) result)
    return (foldr (\mtv -> substTyMTV mtv mtv) node (Map.keys used_mtvs), namedTypes `Map.union` wildcardTypes)

viewLam :: TermExpr dcon annot -> ([IVar], TermExpr dcon annot)
viewLam = go [] where
    go :: [IVar] -> TermExpr dcon annot -> ([IVar], TermExpr dcon annot)
    go vars (Lam annot var _h term) = go (var : vars) term
    go vars term = (vars, term)

unFoldApp :: TermExpr dcon annot -> (TermExpr dcon annot, [TermExpr dcon annot])
unFoldApp = flip go [] where
    go :: TermExpr dcon annot -> [TermExpr dcon annot] -> (TermExpr dcon annot, [TermExpr dcon annot])
    go (App annot term1 term2) terms = go term1 (term2 : terms)
    go term terms = (term, terms)

isPredicate :: MonoType Int -> Bool
isPredicate (TyCon (TCon (TC_Named "o") _)) = True
isPredicate (TyApp (TyApp (TyCon (TCon TC_Arrow _)) typ1) typ2) = isPredicate typ2
isPredicate _ = False

reduceTermExpr :: TermExpr dcon annot -> TermExpr dcon annot
reduceTermExpr = go Map.empty where
    go :: Map.Map IVar (TermExpr tapp annot) -> TermExpr tapp annot -> TermExpr tapp annot
    go mapsto (App annot1 (Lam annot2 var _h term1) term2)
        = go mapsto (go (Map.singleton var term2) term1)
    go mapsto (Var annot var)
        = case Map.lookup var mapsto of
            Nothing -> Var annot var
            Just term -> term
    go mapsto (Con annot con)
        = Con annot con
    go mapsto (App annot term1 term2)
        = App annot (go mapsto term1) (go mapsto term2)
    go mapsto (Lam annot var h term)
        = Lam annot var h (go mapsto term)
