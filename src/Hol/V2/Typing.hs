module Hol.V2.Typing (inferGoal, solveEquations) where

import Control.Monad
import Control.Monad.Trans.Class
import Control.Monad.Trans.Except
import Control.Monad.Trans.State.Strict
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Hol.BETA.Constant
import Hol.BETA.Header
import Hol.BETA.TermNode
import qualified Hol.BETA.TypeChecker as Checker
import Z.Utils (MonadUnique, Unique, getUnique)

data Bound
    = TermBinder (MonoType Int)
    | TypeBinder Unique
    deriving ()

data Inference
    = Inference
        { inferredVariables :: Map.Map LogicVar (MonoType Int)
        , inferredNominals  :: Map.Map DataConstructor (MonoType Int)
        , inferredEquations :: [(MonoType Int, MonoType Int)]
        , inferredRigid     :: Set.Set Unique
        }
    deriving ()

-- This checks Hol's simple types. The constants representing CIC terms are
-- ordinary declared Hol constants; their CIC meaning is never inspected.
-- Ordinary polymorphic constants already carry explicit type arguments.
-- Logical operators have erased type arguments, as in BETA.Compiler.convert.
inferGoal :: MonadUnique m => KindEnv -> TypeEnv -> TermNode -> ExceptT String m (TermNode, Map.Map LogicVar (MonoType Int))
inferGoal kinds declarations goal = do
    ((annotated, actual), state) <- runStateT (infer [] Map.empty goal) (Inference Map.empty Map.empty [] Set.empty)
    solved <- lift (runExceptT (solveEquations ((actual, mkTyO) : inferredEquations state))) >>= either (const (throwE "incompatible Hol types in generated query")) return
    let close = Checker.substMTVars solved
        variables = Map.map close (inferredVariables state)
    let external = Map.elems variables ++ map close (Map.elems (inferredNominals state)) ++ map (close . TyMTV) (Set.toList used)
    when (any (escapes (inferredRigid state)) external) (throwE "an external value type escapes its type binder")
    finished <- either throwE return (finish solved (inferredRigid state) annotated)
    return (finished, variables)
    where
        used = identities goal
        failure = lift . throwE
        fresh = do
            unique <- lift (lift getUnique)
            if unique `Set.member` used then fresh else return unique
        freshType = TyMTV <$> fresh
        equation left right = unless (left == right) (modify (\state -> state { inferredEquations = (left, right) : inferredEquations state }))
        kind typ = either (const (failure "ill-kinded Hol type in generated query")) return (Checker.getKindEither typ)
        annotation aliases typ = do
            result <- case typ of
                TyMTV unique -> return (Map.findWithDefault typ unique aliases)
                TyCon (TCon (TC_Unique unique) declared)
                    | declared == Star -> return (Map.findWithDefault (TyMTV unique) unique aliases)
                    | otherwise -> failure "a runtime Hol type variable does not have kind *"
                TyCon (TCon constructor declared) -> case Map.lookup constructor kinds of
                    Just actual
                        | actual == declared -> return typ
                    _ -> failure "unknown or inconsistent Hol type constructor kind"
                TyApp function argument -> TyApp <$> annotation aliases function <*> annotation aliases argument
                TyVar _ -> failure "generalized type variable outside its scheme"
            void (kind result)
            return result
        typeArgument local aliases term = do
            result <- case term of
                LVar (LV_ty_var unique) -> return (TyMTV unique)
                NCon (TC constructor) _ -> case constructor of
                    TC_Unique unique -> return (TyMTV unique)
                    _ -> maybe (failure "unknown explicit Hol type constructor") (return . TyCon . TCon constructor) (Map.lookup constructor kinds)
                NIdx index -> case drop index local of
                    TypeBinder unique : _
                        | index >= 0 -> return (TyCon (TCon (TC_Unique unique) Star))
                    _ -> failure "a term binder is used as an explicit Hol type argument"
                NApp function argument _ -> TyApp <$> typeArgument local aliases function <*> typeArgument local aliases argument
                Susp {} -> typeArgument local aliases (rewrite NF term)
                _ -> failure "missing or invalid explicit Hol type argument"
            void (kind result)
            return result
        instantiate replacements typ = case typ of
            TyVar index -> case drop index replacements of
                value : _
                    | index >= 0 -> return value
                _ -> failure "invalid quantified Hol type scheme"
            TyApp function argument -> TyApp <$> instantiate replacements function <*> instantiate replacements argument
            _ -> annotation Map.empty typ
        variable entry = do
            variables <- gets inferredVariables
            case Map.lookup entry variables of
                Just known -> return known
                Nothing -> do
                    typ <- freshType
                    modify (\state -> state { inferredVariables = Map.insert entry typ (inferredVariables state) })
                    return typ
        nominal constructor = do
            nominals <- gets inferredNominals
            case Map.lookup constructor nominals of
                Just known -> return known
                Nothing -> do
                    typ <- freshType
                    modify (\state -> state { inferredNominals = Map.insert constructor typ (inferredNominals state) })
                    return typ
        infer local aliases term = case spine term of
            (NCon (DC (DC_LO LO_ty_pi)) location, (NLam hint marker body lambdaLocation, applicationLocation) : rest) -> do
                unique <- fresh
                let rigid = TyCon (TCon (TC_Unique unique) Star)
                    previous = case unLamType marker of
                        Just (TyMTV old) -> Just old
                        Just (TyCon (TCon (TC_Unique old) _)) -> Just old
                        _ -> Nothing
                    nextAliases = maybe aliases (\old -> Map.insert old rigid aliases) previous
                modify (\state -> state { inferredRigid = Set.insert unique (inferredRigid state) })
                (body', bodyType) <- infer (TypeBinder unique : local) nextAliases body
                equation bodyType mkTyO
                let result = NApp (NCon (DC (DC_LO LO_ty_pi)) location) (NLam hint (mkLamType (TyMTV unique)) body' lambdaLocation) applicationLocation
                foldM (apply local aliases) (result, mkTyO) rest
            (head@(NCon (DC constructor) _), arguments) -> do
                (prefix, functionType, values) <- case constructor of
                    DC_NatL number
                        | number >= 0 -> return (head, mkTyNat, arguments)
                        | otherwise -> failure "negative natural literal in generated query"
                    DC_ChrL _ -> return (head, mkTyChr, arguments)
                    DC_Unique {} -> do
                        typ <- nominal constructor
                        return (head, typ, arguments)
                    DC_LO LO_ty_pi -> failure "a Hol type binder needs one abstraction"
                    _ -> case Map.lookup constructor declarations of
                        Nothing -> failure ("undeclared Hol constant in generated query: " ++ show constructor)
                        Just (Forall parameters scheme) -> do
                            let erased = case constructor of
                                    DC_LO _ -> True
                                    _ -> False
                                count = if erased then 0 else length parameters
                                (types, values) = splitAt count arguments
                            when (length types /= count) (failure "missing explicit Hol type arguments")
                            replacements <- if erased then mapM (const freshType) parameters else mapM (typeArgument local aliases . fst) types
                            mapM_ (\typ -> kind typ >>= \actual -> unless (actual == Star) (failure "an explicit Hol type argument does not have kind *")) replacements
                            typ <- instantiate replacements scheme
                            return (foldl (\node (argument, location) -> NApp node argument location) head types, typ, values)
                foldM (apply local aliases) (prefix, functionType) values
            (_, arguments)
                | not (null arguments) -> do
                    let (head, _) = spine term
                    initial <- infer local aliases head
                    foldM (apply local aliases) initial arguments
            _ -> case term of
                LVar (LV_ty_var _) -> failure "a Hol type variable is used as a term"
                LVar entry -> (,) term <$> variable entry
                NIdx index -> case drop index local of
                    TermBinder typ : _
                        | index >= 0 -> return (term, typ)
                    _ -> failure "unbound de Bruijn index or type binder used as a term"
                NLam hint marker body location -> do
                    domain <- maybe freshType (annotation aliases) (unLamType marker)
                    domainKind <- kind domain
                    unless (domainKind == Star) (failure "a Hol lambda domain does not have kind *")
                    (body', codomain) <- infer (TermBinder domain : local) aliases body
                    return (NLam hint (mkLamType domain) body' location, mkTyArrow domain codomain)
                NPresburgerCheck formula free location -> do
                    free' <- forM free $ \value -> do
                        (value', typ) <- infer local aliases value
                        equation typ mkTyNat
                        return value'
                    return (NPresburgerCheck formula free' location, mkTyO)
                Susp {} -> infer local aliases (rewrite NF term)
                _ -> failure "an explicit type constructor is used as a Hol term"
        expect local aliases expected term = case (expected, term) of
            (TyApp (TyApp (TyCon (TCon TC_Arrow _)) domain) result, NLam hint marker body location) -> do
                mapM_ (\typ -> annotation aliases typ >>= equation domain) (unLamType marker)
                (body', _) <- expect (TermBinder domain : local) aliases result body
                return (NLam hint (mkLamType domain) body' location, expected)
            (_, LVar entry)
                | not (isTypeVariable entry) -> do
                    known <- gets (Map.lookup entry . inferredVariables)
                    case known of
                        Just old -> equation old expected
                        Nothing -> modify (\state -> state { inferredVariables = Map.insert entry expected (inferredVariables state) })
                    return (term, expected)
            _ -> do
                (term', actual) <- infer local aliases term
                equation actual expected
                return (term', expected)
        apply local aliases (function, functionType) (argument, location) = case functionType of
            TyApp (TyApp (TyCon (TCon TC_Arrow _)) domain) result -> do
                (argument', _) <- expect local aliases domain argument
                return (NApp function argument' location, result)
            _ -> do
                (argument', argumentType) <- infer local aliases argument
                result <- freshType
                equation functionType (mkTyArrow argumentType result)
                return (NApp function argument' location, result)
        isTypeVariable (LV_ty_var _) = True
        isTypeVariable _ = False
        identities term = case term of
            LVar (LV_Unique unique _) -> Set.singleton unique
            LVar (LV_ty_var unique) -> Set.singleton unique
            NCon (DC constructor) _ -> Set.union ownIdentity declaredIdentities where
                ownIdentity = case constructor of
                    DC_Unique unique _ -> Set.singleton unique
                    _ -> Set.empty
                declaredIdentities = case Map.lookup constructor declarations of
                    Just (Forall _ typ) -> typeIdentities typ
                    Nothing -> Set.empty
            NCon (TC (TC_Unique unique)) _ -> Set.singleton unique
            NApp function argument _ -> identities function `Set.union` identities argument
            NLam _ marker body _ -> maybe Set.empty typeIdentities (unLamType marker) `Set.union` identities body
            NPresburgerCheck _ free _ -> Set.unions (map identities (Map.elems free))
            Susp body _ _ environment -> identities body `Set.union` Set.unions [identities value | Binds value _ <- environment]
            _ -> Set.empty

spine :: TermNode -> (TermNode, [(TermNode, Maybe SLoc)])
spine = collect [] where
    collect arguments (NApp function argument location) = collect ((argument, location) : arguments) function
    collect arguments head = (head, arguments)

typeIdentities :: MonoType Int -> Set.Set Unique
typeIdentities typ = case typ of
    TyMTV unique -> Set.singleton unique
    TyCon (TCon (TC_Unique unique) _) -> Set.singleton unique
    TyApp function argument -> typeIdentities function `Set.union` typeIdentities argument
    _ -> Set.empty

escapes :: Set.Set Unique -> MonoType Int -> Bool
escapes bound typ = case typ of
    TyCon (TCon (TC_Unique unique) _) -> unique `Set.member` bound
    TyApp function argument -> escapes bound function || escapes bound argument
    _ -> False

finish :: Checker.TypeSubst -> Set.Set Unique -> TermNode -> Either String TermNode
finish solved rigid = term where
    typ = unrigid . Checker.substMTVars solved
    unrigid value = case value of
        TyCon (TCon (TC_Unique unique) _)
            | unique `Set.member` rigid -> TyMTV unique
        TyApp function argument -> TyApp (unrigid function) (unrigid argument)
        _ -> value
    typeNode value = case value of
        TyMTV unique -> return (LVar (LV_ty_var unique))
        TyCon (TCon constructor _) -> return (NCon (TC constructor) Nothing)
        TyApp function argument -> NApp <$> typeNode function <*> typeNode argument <*> pure Nothing
        TyVar _ -> Left "inference produced an uninstantiated type scheme"
    term node = case node of
        LVar (LV_ty_var unique) -> typeNode (typ (TyMTV unique))
        NCon (TC (TC_Unique unique)) _ -> typeNode (typ (TyMTV unique))
        NApp function argument location -> NApp <$> term function <*> term argument <*> pure location
        NLam hint marker body location -> NLam hint (LamType (typ <$> unLamType marker)) <$> term body <*> pure location
        NPresburgerCheck formula free location -> NPresburgerCheck formula <$> traverse term free <*> pure location
        _ -> return node

-- Keep the remaining equations untouched. Each one sees the current bindings
-- when it is solved; following a metavariable also compresses its alias path.
-- The established checker still decides kinds, rigid equality and occurs.
solveEquations :: Monad m => [(MonoType Int, MonoType Int)] -> ExceptT ((MonoType Int, MonoType Int), Checker.TypeError) m Checker.TypeSubst
solveEquations equations = do
    bindings <- execStateT (mapM_ solve equations >> closeBindings) Map.empty
    return (Checker.TypeSubst bindings)
    where
        solve (left, right) = do
            left' <- zonk left
            right' <- zonk right
            Checker.TypeSubst additions <- lift (Checker.getMGU left' right')
            modify (Map.union additions)
        closeBindings = gets Map.keys >>= mapM_ (zonk . TyMTV)
        zonk typ = case typ of
            TyMTV unique -> do
                found <- gets (Map.lookup unique)
                case found of
                    Nothing -> return typ
                    Just replacement -> do
                        result <- zonk replacement
                        modify (Map.insert unique result)
                        return result
            TyApp function argument -> TyApp <$> zonk function <*> zonk argument
            _ -> return typ
