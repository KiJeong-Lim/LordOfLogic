module LoL.Front.ArgumentScopes where

import Control.Monad (foldM)
import Data.Foldable (toList)
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import qualified LoL.Core as Core
import qualified LoL.Env as Env
import LoL.Front.Syntax
import LoL.Hol.Session (Kernel, Limits)

-- The class of an argument comes from its checked telescope. A named type
-- keeps its identity even when its transparent definition is another type.
argumentClasses :: Kernel -> Limits -> Env.Env -> Core.Global -> IO (Either Env.Refusal [Maybe (ScopeClass Core.Global)])
argumentClasses kernel limits env global = case lookup global signatures >>= telescope of
    Just result -> return (Right result)
    Nothing -> fmap (fmap normalized) (Env.scopeSignature kernel limits env global)
    where
        owner = globalOwner global
        signatures = case Map.lookup owner (Env.envDecls env) of
            Nothing -> []
            Just entry -> zip [g | (_, g) <- Env.declGlobals owner (Env.entryName entry) (Env.entryDecl entry), stored g] (Env.declTypes (Env.entryDecl entry))
        stored Core.GlobalProj {} = False
        stored _ = True
        normalized (Core.Pi _ domain rest) = classOf domain : normalized rest
        normalized _ = []
        classOf (Core.Proj b j _) = Just (ReferenceClass (Core.GlobalProj b j))
        classOf t = case inspect t of
            Just a -> a
            Nothing -> Nothing
        telescope (Core.Pi _ domain rest) = (:) <$> inspect domain <*> telescope rest
        telescope t = [] <$ inspect t
        inspect (Core.App f _) = inspect f
        inspect (Core.Cst n _) = Just (Just (ReferenceClass (Core.GlobalCst n)))
        inspect (Core.Ind b i _) = Just (Just (ReferenceClass (Core.GlobalInd b i)))
        inspect Core.Proj {} = Nothing
        inspect (Core.PField b j _) = Just (Just (ReferenceClass (Core.GlobalProj b j)))
        inspect Core.Prop = Just (Just SortClass)
        inspect Core.Type {} = Just (Just SortClass)
        inspect Core.Pi {} = Just (Just FunClass)
        inspect Core.Var {} = Just Nothing
        inspect Core.Con {} = Just Nothing
        inspect _ = Nothing

globalOwner :: Core.Global -> Core.ConstId
globalOwner (Core.GlobalCst c) = c
globalOwner (Core.GlobalInd c _) = c
globalOwner (Core.GlobalCon c _ _) = c
globalOwner (Core.GlobalProj c _) = c

-- Populate only when a class binding is active. Section discharge invalidates
-- the rebuilt telescopes; Undo restores the previous cache with the document.
prepare :: Kernel -> Limits -> Env.Env -> [Core.Global] -> IO (Either Env.Refusal Env.Syntax)
prepare kernel limits env globals
    | Map.null (Env.syntaxBindings syntax) = return (Right syntax)
    | otherwise = do
        cached <- foldM classify (Right (Env.syntaxClasses syntax)) globals
        return (fmap (\classes -> syntax { Env.syntaxClasses = classes }) cached)
    where
        syntax = Env.envSyntax env
        classify (Left failure) _ = return (Left failure)
        classify (Right memo) global = case Map.lookup global memo of
            Just _ -> return (Right memo)
            Nothing -> do
                answer <- argumentClasses kernel limits env global
                return (fmap (\cls -> Map.insert global cls memo) answer)

classScopes :: Env.Env -> ScopeClass Core.Global -> [String]
classScopes = syntaxClassScopes . Env.envSyntax

syntaxClassScopes :: Env.Syntax -> ScopeClass Core.Global -> [String]
syntaxClassScopes syntax cls = case Map.lookup cls (Env.syntaxBindings syntax) of
    Just (top, bottom) -> top ++ bottom
    Nothing -> []

headReference :: Env.Env -> Term -> Maybe (Core.Global, Bool)
headReference env (Term _ form) = case form of
    SName n -> named n False
    SDeclared n -> named n True
    SExplicit n -> named n True
    SInstance explicit n _ -> named n explicit
    SGlobal g -> Just (g, False)
    SExplicitGlobal g -> Just (g, True)
    SParen t -> headReference env t
    _ -> Nothing
    where
        named n explicit = (\g -> (g, explicit)) <$> lookupReference (Env.envNames env) n

positions :: Env.Env -> Term -> [[String]]
positions env headTerm = case headReference env headTerm of
    Nothing -> []
    Just (g, explicit) -> globalPositions (Env.envSyntax env) g explicit

globalPositions :: Env.Syntax -> Core.Global -> Bool -> [[String]]
globalPositions syntax g explicit = [scopes | (scopes, implicit) <- zip combined flags, explicit || not implicit] where
    classes = Map.findWithDefault [] g (Env.syntaxClasses syntax)
    defaults = Map.findWithDefault (Map.findWithDefault [] g (Env.syntaxDefaults syntax)) g (Env.syntaxObserved syntax)
    automatic = take (max (length classes) (length defaults)) (zipWith combine (classes ++ repeat Nothing) (defaults ++ repeat []))
    combine cls saved = case cls >>= (\key -> Map.lookup key (Env.syntaxBindings syntax)) of
        Nothing -> saved
        Just (top, bottom) -> top ++ filter (\sc -> sc `notElem` top && sc `notElem` bottom) saved ++ bottom
    combined = case Map.lookup g (Env.syntaxArgScopes syntax) of
        Nothing -> automatic
        Just manual -> take prefix (automatic ++ repeat []) ++ drop prefix manual
    prefix = Map.findWithDefault 0 g (Env.syntaxArgPrefixes syntax)
    flags = Map.findWithDefault [] g (Env.syntaxArguments syntax) ++ repeat False

-- Surface annotations can already identify a scope class before elaboration.
-- An arbitrary application is not evaluated to guess one.
expected :: Env.Env -> Term -> [String]
expected env _ | Map.null (Env.syntaxBindings (Env.envSyntax env)) = []
expected env t@(Term _ form) = case form of
    SApp f _ -> expected env f
    SParen x -> expected env x
    SForall {} -> classScopes env FunClass
    SArrow {} -> classScopes env FunClass
    SProp -> sortScopes
    SSet -> sortScopes
    SType {} -> sortScopes
    SUniverse {} -> sortScopes
    SInferredType -> sortScopes
    _ -> maybe [] (classScopes env . ReferenceClass . fst) (headReference env t)
    where
        sortScopes = classScopes env SortClass

withoutNames :: Env.Env -> [Name] -> Env.Env
withoutNames env _ | Map.null (Env.syntaxAliases syntax) && Map.null (Env.syntaxArgScopes syntax) && Map.null (Env.syntaxBindings syntax) && Map.null (Env.syntaxDefaults syntax) = env where
    syntax = Env.envSyntax env
withoutNames env names = Env.withSyntax (envSyntax { Env.syntaxAliases = Map.withoutKeys (Env.syntaxAliases envSyntax) keys }) (Env.withNames (Map.withoutKeys (Env.envNames env) keys) env) where
    keys = Set.fromList (map nameText names)
    envSyntax = Env.envSyntax env

-- A notation records where its parameters occurred in the RHS when it was
-- declared. Later Bind Scope or Arguments commands cannot change that grammar.
capture :: Env.Env -> [String] -> Term -> [(String, [String])]
capture env names term = Map.toList (Map.filter (not . null) first) where
    first = Map.fromListWith (flip const) (visit [] [] term)
    keys = Set.fromList names
    visit temp sticky t@(Term _ form) = case form of
        SName n | Set.member (nameText n) keys -> [(nameText n, temp ++ sticky)]
        SApp {} -> visit [] sticky h ++ concat (zipWith (\sc -> visit sc sticky) (positions env h ++ repeat []) args) where
            (h, args) = spine [] t
        SNotation parts args -> case Env.activeInterpretation syntax parts of
            Just (SyntaxRule _ _ _ (RocqTarget _ vars _ tpl)) -> concat (zipWith (\sc -> visit sc sticky) (slotPolicies parts vars tpl) args)
            _ -> concatMap (visit [] sticky) args
        SDelimited key arg -> case nameText key of
            '_' : label -> visit (resolved label) sticky arg
            label -> visit [] (resolved label ++ sticky) arg
        SAnnotation arg ty -> visit (expected env ty) sticky arg ++ visit sorts sticky ty
        SParen x -> visit temp sticky x
        SArrow a b -> visit sorts sticky a ++ visit sorts sticky b
        SLambda bs b -> binderTypes bs ++ visit [] sticky b
        SForall bs b -> binderTypes bs ++ visit sorts sticky b
        SLet _ m value body -> maybe [] (visit sorts sticky) m ++ visit [] sticky value ++ visit temp sticky body
        SProjection x _ -> visit [] sticky x
        SSequence xs -> concatMap (visit temp sticky) xs
        SMatch x _ _ m bs -> visit [] sticky x ++ maybe [] (visit sorts sticky) m ++ concat [visit temp sticky b | Branch _ _ b <- bs]
        SOperators x tailOps -> visit [] sticky x ++ concat [visit [] sticky b | (_, b) <- tailOps]
        SFix fs _ -> concat [binderTypes bs ++ visit sorts sticky ty ++ visit (expected env ty) sticky rhs | FixBody _ _ bs _ ty rhs <- fs]
        SMask _ _ x -> visit temp sticky x
        SWithout _ x -> visit temp sticky x
        _ -> []
        where
            resolved n = maybe [] pure (Map.lookup n (Env.syntaxKeys syntax))
            binderTypes = concatMap (maybe [] (visit sorts sticky) . binderType)
    sorts = classScopes env SortClass
    syntax = Env.envSyntax env
    spine xs (Term _ (SApp f x)) = spine (x : xs) f
    spine xs (Term _ (SParen f)) = spine xs f
    spine xs f = (f, xs)

slotPolicies :: [RulePart] -> [String] -> Template a -> [[String]]
slotPolicies parts names source = walk parts names where
    stored (TFormat _ t) = stored t
    stored (TSlotScopes keys _) = Map.fromList keys
    stored _ = Map.empty
    policies = stored source
    walk (AliasHead _ : more) ns = walk more ns
    walk (EntryRoot _ : more) ns = walk more ns
    walk (Literal _ : more) ns = walk more ns
    walk (RepeatSlot _ _ : more) (x : _ : ns) = scope x : walk more ns
    walk (AliasArg (Just name) : more) (_ : ns) = [name] : walk more ns
    walk (_ : more) (x : ns) = scope x : walk more ns
    walk _ _ = []
    scope name = Map.findWithDefault [] name policies

hasPolicies :: Env.Syntax -> Bool
hasPolicies syntax = any (not . Map.null) [Env.syntaxArgScopes syntax, Env.syntaxDefaults syntax] || not (Map.null (Env.syntaxBindings syntax))

-- In Rocq, consulting the argument scopes of a reference saves the merged
-- list. A later replacement of its class binding adds its new scopes to
-- that saved list. Keep only changed rows; the caller commits them with
-- the document checkpoint after the command has succeeded.
observedScopes :: Env.Syntax -> Set.Set Core.Global -> Map.Map Core.Global [[String]]
observedScopes syntax used
    | Map.null (Env.syntaxBindings syntax) = Map.empty
    | otherwise = Map.fromList [(g, value) | g <- Set.toAscList used, let value = updated g, any (not . null) value, value /= prior g]
    where
        prior g = automatic g (Map.findWithDefault (Map.findWithDefault [] g (Env.syntaxDefaults syntax)) g (Env.syntaxObserved syntax))
        updated g = automatic g (globalPositions syntax g True)
        automatic g value
            | Map.member g (Env.syntaxArgScopes syntax) = take (Map.findWithDefault 0 g (Env.syntaxArgPrefixes syntax)) value
            | otherwise = value

commandLookups :: Env.Env -> Command -> Set.Set Core.Global
commandLookups env command = case command of
    CCheck _ t -> term t
    CCompute _ t -> term t
    CPrint _ n -> maybe Set.empty Set.singleton (lookupReference (Env.envNames env) n)
    CAxiom _ _ t -> term t
    CDefinition loc _ _ bs typ rhs -> term (Term loc (SForall bs typ)) <> term (Term loc (SLambda bs rhs))
    CInductive loc fs -> Set.unions [term (Term loc (SForall bs t)) | IndBody _ _ bs ty cs <- fs, t <- ty : [v | Constructor _ _ v <- cs]]
    CFixpoint loc fs -> term (Term loc (SFix fs Nothing))
    CContext loc bs -> term (Term loc (SForall bs (Term loc SHole)))
    CRocqNotation loc _ _ _ _ _ names _ _ t -> termLookups (withoutNames env [Name loc s | s <- names]) t
    CSelectNotation loc _ _ vars t -> termLookups (withoutNames env [Name loc s | s <- vars]) t
    CWhere _ inner rules -> Set.unions (map (commandLookups env) (inner : rules))
    CUniverses _ _ inner -> commandLookups env inner
    CTemplate _ inner -> commandLookups env inner
    CPrimitive _ _ _ inner -> commandLookups env inner
    COrdinaryRecord _ _ inner -> commandLookups env inner
    CRecordDefinitions _ _ inner ds -> Set.unions (map (commandLookups env) (inner : [t | RecordDefinition t _ _ _ <- ds]))
    _ -> Set.empty
    where
        term = termLookups env

-- A bare @f bypasses implicit arguments; an application @f t still asks
-- for scopes on its operands. Lexical binders shadow references, including
-- in branch bodies. Reading a notation uses its captured globals.
termLookups :: Env.Env -> Term -> Set.Set Core.Global
termLookups env _ | Map.null (Env.syntaxBindings (Env.envSyntax env)) = Set.empty
termLookups env t = visit env [] False t where
    visit local temp applied input@(Term _ form) = case form of
        SApp {} -> visit local [] True headTerm <> Set.unions (zipWith (\sc -> visit local sc False) (policies ++ repeat []) operands) where
            (headTerm, operands) = spine [] input
            policies = case alias local headTerm of
                Just (SyntaxRule parts _ _ (RocqTarget _ vars _ tpl)) -> slotPolicies parts vars tpl
                _ -> positions local headTerm
        SName _ | Just (SyntaxRule _ _ _ (RocqTarget _ _ _ tpl)) <- alias local input -> Set.fromList (toList tpl)
        SNotation parts args -> case Env.activeInterpretation active parts of
            Just (SyntaxRule _ _ _ (RocqTarget _ vars _ tpl)) -> Set.fromList (toList tpl) <> Set.unions (zipWith (\sc -> visit local sc False) (slotPolicies parts vars tpl) args)
            _ -> Set.unions (map child args)
        SDelimited key value -> case nameText key of
            '_' : k -> visit local (keyScope k) applied value
            k -> visit (Env.withSyntax (foldr open syntax (keyScope k)) local) [] applied value
        SParen x -> visit local temp applied x
        SAnnotation v ty -> visit local (expected local ty) False v <> child ty
        SArrow a b -> child a <> child b
        SForall bs body -> bound local bs body
        SLambda bs body -> bound local bs body
        SLet name ty v body -> foldMap child ty <> child v <> visit (withoutNames local [name]) temp applied body
        SProjection v n -> child v <> reference local n
        SSequence xs -> foldMap child xs
        SPatternOperand _ v -> child v
        SOperators v ops -> child v <> foldMap (\(op, b) -> maybe Set.empty (\(g,_,_) -> Set.singleton g) (Map.lookup (nameText op) (Env.syntaxInfix syntax)) <> child b) ops
        SMask _ _ v -> visit local temp applied v
        SWithout n v -> visit (withoutNames local [n]) temp applied v
        SMatch v name family motive branches -> child v <> foldMap (visit (withoutNames local (maybe [] pure name ++ maybe [] patternNames family)) [] False) motive <> foldMap branch branches
        SFix fs _ -> Set.unions [bound local bs ty <> bound (withoutNames local [n | FixBody _ n _ _ _ _ <- fs]) bs body | FixBody _ _ bs _ ty body <- fs]
        _ -> case headReference local input of
            Just (g, explicit) | applied || not explicit -> Set.singleton g
            _ -> Set.empty
        where
            syntax = Env.envSyntax local
            active = foldr open syntax temp
            keyScope k = maybe [] pure (Map.lookup k (Env.syntaxKeys syntax))
            child = visit local [] False
            branch (Branch _ pat rhs) = visit (withoutNames local (patternNames pat)) temp False rhs
            patternNames (Pattern _ _ n vs) = [n | lookupReference (Env.envNames local) n == Nothing] ++ vs
            patternNames _ = []
    reference e n = maybe Set.empty Set.singleton (lookupReference (Env.envNames e) n)
    alias e (Term _ (SName n)) = enabled e n
    alias e (Term _ (SExplicit n)) = enabled e n
    alias e (Term _ (SParen inner)) = alias e inner
    alias _ _ = Nothing
    enabled e n = case Map.lookup (nameText n) (Env.syntaxAliases syntax) of
        Just rule | Env.enabledFor syntax ParsingOnly rule -> Just rule
        _ -> Nothing
        where syntax = Env.envSyntax e
    open sc syntax = syntax { Env.syntaxHistory = Left (OpenScope sc) : Env.syntaxHistory syntax, Env.syntaxOpen = sc : Env.syntaxOpen syntax }
    bound local [] body = visit local [] False body
    bound local (b : rest) body = foldMap (visit local [] False) (binderType b) <> bound (withoutNames local (binderVars b)) rest body
    spine xs (Term _ (SApp f x)) = spine (x : xs) f
    spine xs f = (f, xs)
