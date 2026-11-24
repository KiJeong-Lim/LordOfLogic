module LoL.Front.Template where

import Control.Monad (foldM, unless)
import Data.List (elemIndex, foldl', intercalate)
import Data.Functor.Identity (Identity (..))
import Data.Functor.Const (Const (..))
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import LoL.Core (Global (..))
import qualified LoL.Front.HostLexer as Lex
import LoL.Front.Syntax

printFormat :: Template a -> (Maybe String, Template a)
printFormat (TFormat fmt body) = (Just fmt, snd (printFormat body))
printFormat (TSlotScopes _ body) = printFormat body
printFormat body = (Nothing, body)

-- Free identifiers are resolved in the declaring module. A metavariable
-- denotes the caller's syntax. Ordinary RHS binders must not capture it.
compile :: (Name -> Either String Global) -> [String] -> Term -> Either String (Template Global)
compile = compileBlock Set.empty

compileBlock :: Set.Set String -> (Name -> Either String Global) -> [String] -> Term -> Either String (Template Global)
compileBlock members resolve variables = walk [] where
    global explicit n
        | Set.member (nameText n) members = Right (TBlockName explicit (nameText n))
        | otherwise = TReference explicit <$> resolve n
    walk bound (Term _ form) = case form of
        SName name
            | nameText name `elem` bound || nameText name `elem` variables -> Right (TVariable (nameText name))
            | otherwise -> global False name
        SDeclared name -> global True name
        SExplicit name -> global True name
        SGlobal name -> Right (TReference False name)
        SExplicitGlobal name -> Right (TReference True name)
        SApp (Term _ (SName name)) arg
            | nameText name == ".." -> TRecursion <$> walk bound arg
        SApp f x -> TApply <$> walk bound f <*> walk bound x
        SArrow a b -> TArrow <$> walk bound a <*> walk bound b
        SAnnotation a b -> TCast <$> walk bound a <*> walk bound b
        SForall bs inner -> bind True bound bs inner
        SLambda bs inner -> bind False bound bs inner
        SLet name ty val inner -> TLet (nameText name) <$> traverse (walk bound) ty <*> walk bound val <*> walk (nameText name : bound) inner
        SProjection inner label -> TProjection <$> walk bound inner <*> resolve label
        SInstance explicit n levels -> TInstance explicit <$> resolve n <*> pure (map saveLevel levels)
        SUniverse level -> Right (TUniverse (saveLevel level))
        SMatch subject alias family motive arms -> do
            let patternVars (Pattern _ _ _ ns) = map nameText ns
                patternVars _ = []
                savePattern RawPattern {} = Left "Unexpanded notation in a pattern."
                savePattern (WildPattern _) = Right AnyPattern
                savePattern (Pattern _ False n []) | nameText n `elem` variables = Right (VariablePattern (nameText n))
                savePattern (Pattern _ e n ns) = ConstructorPattern e <$> resolve n <*> pure (map nameText ns)
                branch (Branch _ pat rhs) = TemplateBranch <$> savePattern pat <*> walk (patternVars pat ++ bound) rhs
                locals = maybe [] (pure . nameText) alias ++ maybe [] patternVars family
            TCase <$> walk bound subject <*> pure (nameText <$> alias) <*> traverse savePattern family <*> traverse (walk (locals ++ bound)) motive <*> mapM branch arms
        SFix functions chosen -> do
            let members = [nameText fn | FixBody _ fn _ _ _ _ <- functions]
                function (FixBody _ fn groups struct ty rhs) = do
                    let bindings outer [] = Right ([], outer)
                        bindings outer (b:bs) = do
                            let ns = map nameText (binderVars b)
                            domain <- traverse (walk outer) (binderType b)
                            (rest, inner) <- bindings (ns ++ outer) bs
                            Right ((binderImpl b, ns, domain) : rest, inner)
                    (bs, locals) <- bindings bound groups
                    TemplateFunction (nameText fn) bs (nameText <$> struct) <$> walk locals ty <*> walk (take (length locals - length bound) locals ++ members ++ bound) rhs
            TFix <$> mapM function functions <*> pure (nameText <$> chosen)
        SParen inner -> walk bound inner
        SProp -> Right (TSort "Prop")
        SSet -> Right (TSort "Set")
        SInferredType -> Right (TSort "Type")
        SType n -> Right (TSort ("Type@" ++ show n))
        SHole -> Right (TSort "_")
        SNumeral n -> Right (TNumber n)
        _ -> Left "Unsupported term in a notation interpretation."
    bind _ bound [] inner = walk bound inner
    bind prod bound (Binder _ names typ implicit : rest) inner = do
        domain <- traverse (walk bound) typ
        let labels = map nameText names
        body <- bind prod (reverse labels ++ bound) rest inner
        Right (foldr (\name -> TAbstraction prod implicit name domain) body labels)

saveLevel :: LevelSyntax -> TemplateLevel
saveLevel (LevelSyntax _ form) = case form of
    LNumber n -> UNumber n
    LName x -> UNamed (nameText x)
    LHole -> UHole
    LOffset u _ n -> UOffset (saveLevel u) n
    LMaximum _ a b -> UMaximum (saveLevel a) (saveLevel b)

loadLevel :: Span -> TemplateLevel -> LevelSyntax
loadLevel at level = LevelSyntax at $ case level of
    UNumber n -> LNumber n
    UNamed n -> LName (Name at n)
    UHole -> LHole
    UOffset u n -> LOffset (loadLevel at u) (Name at "+") n
    UMaximum a b -> LMaximum (Name at "max") (loadLevel at a) (loadLevel at b)

-- Names in operands are kept free under all private interpretation binders.
-- This also works in dependent matches whose implicit indices are inserted
-- later by Hol: resolving by name does not guess a de Bruijn depth.
operandNames :: Term -> [String]
operandNames (Term _ form) = case form of
    SName n -> [nameText n]
    SExplicit n -> [nameText n]
    SNotation _ args -> concatMap operandNames args
    SSequence args -> concatMap operandNames args
    SPatternOperand _ value -> operandNames value
    SDelimited _ t -> operandNames t
    SMask _ _ t -> operandNames t
    SWithout n t -> nameText n : operandNames t
    SApp f x -> both f x
    SArrow a b -> both a b
    SAnnotation a b -> both a b
    SOperators a rest -> operandNames a ++ concatMap (operandNames . snd) rest
    SProjection t _ -> operandNames t
    SParen t -> operandNames t
    SForall bs t -> under bs t
    SLambda bs t -> under bs t
    SLet n ty v t -> nameText n : maybe [] operandNames ty ++ both v t
    SMatch t alias family motive arms -> operandNames t ++ maybe [] (pure . nameText) alias ++ maybe [] patternNames family ++ maybe [] operandNames motive ++ concat [patternNames pat ++ operandNames rhs | Branch _ pat rhs <- arms]
    SFix fs _ -> concat [nameText n : under bs ty ++ operandNames rhs | FixBody _ n bs _ ty rhs <- fs]
    _ -> []
    where
        both a b = operandNames a ++ operandNames b
        under bs t = concat [map nameText (binderVars b) ++ maybe [] operandNames (binderType b) | b <- bs] ++ operandNames t
        patternNames (Pattern _ _ _ ns) = map nameText ns
        patternNames (RawPattern source) = operandNames source
        patternNames _ = []

slotBindings :: [RulePart] -> [String] -> Bool
slotBindings parts names = length names == sum (map arity parts) && Set.size (Set.fromList names) == length names where
    arity AliasHead {} = 0
    arity EntryRoot {} = 0
    arity Literal {} = 0
    arity RepeatSlot {} = 2
    arity _ = 1

-- Visit the immediate subterms without changing the references or binder names.
children :: Applicative f => (Template a -> f (Template a)) -> Template a -> f (Template a)
children f t = case t of
    TApply a b -> TApply <$> f a <*> f b
    TArrow a b -> TArrow <$> f a <*> f b
    TCast a b -> TCast <$> f a <*> f b
    TAbstraction p i x ty b -> TAbstraction p i x <$> traverse f ty <*> f b
    TLet x ty a b -> TLet x <$> traverse f ty <*> f a <*> f b
    TSlotScopes scopes b -> TSlotScopes scopes <$> f b
    TFormat fmt b -> TFormat fmt <$> f b
    TProjection a field -> flip TProjection field <$> f a
    TCase v alias family motive bs -> TCase <$> f v <*> pure alias <*> pure family <*> traverse f motive <*> traverse branch bs
        where branch (TemplateBranch pat rhs) = TemplateBranch pat <$> f rhs
    TFix fs chosen -> flip TFix chosen <$> traverse member fs
        where
            member (TemplateFunction n bs struct ty rhs) = TemplateFunction n <$> traverse binder bs <*> pure struct <*> f ty <*> f rhs
            binder (i,ns,dom) = (,,) i ns <$> traverse f dom
    TRecursion b -> TRecursion <$> f b
    _ -> pure t

-- The prefix/suffix outside the iterated context is applied just once.
-- The printer uses the same split in reverse, including for left iteration.
data Iteration a = Iteration
    { iterWrap    :: Template a -> Template a
    , iterStep    :: Template a
    , iterBase    :: Template a
    , iterFirst   :: String
    , iterLast    :: String
    , iterReverse :: Bool
    }

iteration :: Eq a => String -> String -> Template a -> Either String (Iteration a)
iteration first lastVar source = case holes source of
    [base]
        | not (mentions first base) && mentions lastVar base -> split first lastVar False base
        | mentions first base && not (mentions lastVar base) -> split lastVar first True base
    _ : _ : _ -> case [(child,it) | child <- subs source, hasRange first lastVar child, Right it <- [iteration first lastVar child]] of
        (child,it) : _ -> Right it { iterWrap = \value -> runIdentity (children (Identity . replace child (iterWrap it value)) source) }
        [] -> invalid
    _ -> invalid
    where
        replace old new part = if part == old then new else part
        invalid = Left "A recursive notation needs one iterator and two corresponding variables."
        subs = getConst . children (Const . (: []))
        holes (TRecursion b) | mentions first b || mentions lastVar b = [b]
        holes t = concatMap holes (subs t)
        label (TVariable x) = Just x
        label (TAbstraction _ _ x _ _) = Just x
        label (TLet x _ _ _) = Just x
        label _ = Nothing
        mentions x t = label t == Just x || any (mentions x) (subs t)
        outside _ (TRecursion _) = False
        outside x t = label t == Just x || any (outside x) (subs t)
        split x y reversed base = maybe invalid Right (seek source) where
            encloses t = not (null (holes t)) && outside x t
            seek t
                | not (encloses t) = Nothing
                | child : _ <- filter encloses (subs t), Just inner <- seek child =
                    Just (inner { iterWrap = \value -> runIdentity (children (Identity . wrap inner value) t) })
                | fits t base = Just (Iteration id t base x y reversed)
                | otherwise = Nothing
            wrap inner value node = if encloses node then iterWrap inner value else node
            -- A binder's own lambda can enclose both the variable and the
            -- dots while the true repeated context also includes its head.
            -- Match the two contexts up to the varying name and recursive tail.
            fits (TRecursion _) _ = True
            fits a b = headOf a == skeleton b && length left == length right && and (zipWith fits left right) where
                left = subs a
                right = subs b
            skeleton = runIdentity . children (const (Identity (TSort "_")))
            headOf t = case skeleton t of
                TVariable k | k == x -> TVariable y
                TAbstraction p i k ty b | k == x -> TAbstraction p i y ty b
                TLet k ty a b | k == x -> TLet y ty a b
                other -> other

-- Check the iterator while the declaration (or object entry) is being
-- installed. An invalid interpretation must not become a deferred failure.
validateIteration :: Eq a => [RulePart] -> [String] -> Template a -> Either String ()
validateIteration parts names template = () <$ iterationPlan (rangeNames parts names) template

rangeNames :: [RulePart] -> [String] -> [(String,String)]
rangeNames (Literal _ : ps) ns = rangeNames ps ns
rangeNames (EntryRoot _ : ps) ns = rangeNames ps ns
rangeNames (AliasHead _ : ps) ns = rangeNames ps ns
rangeNames (RepeatSlot _ _ : ps) (x:y:ns) = (x,y) : rangeNames ps ns
rangeNames (_:ps) (_:ns) = rangeNames ps ns
rangeNames _ _ = []

hasRange :: String -> String -> Template a -> Bool
hasRange x y = any mentions . recursions where
    recursions (TRecursion b) = b : concatMap recursions (subs b)
    recursions t = concatMap recursions (subs t)
    subs = getConst . children (Const . (: []))
    mentions t = case t of
        TVariable n -> n == x || n == y
        TAbstraction _ _ n _ _ | n == x || n == y -> True
        TLet n _ _ _ | n == x || n == y -> True
        _ -> any mentions (subs t)

-- Give every range its own private continuation. No legal surface name can
-- start with '#'. Independent ranges can have different lengths and fold
-- directions even when both use the same representation of a list.
iterationPlan :: Eq a => [(String,String)] -> Template a -> Either String (Template a, Map.Map String (String,Iteration a))
iterationPlan ranges source = do
    result@(shape, _) <- foldM mark (source, Map.empty) ranges
    unless (not (hasDots shape)) (Left "The interpretation contains dots without a matching recursive range.")
    Right result
    where
        hasDots TRecursion {} = True
        hasDots t = or (getConst (children (Const . pure . hasDots) t) :: [Bool])
        mark previous (x,y) = install (0 :: Int) previous where
            install i (shape, iters) = do
                it <- iteration x y shape
                let key = "#" ++ x ++ ":" ++ show i
                    tailRef (TRecursion b) | b == iterBase it = TVariable key
                    tailRef t = runIdentity (children (Identity . tailRef) t)
                    replaced = iterWrap it (TVariable key)
                    updated = (replaced, Map.insert key (x,it { iterStep = tailRef (iterStep it) }) iters)
                if hasRange x y replaced then install (i + 1) updated else Right updated

unroll :: Eq a => String -> String -> [String] -> Template a -> Either String (Template a)
unroll first lastVar elements source = do
    it <- iteration first lastVar source
    let ordered = if iterReverse it then elements else reverse elements
    case ordered of
        [] -> Left "A recursive notation needs at least one operand."
        final : earlier -> do
            let initial = substitute (iterLast it) final Nothing (iterBase it)
                step tailTerm key = substitute (iterFirst it) key (Just tailTerm) (iterStep it)
            let updated = iterWrap it (foldl' step initial earlier)
            if hasRange first lastVar updated then unroll first lastVar elements updated else Right updated
    where
        substitute x key tailTerm t = case t of
            TRecursion _ | Just value <- tailTerm -> value
            _ -> rename (runIdentity (children (Identity . substitute x key tailTerm) t))
            where
                rename (TVariable v) | v == x = TVariable key
                rename (TAbstraction p i v ty b) | v == x = TAbstraction p i key ty b
                rename (TLet v ty a b) | v == x = TLet key ty a b
                rename original = original

-- Gallina's "as pattern" constr entry must bind at least once in the RHS.
validatePatternSlots :: [RulePart] -> [String] -> Template a -> Either String ()
validatePatternSlots parts names body = validateSlots parts names where
    validateSlots (EntryRoot _ : rest) ns = validateSlots rest ns
    validateSlots (AliasHead _ : rest) ns = validateSlots rest ns
    validateSlots (Literal _ : rest) ns = validateSlots rest ns
    validateSlots (RepeatSlot _ item : rest) (x : y : ns) = do
        unless (item `notElem` [BinderSlot, TokenSlot "closed binder"] || all (\n -> binds n body) [x, y]) (Left "Both ends of a recursive binder must occur in binding position.")
        validateSlots rest ns
    validateSlots (AsNameSlot {} : rest) ns = validateSlots (PatternSlot CurrentPattern False Nothing : rest) ns
    validateSlots (PatternSlot mode _ _ : rest) (n : ns) | mode /= NativePattern = do
        unless (binds n body) (Left ("Expected " ++ n ++ " in a binding position in the notation interpretation."))
        validateSlots rest ns
    validateSlots (_ : rest) (_ : ns) = validateSlots rest ns
    validateSlots _ _ = Right ()
    binds n t = named || any (binds n) (getConst (children (Const . (: [])) t)) where
        named = case t of
            TAbstraction _ _ x _ _ -> x == n
            TLet x _ _ _ -> x == n
            TCase _ alias family _ arms -> alias == Just n || maybe False binder family || any (\(TemplateBranch pat _) -> binder pat) arms
            TFix fs _ -> any (\(TemplateFunction fn bs _ _ _) -> n == fn || any (\(_, xs, _) -> n `elem` xs) bs) fs
            _ -> False
        binder (ConstructorPattern _ _ xs) = n `elem` xs
        binder (VariablePattern x) = n == x
        binder AnyPattern = False

-- Pattern operands that bind through a single constructor expand to the same
-- flat match syntax as the user's Gallina. Exhaustiveness is checked by Hol.
patternOperand :: (Name -> Maybe Global) -> Term -> Either String Term
patternOperand lookupName source = gather [] source where
    at = termSpan source
    gather items (Term _ form) = case form of
        SParen x -> gather items x
        SWithout n (Term _ (SName _)) | null items -> Right (Term at (SName n))
        SApp f x -> argument x >>= \name -> gather (name : items) f
        SName name -> case lookupName name of
            Just g@GlobalCon {} -> named False (ResolvedName (nameSpan name) (nameText name) g) items
            _ | null items -> Right (Term at (SName name))
            _ -> invalid
        SExplicit name -> case lookupName name of
            Just g@GlobalCon {} -> named True (ResolvedName (nameSpan name) (nameText name) g) items
            _ -> invalid
        SGlobal g@GlobalCon {} -> named False (ResolvedName at ("#" ++ show g) g) items
        SExplicitGlobal g@GlobalCon {} -> named True (ResolvedName at ("#" ++ show g) g) items
        SHole | null items -> Right (Term at SHole)
        _ -> invalid
    argument (Term loc form) = case form of
        SName n -> Right n
        SWithout n (Term _ (SName _)) -> Right n
        SHole -> Right (Name loc "_")
        SParen x -> argument x
        _ -> invalid
    named explicit n items = Right (Term at (SPatternOperand (Pattern at explicit n items) source))
    invalid = Left "Expected a variable, a wildcard, or a flat constructor pattern."

instantiate :: (Name -> Maybe Global) -> Span -> [RulePart] -> [String] -> [Term] -> Template Global -> Either String Term
instantiate lookupName at parts names operands source = do
    let (_, template) = printFormat source
    (arguments, recursive) <- bindSlots parts names operands
    expression <- foldM (\t (x,y,keys) -> unroll x y keys t) template recursive
    expand arguments [] expression
    where
        bindSlots [] [] [] = Right (Map.empty, [])
        bindSlots (AliasHead _ : rest) vs args = bindSlots rest vs args
        bindSlots (EntryRoot _ : rest) vars args = bindSlots rest vars args
        bindSlots (Literal _ : rest) vars args = bindSlots rest vars args
        bindSlots (RepeatSlot _ _ : rest) (x : y : vars) (Term _ (SSequence (a : as)) : args) = do
            (env, repeat') <- bindSlots rest vars args
            let items = a : as
                keys = zipWith (\n _ -> "#" ++ x ++ ":" ++ show n) [0 :: Int ..] items
            Right (Map.union (Map.fromList (zip keys items)) env, (x, y, keys) : repeat')
        bindSlots (AsNameSlot strict _ _ : rest) (x : vars) (a : args) = do
            let name (Term _ (SParen t)) = name t
                name t@(Term loc (SName n)) | '.' `notElem` nameText n = Right (Term loc (SWithout n t))
                name t@(Term _ SHole) | not strict = Right t
                name _ = Left ("Expected a binder name for " ++ x)
            value <- name a
            (env, ranges) <- bindSlots rest vars args
            Right (Map.insert x value env,ranges)
        bindSlots (PatternSlot {} : rest) (x : vars) (a : args) = do
            prepared <- patternOperand lookupName a
            (env, recursive) <- bindSlots rest vars args
            Right (Map.insert x prepared env, recursive)
        bindSlots (kind : rest) (x : vars) (a : args) = do
            (env, repeat') <- bindSlots rest vars args
            let value = case a of
                    Term loc (SName n) | kind == NameSlot || kind == TokenSlot "name" -> Term loc (SWithout n a)
                    _ -> a
            Right (Map.insert x value env, repeat')
        bindSlots _ _ _ = Left "Notation arguments do not fit their declaration."
        node = Term at
        unavailable = Set.fromList (concatMap operandNames operands)
        boundName env bound key = case Map.lookup key env of
            Just (Term _ SPatternOperand {}) -> boundName Map.empty bound "pattern_value"
            Just (Term _ (SWithout actual (Term _ (SName _)))) -> Right actual
            Just (Term _ (SName actual)) -> Right actual
            Just (Term _ (SLambda [Binder _ [actual] _ _] (Term _ SHole))) -> Right actual
            Just (Term _ SHole) -> Right (Name at "_")
            Just _ -> Left ("Expected a binder name for " ++ key)
            Nothing | key == "_" -> Right (Name at key)
                    | otherwise -> Right (Name at (fresh key))
                where
                    fresh n | Set.member n unavailable || any ((== n) . nameText . snd) bound = fresh (n ++ "'")
                            | otherwise = n
        destructure env key name inner = case Map.lookup key env of
            Just (Term _ (SPatternOperand pat _)) -> node (SMatch (node (SName name)) Nothing Nothing Nothing [Branch at pat inner])
            _ -> inner
        expand env bound expr = case expr of
            TBlockName explicit key -> Right (node ((if explicit then SExplicit else SName) (Name at key)))
            TReference explicit global -> Right (node (if explicit then SExplicitGlobal global else SGlobal global))
            TVariable x -> case lookup x bound of
                Just name -> Right (node (SName name))
                Nothing -> case Map.lookup x env of
                    Just (Term _ (SPatternOperand _ given)) -> Right given
                    Just value -> Right value
                    Nothing -> Left ("Unbound notation variable " ++ x)
            TApply f a -> node <$> (SApp <$> part f <*> part a)
            TArrow a b -> node <$> (SArrow <$> part a <*> part b)
            TCast a b -> node <$> (SAnnotation <$> part a <*> part b)
            TAbstraction product' implicit key domain body -> do
                name <- boundName env bound key
                ty <- traverse part domain
                value <- expand env ((key,name) : bound) body
                let bs = case Map.lookup key env of
                        Just (Term _ (SLambda [provided] (Term _ SHole))) ->
                            [provided { binderType = case binderType provided of { Nothing -> ty; domain -> domain } }]
                        _ -> [Binder at [name] ty implicit]
                let inside = destructure env key name value
                Right (node (if product' then SForall bs inside else SLambda bs inside))
            TLet key ty val body -> do
                name <- boundName env bound key
                inside <- destructure env key name <$> expand env ((key,name) : bound) body
                node <$> (SLet name <$> traverse part ty <*> part val <*> pure inside)
            TProjection val field -> node . flip SProjection (resolved field) <$> part val
            TUniverse level -> Right (node (SUniverse (loadLevel at level)))
            TInstance e g ls -> Right (node (SInstance e (resolved g) (map (loadLevel at) ls)))
            TCase v alias family motive arms -> do
                subject <- part v
                let variable (VariablePattern key) = case Map.lookup key env of
                        Just (Term _ (SName name)) -> Just name
                        _ -> Nothing
                    variable _ = Nothing
                case (alias, family, motive, arms) of
                    (Nothing, Nothing, Nothing, [TemplateBranch pat rhs]) | Just n <- variable pat ->
                        node . SLet n Nothing subject <$> part rhs
                    _ -> do
                        (pat, indices) <- maybe (Right (Nothing,[])) (fmap (\(p,ns) -> (Just p,ns)) . pattern') family
                        self <- traverse (boundName env (indices ++ bound)) alias
                        sharedName <- boundName Map.empty bound "pattern_subject"
                        let aliasScope = maybe [] pure ((,) <$> alias <*> self)
                            shared = any (\(TemplateBranch p _) -> maybe False (const True) (variable p)) arms
                            value = if shared then node (SName sharedName) else subject
                            branch (TemplateBranch p rhs) = do
                                (headPat, locals) <- pattern' p
                                inner <- expand env (locals ++ bound) rhs
                                let body = maybe inner (\n -> node (SLet n Nothing value inner)) (variable p)
                                return (Branch at headPat body)
                        result <- traverse (expand env (aliasScope ++ indices ++ bound)) motive
                        expression <- node . SMatch value self pat result <$> mapM branch arms
                        return (if shared then node (SLet sharedName Nothing subject expression) else expression)
            TFix fs chosen -> do
                members <- bindNames bound [n | TemplateFunction n _ _ _ _ <- fs]
                let function (TemplateFunction fn bs struct ty rhs) = do
                        let bindings locals [] = Right ([],locals)
                            bindings locals ((impl,vs,dom):rest) = do
                                ns <- bindNames locals vs
                                t <- traverse (expand env locals) dom
                                (more,inner) <- bindings (reverse ns ++ locals) rest
                                Right (Binder at (map snd ns) t impl : more, inner)
                        (binders,locals) <- bindings bound bs
                        name <- required members fn
                        decreases <- traverse (required locals) struct
                        FixBody at name binders decreases <$> expand env locals ty <*> expand env (take (length locals - length bound) locals ++ members ++ bound) rhs
                node <$> (SFix <$> mapM function fs <*> traverse (required members) chosen)
            TNumber n -> Right (node (SNumeral n))
            TSort s -> case s of
                "Prop" -> Right (node SProp)
                "Set" -> Right (node SSet)
                "Type" -> Right (node SInferredType)
                "_" -> Right (node SHole)
                _ -> case splitAt 5 s of
                    ("Type@", ns) | [(n,"")] <- reads ns, n >= 0 -> Right (node (SType n))
                    _ -> Left "Invalid notation sort."
            TFormat _ body -> part body
            TRecursion _ -> Left "A recursive interpretation needs a recursive notation."
            where
                part = expand env bound
                resolved g = ResolvedName at ("#" ++ show g) g
                bindNames _ [] = Right []
                bindNames locals (x:xs) = do
                    n <- boundName env locals x
                    ((x,n) :) <$> bindNames ((x,n) : locals) xs
                required locals x = maybe (Left ("Unknown notation binder " ++ x)) Right (lookup x locals)
                pattern' AnyPattern = Right (WildPattern at,[])
                pattern' (VariablePattern key) = case Map.lookup key env of
                    Just (Term _ (SPatternOperand pat _)) -> Right (pat, [])
                    Just (Term _ SHole) -> Right (WildPattern at, [])
                    Just (Term _ (SName _)) -> Right (WildPattern at, [])
                    _ -> Left ("Expected a flat pattern for " ++ key)
                pattern' (ConstructorPattern explicit g vars) = do
                    ns <- bindNames bound vars
                    Right (Pattern at explicit (resolved g) (map snd ns), reverse ns)

-- Used for --explicit to reconstruct the public syntax after all globals.
render :: (a -> Either String String) -> SyntaxRule a -> Either String String
render reference (SyntaxRule parts level assoc (RocqTarget scope names mode body)) = do
    let (fmt, expr) = printFormat body
    target <- traverse reference expr
    let (entry, patternParts) = ruleEntry parts
    tokens <- case patternParts of
        AliasHead key : _ -> Right (key : names)
        _ -> spell patternParts names
    let direction = [assoc ++ " associativity" | assoc /= "no"]
        usage = case mode of
            BothWays -> []
            ReservedSyntax -> []
            ParsingOnly -> ["only parsing"]
            PrintingOnly -> ["only printing"]
        options = join ", " ([maybe "" (\e -> "in custom " ++ e ++ " ") entry ++ "at level " ++ show level] ++ direction ++ modifiers patternParts names ++ usage ++ maybe [] (\f -> ["format \"" ++ f ++ "\""]) fmt)
    let (command, interpretation) = if mode == ReservedSyntax then ("Reserved Notation", "") else ("Notation", " := (" ++ expression target ++ ")")
    case patternParts of
        AliasHead key : slots -> do
            let policies = [n ++ " in scope " ++ sc | (n,AliasArg (Just sc)) <- zip names slots] ++ usage
            Right ("Abbreviation " ++ unwords (key:names) ++ interpretation ++ (if null policies then "" else " (" ++ join ", " policies ++ ")") ++ ".")
        _ -> Right (concat [command, " \"", unwords tokens, "\"", interpretation, " (", options, ")", maybe "" (" : " ++) scope, "."])
    where
        spell [] [] = Right []
        spell (Literal s : rest) ns = (quotedWord s :) <$> spell rest ns
        spell (RepeatSlot sep _ : rest) (x : y : ns) = (([x] ++ words sep ++ [".."] ++ words sep ++ [y]) ++) <$> spell rest ns
        spell (_ : rest) (x : ns) = (x :) <$> spell rest ns
        spell _ _ = Left "Invalid notation variable table."
        quotedWord s
            | c:cs <- s, Lex.identStart c, all Lex.identContinue cs = "'" ++ s ++ "'"
            | otherwise = s
        modifiers [] _ = []
        modifiers (Literal _ : rest) ns = modifiers rest ns
        modifiers (RepeatSlot _ item : rest) (x : y : ns) = modifiers [item, item] [x, y] ++ modifiers rest ns
        modifiers (LevelSlot n : rest) (x : ns) = (x ++ " at level " ++ show n) : modifiers rest ns
        modifiers (AsNameSlot strict e strength : rest) (x : ns) = unwords ([x] ++ maybe [] (\n -> ["custom",n]) e ++ maybe [] (\n -> ["at","level",show n]) strength ++ ["as",if strict then "ident" else "name"]) : modifiers rest ns
        modifiers (EntrySlot e strength : rest) (x : ns) = (x ++ maybe " constr" (" custom " ++) e ++ maybe "" ((" at level " ++) . show) strength) : modifiers rest ns
        modifiers (PatternSlot mode strict lvl : rest) (x : ns) = (unwords ([x] ++ option) : modifiers rest ns) where
            strength = maybe [] (\n -> ["at","level",show n]) lvl
            kind = ["strict" | strict] ++ ["pattern"]
            option = case mode of
                NativePattern -> kind ++ strength
                CurrentPattern -> strength ++ ["as"] ++ kind
                OtherPattern target -> maybe ["constr"] (\e -> ["custom", e]) target ++ strength ++ ["as"] ++ kind
        modifiers (TokenSlot k : rest) (x : ns) = (x ++ " " ++ k) : modifiers rest ns
        modifiers (BinderSlot : rest) (x : ns) = (x ++ " binder") : modifiers rest ns
        modifiers (NameSlot : rest) (x : ns) = (x ++ " ident") : modifiers rest ns
        modifiers (_ : rest) (_ : ns) = modifiers rest ns
        modifiers _ _ = []
        join _ [] = ""
        join sep (x : xs) = x ++ concatMap (sep ++) xs
render _ _ = Left "Expected a Rocq notation interpretation."

expression :: Template String -> String
expression expr = case expr of
    TBlockName e n -> (if e then "@" else "") ++ n
    TReference e name -> (if e then "@" else "") ++ name
    TVariable x -> x
    TApply f x -> "(" ++ expression f ++ " " ++ expression x ++ ")"
    TArrow a b -> "(" ++ expression a ++ " -> " ++ expression b ++ ")"
    TCast a b -> "(" ++ expression a ++ " : " ++ expression b ++ ")"
    TAbstraction p implicit x ty b -> "(" ++ (if p then "forall " else "fun ") ++ binder ++ (if p then ", " else " => ") ++ expression b ++ ")" where
        binder = case ty of
            Nothing -> x
            Just domain -> (if implicit then "{" else "(") ++ x ++ " : " ++ expression domain ++ (if implicit then "}" else ")")
    TLet x ty val b -> "(let " ++ x ++ maybe "" ((" : " ++) . expression) ty ++ " := " ++ expression val ++ " in " ++ expression b ++ ")"
    TNumber n -> show n
    TSort s -> case splitAt 5 s of
        ("Type@",ns) -> "Type@{" ++ ns ++ "}"
        _ -> s
    TProjection r field -> "(" ++ expression r ++ ").(" ++ field ++ ")"
    TInstance explicit global us -> (if explicit then "@" else "") ++ global ++ "@{" ++ unwords (map levelText us) ++ "}"
    TUniverse u -> "Type@{" ++ levelText u ++ "}"
    TCase v alias family motive bs -> concat ["(match ", expression v, maybe "" (" as " ++) alias, maybe "" ((" in " ++) . patternText) family, maybe "" ((" return " ++) . expression) motive, " with", concatMap branchText bs, " end)"]
    TFix fs chosen -> "(fix " ++ intercalate " with " (map functionText fs) ++ maybe "" (" for " ++) chosen ++ ")"
    TSlotScopes _ inner -> expression inner
    TFormat _ inner -> expression inner
    TRecursion inner -> ".. (" ++ expression inner ++ ") .."
    where
        patternText AnyPattern = "_"
        patternText (VariablePattern n) = n
        patternText (ConstructorPattern explicit headName vs) = (if explicit then "@" else "") ++ unwords (headName:vs)
        branchText (TemplateBranch pat b) = " | " ++ patternText pat ++ " => " ++ expression b
        functionText (TemplateFunction n bs arg ty rhs) = concat [n, concatMap binderText bs, maybe "" (\v -> " {struct " ++ v ++ "}") arg, " : ", expression ty, " := ", expression rhs]
        binderText (impl,vs,ty) = case ty of
            Nothing -> " " ++ unwords vs
            Just t -> (if impl then " {" else " (") ++ unwords vs ++ " : " ++ expression t ++ (if impl then "}" else ")")
        levelText u = case u of
            UNumber n -> show n
            UNamed n -> n
            UHole -> "_"
            UOffset a n -> "(" ++ levelText a ++ " + " ++ show n ++ ")"
            UMaximum a b -> "max(" ++ levelText a ++ ", " ++ levelText b ++ ")"


-- Enable/Disable can select by a head alone or by an application pattern.
-- Names from the left-hand side refer to the same positional metavariables
-- even when the enabling command renames them.
matchesInterpretation :: Eq a => [String] -> Template a -> [String] -> Template a -> Bool
matchesInterpretation names query variables actual = case query of
    TReference _ a -> case headOf root of { TReference _ b -> a == b; _ -> False }
    _ -> match [] query root
    where
        root = snd (printFormat actual)
        headOf (TApply f _) = headOf f
        headOf t = t
        match _ (TSort "_") _ = True
        match locals (TVariable x) (TVariable y) = case lookup x locals of
            Just bound -> y == bound
            Nothing -> case elemIndex x names of { Just i -> elemIndex y variables == Just i; _ -> x == y }
        match locals (TAbstraction p i x ty body) (TAbstraction q j y dom rest) = p == q && i == j && optional locals ty dom && match ((x,y):locals) body rest
        match locals (TLet x ty a b) (TLet y dom c d) = optional locals ty dom && match locals a c && match ((x,y):locals) b d
        match _ (TReference _ x) (TReference _ y) = x == y
        match locals a b = skeleton a == skeleton b && and (zipWith (match locals) (subterms a) (subterms b))
        optional locals (Just a) (Just b) = match locals a b
        optional _ Nothing Nothing = True
        optional _ _ _ = False
        skeleton = runIdentity . children (const (Identity (TSort "_")))
        subterms = getConst . children (Const . pure)
