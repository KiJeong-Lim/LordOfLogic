module LoL.Front.Fixity where

import Control.Monad (foldM)
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import LoL.Core (Global (..))
import LoL.Diagnostic
import qualified LoL.Env as Env
import qualified LoL.Front.ArgumentScopes as ArgScopes
import qualified LoL.Front.Notation as Notation
import LoL.Front.Parse (lexSource)
import qualified LoL.Front.Template as Template
import LoL.Front.Syntax
import LoL.Hol.Session (Kernel, Limits)
import LoL.Hol.Embed (Report (..))
import Text.Read (readMaybe)

-- Arguments belongs to the declaration's module, regardless of which local
-- or qualified spelling resolves to that declaration.
validateArgumentsOwner :: [Global] -> Env.Env -> Command -> Either Diagnostic ()
validateArgumentsOwner owned env command = case command of
    CArguments _ name _ _ -> do
        global <- resolve env name
        if global `elem` owned then Right () else Left (Diagnostic (nameSpan name) "LoL-ScopeError" "H-ArgumentsOwner" "Arguments for an imported declaration must be set in its defining module" [nameText name])
    _ -> Right ()

configureWith :: Kernel -> Limits -> Env.Env -> Command -> IO (Either Diagnostic Env.Env)
configureWith kernel limits env command = case (configure env command, command) of
    (Right changed, CArguments position name arguments options) -> case resolve env name of
        Left failure -> return (Left failure)
        Right global -> do
            answer <- Env.argumentArity kernel limits env global
            return $ case answer of
                Left (Env.KernelUndecided message) -> Left (Diagnostic position "LoL-KernelUndecided" "R5" message [])
                Left (Env.KernelRejected (Just report)) -> Left (Diagnostic position "LoL-KernelError" (reportRule report) "the kernel could not inspect the argument type" (reportTerms env report))
                Left failure -> Left (Diagnostic position "LoL-KernelUndecided" "R5" ("could not inspect an admitted constant's type: " ++ show failure) [])
                Right arity
                    | Just count <- projectionCount options, count >= arity -> Left (problem position "H-Arguments" "A projection needs a receiver after its parameters")
                    | length arguments <= arity -> Right changed
                    | map nameText options == ["extra", "scopes"], all scoped (drop arity arguments) ->
                        let syntax = Env.envSyntax changed in Right (Env.withSyntax syntax { Env.syntaxArguments = Map.adjust (take arity) global (Env.syntaxArguments syntax) } changed)
                    | otherwise -> Left (problem position "H-Arguments" "Arguments lists more positions than the constant's type has")
    (result, _) -> return result
    where
        scoped (Argument _ _ _ keys) = not (null keys)

-- Metadata is a surface instruction, never evidence that a term is typed.
-- In particular Numerals does not give its two names a privileged Core type.
configure :: Env.Env -> Command -> Either Diagnostic Env.Env
configure = configureBlock Set.empty

configureBlock :: Set.Set String -> Env.Env -> Command -> Either Diagnostic Env.Env
configureBlock members env command = case command of
    CArguments position name arguments options -> do
        global <- resolve env name
        writtenScopes <- mapM (\(Argument _ _ _ keys) -> mapM resolveKey keys) arguments
        let argScopes
                | map nameText options == ["clear", "scopes"] = Map.insert global [] (Env.syntaxArgScopes syntax)
                | any (not . null) writtenScopes = Map.insert global writtenScopes (Env.syntaxArgScopes syntax)
                | otherwise = Env.syntaxArgScopes syntax
            observed
                | map nameText options == ["clear", "scopes"] || any (not . null) writtenScopes = Map.delete global (Env.syntaxObserved syntax)
                | otherwise = Env.syntaxObserved syntax
            prefixes
                | map nameText options == ["clear", "scopes"] || any (not . null) writtenScopes = Map.delete global (Env.syntaxArgPrefixes syntax)
                | otherwise = Env.syntaxArgPrefixes syntax
            flags = [implicit | ArgSpec _ implicit _ <- arguments]
            masks = if null arguments then Env.syntaxArguments syntax else Map.insert global flags (Env.syntaxArguments syntax)
            previous = Env.syntaxNever syntax
            acceptsSimpl = case global of
                GlobalCst {} -> True
                GlobalProj {} -> True
                _ -> False
            projections = Env.syntaxProjectionParameters syntax
            registered = case (global, projectionCount options) of
                (GlobalCst {}, Just count) -> Map.insert global count projections
                _ -> projections
        never <- case map nameText options of
            [] -> Right previous
            ["extra", "scopes"] -> Right previous
            ["projection", _]
                | GlobalCst {} <- global, Just _ <- projectionCount options -> Right previous
            ["simpl", "never"]
                | acceptsSimpl -> Right (Set.insert global previous)
            ["clear", "scopes"] | not (any (not . null) writtenScopes) -> Right previous
            ["clear", "simpl"]
                | acceptsSimpl -> Right (Set.delete global previous)
            _ -> Left (problem position "H-Arguments" "Expected simpl never or clear simpl on a constant or projection")
        return (Env.withSyntax syntax { Env.syntaxObserved = observed, Env.syntaxArgScopes = argScopes, Env.syntaxArgPrefixes = prefixes, Env.syntaxArguments = masks, Env.syntaxNever = never, Env.syntaxProjectionParameters = registered } env)
    CRocqNotation position locality parts level direction scope names mode fmt source -> do
        mapM_ (checkEntry position locality) [name | part <- parts, name <- case part of { RepeatSlot _ (EntrySlot (Just e) _) -> [e]; EntryRoot e -> [e]; EntrySlot (Just e) _ -> [e]; AsNameSlot _ (Just e) _ -> [e]; PatternSlot (OtherPattern (Just e)) _ _ -> [e]; _ -> [] }]
        body <- rewrite (ArgScopes.withoutNames env [Name position v | v <- names]) source
        template <- either (Left . problem position "H-Notation") Right (Template.compileBlock members lookupGlobal names body)
        let scopes = ArgScopes.capture env names source
            captured = if null scopes then template else TSlotScopes scopes template
            rule = SyntaxRule parts level direction (RocqTarget scope names mode (maybe captured (flip TFormat captured) fmt))
        next <- either (Left . problem position "H-Notation") Right (installRule ("", position) rule syntax)
        Right (Env.withSyntax next env)
    CSelectNotation position _ setting vars source -> do
        body <- rewrite (ArgScopes.withoutNames env [Name position v | v <- vars]) source
        query <- either (Left . problem position "H-Notation") Right (Template.compile lookupGlobal vars body)
        changed <- either (Left . problem position "H-Scope") Right (applyScope (ToggleInterpretation setting vars query) syntax)
        Right (Env.withSyntax changed env)
    CScope position locality action -> do
        case action of
            DeclareCustomEntry name | Map.member (ownEntry name) (Env.syntaxEntries syntax) -> Left (problem position "H-Notation" ("Custom entry already exists: " ++ name))
            _ -> Right ()
        resolved <- case action of
            DeclareCustomEntry name -> Right (DeclareCustomEntry (ownEntry name))
            _ -> traverse (resolve env) action
        changed <- either (Left . problem position "H-Scope") Right (applyScope resolved syntax)
        let result = case action of
                DeclareCustomEntry name -> Env.declareEntry (locality == LocalSyntax) (ownEntry name) changed
                _ -> changed
        Right (Env.withSyntax result env)
    CNotation position _ written -> do
        rule <- resolveRule env written
        next <- either (Left . problem position "H-Notation") Right (installRule ("", position) rule syntax)
        return (Env.withSyntax next env)
    CInfix position symbol name level association -> do
        global <- resolve env name
        case lexSource (nameText symbol) of
            Right [token]
                | tokenKind token == "operator", tokenText token == nameText symbol, Env.validOperator (nameText symbol) -> Right ()
            _ -> Left (problem (nameSpan symbol) "H-Infix" "an infix symbol must lex as one non-reserved operator")
        if level < 0 || level > 200 then
            Left (problem position "H-Infix" "an infix level must be between 0 and 200")
        else do
            let direction = maybe "no" nameText association
            if direction `elem` ["left", "right", "no"] then do
                case infixOverlap (nameText symbol) (global, level, direction) syntax of
                    Just first -> Left (problem position "H-Notation" ("infix conflicts with notation" ++ siteOf syntax first))
                    Nothing -> Right ()
                case Map.lookup (nameText symbol) (Env.syntaxInfix syntax) of
                    Just previous
                        | previous /= (global, level, direction) -> Left (problem position "H-Infix" "conflicting declarations of the same infix symbol")
                    _ -> return (Env.withSyntax syntax { Env.syntaxInfix = Map.insert (nameText symbol) (global, level, direction) (Env.syntaxInfix syntax) } env)
            else Left (problem position "H-Infix" "unknown associativity")
    CNumerals position zero successor -> do
        first <- resolve env zero
        next <- resolve env successor
        case Env.syntaxNumerals syntax of
            Just previous
                | previous /= (first, next) -> Left (problem position "H-Numeral" "conflicting Numerals declarations")
            _ -> return (Env.withSyntax syntax { Env.syntaxNumerals = Just (first, next) } env)
    _ -> Right env
    where
        syntax = Env.envSyntax env
        ownEntry n = if null (Env.syntaxOwner syntax) then n else Env.syntaxOwner syntax ++ "." ++ n
        resolveKey key = case nameText key of
            '_' : value -> lookupKey key value
            value -> lookupKey key value
        lookupKey at value
            | Set.member value (Env.syntaxScopes syntax) = Right value
            | Just sc <- Map.lookup value (Env.syntaxKeys syntax) = Right sc
            | otherwise = Left (problem (nameSpan at) "H-Scope" ("Unknown argument scope: " ++ value))
        checkEntry position locality name = case Map.lookup name (Env.syntaxEntries syntax) of
            Nothing | candidates@(_:_:_) <- Notation.entryCandidates (Env.syntaxReader syntax) name -> Left (problem position "H-Notation" ("Ambiguous custom entry " ++ name ++ ": " ++ unwords candidates))
            Nothing -> Left (problem position "H-Notation" ("Unknown custom entry: " ++ name))
            Just True | locality /= LocalSyntax -> Left (problem position "H-Notation" ("A notation using local custom entry " ++ name ++ " must be Local."))
            _ -> Right ()
        lookupGlobal n = maybe (Left ("Unknown reference in notation: " ++ nameText n)) Right (lookupReference (Env.envNames env) n)

applyScope :: ScopeAction Global -> Env.Syntax -> Either String Env.Syntax
applyScope action syntax = case action of
    _ | Just (Activation _ _ False _ _ _, _:_:_) <- switchTargets action syntax -> Left "More than one interpretation matches. Use the all modifier."
    BindScope _ _ classes | any constructor classes -> Left "Constructors cannot be used as notation scope classes."
    OpenScope requested -> apply OpenScope requested
    CloseScope requested -> apply CloseScope requested
    DelimitScope _ ('_':_) -> Left "Scope delimiters should not start with an underscore."
    UndelimitScope name | Env.scopeDelimiter syntax name == Nothing -> Left ("No bound key for scope " ++ name)
    _ -> Right (replayScope action syntax)
    where
        constructor (ReferenceClass GlobalCon {}) = True
        constructor _ = False
        apply make name
            | Set.member name (Env.syntaxScopes syntax) = Right (replayScope (make name) syntax)
            | Just scope <- Map.lookup name (Env.syntaxKeys syntax) = Right (replayScope (make scope) syntax)
            | otherwise = Left ("Unknown notation scope: " ++ name)

switchTargets :: ScopeAction Global -> Env.Syntax -> Maybe (Activation, [SyntaxRule Global])
switchTargets action syntax = case action of
    ToggleNotation setting -> Just (setting, Env.selectedInterpretations syntax setting)
    ToggleInterpretation setting ns body -> Just (setting, [r | r@(SyntaxRule _ _ _ (RocqTarget _ vars _ tpl)) <- Env.selectedInterpretations syntax setting, Template.matchesInterpretation ns body vars tpl])
    _ -> Nothing

-- Recorded Open/Close events contain the resolved name. A Global Open may
-- outlive the local declaration of that scope, including in a stored object.
replayScope :: ScopeAction Global -> Env.Syntax -> Env.Syntax
replayScope action syntax = updated { Env.syntaxHistory = Left action : Env.syntaxHistory syntax } where
    declare name = syntax { Env.syntaxScopes = Set.insert name (Env.syntaxScopes syntax) }
    switch (Activation enabled mode _ _ _ _) matches = syntax { Env.syntaxDisabled = foldr update (Env.syntaxDisabled syntax) changes } where
        update = if enabled then Set.delete else Set.insert
        changes = [(direction,rule) | rule <- matches, direction <- if mode == BothWays then [ParsingOnly,PrintingOnly] else [mode]]
    updated = case action of
        _ | Just (setting, matches) <- switchTargets action syntax -> switch setting matches
        BindScope name placement classes -> (declare name) { Env.syntaxBindings = foldr add (Env.syntaxBindings syntax) classes }
            where
                add = Map.alter (Just . insert . maybe ([], []) id)
                insert (top, bottom) = case placement of
                    ReplaceScopes -> ([name], [])
                    AddTop -> (name : filter (/= name) top, filter (/= name) bottom)
                    AddBottom -> (filter (/= name) top, filter (/= name) bottom ++ [name])
        DeclareCustomEntry name -> Env.declareEntry False name syntax
        DeclareScope name -> declare name
        DelimitScope name key -> (declare name) { Env.syntaxKeys = Map.insert key name (Env.syntaxKeys syntax) }
        OpenScope name -> syntax { Env.syntaxOpen = name : filter (/= name) (Env.syntaxOpen syntax) }
        UndelimitScope name -> syntax { Env.syntaxKeys = maybe id Map.delete (Env.scopeDelimiter syntax name) (Env.syntaxKeys syntax) }
        CloseScope name -> syntax { Env.syntaxOpen = filter (/= name) (Env.syntaxOpen syntax) }

resolveRule :: Env.Env -> SyntaxRule Name -> Either Diagnostic (SyntaxRule Global)
resolveRule env (SyntaxRule parts level direction target) = SyntaxRule parts level direction <$> case target of
    TermTarget name -> TermTarget <$> resolve env name
    TacticTarget tactic -> Right (TacticTarget tactic)
    RocqTarget scope names usage template -> RocqTarget scope names usage <$> traverse (resolve env) template

conflictsWithInfix :: String -> (Global, Integer, String) -> SyntaxRule Global -> Bool
conflictsWithInfix symbol (global, level, direction) rule@(SyntaxRule (TermSlot : Literal literal : _) _ _ (TermTarget _)) = literal == symbol && rule /= SyntaxRule [TermSlot, Literal symbol, TermSlot] level direction (TermTarget global)
conflictsWithInfix _ _ _ = False

infixOverlap :: String -> (Global, Integer, String) -> Env.Syntax -> Maybe (SyntaxRule Global)
infixOverlap symbol (global, level, direction) syntax = do
    let rule = SyntaxRule [TermSlot, Literal symbol, TermSlot] level direction (TermTarget global)
    previous <- Notation.overlapping rule (Env.syntaxReader syntax)
    if previous == rule then Nothing else Just previous

siteOf :: Env.Syntax -> SyntaxRule Global -> String
siteOf syntax rule = maybe "" ((" at " ++) . showSite) (Map.lookup rule (Env.syntaxRuleSites syntax))

showSite :: (String, Span) -> String
showSite (owner, Span (row, col) _) = (if null owner then "" else owner ++ ":") ++ show row ++ ":" ++ show col

-- A named target has already been resolved to a Global by its defining scope.
-- The same validation serves source declarations, object entries and imports.
installRule :: (String, Span) -> SyntaxRule Global -> Env.Syntax -> Either String Env.Syntax
installRule site rule syntax = do
    Notation.validateRule rule
    case rule of
        SyntaxRule (TermSlot : Literal symbol : _) _ _ (TermTarget _)
            | Just fixity <- Map.lookup symbol (Env.syntaxInfix syntax)
            , conflictsWithInfix symbol fixity rule -> Left ("notation at " ++ showSite site ++ " conflicts with infix " ++ quoted symbol)
        _ -> Right ()
    case rule of
        SyntaxRule parts level direction (RocqTarget scope _ use _) -> do
            let incompatible (SyntaxRule slots lev assoc _) = slots /= parts || lev /= level || assoc /= direction
                previous = Notation.production (Env.syntaxReader syntax) parts
            if use /= PrintingOnly && maybe False incompatible previous then Left "Notation already has a different grammar level, argument level or associativity." else do
                let current = maybe syntax (\name -> syntax { Env.syntaxScopes = Set.insert name (Env.syntaxScopes syntax) }) scope
                Right (Env.registerRule rule site current)
        _ -> case Notation.overlapping rule (Env.syntaxReader syntax) of
            Just previous
                | rule == previous -> Right syntax
                | otherwise -> Left ("conflicting notation at " ++ showSite site ++ siteOf syntax previous)
            Nothing -> Right (Env.registerRule rule site syntax)

projectionCount :: [Name] -> Maybe Int
projectionCount [option, value]
    | nameText option == "projection"
    , Just count <- readMaybe (nameText value) :: Maybe Integer
    , count >= 0 && count <= toInteger (maxBound :: Int) = Just (fromInteger count)
projectionCount _ = Nothing

problem :: Span -> String -> String -> Diagnostic
problem position code message = Diagnostic position "LoL-ScopeError" code message []

resolve :: Env.Env -> Name -> Either Diagnostic Global
resolve env name = maybe (Left (problem (nameSpan name) "H-Name" ("unknown name: " ++ nameText name))) Right (lookupReference (Env.envNames env) name)

reference :: Env.Env -> Span -> Global -> Either Diagnostic Term
reference _ position global = Right (Term position (SGlobal global))

-- H-Infix/H-Numeral only rearrange syntax. No Core evaluation or typing is
-- performed here. Lower levels bind more tightly, as in Gallina.
rewrite :: Env.Env -> Term -> Either Diagnostic Term
rewrite env = rewriteAt env []

-- Argument scopes in Rocq are temporary. An ordinary % delimiter stays
-- active in child expressions; %_ applies only to the immediate expression.
rewriteAt :: Env.Env -> [String] -> Term -> Either Diagnostic Term
rewriteAt env temporary = walk where
    syntax = Env.envSyntax env
    active = foldr (replayScope . OpenScope) syntax temporary
    hasPolicies = ArgScopes.hasPolicies syntax
    ordinary = rewrite env
    typeTerm = rewriteAt env (ArgScopes.classScopes env SortClass)
    walk original@(Term position form)
        | not (Map.null (Env.syntaxAliases syntax))
        , (hd,args) <- spine [] original
        , Just (key,explicit) <- abbreviationHead hd
        , Just rule@(SyntaxRule parts _ _ (RocqTarget _ vars _ tpl)) <- Map.lookup key (Env.syntaxAliases syntax)
        , Env.enabledFor syntax ParsingOnly rule = do
            let (filled, extra) = splitAt (length vars) args
            if length filled /= length vars then Left (problem position "H-Abbreviation" "Abbreviation is not applied enough.") else do
                operands <- sequence (zipWith (rewriteAt env) (ArgScopes.slotPolicies parts vars tpl) filled)
                term <- either (Left . problem position "H-Abbreviation") Right (Template.instantiate (lookupReference (Env.envNames env)) position parts vars operands tpl)
                let interpreted = case term of
                        Term at (SGlobal g) | explicit -> Term at (SExplicitGlobal g)
                        _ -> term
                ordinary (foldl application interpreted extra)
        | otherwise = case form of
        SDelimited key value -> do
            let written = nameText key
                (short, label) = case written of { '_' : rest -> (True, rest); _ -> (False, written) }
            scope <- maybe (Left (problem (nameSpan key) "H-Scope" ("Unknown scope delimiter: " ++ label))) Right (Map.lookup label (Env.syntaxKeys syntax))
            if short then rewriteAt env [scope] value else rewrite (Env.withSyntax (replayScope (OpenScope scope) syntax) env) value
        SNotation parts args -> case Env.activeInterpretation active parts of
            Just (SyntaxRule _ _ _ (RocqTarget _ names _ body)) -> do
                let instantiate operands = either (Left . problem position "H-Notation") Right (Template.instantiate (lookupReference (Env.envNames env)) position parts names operands body)
                sequence (zipWith (rewriteAt env) (ArgScopes.slotPolicies parts names body) args) >>= instantiate
            _
                | [TermSlot, Literal op, TermSlot] <- parts
                , Just (g, _, _) <- Map.lookup op (Env.syntaxInfix syntax) -> foldl application (Term position (SGlobal g)) <$> mapM ordinary args
            _ -> Left (problem position "H-Scope" "No interpretation of this notation in the open scopes.")
        SSequence items -> Term position . SSequence <$> mapM walk items
        SNumeral n -> case Env.envNumerals env of
            Nothing -> Left (problem position "H-Numeral" "a numeral needs a preceding Numerals declaration")
            Just (zero, successor)
                | n < 0 -> Left (problem position "H-Numeral" "a numeral must be nonnegative")
                | n > 100000 -> Left (Diagnostic position "LoL-KernelUndecided" "R5" "numeral expansion exceeds the raw syntax budget of 100000 constructors" [])
                | otherwise -> do
                    first <- reference env position zero
                    next <- reference env position successor
                    return (iterate (application next) first !! fromInteger n)
        SOperators first rest -> chain first rest >>= uncurry finish
        SApp {} | hasPolicies || not (Map.null (Env.syntaxAliases syntax)) -> do
            let (headTerm, args) = spine [] original
                policies = (if hasPolicies then ArgScopes.positions env headTerm else []) ++ repeat []
            fn <- ordinary headTerm
            values <- sequence (zipWith (rewriteAt env) policies args)
            return (foldl application fn values)
        SApp f x -> Term position <$> (SApp <$> ordinary f <*> ordinary x)
        SProjection value field -> do
            receiver <- walk value
            global <- resolve env field
            case Map.lookup global (Env.syntaxProjectionParameters (Env.envSyntax env)) of
                Just count -> Right (foldl (\function argument -> Term position (SApp function argument)) (Term (nameSpan field) (SDeclared field)) (replicate count (Term position SHole) ++ [receiver]))
                Nothing -> Right (Term position (SProjection receiver field))
        SMask prefix count expr -> Term position . SMask prefix count <$> walk expr
        SWithout name expr -> Term position . SWithout name <$> walk expr
        SArrow (Term _ (SOperators first rest)) body -> do
            (values, pending) <- chain first rest
            result <- walk body
            rightOperand 99 arrowTo position result values pending >>= uncurry finish
        SArrow a b -> Term position <$> (SArrow <$> typeTerm a <*> typeTerm b)
        SForall binders body -> do
            (domain, local) <- rewriteBinders env binders
            Term position . SForall domain <$> rewriteAt local (ArgScopes.classScopes local SortClass) body
        SLambda binders body -> do
            (domain, local) <- rewriteBinders env binders
            Term position . SLambda domain <$> rewrite local body
        SLet name annotation value body -> Term position <$> (letIn name <$> mapM typeTerm annotation <*> ordinary value <*> rewriteAt (ArgScopes.withoutNames env [name]) temporary body)
        SParen body -> Term position . SParen <$> walk body
        SAnnotation value annotation -> do
            typ <- typeTerm annotation
            term <- rewriteAt env (ArgScopes.expected env typ) value
            Right (Term position (SAnnotation term typ))
        SMatch subject alias family result branches -> Term position <$> (SMatch <$> walk subject <*> pure alias <*> pure family <*> mapM walk result <*> mapM branch branches)
        SFix functions chosen -> Term position . (`SFix` chosen) <$> mapM function functions
        _ -> Right original
    abbreviationHead (Term _ (SName n)) = Just (nameText n,False)
    abbreviationHead (Term _ (SExplicit n)) = Just (nameText n,True)
    abbreviationHead _ = Nothing
    spine args (Term _ (SApp f x)) = spine (x : args) f
    spine args (Term _ (SParen f)) = spine args f
    spine args headTerm = (headTerm, args)
    branch (Branch position (Pattern at explicit name items) body)
        | Just rule <- Map.lookup (nameText name) (Env.syntaxAliases syntax), Env.enabledFor syntax ParsingOnly rule = do
            let headTerm = Term (nameSpan name) (if explicit then SExplicit name else SName name)
                parameter n = Term (nameSpan n) (if nameText n == "_" then SHole else SName n)
                source = foldl application headTerm (map parameter items)
            branch (Branch position (RawPattern (source { termSpan = at })) body)
    branch (Branch position (RawPattern source) body) = do
        expanded <- walk source
        pat <- flat (termSpan source) [] expanded
        Branch position pat <$> walk body
    branch (Branch position pat body) = Branch position pat <$> walk body
    flat position args (Term at form) = case form of
        SParen value -> flat position args value
        SApp f x -> do
            name <- argument x
            flat position (name : args) f
        SHole | null args -> Right (WildPattern position)
        SGlobal g -> constructor False g
        SExplicitGlobal g -> constructor True g
        SName name -> Right (Pattern position False name args)
        SExplicit name -> Right (Pattern position True name args)
        _ -> invalid at
        where
            invalid place = Left (problem place "H-Match" "A pattern notation must expand to a flat constructor pattern.")
            argument (Term place term) = case term of
                SParen value -> argument value
                SWithout _ value -> argument value
                SHole -> Right (Name place "_")
                SName name -> Right name
                _ -> invalid place
            constructor explicit g@(GlobalCon owner _ _) = case Map.lookup owner (Env.envDecls env) of
                Just entry | label : _ <- [n | (n, found) <- Env.declGlobals owner (Env.entryName entry) (Env.entryDecl entry), found == g] ->
                    Right (Pattern position explicit (ResolvedName at label g) args)
                _ -> invalid at
            constructor _ _ = invalid at
    function (FixBody position name binders structural result body) = do
        (domain, local) <- rewriteBinders env binders
        typ <- rewriteAt local (ArgScopes.classScopes local SortClass) result
        FixBody position name domain structural typ <$> rewriteAt local (ArgScopes.expected local typ) body
    chain first rest = do
        initial <- walk first
        foldM push ([initial], []) rest
    push (values, operators') (symbol, raw)
        | nameText symbol == ":" = do
            annotation <- walk raw
            rightOperand 100 castTo (nameSpan symbol) annotation values operators'
    push (values, operators') (symbol, raw) = do
        info <- maybe (Left (problem (nameSpan symbol) "H-Infix" ("unknown operator: " ++ nameText symbol))) Right (Map.lookup (nameText symbol) (Env.envInfix env))
        argument <- walk raw
        (reduced, remaining) <- drain symbol info values operators'
        return (argument : reduced, (symbol, info) : remaining)
    -- Both -> and : take a complete term on the right. On the left, a
    -- tighter notation closes first, as does a non-right notation at the
    -- same level. Parenthesized operands have already been grouped.
    rightOperand limit build at body values ((old, info@(_, level, direction)) : rest)
        | level < limit || level == limit && direction /= "right" = reduce old info values >>= \reduced -> rightOperand limit build at body reduced rest
    rightOperand _ build _ body (value : rest) pending = Right (build value body : rest, pending)
    rightOperand _ _ at _ [] _ = Left (problem at "H-Infix" "an operator has no left operand")
    drain symbol info@(_, level, direction) values operators' = case operators' of
        (old, previous@(_, oldLevel, oldDirection)) : rest
            | oldLevel == level && (direction == "no" || oldDirection == "no" || direction /= oldDirection) -> Left (problem (nameSpan symbol) "H-Infix" "operators at this level require explicit parentheses")
            | oldLevel < level || oldLevel == level && direction == "left" -> reduce old previous values >>= \reduced -> drain symbol info reduced rest
        _ -> Right (values, operators')
    reduce symbol (global, _, _) values = case values of
        right : left : rest -> do
            head' <- reference env (nameSpan symbol) global
            return (application (application head' left) right : rest)
        _ -> Left (problem (nameSpan symbol) "H-Infix" "an operator has no operand")
    finish [value] [] = Right value
    finish values ((symbol, info) : rest) = reduce symbol info values >>= \reduced -> finish reduced rest
    finish _ [] = Left (problem (Span (1, 1) (1, 1)) "H-Infix" "an operator sequence is malformed")

rewriteBinders :: Env.Env -> [Binder] -> Either Diagnostic ([Binder], Env.Env)
rewriteBinders env [] = Right ([], env)
rewriteBinders env (binder : more) = do
    domain <- mapM (rewriteAt env (ArgScopes.classScopes env SortClass)) (binderType binder)
    (rest, local) <- rewriteBinders (ArgScopes.withoutNames env (binderVars binder)) more
    return (binder { binderType = domain } : rest, local)
