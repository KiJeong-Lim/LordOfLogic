module LoL.Front.Fixity where

import Control.Monad (foldM)
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import LoL.Core (Global (..))
import LoL.Diagnostic
import qualified LoL.Env as Env
import qualified LoL.Front.Notation as Notation
import LoL.Front.Parse (lexSource)
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
                    | otherwise -> Left (problem position "H-Arguments" "Arguments lists more positions than the constant's type has")
    (result, _) -> return result

-- Metadata is a surface instruction, never evidence that a term is typed.
-- In particular Numerals does not give its two names a privileged Core type.
configure :: Env.Env -> Command -> Either Diagnostic Env.Env
configure env command = case command of
    CArguments position name arguments options -> do
        global <- resolve env name
        let flags = [implicit | ArgSpec _ implicit _ <- arguments]
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
            ["projection", _]
                | GlobalCst {} <- global, Just _ <- projectionCount options -> Right previous
            ["simpl", "never"]
                | acceptsSimpl -> Right (Set.insert global previous)
            ["clear", "simpl"]
                | acceptsSimpl -> Right (Set.delete global previous)
            _ -> Left (problem position "H-Arguments" "Expected simpl never or clear simpl on a constant or projection")
        return (Env.withSyntax syntax { Env.syntaxArguments = masks, Env.syntaxNever = never, Env.syntaxProjectionParameters = registered } env)
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
            direction <- maybe (Left (problem position "H-Infix" "an infix declaration must specify left, right, or no associativity")) (Right . nameText) association
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

resolveRule :: Env.Env -> SyntaxRule Name -> Either Diagnostic (SyntaxRule Global)
resolveRule env (SyntaxRule parts level direction target) = SyntaxRule parts level direction <$> case target of
    TermTarget name -> TermTarget <$> resolve env name
    TacticTarget tactic -> Right (TacticTarget tactic)

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
    case Notation.overlapping rule (Env.syntaxReader syntax) of
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
resolve env name = maybe (Left (problem (nameSpan name) "H-Name" ("unknown name: " ++ nameText name))) Right (Map.lookup (nameText name) (Env.envNames env))

reference :: Env.Env -> Span -> Global -> Either Diagnostic Term
reference _ position global = Right (Term position (SGlobal global))

-- H-Infix/H-Numeral only rearrange syntax. No Core evaluation or typing is
-- performed here. Lower levels bind more tightly, as in Gallina.
rewrite :: Env.Env -> Term -> Either Diagnostic Term
rewrite env = walk where
    walk original@(Term position form) = case form of
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
        SApp f x -> Term position <$> (SApp <$> walk f <*> walk x)
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
        SArrow a b -> Term position <$> (SArrow <$> walk a <*> walk b)
        SForall binders body -> Term position <$> (SForall <$> mapM binder binders <*> walk body)
        SLambda binders body -> Term position <$> (SLambda <$> mapM binder binders <*> walk body)
        SLet name annotation value body -> Term position <$> (letIn name <$> mapM walk annotation <*> walk value <*> walk body)
        SParen body -> Term position . SParen <$> walk body
        SAnnotation value annotation -> Term position <$> (SAnnotation <$> walk value <*> walk annotation)
        SMatch subject alias family result branches -> Term position <$> (SMatch <$> walk subject <*> pure alias <*> pure family <*> mapM walk result <*> mapM branch branches)
        SFix functions chosen -> Term position . (`SFix` chosen) <$> mapM function functions
        _ -> Right original
    binder value = do
        annotation <- mapM walk (binderType value)
        return value { binderType = annotation }
    branch (Branch position pattern' body) = Branch position pattern' <$> walk body
    function (FixBody position name binders structural result body) = FixBody position name <$> mapM binder binders <*> pure structural <*> walk result <*> walk body
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
