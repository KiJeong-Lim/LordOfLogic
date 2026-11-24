module LoL.Front.Search where

import Data.Functor.Const (Const (..))
import Data.Functor.Identity (Identity (..))
import qualified Data.IntMap.Strict as IntMap
import Data.List (isInfixOf, isPrefixOf, sortOn)
import qualified Data.Map.Strict as Map
import qualified Data.Map.Lazy as Lazy
import qualified Data.Set as Set
import qualified LoL.Core as Core
import LoL.Diagnostic
import qualified LoL.Env as Env
import qualified LoL.Front.ArgumentScopes as ArgScopes
import qualified LoL.Front.Fixity as Fixity
import qualified LoL.Front.Scope as Scope
import LoL.Front.Syntax
import qualified LoL.Hol.Elab as Elab
import LoL.Hol.Session (Kernel, Limits)
import qualified LoL.Pretty as Pretty

-- Both arguments are syntax from admitted signatures. In particular this
-- matcher never infers a type or unfolds a definition. Bound occurrences
-- in the pattern stay bound; its free proof locals are lifted only by the
-- binders surrounding the candidate occurrence.
contains :: Core.Term -> Core.Term -> Bool
contains patternTerm = visit 0 where
    visit depth term = match depth 0 patternTerm term || any (uncurry visit) (children depth term)
    match outside bound p t = case (p, t) of
        (Core.Hole 0, _) -> True
        (Core.Hole 1, Core.Type _) -> True
        (Core.Var i, Core.Var j) -> (if i < bound then i else i + outside) == j
        (Core.Cst i [], Core.Cst j _) -> i == j
        (Core.Ind b i [], Core.Ind c j _) -> b == c && i == j
        (Core.Con b i j [], Core.Con c k l _) -> (b, i, j) == (c, k, l)
        (Core.PField b i [], Core.PField c j _) -> b == c && i == j
        (Core.PField b i [], Core.Proj c j _) -> b == c && i == j
        (Core.App (Core.PField b i []) r, Core.Proj c j s) -> b == c && i == j && match outside bound r s
        _ -> shape p == shape t && and (zipWith (\(below, sub) (_, target) -> match outside below sub target) (children bound p) (children bound t))
    shape = runIdentity . Core.descend (\_ _ -> Identity Core.Prop) 0
    children depth = getConst . Core.descend (\below sub -> Const [(below, sub)]) depth

type Locals = [(String, Maybe Core.Term)]

search :: (Env.Refusal -> Diagnostic) -> Kernel -> Limits -> Env.Env -> Env.Env -> Core.UniverseContext -> Locals -> Span -> [(Bool, SearchItem)] -> SearchScope -> IO (Either Diagnostic [String])
search refused kernel limits env display universes locals position items scope = case traverse compile items of
    Left failure -> return (Left failure)
    Right tests -> do
        let namesMatch name = all (\(positive, fragment) -> (fragment `isInfixOf` baseName name) == positive) nameTests
            typesMatch typ = all (\(positive, pat) -> contains pat typ == positive) [(p, t) | (p, Just t) <- tests]
            localResults = sequence [line name (renderLocal typ) | (name, Just typ) <- locals, included name, namesMatch name, typesMatch typ]
            globals = [(name, g) | (g, name) <- Map.toList visible, included name, namesMatch name]
        case localResults of
            Left failure -> return (Left failure)
            Right results -> collect typesMatch (reverse results) (sortOn fst globals)
    where
        aliases = map fst locals
        nameTests = [(p, string) | (p, SearchName string) <- items]
        compile (positive, SearchTerm source) = do
            expanded <- Fixity.rewrite (ArgScopes.withoutNames env [Name position n | n <- aliases]) source
            parsed <- Scope.translateSyntax (Just (Env.envArguments env)) (`Set.member` Env.envAmbiguous env) aliases (Env.envNames env) (Env.envDecls env) expanded
            return (positive, Just (Scope.placedTerm parsed))
        compile (positive, SearchName _) = Right (positive, Nothing)
        baseName = reverse . takeWhile (/= '.') . reverse
        included name = case scope of
            Everywhere -> True
            Inside owners -> any (owns name) owners
            Outside owners -> not (any (owns name) owners)
        owns name owner = (nameText owner ++ ".") `isPrefixOf` name
        -- Scope contains both qualified names and unambiguous abbreviations.
        -- The richer display environment also contains indirect dependencies;
        -- searching that environment would disclose out-of-scope candidates.
        visible = Map.fromListWith qualified [(g, name) | (name, g) <- Map.toList (Env.envNames env)]
        qualified a b
            | '.' `elem` a = a
            | otherwise = b
        failed message = Diagnostic position "LoL-SearchError" "H-Search" message []
        line name rendered = either (Left . failed) (Right . ((name ++ " : ") ++)) rendered
        localNames = Pretty.naming (Env.withNames (foldr Map.delete (Env.envNames display) aliases) display)
        naming = localNames { Pretty.namingUniverses = Pretty.universeHints localNames (Core.universeNames universes) }
        printer = Pretty.displayPrinter display naming
        bindings = Pretty.Names (IntMap.fromList (zip [0 ..] (reverse aliases))) (Set.fromList aliases) Map.empty
        renderLocal term = case Pretty.printerFail printer (length aliases) term of
            Just failure -> Left failure
            Nothing -> Right (Pretty.pieceText (Pretty.printerShow printer (length aliases) bindings term) "")
        collect _ results [] = return (Right (reverse results))
        collect matches results ((name, g) : rest) = do
            one <- signature g
            case one of
                Left failure -> return (Left failure)
                Right (context, typ)
                    | matches typ -> case line name (Pretty.displayTermWithUniverses display context typ) of
                        Left failure -> return (Left failure)
                        Right rendered -> collect matches (rendered : results) rest
                    | otherwise -> collect matches results rest
        signature g = case Map.lookup (Elab.globalOwner g) (Env.envDecls env) of
            Nothing -> return (Left (failed "The visible declaration has no stored type."))
            Just entry -> do
                let context = Env.entryUniverses entry
                case g of
                    -- Dependent field signatures are computed by the kernel.
                    Core.GlobalProj {} -> do
                        let levels = map Core.Parameter [0 .. length (Core.universeNames context) - 1]
                        scoped <- Env.admissionView (Elab.globalOwner g) env
                        answer <- Env.typeOfTermWithUniverses kernel limits scoped context (Core.fromGlobalAt levels g)
                        return (either (Left . refused) (Right . (,) context) answer)
                    _ -> return (maybe (Left (failed "The visible declaration has no stored type.")) (Right . (,) context) (Map.lookup (Elab.globalOwner g) ownerTypes >>= Map.lookup g))
        ownerTypes = Lazy.mapWithKey storedTypes (Env.envDecls env)
        storedTypes owner entry = Map.fromList (zip [found | (_, found) <- Env.declGlobals owner (Env.entryName entry) declaration, hasStoredType found] (Env.declTypes declaration)) where
            declaration = Env.entryDecl entry
        hasStoredType Core.GlobalProj {} = False
        hasStoredType _ = True
