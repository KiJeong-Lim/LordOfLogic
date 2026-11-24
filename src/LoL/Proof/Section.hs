-- Discharge the checked declarations of a section. A local assumption has a
-- temporary constant ID while the section is open. On exit its occurrences
-- become de Bruijn variables and references to discharged declarations receive
-- the arguments those declarations actually used.
module LoL.Proof.Section where

import Control.Monad (foldM)
import Data.Functor.Identity (Identity (..))
import Data.List (foldl')
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import LoL.Core
import qualified LoL.Env as Env
import LoL.Hol.Session (Kernel, Limits)
import qualified LoL.Pretty as Pretty

type Variables = Map.Map ConstId (String, Bool)
type Dependencies = Map.Map ConstId [ConstId]

discharge :: Kernel -> Limits -> Env.Env -> Env.Env -> Variables -> IO (Either Env.Refusal (Env.Env, Dependencies))
discharge kernel limits before current variables = do
    built <- foldM admit (Right (before, Map.empty)) entries
    case built of
        Left failure -> return (Left failure)
        Right (next, deps) -> do
            final <- Env.selectUniverseScope (Env.activeUniverses current) (Env.reserveIdentities (Env.envFresh current) next)
            return (Right (final, deps))
    where
        entries = Map.toAscList (snd (Map.split (Env.envFresh before - 1) (Env.envDecls current)))
        admit (Left failure) _ = return (Left failure)
        admit (Right (env, deps)) (identity, entry)
            | Map.member identity variables = return (Right (env, Map.insert identity (parameters ++ [identity]) deps))
            | otherwise = do
                original <- Env.admissionView identity current
                scoped <- Env.selectUniverseScope (Env.activeUniverses original) env
                let visible = Env.withNames Map.empty (Env.reserveIdentities identity scoped)
                checked <- Env.declareWithUniverses kernel limits visible (Env.entryName entry) (Env.entryUniverses entry) declaration
                return (fmap (\(_, next) -> (next, extended)) checked)
            where
                raw = Env.entryDecl entry
                uses = Set.unions (map constantsOf (Env.declTerms raw))
                parameters = Set.toAscList (Set.fromList (concatMap (\c -> Map.findWithDefault [] c deps) (Set.toList uses)))
                extended = Map.insert identity parameters deps
                binders = [(name, replace variables extended earlier domain) | (index, c) <- zip [0 ..] parameters, let earlier = take index parameters, Just (name, _) <- [Map.lookup c variables], Just variable <- [Map.lookup c (Env.envDecls current)], Env.Axiom domain <- [Env.entryDecl variable]]
                close wrap item = foldr (uncurry wrap) (replace variables extended parameters item) binders
                declaration = case raw of
                    Env.Axiom typ -> Env.Axiom (close Pi typ)
                    Env.Definition typ value -> Env.Definition (close Pi typ) (close Lam value)
                    Env.Theorem typ value -> Env.Theorem (close Pi typ) (close Lam value)
                    Env.Inductive count families -> Env.Inductive (count + length parameters) (map family families)
                family item = item { Env.familyType = close Pi (Env.familyType item), Env.familyCons = [(label, close Pi typ) | (label, typ) <- Env.familyCons item] }

-- Ordinary global heads gain leading section arguments; a case stores these
-- in its parameter vector. A primitive projection already carries its receiver.
replace :: Variables -> Dependencies -> [ConstId] -> Term -> Term
replace variables deps parameters = visit 0 where
    indices = Map.fromList (zip (reverse parameters) [0 ..])
    arguments depth c = [Var (depth + i) | variable <- Map.findWithDefault [] c deps, Just i <- [Map.lookup variable indices]]
    visit depth term = case term of
        Cst c _ | Map.member c variables, Just i <- Map.lookup c indices -> Var (depth + i)
        Cst c _ -> apps term (arguments depth c)
        Ind c _ _ -> apps term (arguments depth c)
        Con c _ _ _ -> apps term (arguments depth c)
        PField c _ _ -> apps term (arguments depth c)
        Case c i us qs ns predicate subject branches ->
            Case c i us (arguments depth c ++ map (visit depth) qs) ns (visit (depth + length ns) predicate) (visit depth subject) [(names, visit (depth + length names) body) | (names, body) <- branches]
        _ -> runIdentity (descend (\n t -> Identity (visit n t)) depth term)

-- Arguments from the discharged context precede the declaration's own
-- arguments, including the parameter telescope of a projection.
dischargedSyntax :: Variables -> Dependencies -> Env.Env -> Env.Syntax -> Env.Syntax -> Env.Syntax
dischargedSyntax variables deps env source restored = foldl' adjust restored additions where
    additions = [(global, params) | (c, params) <- Map.toList deps, Map.notMember c variables, Just entry <- [Map.lookup c (Env.envDecls env)], (_, global) <- Env.declGlobals c (Env.entryName entry) (Env.entryDecl entry)]
    adjust syntax (global, params) = syntax
        { Env.syntaxArguments = if or flags || Map.member global (Env.syntaxArguments source) then Map.insert global flags (Env.syntaxArguments syntax) else Env.syntaxArguments syntax
        , Env.syntaxArgScopes = maybe id (Map.insert global . (replicate (length params) [] ++)) (Map.lookup global (Env.syntaxArgScopes source)) (Env.syntaxArgScopes syntax)
        , Env.syntaxArgPrefixes = if Map.member global (Env.syntaxArgScopes source) && prefix > 0 then Map.insert global prefix (Env.syntaxArgPrefixes syntax) else Env.syntaxArgPrefixes syntax
        , Env.syntaxProjectionParameters = maybe id (Map.insert global . (+ length params)) (Map.lookup global (Env.syntaxProjectionParameters source)) (Env.syntaxProjectionParameters syntax)
        , Env.syntaxNever = if Set.member global (Env.syntaxNever source) then Set.insert global (Env.syntaxNever syntax) else Env.syntaxNever syntax
        }
        where
            prefix = length params + Map.findWithDefault 0 global (Env.syntaxArgPrefixes source)
            flags = [implicit | c <- params, Just (_, implicit) <- [Map.lookup c variables]] ++ Map.findWithDefault [] global (Env.syntaxArguments source)

-- An ordinary Arguments command freezes every position, including a leading
-- position written without a scope. Recreate the enclosing sections when a
-- declaration inherited an automatic prefix on discharge. The identities
-- below exist only in the printer's name table.
explicit :: (Env.Env -> ConstId -> Env.Entry -> Either String String) -> Env.Env -> ConstId -> Env.Entry -> Map.Map Global (Int, [Bool], [[String]]) -> Either String String
explicit printer env owner entry policies
    | null relevant = printer env owner entry
    | otherwise = do
        signature <- case Env.declTypes declaration of
            a : _ -> Right a
            [] -> Left "a discharged declaration has no type"
        binders <- domains 0 signature
        opened <- reopen declaration
        rendered <- printer temporary owner entry { Env.entryDecl = opened }
        Right (unlines (nest 0 stages binders rendered))
    where
        declaration = Env.entryDecl entry
        relevant = [(label, n, flags, scopes) | (label, g) <- Env.declGlobals owner (Env.entryName entry) declaration, Just (n, flags, scopes) <- [Map.lookup g policies]]
        stages = Set.toAscList (Set.fromList [n | (_, n, _, _) <- relevant])
        width = last stages
        supplied = head [flags | (_, n, flags, _) <- relevant, n == width]
        fresh = take width [name | i <- [0 :: Int ..], let name = "section_arg" ++ show i, not (Pretty.namingBanned (Pretty.naming env) name)]
        temporary = Env.withNames (Map.union (Map.fromList (zip fresh [GlobalCst (negate i - 1) | i <- [0..]])) (Env.envNames env)) env
        stand i = Cst (negate (toInteger i) - 1) []
        domains i _ | i == width = Right []
        domains i (Pi _ ty tail) = do
            shown <- Pretty.termWithUniverses temporary (Env.entryUniverses entry) (open i 0 ty)
            let implicit = (supplied ++ repeat False) !! i
                binder = (if implicit then "{" else "(") ++ fresh !! i ++ " : " ++ shown ++ (if implicit then "}" else ")")
            (("Context " ++ binder ++ ".") :) <$> domains (i + 1) tail
        domains _ _ = Left "discharged scope prefix exceeds the declaration telescope"
        nest _ [] _ text = [text]
        nest prior (n : more) binders text = ["Section " ++ section ++ "."] ++ here ++ nest n more later text ++ settings ++ ["End " ++ section ++ "."] where
            section = "LoLArgumentScopes" ++ show n
            (here, later) = splitAt (n - prior) binders
            settings = [arguments label (drop n flags) (drop n scopes) | (label, count, flags, scopes) <- relevant, count == n]
        arguments name flags scopes = unwords ("Global" : "Arguments" : name : slots) ++ suffix ++ "." where
            decorate (i, implicit) sc = (if implicit then "{" ++ v ++ "}" else v) ++ concatMap ("%_" ++) sc where v = "x" ++ show i
            slots = take (max (length flags) (length scopes)) (zipWith decorate (zip [0 :: Int ..] (flags ++ repeat False)) (scopes ++ repeat []))
            suffix
                | all null scopes = " : clear scopes"
                | length scopes > length flags = " : extra scopes"
                | otherwise = ""
        reopen d = case d of
            Env.Axiom a -> Env.Axiom <$> strip True width a
            Env.Definition a t -> Env.Definition <$> strip True width a <*> strip False width t
            Env.Theorem a t -> Env.Theorem <$> strip True width a <*> strip False width t
            Env.Inductive count families
                | count >= width -> Env.Inductive (count - width) <$> mapM family families
                | otherwise -> Left "discharged scope prefix exceeds the inductive parameters"
        family f = do
            typ <- strip True width (Env.familyType f)
            cs <- mapM (\(name, a) -> (,) name <$> strip True width a) (Env.familyCons f)
            Right f { Env.familyType = typ, Env.familyCons = cs }
        strip _ 0 t = Right (open width 0 t)
        strip True n (Pi _ _ t) = strip True (n - 1) t
        strip False n (Lam _ _ t) = strip False (n - 1) t
        strip _ _ _ = Left "discharged scope prefix does not match the stored declaration"
        open count depth term = case term of
            Var i | i >= depth, i - depth < count -> stand (count - 1 - (i - depth))
            App {} | (h, xs) <- spine [] term, isSelf h -> apps h (map (open count depth) (drop count xs))
            Case c i us ps ns motive subject branches | c == owner ->
                Case c i us (map (open count depth) (drop count ps)) ns (open count (depth + length ns) motive) (open count depth subject) [(vs, open count (depth + length vs) body) | (vs, body) <- branches]
            _ -> runIdentity (descend (\k t -> Identity (open count k t)) depth term)
        spine xs (App f x) = spine (x : xs) f
        spine xs t = (t, xs)
        isSelf (Ind c _ _) = c == owner
        isSelf (Con c _ _ _) = c == owner
        isSelf (PField c _ _) = c == owner
        isSelf _ = False
