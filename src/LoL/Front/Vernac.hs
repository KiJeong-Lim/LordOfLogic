module LoL.Front.Vernac where

import Control.Monad (foldM)
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import qualified LoL.Core as Core
import LoL.Diagnostic
import qualified LoL.Env as Env
import qualified LoL.Front.ArgumentScopes as ArgScopes
import qualified LoL.Front.Fixity as Fixity
import qualified LoL.Front.Search as Search
import qualified LoL.Hol.Elab as Elab
import LoL.Front.Scope
import LoL.Front.Syntax
import LoL.Hol.Embed (Report (..), embedTerm, indTypeFact, named, natural, terms)
import Hol.V2.Embedding (foldlNApp)
import LoL.Hol.Session (Kernel, Limits, Verdict (..), kernelElaborator)
import LoL.Oracle (spine, substitute)
import qualified LoL.Pretty as Pretty

-- The declarations that a command asks for, in order, each by rewriting of
-- syntax alone. A command that declares nothing has none.
declarations :: Env.Env -> Command -> [(String, Either Diagnostic Env.Decl)]
declarations env command = case command of
    CDefinition position kind name binders annotation body -> [(nameText name, (if kind == "Definition" then Env.Definition else Env.Theorem) <$> translated (Term position (SForall binders annotation)) <*> translated (Term position (SLambda binders body)))]
    CAxiom _ name annotation -> [(nameText name, Env.Axiom <$> translated annotation)]
    CInductive _ bodies -> [(concat (take 1 [nameText name | IndBody _ name _ _ _ <- bodies]), inductive bodies)]
    -- [H-Fixpoint]: one definition for each function, each a `fix` over the block.
    CFixpoint position bodies -> [(nameText name, translated (Term position (SFix bodies (Just name))) >>= definition position index) | (index, FixBody _ name _ _ _ _) <- zip [0 ..] bodies]
    _ -> []
    where
        translated = fmap placedTerm . translateUnder (`Set.member` Env.envAmbiguous env) [] (Env.envNames env) (Env.envDecls env)
        definition position index whole = case whole of
            Core.Fix _ functions -> Right (Env.Definition (Core.functionType (functions !! index)) (Core.Fix index functions))
            _ -> Left (unsupported position "Fixpoint")
        -- The parameters of a block are the binders of its first family. The
        -- type of a family and the types of its constructors are closed over
        -- the binders of that family; the kernel compares them ([I-Params]).
        -- The names of the families are in scope in the types of the
        -- constructors only, after the binders: a binder is read outside the
        -- block, as in the type of its family.
        inductive bodies = do
            let block = Env.envFresh env
                families = Map.fromList [(nameText name, Core.GlobalInd block index) | (index, IndBody _ name _ _ _) <- zip [0 ..] bodies]
                within binders = fmap placedTerm . translateUnder (`Set.member` Env.envAmbiguous env) (reverse [if nameText variable == "_" then "" else nameText variable | binder <- binders, variable <- binderVars binder]) (Map.union families (Env.envNames env)) (Env.envDecls env)
                under telescope body = case telescope of
                    Core.Pi hint domain rest -> Core.Pi hint domain (under rest body)
                    _ -> body
                constructor binders (Constructor place given signature) = (\telescope body -> (nameText given, under telescope body)) <$> translated (Term place (SForall binders (Term place SProp))) <*> within binders signature
            translatedFamilies <- mapM (\(IndBody at name binders arity constructors) -> Env.Family (nameText name) <$> translated (Term at (SForall binders arity)) <*> mapM (constructor binders) constructors) bodies
            return (Env.Inductive (sum [length (binderVars binder) | IndBody _ _ binders _ _ <- take 1 bodies, binder <- binders]) translatedFamilies)

-- How a declaration that a command asks for is given to the kernel.
type Declare = Kernel -> Limits -> Env.Env -> String -> Core.UniverseContext -> Env.Decl -> IO (Either Env.Refusal (Core.ConstId, Env.Env))

execute :: Kernel -> Limits -> Env.Env -> Command -> IO (Either Diagnostic (Env.Env, [String]))
execute = executeWith Env.declareWithUniverses

executeWith :: Declare -> Kernel -> Limits -> Env.Env -> Command -> IO (Either Diagnostic (Env.Env, [String]))
executeWith = executeWithDisplay id

-- Display names may include dependencies that are deliberately out of scope.
-- They are used only by renderers, never by rewriting or admission.
executeWithDisplay :: (Env.Env -> Env.Env) -> Declare -> Kernel -> Limits -> Env.Env -> Command -> IO (Either Diagnostic (Env.Env, [String]))
executeWithDisplay forDisplay declare kernel limits env (CWhere at inner interpretations) = case owners inner of
    [] -> return (Left (Diagnostic at "LoL-ScopeError" "H-Notation" "A where notation requires an inductive or a fixpoint." []))
    members -> do
        let prepare = foldM (Fixity.configureBlock (Set.fromList members)) env interpretations
        case prepare >>= flip rewriteCommand inner of
            Left failure -> return (Left failure)
            Right checkedSyntax -> do
                admitted <- executePreparedWithDisplay forDisplay declare kernel limits env checkedSyntax
                return $ do
                    (next, messages) <- admitted
                    final <- foldM Fixity.configure next interpretations
                    Right (final, messages)
    where
        owners (CInductive _ fs) = concat [nameText n : [nameText c | Constructor _ c _ <- cs] | IndBody _ n _ _ cs <- fs]
        owners (CFixpoint _ fs) = [nameText n | FixBody _ n _ _ _ _ <- fs]
        owners (CUniverses _ _ inner') = owners inner'
        owners (CTemplate _ inner') = owners inner'
        owners _ = []
executeWithDisplay forDisplay declare kernel limits env written = case rewriteCommand env written of
    Left problem -> return (Left problem)
    Right command -> executePreparedWithDisplay forDisplay declare kernel limits env command

executePrepared :: Declare -> Kernel -> Limits -> Env.Env -> Command -> IO (Either Diagnostic (Env.Env, [String]))
executePrepared = executePreparedWithDisplay id

executePreparedWithDisplay :: (Env.Env -> Env.Env) -> Declare -> Kernel -> Limits -> Env.Env -> Command -> IO (Either Diagnostic (Env.Env, [String]))
executePreparedWithDisplay = executePreparedMode False

executePreparedMode :: Bool -> (Env.Env -> Env.Env) -> Declare -> Kernel -> Limits -> Env.Env -> Command -> IO (Either Diagnostic (Env.Env, [String]))
executePreparedMode elaborate forDisplay declare kernel limits env command = case command of
    CRecordDefinitions _ nonrecursive record definitions -> do
        let fields = [length assumed | RecordDefinition _ _ assumed _ <- definitions]
            define = if nonrecursive then checkRecordFields fields declare else declare
        result <- executePreparedWithDisplay forDisplay define kernel limits env record
        let generated before after = Map.fromList [(given, global) | identity <- [Env.envFresh before .. Env.envFresh after - 1], Just entry <- [Map.lookup identity (Env.envDecls after)], (given, global) <- Env.declGlobals identity (Env.entryName entry) (Env.entryDecl entry)]
            admitField (Left problem) _ = return (Left problem)
            admitField (Right (current, _)) (RecordDefinition accessor original assumed locals) = do
                let owned = generated env current
                    previous = [Map.lookup (nameText field) owned | field <- assumed]
                    hidden = Map.mapKeys (nameText . recordAlias . Name position) owned
                    family = Map.filter isFamily owned
                    isFamily (Core.GlobalInd _ _) = True
                    isFamily _ = False
                    lexical = Env.withNames (Map.unions [hidden, family, Env.envNames env]) current
                    published (next, output) = (Env.withNames (Map.union (generated current next) (Env.envNames current)) next, output)
                    required = any (== Nothing) previous
                case rewriteCommand lexical (if required then original else accessor) of
                    Left failure -> return (Left failure)
                    Right prepared
                        | required -> fmap (fmap published) (computedInRecord lexical previous locals Nothing prepared)
                    Right prepared -> fmap (fmap published) (computed lexical Nothing prepared)
        done <- foldM admitField result definitions
        let fieldNames next = [name | RecordDefinition accessor _ _ _ <- definitions, name <- definitionNames accessor, Map.member (nameText name) (generated env next)]
        return (fmap (\(next, output) -> (fieldArguments next (fieldNames next) record, output)) done)
    CPrimitive _ eta fields inner -> do
        let primitive engine budget current name universes declaration = case declaration of
                Env.Inductive count [family] -> declare engine budget current name universes (Env.Inductive count [family { Env.familyRecord = Just (Env.RecordInfo eta (map nameText fields)) }])
                _ -> return (Left Env.NotClosed)
        result <- executePreparedWithDisplay forDisplay primitive kernel limits env inner
        return (fmap (\(next, output) -> (fieldArguments next fields inner, output)) result)
    COrdinaryRecord _ fields inner -> do
        result <- executePreparedWithDisplay forDisplay declare kernel limits env inner
        case result of
            Left failure -> return (Left failure)
            Right (next, _) -> case Map.lookup (Env.envFresh env) (Env.envDecls next) of
                Just entry@(Env.Entry { Env.entryDecl = Env.Inductive count [family] })
                    | [(_, signature)] <- Env.familyCons family -> do
                        let universes = Env.entryUniverses entry
                            definitions = ordinaryFields (Env.envFresh env) count universes fields signature
                            install current previous [] = return (Right (fieldArguments current [name | ((name, _), Just _) <- zip fields (reverse previous)] inner, []))
                            install current previous ((name, projection) : rest) = case projection previous of
                                Nothing -> install current (Nothing : previous) rest
                                Just declaration -> do
                                    checked <- declare kernel limits current name universes declaration
                                    case checked of
                                        Left (Env.KernelRejected (Just report))
                                            | reportRule report == "I-Elim-Prop" -> install current (Nothing : previous) rest
                                        Left failure -> return (Left (refusalIn (forDisplay current) position failure))
                                        Right (identity, done) -> install done (Just identity : previous) rest
                        install next [] definitions
                _ -> return (Left (unsupported position "a malformed record declaration"))
    CTemplate at inner
        | templateDeclaration inner -> executePreparedWithDisplay forDisplay (markTemplate (recordFloor inner)) kernel limits env inner
        | otherwise -> return (Left (unsupported at "template universes require an inductive declaration"))
    CUniverses _ written inner -> case traverse (Elab.universeRequest env) written of
        Left failure -> return (Left failure)
        Right context -> universeCommand context inner
    CDefinition at kind name binders annotation body
        | any (Elab.needsUniverses env) [Term at (SForall binders annotation), Term at (SLambda binders body)] -> universeCommand Nothing command
        | let signature = Term at (SForall binders annotation), let term = Term at (SLambda binders body), needsProposal signature || needsProposal term -> do
            proposed <- Elab.proposeDisplaying forDisplay kernel limits env (Just signature) term
            either (return . Left) (\(value, typ) -> admit env [(nameText name, Right ((if kind == "Definition" then Env.Definition else Env.Theorem) typ value))]) proposed
        | otherwise -> tryProposal (admit env (declarations env command))
    CAxiom _ name annotation
        | Elab.needsUniverses env annotation -> universeCommand Nothing command
        | needsProposal annotation -> do
            proposed <- Elab.proposeDisplaying forDisplay kernel limits env Nothing annotation
            either (return . Left) (\(typ, _) -> admit env [(nameText name, Right (Env.Axiom typ))]) proposed
        | otherwise -> tryProposal (admit env (declarations env command))
    CInductive _ bodies
        | any universeInductive bodies -> universeCommand Nothing command
        | elaborate || any indNeeded bodies -> inductiveProposal bodies >>= either (return . Left) (\decl -> admit env [(concat (take 1 [nameText name | IndBody _ name _ _ _ <- bodies]), Right decl)])
        | otherwise -> tryProposal (admit env (declarations env command))
    CFixpoint at bodies
        | Elab.needsUniverses env (Term at (SFix bodies Nothing)) -> universeCommand Nothing command
        | let source = Term at (SFix bodies (firstFixName bodies)), needsProposal source -> do
            proposed <- Elab.proposeFixpointDisplaying forDisplay kernel limits env source
            case proposed of
                Left failure -> return (Left failure)
                Right (Core.Fix _ proposedFunctions, _) -> do
                    let names = [nameText name | FixBody _ name _ _ _ _ <- bodies]
                    admit env [(name, Right (Env.Definition (Core.functionType function) (Core.Fix index proposedFunctions))) | (index, (name, function)) <- zip [0 ..] (zip names proposedFunctions)]
                _ -> return (Left (unsupported at "malformed elaborated fix"))
        | otherwise -> tryProposal (admit env (declarations env command))
    CArguments {} -> fmap (fmap (\next -> (next, []))) (Fixity.configureWith kernel limits env command)
    CSelectNotation {} -> return ((\next -> (next, [])) <$> Fixity.configure env command)
    CScope {} -> return ((\next -> (next, [])) <$> Fixity.configure env command)
    CRocqNotation {} -> return ((\next -> (next, [])) <$> Fixity.configure env command)
    CNotation {} -> return ((\next -> (next, [])) <$> Fixity.configure env command)
    CInfix {} -> return ((\next -> (next, [])) <$> Fixity.configure env command)
    CNumerals {} -> return ((\next -> (next, [])) <$> Fixity.configure env command)
    CCheck _ source -> query Env.shownType Env.shownTypeWithUniverses source
    CCompute _ source -> query Env.normalForm Env.normalFormWithUniverses source
    CSearch at items scope -> fmap (fmap ((,) env)) (Search.search (refusalIn (forDisplay env) at) kernel limits env (forDisplay env) Core.emptyUniverses [] at items scope)
    CPrint _ name -> printed ((: []) <$> named name)
    CPrintAssumptions _ name -> fmap (fmap (\(_, rendered) -> (env, if null rendered then ["(* No assumptions. *)"] else rendered))) (printed ((\(constant, _) -> [(assumed, entry) | assumed <- Set.toAscList (Env.assumptions env constant), Just entry <- [Map.lookup assumed (Env.envDecls env)]]) <$> named name))
    _ -> return (Left (unsupported position (commandKind command)))
    where
        needsProposal source = elaborate || Elab.needsGroundElaborator kernel env source
        -- An explicit term gets the direct Core judgment first. On a failed
        -- conversion a surface elaborator can construct an actual eta adapter.
        -- Core-only replay and the C-Pi rule always check the original term.
        tryProposal ground = do
            original <- ground
            case original of
                Left diagnostic
                    | diagnosticCode diagnostic == "T-Conv"
                    , Just _ <- kernelElaborator kernel -> do
                        proposed <- executePreparedMode True forDisplay declare kernel limits env command
                        case proposed of
                            Left problem
                                | diagnosticCode problem /= "R5" -> return original
                            _ -> return proposed
                _ -> return original
        templateDeclaration CInductive {} = True
        templateDeclaration (CPrimitive _ _ _ inner) = templateDeclaration inner
        templateDeclaration (COrdinaryRecord _ _ inner) = templateDeclaration inner
        templateDeclaration (CUniverses _ _ inner) = templateDeclaration inner
        templateDeclaration _ = False
        -- Record syntax in Gallina retains Set in the minimum arity when
        -- the author writes a symbolic result sort. A bare Type leaves the
        -- minimum to the fields. The Core maximum preserves this difference
        -- through the ordinary template judgment and object replay.
        recordFloor (CPrimitive _ _ _ block) = writtenSort block
        recordFloor (COrdinaryRecord _ _ block) = writtenSort block
        recordFloor _ = False
        writtenSort (CUniverses _ _ block) = writtenSort block
        writtenSort (CInductive _ [IndBody _ _ _ arity _]) = symbolic arity
        writtenSort _ = False
        symbolic (Term _ (SParen inner)) = symbolic inner
        symbolic (Term _ (SUniverse _)) = True
        symbolic _ = False
        floorSort (Core.Pi hint domain body) = Core.Pi hint domain (floorSort body)
        floorSort typ@(Core.Type level)
            | not (Set.null (Core.levelParameters level)) = Core.Type (Core.Maximum (Core.Closed 0) level)
            | otherwise = typ
        floorSort typ = typ
        markTemplate bounded session budget current name context declared = declare session budget current name context $ case declared of
            Env.Inductive count families -> Env.Inductive count [family { Env.familyTemplate = True, Env.familyType = if bounded then floorSort (Env.familyType family) else Env.familyType family } | family <- families]
            _ -> declared
        computed current explicit definition = case definition of
            CUniverses _ context inner@(CDefinition _ _ _ _ (Term _ SHole) _) -> case traverse (Elab.universeRequest current) context of
                Left failure -> return (Left failure)
                Right requested -> computed current requested inner
            CDefinition at _ name binders (Term _ SHole) body -> do
                let term = Term at (SLambda binders body)
                proposed <- Elab.proposeUniversesDisplaying forDisplay kernel limits current explicit Nothing term
                case proposed of
                    Left failure -> return (Left failure)
                    Right result -> do
                        accepted <- declare kernel limits current (nameText name) (Elab.proposedUniverses result) (Env.Definition (Elab.proposedType result) (Elab.proposedTerm result))
                        return (either (Left . refusalIn (forDisplay current) at) (\(_, next) -> Right (implicitMetadata next definition, [])) accepted)
            _ -> executePreparedWithDisplay forDisplay declare kernel limits current definition
        computedInRecord current previous locals explicit definition = case definition of
            CUniverses _ context inner -> case traverse (Elab.universeRequest current) context of
                Left failure -> return (Left failure)
                Right requested -> computedInRecord current previous locals requested inner
            CDefinition at _ name binders annotation body -> do
                let expected = case termForm annotation of
                        SHole -> Nothing
                        _ -> Just (Term at (SForall binders annotation))
                    parameters = sum (map (length . binderVars) binders) - length previous - 1
                proposed <- Elab.proposeUniversesDisplaying forDisplay kernel limits current explicit expected (Term at (SLambda binders body))
                checked <- case proposed of
                    Left failure -> return (Left failure)
                    Right result -> do
                        let cast = Core.Cast (Elab.proposedTerm result) (Elab.proposedType result)
                        typed <- Env.typeOfTermWithUniverses kernel limits current (Elab.proposedUniverses result) cast
                        return (either (Left . refusalIn (forDisplay current) at) (const (Right result)) typed)
                case checked >>= computedProjection at parameters previous locals of
                    Left failure -> return (Left failure)
                    Right Nothing -> return (Right (current, []))
                    Right (Just (universes, projection)) -> do
                        checked <- declare kernel limits current (nameText name) universes projection
                        return (either (Left . refusalIn (forDisplay current) at) (\(_, next) -> Right (next, [])) checked)
            _ -> return (Left (unsupported position "malformed computed record field"))
        definitionNames (CDefinition _ _ name _ _ _) = [name]
        definitionNames (CUniverses _ _ inner) = definitionNames inner
        definitionNames _ = []
        position = commandSpan command
        firstFixName bodies = case bodies of
            FixBody _ name _ _ _ _ : _ -> Just name
            _ -> Nothing
        translated =fmap placedTerm . translateUnder (`Set.member` Env.envAmbiguous env) [] (Env.envNames env) (Env.envDecls env)
        named name = case Map.lookup (nameText name) (Env.envNames env) >>= (\constant -> (,) constant <$> Map.lookup constant (Env.envDecls env)) . declarationOf of
            Just entry -> Right entry
            Nothing -> Left (Diagnostic (nameSpan name) "LoL-ScopeError" "H-Name" ("unknown name: " ++ nameText name) [nameText name])
        declarationOf global = case global of
            Core.GlobalCst constant -> constant
            Core.GlobalInd block _ -> block
            Core.GlobalCon block _ _ -> block
            Core.GlobalProj block _ -> block
        printable = either (\message -> Left (Diagnostic position "LoL-Unsupported" "M2-Output" message [])) Right
        -- The declarations as they are shown (Env.visible).
        printed found = case found of
            Left failure -> return (Left failure)
            Right entries -> do
                shown <- mapM (\(constant, entry) -> (,) constant <$> Env.visibleEntry kernel limits env entry) entries
                return ((,) env <$> mapM (\(constant, entry) -> printable (Pretty.displayDeclaration (forDisplay env) constant entry)) shown)
        universeCommand context inner = case inner of
            CDefinition at kind name binders annotation body -> do
                proposed <- Elab.proposeUniversesDisplaying forDisplay kernel limits env context (Just (Term at (SForall binders annotation))) (Term at (SLambda binders body))
                case proposed of
                    Left failure -> return (Left failure)
                    Right result -> admitUniverses (Elab.proposedUniverses result) env [(nameText name, (if kind == "Definition" then Env.Definition else Env.Theorem) (Elab.proposedType result) (Elab.proposedTerm result))]
            CAxiom _ name annotation -> do
                proposed <- Elab.proposeUniversesDisplaying forDisplay kernel limits env context Nothing annotation
                case proposed of
                    Left failure -> return (Left failure)
                    Right result -> admitUniverses (Elab.proposedUniverses result) env [(nameText name, Env.Axiom (Elab.proposedTerm result))]
            CFixpoint at bodies -> do
                proposed <- Elab.proposeFixpointUniversesDisplaying forDisplay kernel limits env context (Term at (SFix bodies Nothing))
                case proposed of
                    Left failure -> return (Left failure)
                    Right result -> case Elab.proposedTerm result of
                        Core.Fix _ functions -> admitUniverses (Elab.proposedUniverses result) env [(nameText name, Env.Definition (Core.functionType function) (Core.Fix index functions)) | (index, (FixBody _ name _ _ _ _, function)) <- zip [0 ..] (zip bodies functions)]
                        _ -> return (Left (unsupported at "malformed elaborated fix"))
            CInductive _ bodies -> do
                proposed <- Elab.proposeInductiveUniversesDisplaying forDisplay kernel limits env context bodies
                case proposed of
                    Left failure -> return (Left failure)
                    Right (universes, declaration) -> admitUniverses universes env [(concat (take 1 [nameText name | IndBody _ name _ _ _ <- bodies]), declaration)]
            _ -> return (Left (unsupported (commandSpan inner) "a polymorphic non-declaration command"))
        admitUniverses _ current [] = return (Right (implicitMetadata current command, []))
        admitUniverses universes current ((name, declaration) : rest) = do
            admitted <- declare kernel limits current name universes declaration
            let display = Env.withNames (Map.union (Map.fromList (Env.declGlobals (Env.envFresh current) name declaration)) (Env.envNames current)) current
            either (return . Left . refusalIn (forDisplay display) position) (\(_, next) -> admitUniverses universes next rest) admitted
        universeInductive (IndBody at _ binders arity constructors) = any (Elab.needsUniverses env) (Term at (SForall binders arity) : [Term place (SForall binders signature) | Constructor place _ signature <- constructors])
        -- The declarations of one command are admitted in order, or none is.
        -- A later one is written against the environment of the command: the
        -- functions of a `Fixpoint` are bound in each of its definitions.
        admit current [] = return (Right (implicitMetadata current command, []))
        admit current ((name, declared) : rest) = case declared of
            Left failure -> return (Left failure)
            Right declaration -> do
                admitted <- declare kernel limits current name Core.emptyUniverses declaration
                let display = Env.withNames (Map.union (Map.fromList (Env.declGlobals (Env.envFresh current) name declaration)) (Env.envNames current)) current
                either (return . Left . refusalIn (forDisplay display) position) (\(_, next) -> admit next rest) admitted
        query operation schemeOperation source
            | Elab.needsUniverses env source = do
                proposed <- Elab.proposeUniversesDisplaying forDisplay kernel limits env Nothing Nothing source
                case proposed of
                    Left failure -> return (Left failure)
                    Right proposal -> do
                        let context = Elab.proposedUniverses proposal
                            value = Core.Cast (Elab.proposedTerm proposal) (Elab.proposedType proposal)
                        answer <- schemeOperation kernel limits env context value >>= mapM (Env.visible kernel limits env context)
                        return $ case answer of
                            Left rejected -> Left (refusalIn (forDisplay env) (termSpan source) rejected)
                            Right output -> do
                                rendered <- printable (Pretty.displayTermWithUniverses (forDisplay env) context output)
                                return (env, [rendered])
            | needsProposal source = do
                proposed <- Elab.proposeDisplaying forDisplay kernel limits env Nothing source
                case proposed of
                    Left failure -> return (Left failure)
                    -- T-Cast independently validates the proposed type and
                    -- preserves an annotation's cumulative type for Check.
                    Right (value, typ) -> answered operation source (Core.Cast value typ)
            | otherwise = case translated source of
                Left failure -> return (Left failure)
                Right value -> tryProposal (answered operation source value)
        answered operation source value = do
            answer <- operation kernel limits env value >>= mapM (Env.visible kernel limits env Core.emptyUniverses)
            return $ case answer of
                Left rejected -> Left (refusalIn (forDisplay env) (termSpan source) rejected)
                Right output -> do
                    rendered <- printable (Pretty.displayTerm (forDisplay env) output)
                    return (env, [rendered])
        indNeeded (IndBody at _ binders arity constructors) = needsProposal (Term at (SForall binders arity)) || any (\(Constructor place _ signature) -> needsProposal (Term place (SForall binders signature))) constructors
        inductiveProposal bodies = do
            signatures <- mapM (\(IndBody at _ binders arity _) -> Elab.proposeDisplaying forDisplay kernel limits env Nothing (Term at (SForall binders arity))) bodies
            case sequence signatures of
                Left failure -> return (Left failure)
                Right values -> do
                    let block = Env.envFresh env
                        globals = Map.fromList [(nameText name, Core.GlobalInd block index) | (index, IndBody _ name _ _ _ ) <- zip [0 ..] bodies]
                        -- The families of the block are in scope in its constructor types and
                        -- its constructors are not: only the families get their status here.
                        temporary = implicitMetadata (Env.withNames (Map.union globals (Env.envNames env)) env) (CInductive position [IndBody at name binders arity [] | IndBody at name binders arity _ <- bodies])
                        premises = [indTypeFact block index typ | (index, (typ, _)) <- zip [0 ..] values]
                    families <- sequence [do
                        constructors' <- mapM (\(Constructor place given signature) -> fmap (fmap (\(typ, _) -> (nameText given, typ))) (Elab.proposeConstructorDisplaying forDisplay premises block index (sum (map (length . binderVars) binders)) env kernel limits temporary (Term place (SForall binders signature)))) constructors
                        return (Env.Family (nameText name) typ <$> sequence constructors')
                        | (index, (IndBody _ name binders _ constructors, (typ, _))) <- zip [0 ..] (zip bodies values)]
                    return (Env.Inductive (sum [length (binderVars binder) | IndBody _ _ binders _ _ <- take 1 bodies, binder <- binders]) <$> sequence families)

-- Local definitions have no constructor slots. A reference to the new
-- family in a computed field is in scope; a real field of Record cannot
-- store that family, including by referring to an earlier computed field.
checkRecordFields :: [Int] -> Declare -> Declare
checkRecordFields positions declare kernel limits env name universes declaration
    | Env.Inductive count [family] <- declaration
    , [(constructor, signature)] <- Env.familyCons family
    , Set.member block (Core.constantsOf (domains signature)) = do
        let trimmed = clean (negate count) signature
            goal = foldlNApp (named "no_family") [natural block, terms [embedTerm (domains trimmed)]]
            family' = family { Env.familyCons = [(constructor, trimmed)] }
        (verdict, _, _) <- Env.run Env.Persistent kernel limits env [] goal []
        case verdict of
            Admitted [] -> declare kernel limits env name universes $ case Env.familyRecord family of
                Just _ -> Env.Inductive count [family']
                Nothing -> declaration
            Rejected _ -> return (Left (Env.KernelRejected (Just (Report "I-Record" [] []))))
            Undecided reason -> return (Left (Env.KernelUndecided reason))
            _ -> return (Left (Env.KernelUndecided "Unexpected record scope output."))
    | otherwise = declare kernel limits env name universes declaration
    where
        block = Env.envFresh env
        domains (Core.Pi hint typ body) = Core.Pi hint typ (domains body)
        domains _ = Core.Prop
        clean index (Core.Pi hint typ body) = Core.Pi hint domain (clean (index + 1) body) where
            domain
                | Set.member block (Core.constantsOf typ) = unbindFields (length (takeWhile (<= index) positions)) typ
                | otherwise = typ
        clean _ term = term

-- Metadata is installed only after every declaration in the command succeeds.
-- An ordinary record projection is a checked transparent definition. Its
-- motive replaces the earlier fields of the constructor telescope with
-- applications of their already admitted projections to the matched value.
ordinaryFields :: Core.ConstId -> Int -> Core.UniverseContext -> [(Name, Int)] -> Core.Term -> [(String, [Maybe Core.ConstId] -> Maybe Env.Decl)]
ordinaryFields block count context fields signature = zipWith build [0 ..] (zip fields domains) where
    telescope term = case term of
        Core.Pi hint domain body -> (hint, domain) : telescope body
        _ -> []
    (parameters, domains) = splitAt count (telescope signature)
    instance' = map Core.Parameter [0 .. length (Core.universeNames context) - 1]
    arguments depth = [Core.Var (index + depth) | index <- reverse [0 .. count - 1]]
    record = Core.apps (Core.Ind block 0 instance') (arguments 0)
    build index ((name, locals), (_, domain)) = (nameText name, projection) where
        projection earlier = do
            let result depth = replaceFields (map (fmap (access depth)) earlier ++ map Just (reverse (arguments depth))) (if any (== Nothing) earlier || Set.member block (Core.constantsOf domain) then unbindFields locals domain else domain)
                access depth identity = Core.apps (Core.Cst identity instance') (arguments depth ++ [Core.Var 0])
            codomain <- result 1
            motive <- result 2
            let typ = foldr (uncurry Core.Pi) (Core.Pi "r" record codomain) parameters
                branch = (map (nameText . fst) fields, Core.Var (length fields - index - 1))
                matched = Core.Case block 0 instance' (arguments 1) ["y"] motive (Core.Var 0) [branch]
                body = foldr (uncurry Core.Lam) (Core.Lam "r" record matched) parameters
            return (Env.Definition typ body)

-- An ordinary Prop record may lack an earlier accessor. Only occurrences
-- of that field in the current type or value make its projection unavailable.
replaceFields :: [Maybe Core.Term] -> Core.Term -> Maybe Core.Term
replaceFields values = replace 0 where
    count = length values
    replace depth term = case term of
        Core.Var i
            | i < depth -> Just term
            | i - depth < count -> Core.lift 0 depth <$> values !! (i - depth)
            | otherwise -> Just (Core.Var (i - count))
        _ -> Core.descend replace depth term

-- The body above has been elaborated and checked with all the constructor
-- fields in scope. Replace its real field binders with the available
-- accessors, in both the body and the inferred (or written) return type.
-- The leading lets are lexical bindings introduced by recordDeclaration.
computedProjection :: Span -> Int -> [Maybe Core.Global] -> Int -> Elab.UniverseProposal -> Either Diagnostic (Maybe (Core.UniverseContext, Env.Decl))
computedProjection at parameters previous locals proposal = fmap (fmap finish) (prefix parameters (Elab.proposedType proposal) (Elab.proposedTerm proposal)) where
    finish (typ, value) = (Elab.proposedUniverses proposal, Env.Definition typ value)
    malformed = Left (unsupported at "malformed computed record telescope")
    prefix n (Core.Pi p a t) (Core.Lam q b v) = do
        inside <- if n > 0 then prefix (n - 1) t v else case spine a of
            (Core.Ind _ _ instance', arguments) ->
                let access global = Core.apps (Core.fromGlobalAt instance' global) (map (Core.lift 0 1) arguments ++ [Core.Var 0])
                in fields (length previous) (reverse (map (fmap access) previous)) t v
            _ -> malformed
        return (fmap (\(typ, value) -> (Core.Pi p a typ, Core.Lam q b value)) inside)
    prefix _ _ _ = malformed
    fields 0 replacements t v = Right ((,) <$> replaceFields replacements (unbindFields locals t) <*> replaceFields replacements (unbindFields locals v))
    fields n replacements (Core.Pi _ _ t) (Core.Lam _ _ v) = fields (n - 1) replacements t v
    fields _ _ _ _ = malformed

unbindFields :: Int -> Core.Term -> Core.Term
unbindFields count (Core.Let _ value _ body)
    | count > 0 = unbindFields (count - 1) (substitute [value] body)
unbindFields _ term = term

fieldArguments :: Env.Env -> [Name] -> Command -> Env.Env
fieldArguments env fields inner = case inner of
    CUniverses _ _ block -> fieldArguments env fields block
    CTemplate _ block -> fieldArguments env fields block
    COrdinaryRecord _ _ block -> fieldArguments env fields block
    CPrimitive _ _ _ block -> fieldArguments env fields block
    CInductive _ [IndBody _ _ binders _ _] ->
        let flags = concatMap (\binder -> replicate (length (binderVars binder)) (binderImpl binder)) binders ++ [False]
            globals = [field | name <- fields, Just field <- [Map.lookup (nameText name) (Env.envNames env)]]
            entries = [(field, flags) | field <- globals, or flags]
            accessors = Map.fromList [(field, length flags - 1) | field@Core.GlobalCst {} <- globals]
            syntax = Env.envSyntax env
        in Env.withSyntax syntax { Env.syntaxArguments = Map.union (Map.fromList entries) (Env.syntaxArguments syntax), Env.syntaxProjectionParameters = Map.union accessors (Env.syntaxProjectionParameters syntax) } env
    _ -> env

implicitMetadata :: Env.Env -> Command -> Env.Env
implicitMetadata env (CUniverses _ _ inner) = implicitMetadata env inner
implicitMetadata env command = Env.withSyntax syntax { Env.syntaxArguments = foldr insert (Env.syntaxArguments syntax) entries } env where
    syntax = Env.envSyntax env
    entries = case command of
        CDefinition _ _ name binders annotation _ -> [(nameText name, flags binders ++ typeFlags annotation)]
        CAxiom _ name annotation -> [(nameText name, typeFlags annotation)]
        CFixpoint _ bodies -> [(nameText name, flags binders ++ typeFlags annotation) | FixBody _ name binders _ annotation _ <- bodies]
        CInductive _ bodies -> concat [[(nameText name, flags binders ++ typeFlags arity)] ++ [(nameText given, flags binders ++ typeFlags signature) | Constructor _ given signature <- constructors] | IndBody _ name binders arity constructors <- bodies]
        _ -> []
    insert (name, mask) old = case Map.lookup name (Env.envNames env) of
        Just global
            | or mask -> Map.insert global mask old
        _ -> old
    flags = concatMap (\binder -> replicate (length (binderVars binder)) (binderImpl binder))
    typeFlags source = case termForm source of
        SForall binders body -> flags binders ++ typeFlags body
        SArrow _ body -> False : typeFlags body
        SParen body -> typeFlags body
        _ -> []

rewriteCommand :: Env.Env -> Command -> Either Diagnostic Command
rewriteCommand env command = case command of
    CRecordDefinitions at nonrecursive inner definitions -> (\block -> CRecordDefinitions at nonrecursive block definitions) <$> rewriteCommand env inner
    CTemplate at inner -> CTemplate at <$> rewriteCommand env inner
    COrdinaryRecord at fields inner -> COrdinaryRecord at fields <$> rewriteCommand env inner
    CPrimitive at eta fields inner -> CPrimitive at eta fields <$> rewriteCommand env inner
    CUniverses at context inner -> CUniverses at context <$> rewriteCommand env inner
    CDefinition at kind name binders annotation body -> do
        (parameters, local) <- Fixity.rewriteBinders env binders
        typ <- Fixity.rewriteAt local (ArgScopes.classScopes local SortClass) annotation
        CDefinition at kind name parameters typ <$> Fixity.rewriteAt local (ArgScopes.expected local typ) body
    CAxiom at name annotation -> CAxiom at name <$> Fixity.rewriteAt env (ArgScopes.classScopes env SortClass) annotation
    CCheck at source -> CCheck at <$> term source
    CCompute at source -> CCompute at <$> term source
    CInductive at bodies -> CInductive at <$> mapM inductive bodies
    CFixpoint at functions -> CFixpoint at <$> mapM function functions
    _ -> Right command
    where
        term = Fixity.rewrite env
        binder value = (\annotation -> value { binderType = annotation }) <$> traverse term (binderType value)
        inductive (IndBody at name binders arity constructors) = IndBody at name <$> mapM binder binders <*> term arity <*> mapM constructor constructors
        constructor (Constructor at name signature) = Constructor at name <$> term signature
        function (FixBody at name binders structural annotation body) = FixBody at name <$> mapM binder binders <*> pure structural <*> term annotation <*> term body

refusal :: Span -> Env.Refusal -> Diagnostic
refusal position rejected = case rejected of
    Env.DuplicateName name -> Diagnostic position "LoL-ScopeError" "H-Name" ("duplicate declaration: " ++ name) [name]
    Env.NotClosed -> Diagnostic position "LoL-ScopeError" "H-Name" "the term is not closed" []
    Env.OracleRejected report reason -> Diagnostic position "LoL-KernelError" (reportRule report) "the oracle rejected this command" ["the oracle says: " ++ reason]
    Env.KernelRejected (Just report) -> Diagnostic position "LoL-KernelError" (reportRule report) "the kernel rejected this command" (if null (reportArgs report) then [] else "the kernel reports, in its own notation:" : map ("  " ++) (reportArgs report))
    Env.KernelRejected Nothing -> Diagnostic position "LoL-KernelError" "" "the kernel rejected this command without a rule report" []
    Env.KernelUndecided reason -> Diagnostic position "LoL-KernelUndecided" "R5" reason []

-- A located host renderer interprets only the report's transport terms.
refusalIn :: Env.Env -> Span -> Env.Refusal -> Diagnostic
refusalIn env position rejected = case rejected of
    Env.KernelRejected (Just report) -> Diagnostic position "LoL-KernelError" (reportRule report) "the kernel rejected this command" (reportTerms env report)
    _ -> refusal position rejected
