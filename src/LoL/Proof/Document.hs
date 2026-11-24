module LoL.Proof.Document where

import Control.Exception (IOException, mask, onException, try)
import Control.Monad (filterM, foldM, when)
import Data.IORef
import Data.List (find, foldl')
import Data.Word (Word64)
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import qualified Hol.V2.Embedding as Hol
import qualified LoL.Core as Core
import LoL.Diagnostic
import qualified LoL.Env as Env
import qualified LoL.Front.ArgumentScopes as ArgScopes
import qualified LoL.Front.Scope as Scope
import qualified LoL.Front.Search as Search
import qualified LoL.Front.Parse as Front
import qualified LoL.Front.Syntax as Front
import qualified LoL.Front.Vernac as Vernac
import qualified LoL.Hol.Elab as Elab
import LoL.Hol.Embed (Report (..), ReportValue (..), numberHoles, recoverReport, termType)
import LoL.Hol.Session (defaultLimits, Kernel (kernelTypes, kernelBundled), Limits (..), closeKernel, loadKernel, loadProofProgram)
import qualified LoL.Module as Module
import qualified LoL.ImportCache as Cache
import qualified LoL.Object as Object
import qualified LoL.Pretty as Pretty
import qualified LoL.Proof.Command as Command
import qualified LoL.Proof.Module as ModuleState
import qualified LoL.Proof.Session as Proof
import System.Directory (canonicalizePath)
import System.FilePath ((</>), isAbsolute, makeRelative)
import System.Timeout (timeout)

data ProofHandle
    = ProofHandle
        { handleIdentity :: Integer
        , handleSession  :: Proof.ProofSession
        , handleCurrent  :: IORef Proof.StateId
        , handleRetained :: IORef (Set.Set Proof.StateId)
        , handleBytes    :: IORef Word64
        }
    deriving ()

data Pending
    = Pending
        { pendingHeader    :: Front.Command
        , pendingHandle    :: ProofHandle
        , pendingView      :: Proof.ProofView
        , pendingType      :: Core.Term
        , pendingRequest   :: Maybe Elab.UniverseRequest
        , pendingMarks     :: [(Integer, Core.Level)]
        , pendingOriginal  :: Core.UniverseContext
        , pendingDirect    :: Bool
        , pendingBullets   :: [Bullet]
        }
    deriving ()

-- pendingType is the statement as its header reads it under the universes
-- pendingOriginal, pendingRequest the universes that the header writes, and
-- pendingMarks the kind and the level of each universe marker of the
-- statement there (Elab.proposedMarks). pendingDirect says that the proof
-- was complete where it started and that every universe of the statement is
-- one that nothing settles. The theorem is what the end of the proof gives,
-- and Qed holds it to the header (theoremKept).

-- Region identities come from Hol. The host only checks ancestry membership;
-- it does not inspect the unfinished CIC term to decide which goal was solved.
data Bullet
    = Bullet
        { bulletMarker :: (Char, Int)
        , bulletRegion :: Maybe Hol.TermNode
        }
    deriving (Eq, Show)

data Checkpoint
    = Checkpoint
        { checkpointId        :: Integer
        , checkpointModule    :: ModuleState.ModuleState
        , checkpointProof     :: Maybe Pending
        , checkpointProgram   :: Maybe Kernel
        , checkpointProgramId :: Integer
        , checkpointCursor    :: Int
        , checkpointPosition  :: Front.Position
        , checkpointUndo      :: Maybe Integer
        }
    deriving ()

data Document
    = Document
        { documentRoot            :: FilePath
        , documentPath            :: FilePath
        , documentSource          :: String
        , documentRemaining       :: String
        , documentCurrent         :: Checkpoint
        , documentHistory         :: [Checkpoint]
        , documentNext            :: Integer
        , documentHandles         :: Map.Map Integer ProofHandle
        , documentRetired         :: [ProofHandle]
        , documentAncestors       :: [(String, FilePath)]
        , documentDefault         :: Maybe Kernel
        , documentPrograms        :: Map.Map Integer Kernel
        , documentRetiredPrograms :: [Kernel]
        , documentCacheInputs     :: Maybe Cache.Inputs
        , documentBudget          :: Word64
        }
    deriving ()

data Reply
    = Reply
        { replyDocument :: Document
        , replyOutput   :: [String]
        , replyFailure  :: Maybe Diagnostic
        , replyAtEnd    :: Bool
        }
    deriving ()

newDocument :: Kernel -> FilePath -> FilePath -> String -> Document
newDocument program = newDocumentWith (Just program)

-- Ordinary source checking does not load the tactic library. Acquire it only
-- if this file or one of its imports actually starts an interactive proof.
newBatchDocument :: FilePath -> FilePath -> String -> Document
newBatchDocument = newDocumentWith Nothing

newDocumentWith :: Maybe Kernel -> FilePath -> FilePath -> String -> Document
newDocumentWith program root path source = Document root path source source initial [] 1 Map.empty [] [(name, path)] program Map.empty [] Nothing 0 where
    name = Module.moduleIdentity root path
    initial = Checkpoint 0 (ModuleState.emptyModule name) Nothing program 0 0 (1, 1) Nothing

closeDocument :: Document -> IO ()
closeDocument document = do
    mapM_ (Proof.closeProof . handleSession) (Map.elems (documentHandles document) ++ documentRetired document)
    mapM_ closeKernel (Map.elems (documentPrograms document) ++ documentRetiredPrograms document)

-- Publish the new document before disposal. Cancelling a command must not
-- leave its still-published predecessor pointing at an already closed worker.
disposeRetired :: Document -> IO Document
disposeRetired document = do
    mapM_ (Proof.closeProof . handleSession) (documentRetired document)
    mapM_ closeKernel (documentRetiredPrograms document)
    return document { documentRetired = [], documentRetiredPrograms = [] }

documentState :: Document -> Integer
documentState = checkpointId . documentCurrent

documentProof :: Document -> Maybe Pending
documentProof = checkpointProof . documentCurrent

retainedStates :: Document -> [Integer]
retainedStates document = map checkpointId (documentCurrent document : documentHistory document)

appendSource :: String -> Document -> Either (String, String) Document
appendSource source document
    | length source > Front.inputLimit - length (documentSource document) = Left ("document-limit", "The document exceeds " ++ show Front.inputLimit ++ " characters.")
    | null (documentRemaining document), c : _ <- source, not (Front.sourceSpace c), lastDot = Left ("document-boundary", "Insert whitespace after the executed command, or undo it before editing its final dot.")
    | otherwise = Right document { documentSource = documentSource document ++ source, documentRemaining = documentRemaining document ++ source }
    where
        lastDot = case documentSource document of
            [] -> False
            text -> last text == '.'

-- Editing an executed prefix requires Undo first. Its surviving checkpoints
-- still refer to the identical prefix and remain meaningful in the new text.
replaceRemaining :: String -> Document -> Either (String, String) Document
replaceRemaining source document = appendSource source document { documentSource = take (checkpointCursor (documentCurrent document)) (documentSource document), documentRemaining = "" }

-- A prompt after a file or discarded suffix may start immediately after a
-- period. Parsing, saving and rendering a refused command share its boundary.
terminalChunk :: Document -> String -> String
terminalChunk document source = case documentSource document of
    text@(_ : _)
        | not (Front.sourceSpace (last text)) -> '\n' : source
    _ -> source

-- The terminal records successful commands. A rejected command is shown to
-- the user but must not become an unexecutable prefix before the next input.
submitText :: Kernel -> Limits -> Integer -> String -> Document -> IO Reply
submitText base limits request source document = case Front.lexAt (checkpointPosition current) remaining of
    Right [] -> case appendSource (terminalChunk document source) prepared of
        Left (_, message) -> return (refused document position "P-DocumentLimit" message)
        Right candidate -> do
            result <- advanceDocument base limits request candidate
            return $ case replyFailure result of
                Nothing -> result
                Just _ -> result { replyDocument = (replyDocument result) { documentSource = documentSource document, documentRemaining = remaining, documentCurrent = (documentCurrent (replyDocument result)) { checkpointCursor = checkpointCursor current, checkpointPosition = checkpointPosition current } } }
    _ -> return (refused document position "P-PendingSource" "The document has an unexecuted command; execute or replace it first.")
    where
        current = documentCurrent document
        remaining = documentRemaining document
        prepared = document { documentCurrent = consumed remaining current, documentRemaining = "" }
        position = Front.Span (checkpointPosition current) (checkpointPosition current)

advanceDocument :: Kernel -> Limits -> Integer -> Document -> IO Reply
advanceDocument base limits request original = case Front.commandChunks remaining of
    [] -> return (Reply document [] Nothing True)
    (_, source) : _ -> case parseNext document source of
        Left problem -> return (Reply document [] (Just (fromFrontError problem)) False)
        Right Nothing -> advanceDocument base limits request document { documentCurrent = consumed source current, documentRemaining = drop (length source) remaining }
        Right (Just command) -> case command of
            Command.UndoProof position -> case checkpointUndo current of
                Nothing -> return (refused document position "P-NoHistory" "There is no earlier changing command to undo.")
                Just target -> do
                    restored <- rewindDocument request target document
                    return $ case replyFailure restored of
                        Nothing -> restored { replyDocument = (replyDocument restored) { documentRemaining = drop (length source) remaining, documentCurrent = (documentCurrent (replyDocument restored)) { checkpointCursor = checkpointCursor after, checkpointPosition = checkpointPosition after } } }
                        Just _ -> restored
                    where
                        after = consumed source current
            _ -> do
                response <- execute base limits request command source document
                return $ case replyFailure response of
                    Nothing -> response { replyDocument = (replyDocument response) { documentRemaining = drop (length source) remaining } }
                    Just _ -> response
    where
        document = original { documentBudget = limitBytes limits }
        current = documentCurrent document
        remaining = documentRemaining document

-- Both the executor's cancellation classification and actual execution must
-- parse against the identical immutable checkpoint, even after a rewind.
parseNext :: Document -> String -> Either Front.FrontError (Maybe Command.Command)
parseNext document = Command.parseCommandAtIndexed (Env.syntaxReader (ModuleState.moduleSyntax (checkpointModule checkpoint))) (checkpointPosition checkpoint) where
    checkpoint = documentCurrent document

consumed :: String -> Checkpoint -> Checkpoint
consumed source current = current
    { checkpointCursor = checkpointCursor current + length source
    , checkpointPosition = foldl' Front.advance (checkpointPosition current) source
    }

refused :: Document -> Front.Span -> String -> String -> Reply
refused document position code message = Reply document [] (Just diagnostic) False
    where
        diagnostic
            | code == "R5" = Vernac.refusal position (Env.KernelUndecided message)
            | otherwise = Diagnostic position "LoL-ProofError" code message []

-- The universes of a theorem are settled where its proof ends, as Rocq
-- settles them: the header refuses a statement that Rocq refuses there (a
-- level that is left out of a statement with named universes and that
-- nothing settles, a constraint that a closed context lacks), the proof
-- reads the statement as it is written, and Qed admits what the end of the
-- proof gave (Proof.completedTheorem).
-- What the answer of a proof program must be for the header of its theorem.
-- The program is not trusted: the clean kernel checks the term against the
-- statement and the universes that Qed gives it, so those must be the ones
-- that were asked for. A header that closes its constraints (`@{u v | ...}`)
-- has exactly its universes and constraints. One that names its universes
-- (`@{u v}`) has exactly those universes, and the constraints are what the
-- proof needs. One that names none is held by its markers (headerKept).
theoremKept :: Pending -> Core.UniverseContext -> Core.Term -> [Core.Level] -> Either String [Core.UniverseConstraint]
theoremKept pending settled statement images = case headerKept named (length (Core.universeNames original)) (pendingMarks pending) (pendingType pending) (length (Core.universeNames settled)) statement images of
    Nothing -> Left "The proof program answered with a statement or public universe list that is not the one of the theorem."
    Just (levels, equal) -> case pendingRequest pending of
        Just (Elab.ClosedUniverses context) | settled /= context -> Left "The proof program answered with universes or constraints that the theorem does not declare."
        Just (Elab.OpenUniverses context) | Core.universeNames settled /= Core.universeNames context -> Left "The proof program answered with universes that the theorem does not name."
        _ -> Right (equal ++ [constraint | Right constraint <- map (substituted levels) (Core.universeConstraints original)])
    where
        original = pendingOriginal pending
        named = maybe 0 (length . Core.universeNames . Elab.requestedUniverses) (pendingRequest pending)
        substituted levels constraint = case constraint of
            Core.UniverseLe left right -> Core.UniverseLe <$> Core.substituteLevel levels left <*> Core.substituteLevel levels right
            Core.UniverseEq left right -> Core.UniverseEq <$> Core.substituteLevel levels left <*> Core.substituteLevel levels right

-- The answer for a statement whose header reads it under `original`
-- universes with the markers `marks` (kind and level): `particular` under
-- `count` universes, with the level `images` of each marker. A header that
-- names its universes (`named` of them) keeps them as they are. Otherwise:
-- - the answer is the statement of the header with a level for each of its
--   universes, which is the level of the markers that are that universe;
-- - a marker that nothing settles (a `Type` without a level, kind 1, or a
--   universe that an argument's type got, kind 6 and above) is a universe of
--   its own, and those are in the order in which they were written;
-- - every universe of the answer is the level of a marker: the theorem has
--   no universe that its statement did not make.
-- Cast annotations stay in Core. If an input still claims that a header
-- universe occurs nowhere, it cannot use that absence to identify it with
-- a different universe. Return the substitution and remaining obligations.
headerKept :: Int -> Int -> [(Integer, Core.Level)] -> Core.Term -> Int -> Core.Term -> [Core.Level] -> Maybe ([Core.Level], [Core.UniverseConstraint])
headerKept named original marks general count particular images = do
    found <- Core.instanceOf general particular
    if all (Core.wellScopedLevel count . snd) found then Just () else Nothing
    if named > 0 then (if count == named && and [value == Core.Parameter index | (index, value) <- found, index < named] then Just (map Core.Parameter [0 .. named - 1], []) else Nothing) else do
        if length images == length marks && all (Core.wellScopedLevel count) images then Just () else Nothing
        owned <- foldl' own (Just Map.empty) (zip (map snd marks) images)
        if all (\(index, value) -> Map.lookup index owned == Just value) found then Just () else Nothing
        levels <- mapM (`Map.lookup` owned) [0 .. original - 1]
        places <- sequence [place image | ((kind, _), image) <- zip marks images, rigid kind]
        if and (zipWith (<) places (drop 1 places)) && Set.unions (map Core.levelParameters images) == Set.fromList [0 .. count - 1] then Just () else Nothing
        let visible = Core.termParameters general
            distinct (index, level@(Core.Parameter _)) = Set.member index visible || and [other /= level | (j, other) <- zip [0 ..] levels, index /= j]
            distinct _ = True
            equal = [Core.UniverseEq image expected | ((_, level), image) <- zip marks images, Right expected <- [Core.substituteLevel levels level], expected /= image]
        if all distinct (zip [0 ..] levels) then Just (levels, equal) else Nothing
    where
        rigid kind = kind == 1 || kind >= 6
        place level = case level of
            Core.Parameter index -> Just index
            _ -> Nothing
        own acc (level, image) = case (acc, level) of
            (Just seen, Core.Parameter index) -> case Map.lookup index seen of
                Nothing -> Just (Map.insert index image seen)
                Just value -> if value == image then acc else Nothing
            _ -> acc

proofHeader :: Env.Env -> Front.Command -> Either Diagnostic (Maybe Elab.UniverseRequest, [Front.Binder], Front.Term)
proofHeader env header = case header of
    Front.CDefinition _ _ _ binders signature _ -> Right (Nothing, binders, signature)
    Front.CUniverses _ written inner -> do
        context <- traverse (Elab.universeRequest env) written
        (_, binders, signature) <- proofHeader env inner
        return (context, binders, signature)
    _ -> Left (Diagnostic (Front.commandSpan header) "LoL-ProofError" "P-Header" "Expected a theorem header." [])

-- The host calls this entry with twelve value arguments and no type arguments.
statementEntry :: Hol.PolyType
statementEntry = Hol.Forall [] (foldr Hol.mkTyArrow Hol.mkTyO arguments) where
    ty name = Hol.TyCon (Hol.TCon (Hol.TC_Named name) Hol.Star)
    nat = Hol.mkTyNat
    constraints = Hol.mkTyList (ty "uconstraint")
    arguments = [nat, Hol.mkTyList nat, constraints, nat, ty "raw", Hol.mkTyList (ty "ptac"), nat, nat, constraints, termType, termType, termType]

-- The universes of a proof as they are now (Rocq: Show Universes): those of
-- the statement, the universes of the proof that are still open (`_0`, `_1`,
-- ...), the declared constraints and what the kernel has recorded since.
-- Nothing is judged here: the record is shown as it is, and a constraint
-- that follows from the others is not taken out.
universesShown :: ModuleState.ModuleState -> Proof.ProofView -> String
universesShown state view = case Proof.proofRecorded view of
    Nothing -> unreadable
    Just recorded
        | null (Core.universeNames universes) -> "This proof has no universe."
        | otherwise -> either (const unreadable) (\header -> "Universes of the proof: " ++ header "") (Pretty.universeHeader Pretty.Surface names (universes { Core.universeConstraints = Proof.distinct (Core.universeConstraints universes ++ recorded) }))
    where
        unreadable = "The universe constraints of this proof state have no surface spelling."
        universes = Proof.proofUniverses view
        base = Pretty.naming (ModuleState.displayEnvironment state (ModuleState.environment state))
        names = base { Pretty.namingUniverses = Pretty.universeHints base (Core.universeNames universes) }

execute :: Kernel -> Limits -> Integer -> Command.Command -> String -> Document -> IO Reply
execute base limits request command source document = case command of
    Command.Ordinary (Front.CSearch at items scope)
        | Just pending <- checkpointProof current -> do
            let view = pendingView pending
                display = ModuleState.displayEnvironment state env
                inspect binding = (Proof.localName binding, Proof.localType binding >>= either (const Nothing) Just . Proof.inspectTerm view)
                locals = map inspect (Proof.proofLocals view)
            result <- Search.search (Vernac.refusalIn display at) base limits env display (Proof.proofUniverses view) locals at items scope
            case result of
                Left failure -> return (Reply document [] (Just (Module.ambiguous (Module.scopeCanonical (ModuleState.moduleScope state)) failure)) False)
                Right messages -> done False current messages
    Command.Ordinary ordinary
        | Just _ <- checkpointProof current, not (query ordinary) -> return (bad "P-InProof" "Finish or abort the proof before changing declarations.")
        | otherwise -> do
            result <- ModuleState.executeWith (loadImport base limits document) base limits state ordinary
            case result of
                Left failure -> return (Reply document [] (Just failure) False)
                Right (_, messages) | Just _ <- checkpointProof current, query ordinary -> done False current messages
                Right (next, messages) -> do
                    case ordinary of
                        Front.CImport {} -> return ()
                        _ -> extendProgram next
                    done (not (query ordinary) || Env.syntaxObserved (ModuleState.moduleSyntax state) /= Env.syntaxObserved (ModuleState.moduleSyntax next)) current { checkpointModule = next } messages
    Command.TheoremHeader position header
        | Just _ <- checkpointProof current -> return (bad "P-InProof" "A proof is already active.")
        | otherwise -> case ModuleState.namesAvailable state position (Module.commandNames header) >> Vernac.rewriteCommand env header of
            Left failure -> return (Reply document [] (Just failure) False)
            Right written -> case proofHeader env written of
                Left failure -> return (Reply document [] (Just failure) False)
                Right (context, parameters, typ) -> do
                    let written' = Front.Term position (Front.SForall parameters typ)
                    preparedHeader <- readHeader context written'
                    case preparedHeader of
                        Left failure -> return (Reply document [] (Just failure) False)
                        Right (proposal, statement) -> mask $ \restore -> do
                            let expected = Elab.proposedTerm proposal
                                named = maybe Core.emptyUniverses Elab.requestedUniverses context
                            prepared <- restore (proofProgram document)
                            case prepared of
                                Left message -> return (bad "P-Tactics" message)
                                Right (ready, program) -> do
                                    when (kernelBundled program) (Cache.sawProgram (documentCacheInputs document) "lol/hol/tactics.hol" program)
                                    let release = mapM_ closeKernel (Map.elems (Map.difference (documentPrograms ready) (documentPrograms document)))
                                    budget <- remainingLimits limits ready Nothing
                                    started <- case budget of
                                        Left message -> return (Left (Proof.ProofRuntimeFailure message))
                                        Right available -> restore (Proof.startSectionProof base program available env named statement [if Front.nameText name == "_" then "" else Front.nameText name | binder <- parameters, name <- Front.binderVars binder] (Map.keys (ModuleState.contextVariables state))) `onException` release
                                    case started of
                                        Left failure@(Proof.ProofResourceFailure _) -> release >> return (bad "R5" (Proof.describeProofFailure failure))
                                        Left failure -> release >> return (bad "P-Runtime" (Proof.describeProofFailure failure))
                                        Right (session, view) -> do
                                            actual <- newIORef (Proof.proofStateId view)
                                            retained <- newIORef (Set.fromList (map fst (Proof.proofRetained view)))
                                            bytes <- newIORef (Proof.proofNativeBytes view)
                                            let handle = ProofHandle (documentNext ready) session actual retained bytes
                                                original = Elab.proposedUniverses proposal
                                                marks = Elab.proposedMarks proposal
                                                completed = case Proof.completedTheorem view of
                                                    Right (Just _) -> True
                                                    _ -> False
                                                -- Without a cell that was left, the universes of the answer are those of the header.
                                                stable = maybe (Set.fromList [index | (kind, Core.Parameter index) <- marks, kind == 1 || kind >= 6] == Set.fromList [0 .. length (Core.universeNames original) - 1]) (const True) context
                                                pending = Pending written handle view expected context marks original (completed && stable) []
                                                registered = ready { documentHandles = Map.insert (handleIdentity handle) handle (documentHandles ready) }
                                            commit True (consumed source (documentCurrent ready) { checkpointModule = ModuleState.observe env (ArgScopes.commandLookups env header) state, checkpointProof = Just pending }) registered [] `onException` (Proof.closeProof session >> release)
    Command.ProofStart _ -> case checkpointProof current of
        Nothing -> return (bad "P-NoProof" "There is no active proof.")
        Just _ -> done False current []
    Command.ShowProof _ -> done False current []
    Command.ShowUniverses _ -> case checkpointProof current of
        Nothing -> return (bad "P-NoProof" "There is no active proof.")
        Just pending -> done False current [universesShown state (pendingView pending)]
    Command.QedProof _ -> case checkpointProof current of
        Nothing -> return (bad "P-NoProof" "There is no active proof.")
        Just pending -> case Proof.completedTheorem (pendingView pending) of
            Left rules -> return (qedRefusal pending rules)
            Right Nothing -> return (bad "P-RemainingGoals" "The proof still has unresolved goals or constraints.")
            -- A proof program answers with a theorem: it is the written one
            -- with its universes settled, or it is none.
            Right (Just (settled, statement, value, images)) -> case theoremKept pending settled statement images of
                Left message -> return (bad "P-Statement" message)
                Right owed -> do
                    -- The names of the binders are those of the written statement.
                    checked <- case pendingRequest pending of
                        Just (Elab.ClosedUniverses _) -> return (Right ())
                        _ -> Elab.proofConstraints base limits env position owed (pendingDirect pending) settled statement value
                    admitted <- either (return . Left) (const (ModuleState.admitTheoremWithUniverses base limits state (pendingHeader pending) settled (Core.hinted (pendingType pending) statement) value)) checked
                    case admitted of
                        Left failure -> return (Reply document [] (Just failure) False)
                        Right next -> do
                            extendProgram next
                            done True current { checkpointModule = next, checkpointProof = Nothing } ["The theorem was accepted."]
    Command.AbortProof _ -> case checkpointProof current of
        Nothing -> return (bad "P-NoProof" "There is no active proof.")
        Just _ -> done True current { checkpointProof = Nothing } ["The proof was aborted."]
    Command.LoadTactics _ path
        | Just _ <- checkpointProof current -> return (bad "P-InProof" "Load tactics before starting a proof.")
        | otherwise -> do
            loaded <- loadKernel (if isAbsolute path then path else documentRoot document </> path)
            case loaded of
                Left message -> return (bad "P-Tactics" message)
                Right program
                    | Map.lookup (Hol.DC_Named "p_universe_statement") (kernelTypes program) /= Just statementEntry -> closeKernel program >> return (bad "P-Tactics" "The tactic program must declare p_universe_statement with the signature in lol/hol/proof.hol.")
                    | otherwise -> do
                        Cache.sawProgram (documentCacheInputs document) (if isAbsolute path then path else documentRoot document </> path) program
                        let identity = documentNext document
                            registered = document { documentPrograms = Map.insert identity program (documentPrograms document) }
                            next = consumed source current { checkpointProgram = Just program, checkpointProgramId = identity }
                        commit True next registered ["The tactic program was loaded."] `onException` closeKernel program
    Command.RunTactic location tactic -> case checkpointProof current of
        Nothing -> return (bad "P-NoProof" "There is no active proof.")
        Just pending -> case bulletCommand pending tactic of
            Left message -> return (bad "P-Bullet" message)
            Right (selected, marker, stack) -> runTactic pending (Command.RunTactic location selected) marker stack
    Command.UndoProof _ -> return (bad "P-Internal" "Undo must be dispatched by the document cursor.")
    where
        current = documentCurrent document
        state = checkpointModule current
        env = ModuleState.environment state
        position = Command.commandSpan command
        bad = refused document position
        qedRefusal pending rules = case [report | Right report <- map recoverReport (Proof.proofReports (pendingView pending))] of
            report : _
                | reportRule report == code
                , [Just (ReportConstraint _ _ _)] <- reportCore report ->
                    let details = reportTermsAt env (Core.universeNames (pendingOriginal pending)) report
                    in plain { replyFailure = fmap (\failure -> failure { diagnosticBody = details }) (replyFailure plain) }
            _ -> plain
            where
                code = case rules of
                    first : _ -> first
                    [] -> "P-Universes"
                plain = bad code (Proof.describeUnsettled rules)
        -- Reuse a closed, monomorphic statement only after its judgment in
        -- the kernel. A custom proof program still receives its written raw
        -- syntax. The builtin entry rechecks the core term under its oracle.
        readHeader context source = case context of
            Nothing
                | not (Elab.needsUniverses env source || Elab.needsGroundElaborator base env source)
                , Right located <- Scope.translate (Env.envNames env) (Env.envDecls env) source
                , let term = Scope.placedTerm located
                , snd (numberHoles [term]) == 0 -> do
                    checked <- Env.typeOfTerm base limits env term
                    case checked of
                        Right typ -> return $ do
                            statement <- Elab.statementOf env Nothing Set.empty source
                            return (Elab.UniverseProposal term typ Core.emptyUniverses Set.empty [], statement { Elab.statementCore = if checkpointProgramId current == 0 then Just term else Nothing })
                        Left failure@(Env.KernelUndecided _) -> return (Left (Vernac.refusal position failure))
                        Left _ -> elaborate
            _ -> elaborate
            where
                elaborate = do
                    proposed <- Elab.proposeUniversesDisplaying (ModuleState.displayEnvironment state) base limits env context Nothing source
                    return (proposed >>= \proposal -> (,) proposal <$> Elab.statementOf env context (Elab.proposedRefresh proposal) source)
        extendProgram next = case checkpointProgram current of
            Just selected -> extend selected
            Nothing -> mapM_ extend (documentDefault document)
            where
                extend selected = Proof.extendAfterAdmission selected env (ModuleState.environment next)
        done changed next = commit changed (consumed source next) document
        runTactic pending selectedCommand marker stack = do
            let handle = pendingHandle pending
            (refreshed, problem) <- configureProof limits request handle document
            let prepared = maybe pending (\view -> pending { pendingView = view }) refreshed
                selected = document { documentCurrent = current { checkpointProof = Just prepared } }
            case problem of
                Just message -> do
                    retained <- readIORef (handleRetained handle)
                    if Set.null retained then failedWorker position prepared Proof.ClosedProof selected else return (refused selected position "P-ProofBudget" message)
                Nothing -> do
                    result <- Proof.submitProof (handleSession handle) (proofRequest request) (Proof.proofStateId (pendingView prepared)) selectedCommand
                    case result of
                        Left failure -> failedWorker position prepared failure selected
                        Right Proof.ProofAborted -> done True current { checkpointProof = Nothing } ["The proof was aborted."]
                        Right (Proof.ProofAdvanced view) -> do
                            recordView handle view
                            let bullets = maybe stack (\key -> Bullet key (firstNewRegion (pendingView prepared) view) : stack) marker
                            done True current { checkpointProof = Just prepared { pendingView = view, pendingBullets = bullets } } []
                        Right restoredReply@(Proof.ProofRestored view message) -> do
                            recordView handle view
                            let restored = document { documentCurrent = current { checkpointId = documentNext document, checkpointProof = Just prepared { pendingView = view } }, documentNext = documentNext document + 1 }
                            next <- collect restored
                            return (refused next position (Proof.restoredCode restoredReply) (if message == "The proof step failed." || message == "The proof command failed." then maybe message id (Proof.describeRefusedStep view) else message))
        query ordinary = case ordinary of
            Front.CCheck {} -> True
            Front.CCompute {} -> True
            Front.CSearch {} -> True
            Front.CPrint {} -> True
            Front.CPrintAssumptions {} -> True
            _ -> False

firstNewRegion :: Proof.ProofView -> Proof.ProofView -> Maybe Hol.TermNode
-- A user tactic may enter another dispatcher. Its innermost region can end
-- before the outer command's siblings, so anchor the oldest new region.
firstNewRegion before after = case reverse (filter (`notElem` Proof.proofRegions before) (Proof.proofRegions after)) of
    region : _ -> Just region
    [] -> Nothing

bulletCommand :: Pending -> Command.Tactic -> Either String (Command.Tactic, Maybe (Char, Int), [Bullet])
bulletCommand pending tactic = case tactic of
    Command.Bullet _ marker count inner -> do
        noInnerBullets inner
        noGlobalSelector inner
        let key = (marker, count)
        case break ((== key) . bulletMarker) stack of
            (above, previous : outer)
                | any active (previous : above) -> Left "Finish the current bullet block before starting its next sibling."
                | otherwise -> Right (inner, Just key, outer)
            _
                | first : _ <- stack, not (active first) -> Left "Continue with the same bullet or a completed enclosing bullet."
                | otherwise -> Right (inner, Just key, stack)
    _ -> do
        noInnerBullets tactic
        case stack of
            first : _
                | not (active first) -> Left "The bullet block is complete; start the next block with a bullet."
                | otherwise -> noGlobalSelector tactic
            [] -> Right ()
        Right (tactic, Nothing, stack)
    where
        stack = pendingBullets pending
        active bullet = maybe False (`elem` Proof.proofRegions (pendingView pending)) (bulletRegion bullet)
        noGlobalSelector value = case value of
            Command.All {} -> Left "The all: selector cannot cross a bullet boundary."
            _ -> Right ()
        noInnerBullets value = case value of
            Command.Bullet {} -> Left "A bullet is allowed only at the outermost tactic position."
            Command.Then _ left right -> noInnerBullets left >> noInnerBullets right
            Command.Try _ inner -> noInnerBullets inner
            Command.Repeat _ inner -> noInnerBullets inner
            Command.First _ alternatives -> mapM_ noInnerBullets alternatives
            Command.All _ inner -> noInnerBullets inner
            _ -> Right ()

commit :: Bool -> Checkpoint -> Document -> [String] -> IO Reply
commit changed next document messages = do
    let previous = documentCurrent document
        installed = next { checkpointId = documentNext document, checkpointUndo = if changed then Just (checkpointId previous) else checkpointUndo previous }
        candidates = previous : documentHistory document
        -- The states that successive Undo commands return to are kept before
        -- the others: a state that only a query made is given up first. The
        -- history has 15 states beside the current one; the chain gets the
        -- first seven of them, close to half, and the most recent other
        -- states the rest. So Undo works seven times in a row, and no more
        -- is promised.
        targets = take 7 (undoChain (checkpointUndo installed))
        undoChain identity = case identity >>= (\target -> find ((== target) . checkpointId) candidates) of
            Just target -> target : undoChain (checkpointUndo target)
            Nothing -> []
        kept = Set.fromList (map checkpointId targets)
        recent = take (15 - length targets) [candidate | candidate <- candidates, Set.notMember (checkpointId candidate) kept]
        chosen = Set.union kept (Set.fromList (map checkpointId recent))
        retained = [candidate | candidate <- candidates, Set.member (checkpointId candidate) chosen]
        revised = document { documentCurrent = installed, documentHistory = retained, documentNext = documentNext document + 1 }
    kept <- collect revised
    return (Reply kept messages Nothing False)

rewindDocument :: Integer -> Integer -> Document -> IO Reply
rewindDocument request target document
    | target == documentState document = return (Reply document [] Nothing False)
    | otherwise = case break ((== target) . checkpointId) (documentHistory document) of
        (_, []) -> return (refused document origin "P-ExpiredState" "The requested document state is no longer retained.")
        (_, chosen : older) -> do
            restored <- case checkpointProof chosen of
                Nothing -> return (Right chosen)
                Just pending -> do
                    let handle = pendingHandle pending
                    (_, problem) <- configureProof limitsForRestore request handle document
                    case problem of
                        Just message -> return (Left (pending, message))
                        Nothing -> do
                            actual <- readIORef (handleCurrent handle)
                            result <- Proof.restoreProof (handleSession handle) (proofRequest request) actual (Proof.proofStateId (pendingView pending))
                            case result of
                                Left failure -> do
                                    case failure of
                                        Proof.ClosedProof -> writeIORef (handleRetained handle) Set.empty
                                        Proof.ProofRuntimeFailure _ -> writeIORef (handleRetained handle) Set.empty
                                        _ -> return ()
                                    return (Left (pending, Proof.describeProofFailure failure))
                                Right (Proof.ProofRestored view _) -> do
                                    recordView handle view
                                    return (Right chosen { checkpointProof = Just pending { pendingView = view } })
                                _ -> return (Left (pending, "The proof worker did not return a restored state."))
            case restored of
                Left (pending, message) -> do
                    retained <- readIORef (handleRetained (pendingHandle pending))
                    if Set.null retained then failedWorker origin pending Proof.ClosedProof document else do
                        kept <- collect document
                        return (refused kept origin "P-Restore" message)
                Right next -> do
                    let revised = document { documentCurrent = next { checkpointId = documentNext document }, documentHistory = older, documentRemaining = drop (checkpointCursor next) (documentSource document), documentNext = documentNext document + 1 }
                    kept <- collect revised
                    return (Reply kept ["The previous document state was restored."] Nothing False)
    where
        origin = Front.Span (checkpointPosition (documentCurrent document)) (checkpointPosition (documentCurrent document))
        limitsForRestore = defaultLimits { limitMicros = 0, limitBytes = documentBudget document, limitAllocBytes = 0 }

collect :: Document -> IO Document
collect document = do
    history <- filterM retained (documentHistory document)
    let referenced = Set.fromList [handleIdentity (pendingHandle pending) | checkpoint <- documentCurrent document : history, Just pending <- [checkpointProof checkpoint]]
        retired = Map.elems (Map.withoutKeys (documentHandles document) referenced)
        programs = Set.insert 0 (Set.fromList (map checkpointProgramId (documentCurrent document : history)))
        retiredPrograms = Map.elems (Map.withoutKeys (documentPrograms document) programs)
    return document { documentHistory = history, documentHandles = Map.restrictKeys (documentHandles document) referenced, documentRetired = documentRetired document ++ retired, documentPrograms = Map.restrictKeys (documentPrograms document) programs, documentRetiredPrograms = documentRetiredPrograms document ++ retiredPrograms }
    where
        retained checkpoint = case checkpointProof checkpoint of
            Nothing -> return True
            Just pending -> Set.member (Proof.proofStateId (pendingView pending)) <$> readIORef (handleRetained (pendingHandle pending))

recordView :: ProofHandle -> Proof.ProofView -> IO ()
recordView handle view = do
    writeIORef (handleCurrent handle) (Proof.proofStateId view)
    writeIORef (handleRetained handle) (Set.fromList (map fst (Proof.proofRetained view)))
    writeIORef (handleBytes handle) (Proof.proofNativeBytes view)

proofProgram :: Document -> IO (Either String (Document, Kernel))
proofProgram document = case checkpointProgram (documentCurrent document) of
    Just program -> return (Right (document, program))
    Nothing -> case documentDefault document of
        Just program -> return (Right (document, program))
        Nothing -> do
            loaded <- loadProofProgram
            return $ case loaded of
                Left message -> Left message
                Right program -> Right (document { documentDefault = Just program, documentPrograms = Map.insert 0 program (documentPrograms document) }, program)

-- Document request IDs and worker bookkeeping IDs are separate. A tactic's
-- cancellation always addresses this slot, never a preceding prune request.
proofRequest :: Integer -> Integer
proofRequest request = 8 * request + 4

remainingLimits :: Limits -> Document -> Maybe Integer -> IO (Either String Limits)
remainingLimits limits document active
    | limitBytes limits == 0 = return (Right limits)
    | otherwise = do
        charges <- mapM (readIORef . handleBytes) others
        let remaining = toInteger (limitBytes limits) - sum (map toInteger charges)
        return $ if remaining <= 0 then Left "The retained proof workers exhaust the document's native proof budget." else Right limits { limitBytes = fromInteger remaining }
    where
        others = filter (\handle -> Just (handleIdentity handle) /= active) (Map.elems (documentHandles document) ++ documentRetired document)

configureProof :: Limits -> Integer -> ProofHandle -> Document -> IO (Maybe Proof.ProofView, Maybe String)
configureProof limits request handle document = do
    available <- remainingLimits limits document (Just (handleIdentity handle))
    case available of
        Left message -> return (Nothing, Just message)
        Right budget -> do
            actual <- readIORef (handleCurrent handle)
            result <- Proof.configureProofHistory (handleSession handle) (8 * request) actual keep (Just (limitBytes budget))
            case result of
                Right (Proof.ProofAdvanced view) -> recordView handle view >> return (Just view, Nothing)
                Left failure -> do
                    case failure of
                        Proof.ClosedProof -> writeIORef (handleRetained handle) Set.empty
                        Proof.ProofRuntimeFailure _ -> writeIORef (handleRetained handle) Set.empty
                        _ -> return ()
                    -- A failed budget change may already have released
                    -- unreferenced snapshots. Refresh its transport metadata.
                    refreshed <- Proof.submitProof (handleSession handle) (8 * request + 1) actual (Command.ShowProof Module.origin)
                    case refreshed of
                        Right (Proof.ProofAdvanced view) -> recordView handle view >> return (Just view, Just (Proof.describeProofFailure failure))
                        _ -> return (Nothing, Just (Proof.describeProofFailure failure))
                _ -> return (Nothing, Just "The proof worker did not return its configured state.")
    where
        keep = [Proof.proofStateId (pendingView pending) | checkpoint <- documentCurrent document : documentHistory document, Just pending <- [checkpointProof checkpoint], handleIdentity (pendingHandle pending) == handleIdentity handle]

failedWorker :: Front.Span -> Pending -> Proof.ProofFailure -> Document -> IO Reply
failedWorker position pending failure document = case failure of
    Proof.ProofDiagnostic diagnostic -> return (Reply document [] (Just diagnostic) False)
    Proof.ClosedProof -> closed
    Proof.ProofRuntimeFailure _ -> closed
    _ -> return (refused document position "P-Runtime" (Proof.describeProofFailure failure))
    where
        closed = do
            writeIORef (handleRetained (pendingHandle pending)) Set.empty
            let current = documentCurrent document
                surviving = case checkpointProof current of
                    Just actual
                        | handleIdentity (pendingHandle actual) == handleIdentity (pendingHandle pending) -> Nothing
                    other -> other
                next = document { documentCurrent = current { checkpointId = documentNext document, checkpointProof = surviving }, documentNext = documentNext document + 1 }
            kept <- collect next
            return (refused kept position "P-ProofClosed" ("The proof worker closed without admitting a theorem: " ++ Proof.describeProofFailure failure))

-- Imports run through the same command executor, with the parent's admitted
-- identities but a fresh lexical scope and the default tactic program.
loadImport :: Kernel -> Limits -> Document -> Module.Loaded -> String -> IO (Either Module.Failure Module.Loaded)
loadImport base limits parent loaded name = do
    result <- load
    case result of
        Right next | Just unit <- Map.lookup name (Module.loadedUnits next) -> Cache.sawImport (documentCacheInputs parent) unit
        _ -> return ()
    return result
    where
        load = do
            paths <- try ((,) <$> canonicalizePath (documentRoot parent) <*> canonicalizePath requested) :: IO (Either IOException (FilePath, FilePath))
            case paths of
                Left problem -> return (Left (Module.inputFailure requested problem))
                Right (root, path)
                    | not (Module.inside (makeRelative root path)) -> return (Left (bad path "I-Root" "An imported module resolves outside the project root."))
                    | name `elem` map fst active || path `elem` map snd active -> return (Left (bad path "I-Cycle" "The import reaches a module that is already being executed."))
                    | Just unit <- Map.lookup name (Module.loadedUnits loaded) -> if Module.unitPath unit == path then validateCaptured root unit else return (Left (bad path "I-ModuleName" "Two files have the same module name."))
                    | otherwise -> do
                        input <- Module.readSource path
                        case input of
                            Left problem -> return (Left (Module.inputFailure path problem))
                            Right source -> do
                                budget <- remainingLimits limits parent Nothing
                                case budget of
                                    Left message -> return (Left (bad path "P-ProofBudget" message))
                                    Right available -> importSource root path source available
        -- A diamond may meet a module already admitted in this document.
        -- Only reuse the earlier identities if their source closure still
        -- resolves to the exact files and revisions it captured.
        validateCaptured root unit = do
            checked <- visit Set.empty [unit]
            return (loaded <$ checked)
            where
                visit _ [] = return (Right ())
                visit seen (current : rest)
                    | Set.member key seen = visit seen rest
                    | otherwise = case traverse pinned (Object.objectImports (Module.unitObject current)) of
                        Nothing -> return conflict
                        Just children -> case Module.unitSource current of
                            -- Explicit .lolo graphs already attest and check
                            -- their imports without requiring a source tree.
                            Nothing -> descend children
                            Just expected -> do
                                resolved <- try (canonicalizePath (Module.modulePath root key)) :: IO (Either IOException FilePath)
                                case resolved of
                                    Right actual | actual == Module.unitPath current -> do
                                        source <- Module.readSource actual
                                        case source of
                                            Right text | text == expected -> descend children
                                            _ -> return conflict
                                    _ -> return conflict
                    where
                        key = Module.unitName current
                        conflict = Left (bad (Module.unitPath current) "I-VersionConflict" ("An already admitted module or its pinned dependency changed: " ++ key))
                        descend children = visit (Set.insert key seen) (children ++ rest)
                        pinned (dependency, digest) = case Map.lookup dependency (Module.loadedUnits loaded) of
                            Just child | Module.unitDigest child == digest -> Just child
                            _ -> Nothing
        importSource root path source available = do
            let child = (newDocumentWith (documentDefault parent) root path source) { documentAncestors = (name, path) : active }
                restoreMain result = result { Module.loadedMain = Module.loadedMain loaded }
                execute storage = do
                    tracker <- traverse (const Cache.newInputs) storage
                    scoped <- Module.universeView loaded [] []
                    let initial = documentCurrent child
                        state = (ModuleState.emptyModule name) { ModuleState.moduleLoaded = loaded { Module.loadedMain = name, Module.loadedEnv = scoped } }
                        fresh = child { documentCurrent = initial { checkpointModule = state }, documentCacheInputs = tracker }
                    result <- runDocument base available fresh (const (return ()))
                    case (storage, tracker, result) of
                        (Just target, Just seen, Right next) | Just unit <- Map.lookup name (Module.loadedUnits next) -> Cache.writeEntry target seen unit
                        _ -> return ()
                    return (fmap restoreMain result)
                dependency Nothing _ = return Nothing
                dependency (Just previous) (imported, pin) = do
                    checked <- loadImport base available child previous imported
                    return $ case checked of
                        Right next | Just unit <- Map.lookup imported (Module.loadedUnits next), Module.unitDigest unit == pin -> Just next
                        _ -> Nothing
                tryCached target = do
                    cached <- Cache.readEntry target name
                    case cached of
                        Nothing -> return Nothing
                        Just object -> do
                            dependencies <- foldM dependency (Just loaded) (Object.objectImports object)
                            case dependencies of
                                Nothing -> return Nothing
                                Just ready -> do
                                    verdict <- Module.replayImport base available path (Just source) object (Object.fingerprint object) ready
                                    return (either (const Nothing) Just verdict)
            storage <- Cache.location base (documentDefault parent) available root path source
            -- A bad/stale packet may require many small kernel judgments.
            -- Bound the whole speculative branch as well as each judgment;
            -- source fallback starts from the original immutable environment.
            checked <- case storage of
                Nothing -> return Nothing
                Just target -> timeout (limitMicros available) (tryCached target)
            case checked of
                Just (Just next) -> Cache.hit name >> return (Right (restoreMain next))
                _ -> execute storage
        requested = Module.modulePath (documentRoot parent) name
        active = documentAncestors parent
        bad path code message = Module.failure path "" Module.origin code message

-- No incomplete proof is exportable at EOF. Qed alone admits its checked
-- proposal; closing workers here never turns a pending theorem into an axiom.
runDocument :: Kernel -> Limits -> Document -> ([String] -> IO ()) -> IO (Either Module.Failure Module.Loaded)
runDocument base limits initial emit = mask $ \restore -> do
    latest <- newIORef initial
    let loop request document = do
            result <- restore (advanceDocument base limits request document)
            writeIORef latest (replyDocument result)
            next <- disposeRetired (replyDocument result)
            writeIORef latest next
            case replyFailure result of
                Just failure -> return (Left (Module.Failure (documentPath next) (documentSource next) failure))
                Nothing -> do
                    restore (emit (replyOutput result))
                    if not (replyAtEnd result) then loop (request + 1) next else
                        case documentProof next of
                            Just _ -> return (Left (Module.failure (documentPath next) (documentSource next) Module.origin "P-UnfinishedProof" "The source ends with an unfinished proof; use Qed or Abort."))
                            Nothing -> return (either (Left . Module.failure (documentPath next) (documentSource next) Module.origin "I-Object") Right (ModuleState.finish (documentPath next) (documentSource next) (checkpointModule (documentCurrent next))))
        cleanup = readIORef latest >>= closeDocument
    result <- loop 1 initial `onException` cleanup
    cleanup
    return result
