{-# LANGUAGE BangPatterns #-}
module LoL.Proof.View where

import Control.Monad.Trans.State.Strict
import qualified Data.IntMap.Strict as IntMap
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import qualified Hol.V2.Embedding as Hol
import qualified LoL.Core as Core
import qualified LoL.Diagnostic as Diagnostic
import qualified LoL.Env as Env
import qualified LoL.Front.Syntax as Front
import qualified LoL.Pretty as Pretty
import qualified LoL.Proof.Document as Document
import qualified LoL.Proof.Executor as Executor
import qualified LoL.Proof.Json as Json
import qualified LoL.Proof.Module as Module
import qualified LoL.Proof.Protocol as Protocol
import qualified LoL.Proof.Session as Proof

itemLimit, textLimit :: Int
itemLimit = 50000
textLimit = 262144

data Graph
    = Graph
        { graphNext               :: !Int
        , graphNodes              :: [Json.Value]
        , graphTruncated          :: !Bool
        , graphItemsLeft          :: !Int
        , graphTextLeft           :: !Int
        , graphOmittedText        :: !Int
        , graphOmittedCollections :: !Int
        }
    deriving ()

type Build = State Graph

emptyGraph :: Graph
emptyGraph = Graph 0 [] False itemLimit textLimit 0 0

reserve :: Build Bool
reserve = do
    current <- get
    if graphItemsLeft current <= 0 then do
        put current { graphTruncated = True }
        return False
    else do
        put current { graphItemsLeft = graphItemsLeft current - 1 }
        return True

-- Stop at the first omitted entry. Counting an unvisited tail would defeat
-- the bound; the report counts uninspected tails, whose lengths stay unknown.
collection :: (a -> Build Json.Value) -> [a] -> Build Json.Value
collection build values = Json.Array <$> walk values where
    walk remaining = do
        current <- get
        if graphItemsLeft current <= 0 then do
            put current { graphTruncated = True, graphOmittedCollections = graphOmittedCollections current + 1 }
            return []
        else case remaining of
            [] -> return []
            value : rest -> do
                put current { graphItemsLeft = graphItemsLeft current - 1 }
                first <- build value
                more <- walk rest
                return (first : more)

-- Inspected bytes consume the common budget even when an oversized field is
-- omitted. A sequence of large names cannot repeatedly scan the same budget.
text :: String -> Build Json.Value
text value = do
    current <- get
    if graphTextLeft current <= 0 then omitText else do
        let (used, exact) = inspect (graphTextLeft current) 0 value
        put current { graphTextLeft = graphTextLeft current - used }
        if exact then return (Json.String value) else omitText
    where
        inspect _ !used [] = (used, True)
        inspect !remaining !used (character : rest)
            | not (Json.scalar character) = (used, False)
            | width > remaining = (used + remaining, False)
            | otherwise = inspect (remaining - width) (used + width) rest
            where width = Json.utf8Size character

omitText :: Build Json.Value
omitText = do
    modify' (\current -> current { graphTruncated = True, graphOmittedText = graphOmittedText current + 1 })
    return Json.Null

-- Avoid constructing the decimal expansion of an arbitrarily large natural.
-- IDs in the public runtime fit well inside this presentation-only bound.
decimalText :: Integral a => a -> Build Json.Value
decimalText value = do
    current <- get
    if graphTextLeft current <= 0 then omitText
    else if abs integer >= maximumDecimal then do
        put current { graphTextLeft = max 0 (graphTextLeft current - 4096) }
        omitText
    else text (show integer)
    where integer = toInteger value

maximumDecimal :: Integer
maximumDecimal = 10 ^ (4096 :: Int)

optionalBuild :: (a -> Build Json.Value) -> Maybe a -> Build Json.Value
optionalBuild = maybe (return Json.Null)

-- Every node and every collection wrapper consumes the same item budget.
-- The flat references keep JSON depth independent of term and kind depth.
node :: String -> Build [(String, Json.Value)] -> Build Json.Value
node tag fields = do
    available <- reserve
    if not available then return Json.Null else do
        current <- get
        let identity = graphNext current
        put current { graphNext = identity + 1 }
        members <- fields
        modify' (\after -> after { graphNodes = Json.object (("id", number identity) : ("tag", Json.String tag) : members) : graphNodes after })
        return (number identity)

number :: Integral a => a -> Json.Value
number = Json.Integer . toInteger

optional :: (a -> Json.Value) -> Maybe a -> Json.Value
optional = maybe Json.Null

budgetJson :: Graph -> Json.Value
budgetJson graph = Json.object
    [ ("truncated", Json.Boolean (graphTruncated graph))
    , ("itemLimit", number itemLimit)
    , ("itemsUsed", number (itemLimit - graphItemsLeft graph))
    , ("textByteLimit", number textLimit)
    , ("textBytesInspected", number (textLimit - graphTextLeft graph))
    , ("omittedTextFields", number (graphOmittedText graph))
    , ("uninspectedCollectionTails", number (graphOmittedCollections graph))
    ]

variable :: Hol.LogicVar -> Build Json.Value
variable identity = case identity of
    Hol.LV_Named name -> do
        value <- text name
        return (Json.object [("kind", Json.String "named"), ("name", value)])
    Hol.LV_Unique (Hol.Unique value) _ -> unique "term" value
    Hol.LV_ty_var (Hol.Unique value) -> unique "type" value
    where
        unique tag value = do
            encoded <- decimalText value
            return (Json.object [("kind", Json.String tag), ("id", encoded)])

constant :: Hol.Constant -> Build Json.Value
constant symbol = case symbol of
    Hol.DC (Hol.DC_Named name) -> named "data" name
    Hol.TC (Hol.TC_Named name) -> named "type" name
    Hol.DC (Hol.DC_Unique (Hol.Unique value) _) -> unique "data-nominal" value
    Hol.TC (Hol.TC_Unique (Hol.Unique value)) -> unique "type-nominal" value
    Hol.DC (Hol.DC_NatL value) -> do
        encoded <- decimalText value
        return (Json.object [("kind", Json.String "natural"), ("value", encoded)])
    Hol.DC (Hol.DC_ChrL value) -> do
        encoded <- text [value]
        return (Json.object [("kind", Json.String "character"), ("value", encoded)])
    Hol.DC value -> named "data-builtin" (show value)
    Hol.TC value -> named "type-builtin" (show value)
    where
        named tag name = do
            encoded <- text name
            return (Json.object [("kind", Json.String tag), ("name", encoded)])
        unique tag value = do
            encoded <- decimalText value
            return (Json.object [("kind", Json.String tag), ("id", encoded)])

monoType :: Hol.MonoType Int -> Build Json.Value
monoType typ = case typ of
    Hol.TyVar index -> node "type-variable" (return [("index", number index)])
    Hol.TyMTV (Hol.Unique identity) -> node "type-meta" $ do
        encoded <- decimalText identity
        return [("identity", encoded)]
    Hol.TyCon (Hol.TCon symbol kind) -> node "type-constant" $ do
        symbolValue <- constant (Hol.TC symbol)
        shape <- kindJson kind
        return [("constant", symbolValue), ("kind", shape)]
    Hol.TyApp function argument -> node "type-application" $ do
        left <- monoType function
        right <- monoType argument
        return [("function", left), ("argument", right)]
    where
        kindJson Hol.Star = node "kind-star" (return [])
        kindJson (Hol.KArr domain codomain) = node "kind-arrow" $ do
            first <- kindJson domain
            second <- kindJson codomain
            return [("from", first), ("to", second)]

term :: Hol.TermNode -> Build Json.Value
term value = case value of
    Hol.LVar identity -> node "variable" $ do
        encoded <- variable identity
        return [("identity", encoded)]
    Hol.NCon symbol _ -> node "constant" $ do
        encoded <- constant symbol
        return [("constant", encoded)]
    Hol.NIdx index -> node "index" (return [("index", number index)])
    Hol.NApp function argument _ -> node "application" $ do
        left <- term function
        right <- term argument
        return [("function", left), ("argument", right)]
    Hol.NLam hint annotation body _ -> node "abstraction" $ do
        typ <- maybe (return Json.Null) monoType (Hol.unLamType annotation)
        inner <- term body
        shownHint <- optionalBuild text hint
        return [("hint", shownHint), ("type", typ), ("body", inner)]
    Hol.Susp body old new entries -> node "suspension" $ do
        inner <- term body
        environment <- collection suspended entries
        return [("body", inner), ("oldLevel", number old), ("newLevel", number new), ("environment", environment)]
    Hol.NPresburgerCheck syntax free _ -> node "presburger-check" $ do
        view <- formulaView (Hol.FormulaView syntax free)
        return [("formula", view)]
    where
        suspended (Hol.Dummy level) = return (Json.object [("kind", Json.String "dummy"), ("level", number level)])
        suspended (Hol.Binds body level) = do
            inner <- term body
            return (Json.object [("kind", Json.String "binding"), ("level", number level), ("term", inner)])

formulaView :: Hol.FormulaView -> Build Json.Value
formulaView view = do
    syntax <- formula (Hol.formulaSyntax view)
    free <- collection binding (Map.toAscList (Hol.formulaFreeTerms view))
    return (Json.object [("syntax", syntax), ("freeTerms", free)])
    where
        binding (identity, value) = do
            reference <- term value
            encoded <- decimalText identity
            return (Json.object [("variable", encoded), ("term", reference)])

formula :: Hol.PresburgerFormula Hol.PresburgerTermRep -> Build Json.Value
formula syntax = case syntax of
    Hol.ValF value -> node "formula-value" (return [("value", Json.Boolean value)])
    Hol.EqnF left right -> comparison "formula-equal" left right
    Hol.LtnF left right -> comparison "formula-less" left right
    Hol.LeqF left right -> comparison "formula-less-equal" left right
    Hol.GtnF left right -> comparison "formula-greater" left right
    Hol.ModF left modulus right -> node "formula-modulo" $ do
        first <- arithmetic left
        second <- arithmetic right
        encoded <- decimalText modulus
        return [("left", first), ("modulus", encoded), ("right", second)]
    Hol.NegF inner -> node "formula-not" $ do
        child <- formula inner
        return [("body", child)]
    Hol.DisF left right -> logical "formula-or" left right
    Hol.ConF left right -> logical "formula-and" left right
    Hol.ImpF left right -> logical "formula-implies" left right
    Hol.IffF left right -> logical "formula-iff" left right
    Hol.AllF identity inner -> quantified "formula-all" identity inner
    Hol.ExsF identity inner -> quantified "formula-exists" identity inner
    where
        comparison tag left right = binary tag arithmetic left right
        logical tag left right = binary tag formula left right
        binary tag build left right = node tag $ do
            first <- build left
            second <- build right
            return [("left", first), ("right", second)]
        quantified tag identity inner = node tag $ do
            child <- formula inner
            encoded <- decimalText identity
            return [("variable", encoded), ("body", child)]

arithmetic :: Hol.PresburgerTermRep -> Build Json.Value
arithmetic syntax = case syntax of
    Hol.IVar identity -> node "arithmetic-variable" $ do
        encoded <- decimalText identity
        return [("variable", encoded)]
    Hol.Zero -> node "arithmetic-zero" (return [])
    Hol.Succ inner -> node "arithmetic-successor" $ do
        child <- arithmetic inner
        return [("body", child)]
    Hol.Plus left right -> node "arithmetic-plus" $ do
        first <- arithmetic left
        second <- arithmetic right
        return [("left", first), ("right", second)]

constraint :: Hol.Constraint -> Build Json.Value
constraint item = case Hol.constraintView item of
    Hol.DisagreementView left right -> pair "unification" left right
    Hol.EvaluationView left right -> pair "evaluation" left right
    Hol.ArithmeticView premises value -> do
        given <- assumptions premises
        target <- term value
        return (Json.object [("kind", Json.String "arithmetic"), ("premises", given), ("term", target)])
    Hol.PresburgerView premises value -> do
        given <- assumptions premises
        target <- formulaView value
        return (Json.object [("kind", Json.String "presburger"), ("premises", given), ("formula", target)])
    where
        pair kind left right = do
            first <- term left
            second <- term right
            return (Json.object [("kind", Json.String kind), ("left", first), ("right", second)])
        assumptions premises = do
            comparisons <- collection term (Hol.premiseComparisons premises)
            formulas <- collection formulaView (Hol.premiseFormulas premises)
            return (Json.object [("comparisons", comparisons), ("formulas", formulas)])

proofJson :: Module.ModuleState -> Proof.ProofView -> Json.Value
proofJson state view = evalState (proofBuild state view) emptyGraph

proofBuild :: Module.ModuleState -> Proof.ProofView -> Build Json.Value
proofBuild state view = do
    available <- reserve
    if available then proofInner state view else return Json.Null

proofInner :: Module.ModuleState -> Proof.ProofView -> Build Json.Value
proofInner state view = do
    -- Names used by the printer are checked once before building its sets.
    -- A large scope omits display only; its structured prefix remains visible.
    scopeOkay <- if length (take 129 scopeNames) > 128 || length (take 129 (Core.universeConstraints (Proof.proofUniverses view))) > 128 then omitText >> return False else do
        aliases <- mapM text scopeNames
        return (all exactString aliases)
    expected <- term (Proof.proofExpected view)
    goal <- optionalBuild (\(Proof.GoalId identity) -> variable identity) (Proof.proofGoalId view)
    source <- optionalBuild decimalText (Proof.proofFocusPosition view)
    beforeUniverses <- get
    universes <- universeContext (Proof.proofUniverses view)
    afterUniverses <- get
    universeRecorded <- optionalBuild (collection universeRelation) (Proof.proofRecorded view)
    universeParameters <- collection term (Proof.proofUniverseParameters view)
    let universeComplete = graphItemsLeft afterUniverses > 0 && graphOmittedText afterUniverses == graphOmittedText beforeUniverses && graphOmittedCollections afterUniverses == graphOmittedCollections beforeUniverses
    universeDisplay <- if scopeOkay && universeComplete then text (displayUniverses state (Proof.proofUniverses view)) else return Json.Null
    display <- displayText scopeOkay state view (Proof.proofExpected view)
    bindings <- collection (local scopeOkay) locals
    machine <- optionalBuild runtime (Proof.proofMachine view)
    reports <- collection term (Proof.proofReports view)
    regions <- collection term (Proof.proofRegions view)
    positions <- collection sourcePosition (Map.toAscList (Proof.proofPositions view))
    allocated <- decimalText (Proof.proofNativeBytes view)
    peak <- decimalText (Proof.proofPeakNative view)
    graph <- get
    return (Json.object
        [ ("state", number (Proof.proofStateId view))
        , ("goal", goal)
        , ("sourcePosition", source)
        , ("sourceRange", optional spanJson (Proof.proofFocusPosition view >>= (`Map.lookup` Proof.proofPositions view)))
        , ("expected", expected)
        , ("universes", universes)
        , ("universeRecorded", universeRecorded)
        , ("universeParameters", universeParameters)
        , ("universeDisplay", universeDisplay)
        , ("display", display)
        , ("locals", bindings)
        , ("complete", Json.Boolean theoremComplete)
        , ("runtime", machine)
        , ("reports", reports)
        , ("regions", regions)
        , ("sourcePositions", positions)
        , ("nativeBytes", allocated)
        , ("nativePeakBytes", peak)
        , ("nodes", Json.Array (reverse (graphNodes graph)))
        , ("truncated", Json.Boolean (graphTruncated graph))
        , ("viewBudget", budgetJson graph)
        ])
    where
        locals = Proof.proofLocals view
        theoremComplete = case Proof.proofTheorem view of
            Nothing -> False
            Just _ -> True
        scopeNames =map Proof.localName locals ++ Core.universeNames (Proof.proofUniverses view)
        exactString (Json.String _) = True
        exactString _ = False
        local scopeOkay binding = do
            name <- text (Proof.localName binding)
            hint <- text (Proof.localHint binding)
            value <- term (Proof.localValue binding)
            typ <- optionalBuild term (Proof.localType binding)
            display <- optionalBuild (displayText scopeOkay state view) (Proof.localType binding)
            body <- optionalBuild (displayText scopeOkay state view) (Proof.localBody binding)
            return (Json.object [("name", name), ("hint", hint), ("value", value), ("type", typ), ("typeDisplay", display), ("bodyDisplay", body)])
        runtime machine = do
            variables <- collection meta (Hol.proofVariables machine)
            nominals <- collection nominal (Hol.proofNominals machine)
            constraints <- collection constraint (Hol.proofConstraints machine)
            return (Json.object [("variables", variables), ("nominals", nominals), ("constraints", constraints)])
        meta value = do
            identity <- variable (Hol.variableIdentity value)
            typ <- optionalBuild monoType (Hol.variableType value)
            return (Json.object [("identity", identity), ("type", typ), ("scope", number (Hol.variableScope value))])
        nominal value = do
            identity <- constant (Hol.nominalConstant value)
            typ <- optionalBuild monoType (Hol.nominalType value)
            name <- optionalBuild text (Hol.nominalName value)
            return (Json.object [("identity", identity), ("type", typ), ("name", name), ("scope", number (Hol.nominalScope value))])
        sourcePosition (identity, position) = do
            encoded <- decimalText identity
            return (Json.object [("identity", encoded), ("range", spanJson position)])

-- The display probe consumes the same work budget as graph construction.
-- A budget failure returns null, never a shortened usable identifier.
universeContext :: Core.UniverseContext -> Build Json.Value
universeContext context = do
    names <- collection text (Core.universeNames context)
    constraints <- collection universeRelation (Core.universeConstraints context)
    return (Json.object [("parameters", names), ("constraints", constraints)])

universeRelation :: Core.UniverseConstraint -> Build Json.Value
universeRelation constraint = case constraint of
    Core.UniverseLe left right -> pair "le" left right
    Core.UniverseEq left right -> pair "eq" left right
    where
        pair tag left right = do
            first <- level left
            second <- level right
            return (Json.object [("relation", Json.String tag), ("left", first), ("right", second)])
        level value = node "universe" $ case value of
            Core.Closed natural -> do
                encoded <- decimalText natural
                return [("kind", Json.String "closed"), ("value", encoded)]
            Core.DefaultLevel owner slot -> return [("kind", Json.String "template-default"), ("owner", Json.String (show owner)), ("slot", number slot)]
            Core.Parameter index -> return [("kind", Json.String "parameter"), ("index", number index)]
            Core.Successor inner -> do
                encoded <- level inner
                return [("kind", Json.String "successor"), ("inner", encoded)]
            Core.Maximum left right -> do
                first <- level left
                second <- level right
                return [("kind", Json.String "maximum"), ("left", first), ("right", second)]

displayText :: Bool -> Module.ModuleState -> Proof.ProofView -> Hol.TermNode -> Build Json.Value
displayText scopeOkay state view value = do
    current <- get
    if not scopeOkay || graphTextLeft current <= 0 then omitText else do
        let (used, complete) = inspect (min 4000 (graphItemsLeft current)) 0 [value]
        put current { graphItemsLeft = graphItemsLeft current - used }
        if complete then text (displayTerm state view value) else omitText
    where
        inspect _ used [] = (used, True)
        inspect remaining used _
            | remaining <= 0 = (used, False)
        inspect remaining used (item : rest) = case item of
            Hol.NCon (Hol.DC (Hol.DC_NatL natural)) _
                | abs natural >= maximumDecimal -> (used + 1, False)
            Hol.NPresburgerCheck {} -> (used + 1, False)
            Hol.NApp left right _ -> inspect (remaining - 1) (used + 1) (left : right : rest)
            Hol.NLam _ _ body _ -> inspect (remaining - 1) (used + 1) (body : rest)
            Hol.Susp {} -> (used + 1, False)
            _ -> inspect (remaining - 1) (used + 1) rest

-- Reuse the Core printer and the worker's actual usable aliases. No judgment
-- or reduction is performed to obtain display text. Unrecovered terms keep
-- their Hol representation, whose structure is also present in the graph.
displayUniverses :: Module.ModuleState -> Core.UniverseContext -> String
displayUniverses state context
    | context == Core.emptyUniverses = ""
    | otherwise = either (const "<universe context has no surface spelling>") (\header -> header "") (Pretty.universeHeader Pretty.Surface names context)
    where
        base = Pretty.naming (Module.displayEnvironment state (Module.environment state))
        names = base { Pretty.namingUniverses = Pretty.universeHints base (Core.universeNames context) }

displayTerm :: Module.ModuleState -> Proof.ProofView -> Hol.TermNode -> String
displayTerm state view value
    | not (small 4000 [value]) = "<term display exceeds 4000 nodes>"
    | otherwise = case Proof.inspectTerm view value of
        Left _ -> Hol.prettyTerm Hol.initial Hol.initialCache value ""
        Right core -> case Pretty.printerFail printer depth core of
            Just _ -> Hol.prettyTerm Hol.initial Hol.initialCache value ""
            Nothing -> Pretty.pieceText (Pretty.printerShow printer depth scope core) ""
    where
        locals = Proof.proofLocals view
        universes = Proof.proofUniverses view
        aliases = map Proof.localName locals
        env = Module.displayEnvironment state (Module.environment state)
        base = Pretty.naming (Env.withNames (foldr Map.delete (Env.envNames env) aliases) env)
        naming = base { Pretty.namingUniverses = Pretty.universeHints base (Core.universeNames universes) }
        printer = Pretty.displayPrinter env naming
        depth = length locals
        scope = Pretty.Names (IntMap.fromList (zip [0 ..] (reverse aliases))) (Set.fromList aliases) Map.empty
        small _ [] = True
        small remaining _
            | remaining <= 0 = False
        small remaining (term : rest) = small (remaining - 1) (children term ++ rest)
        children term = case term of
            Hol.NApp left right _ -> [left, right]
            Hol.NLam _ _ body _ -> [body]
            Hol.Susp body _ _ entries -> body : [part | Hol.Binds part _ <- entries]
            Hol.NPresburgerCheck _ _ _ -> replicate 4001 (Hol.NIdx 0)
            _ -> []

spanJson :: Front.Span -> Json.Value
spanJson (Front.Span first last) = Json.object [("from", position first), ("to", position last)] where
    position (line, column) = Json.object [("line", number line), ("column", number column)]

diagnosticJson :: Diagnostic.Diagnostic -> Json.Value
diagnosticJson failure = evalState (diagnosticBuild failure) emptyGraph

diagnosticBuild :: Diagnostic.Diagnostic -> Build Json.Value
diagnosticBuild failure = do
    kind <- text (Diagnostic.diagnosticKind failure)
    code <- text (Diagnostic.diagnosticCode failure)
    message <- text (Diagnostic.diagnosticText failure)
    details <- collection text (Diagnostic.diagnosticBody failure)
    return (Json.object
        [ ("range", spanJson (Diagnostic.diagnosticSpan failure))
        , ("kind", kind)
        , ("code", code)
        , ("message", message)
        , ("details", details)
        ])

documentJson :: Executor.OpenDocument -> [(String, Json.Value)]
documentJson opened = evalState (documentBuild opened) emptyGraph

documentBuild :: Executor.OpenDocument -> Build [(String, Json.Value)]
documentBuild opened = do
    identity <- text (Executor.openIdentity opened)
    path <- text (Document.documentPath document)
    retained <- collection (return . number) (Document.retainedStates document)
    name <- optionalBuild (text . theoremName) (Document.documentProof document)
    proof <- optionalBuild (proofBuild (Document.checkpointModule current) . Document.pendingView) (Document.documentProof document)
    return
        [ ("document", identity)
        , ("incarnation", number (Executor.openIncarnation opened))
        , ("revision", number (Executor.openRevision opened))
        , ("state", number (Document.documentState document))
        , ("path", path)
        , ("position", spanJson (Front.Span position position))
        , ("retainedStates", retained)
        , ("proofName", name)
        , ("proof", proof)
        ]
    where
        document = Executor.openDocument opened
        current = Document.documentCurrent document
        position = Document.checkpointPosition current
        theoremName = headerName . Document.pendingHeader
        headerName header = case header of
            Front.CUniverses _ _ inner -> headerName inner
            Front.CDefinition _ _ given _ _ _ -> Front.nameText given
            _ -> "<proof>"

resultJson :: Integer -> Executor.Result -> Json.Value
resultJson identity result = Protocol.reply (Just identity) status (fields ++ [("viewBudget", budgetJson graph)]) where
    (fields, graph) = runState build emptyGraph
    response = Executor.resultReply result
    diagnostic = response >>= Document.replyFailure
    status = case (Executor.resultError result, diagnostic) of
        (Nothing, Nothing) -> "ok"
        _ -> "error"
    build = do
        output <- collection text (maybe [] Document.replyOutput response)
        problem <- case Executor.resultError result of
            Just (code, message) -> do
                encodedCode <- text code
                encodedMessage <- text message
                return [("error", Json.object [("code", encodedCode), ("message", encodedMessage)])]
            Nothing -> case diagnostic of
                Nothing -> return []
                Just failure -> do
                    encoded <- diagnosticBuild failure
                    rendered <- case Executor.resultDocument result of
                        Nothing -> text (Diagnostic.diagnosticText failure)
                        Just opened -> do
                            current <- get
                            if graphTruncated current then omitText else do
                                path <- text (Document.documentPath (Executor.openDocument opened))
                                let source = maybe (Document.documentSource (Executor.openDocument opened)) id (Executor.resultInput result)
                                case path of
                                    Json.String name -> text (Diagnostic.renderDiagnostic name source failure)
                                    _ -> omitText
                    let displayed = case encoded of
                            Json.Object members -> Json.Object (Map.insert "display" rendered members)
                            _ -> encoded
                    return [("error", displayed)]
        document <- maybe (return []) documentBuild (Executor.resultDocument result)
        return (document ++ [("output", output), ("atEnd", Json.Boolean (maybe False Document.replyAtEnd response))] ++ problem)

-- The terminal consumes the same bounded representation as an editor. Null
-- names are labelled as omitted; no shortened name is presented as usable.
terminal :: Executor.Result -> String
terminal result = (outputs . failure . state . omitted) "" where
    view = resultJson 0 result
    outputs = foldr (.) id [shown "<output omitted>" line . showChar '\n' | line <- array (field "output" view)]
    failure = case field "error" view of
        Json.Null -> id
        problem -> case field "display" problem of
            Json.String rendered -> showString rendered . showChar '\n'
            _ -> showChar '[' . shown "error" (field "code" problem) . showString "] " . shown "<message omitted>" (field "message" problem) . showChar '\n'
    state = case field "proof" view of
        Json.Null -> id
        proof
            | field "complete" proof == Json.Boolean True -> showString "No goals remain.\n"
            | otherwise -> showString "Proof " . shown "<name omitted>" (field "proofName" view) . showString " - Step " . integer (field "state" proof) . showString "\n\n" . universes proof . bindings proof . showString "--------------------\n" . shown "<goal display omitted>" (field "display" proof) . showChar '\n' . constraints proof
    universes proof = case field "universeDisplay" proof of
        Json.String "" -> id
        value -> showString "Universes " . shown "<context omitted>" value . showChar '\n'
    -- A local definition is shown with its body, as Rocq shows it: `x := t : A`.
    bindings proof = foldr (.) id [shown "<name omitted>" (field "name" binding) . definition (field "bodyDisplay" binding) . showString " : " . shown "<type unavailable or omitted>" (field "typeDisplay" binding) . showChar '\n' | binding <- reverse (array (field "locals" proof))]
    definition value = case value of
        Json.String body -> showString " := " . showString body
        _ -> id
    constraints proof = case length (array (field "constraints" (field "runtime" proof))) of
        0 -> id
        count -> shows count . showString " residual constraints displayed; use the structured proof state for details.\n"
    omitted
        | field "truncated" (field "viewBudget" view) == Json.Boolean True = showString "Some view fields were omitted because the display limit was reached.\n"
        | otherwise = id
    field key (Json.Object members) = Map.findWithDefault Json.Null key members
    field _ _ = Json.Null
    array (Json.Array values) = values
    array _ = []
    shown _ (Json.String value) = showString value
    shown fallback _ = showString fallback
    integer (Json.Integer value) = shows value
    integer _ = showString "?"
