{-# LANGUAGE DeriveFoldable, DeriveFunctor, DeriveTraversable, PatternSynonyms #-}
module LoL.Front.Syntax where

import Data.Char (isPrint)
import qualified Data.Map.Strict as Map
import GHC.Show (showLitChar)
import LoL.Core (Global)

sourceSpace :: Char -> Bool
sourceSpace c = c `elem` " \t\r\n"

quoted :: String -> String
quoted value = '"' : concatMap quote value ++ "\"" where
    quote c
        | c == '\n' = "\\n"
        | c == '\r' = "\\r"
        | c == '\t' = "\\t"
        | c == '"' || c == '\\' = ['\\', c]
        | isPrint c = [c]
        | otherwise = showLitChar c ""

type Position = (Int, Int)

data Span
    = Span
        { spanFrom :: Position
        , spanTill :: Position
        }
    deriving (Eq, Ord, Show)

instance Semigroup Span where
    Span start _ <> Span _ end = Span start end

data Name
    = Name
        { nameSpan :: Span
        , nameText :: String
        }
    | ResolvedName
        { nameSpan   :: Span
        , nameText   :: String
        , nameGlobal :: Global
        }
    deriving (Eq, Ord, Show)

-- Constructor heads and projection labels in a notation refer to their
-- declaration even when the importing module shadows their spelling.
lookupReference :: Map.Map String Global -> Name -> Maybe Global
lookupReference _ (ResolvedName _ _ g) = Just g
lookupReference globals name = Map.lookup (nameText name) globals

data Term
    = Term
        { termSpan :: Span
        , termForm :: TermForm
        }
    deriving (Eq, Show)

data TermForm
    = SName Name
    | SGlobal Global
    | SExplicitGlobal Global
    | SNotation [RulePart] [Term]
    | SDelimited Name Term
    | SSequence [Term]
    | SPatternOperand Pattern Term
    | SDeclared Name
    | SBound Int
    | SMask Int Int Term
    | SWithout Name Term
    | SExplicit Name
    | SProp
    | SSet
    | SType Integer
    | SInferredType
    | SUniverse LevelSyntax
    | SInstance Bool Name [LevelSyntax]
    | SHole
    | SNumeral Integer
    | SApp Term Term
    | SProjection Term Name
    | SArrow Term Term
    | SOperators Term [(Name, Term)]
    | SForall [Binder] Term
    | SLambda [Binder] Term
    | SLet Name (Maybe Term) Term Term
    | SParen Term
    | SAnnotation Term Term
    | SMatch Term (Maybe Name) (Maybe Pattern) (Maybe Term) [Branch]
    | SFix [FixBody] (Maybe Name)
    deriving (Eq, Show)

data LevelSyntax
    = LevelSyntax
        { levelSpan :: Span
        , levelForm :: LevelForm
        }
    deriving (Eq, Show)

data LevelForm
    = LNumber Integer
    | LName Name
    | LHole
    | LOffset LevelSyntax Name Integer
    | LMaximum Name LevelSyntax LevelSyntax
    deriving (Eq, Show)

-- `@{u v}` is open: it has no constraint clause, and the declaration gets the
-- constraints that it needs. `@{u v | ...}` is closed, also with nothing after
-- the bar: its constraints are all that the declaration has.
data UniverseDecl
    = UniverseDecl
        { universeBinders   :: [Name]
        , universeOpen      :: Bool
        , universeRelations :: [(LevelSyntax, Name, LevelSyntax)]
        }
    deriving (Eq, Show)

data Binder
    = Binder
        { binderSpan :: Span
        , binderVars :: [Name]
        , binderType :: Maybe Term
        , binderImpl :: Bool
        }
    deriving (Eq, Show)

data Pattern
    = Pattern Span Bool Name [Name]
    | WildPattern Span
    | RawPattern Term
    deriving (Eq, Show)

data Branch
    = Branch Span Pattern Term
    deriving (Eq, Show)

data FixBody
    = FixBody Span Name [Binder] (Maybe Name) Term Term
    deriving (Eq, Show)

data Constructor
    = Constructor Span Name Term
    deriving (Eq, Show)

data IndBody
    = IndBody Span Name [Binder] Term [Constructor]
    deriving (Eq, Show)

data ArgSpec = Argument Span Bool Name [Name] deriving (Eq, Show)

pattern ArgSpec :: Span -> Bool -> Name -> ArgSpec
pattern ArgSpec position implicit name <- Argument position implicit name _ where
    ArgSpec position implicit name = Argument position implicit name []

data SearchItem = SearchTerm Term | SearchName String deriving (Eq, Show)

data SearchScope = Everywhere | Inside [Name] | Outside [Name] deriving (Eq, Show)

-- The name argument is a surface identifier before registration and a fixed
-- global identity thereafter. Slot numbers in ScopedSlot count slots from 1.
data PatternEntry = NativePattern | CurrentPattern | OtherPattern (Maybe String) deriving (Eq, Ord, Read, Show)

patternEntry :: Maybe String -> PatternEntry -> Maybe String
patternEntry _ NativePattern = Nothing
patternEntry current CurrentPattern = current
patternEntry _ (OtherPattern target) = target

data RulePart = Literal String | TermSlot | BinderSlot | NameSlot | ScopedSlot Int | TacticSlot
    | AliasHead String | AliasArg (Maybe String)
    | EntryRoot String | EntrySlot (Maybe String) (Maybe Integer)
    | AsNameSlot Bool (Maybe String) (Maybe Integer)
    | PatternSlot PatternEntry Bool (Maybe Integer) | TokenSlot String | LevelSlot Integer | RepeatSlot String RulePart deriving (Eq, Ord, Read, Show)

repeatOperand :: RulePart -> Bool
repeatOperand TermSlot = True
repeatOperand LevelSlot {} = True
repeatOperand EntrySlot {} = True
repeatOperand BinderSlot = True
repeatOperand (TokenSlot "closed binder") = True
repeatOperand _ = False

-- A source spelling is resolved once when the rule is declared. Each entry
-- in the stored production refers to the module that declared that entry.
mapRuleEntry :: (String -> String) -> RulePart -> RulePart
mapRuleEntry f (RepeatSlot separator item) = RepeatSlot separator (mapRuleEntry f item)
mapRuleEntry f (EntryRoot name) = EntryRoot (f name)
mapRuleEntry f (PatternSlot (OtherPattern entry) strict n) = PatternSlot (OtherPattern (fmap f entry)) strict n
mapRuleEntry f (AsNameSlot strict entry n) = AsNameSlot strict (fmap f entry) n
mapRuleEntry f (EntrySlot entry n) = EntrySlot (fmap f entry) n
mapRuleEntry _ part = part

-- A leading EntryRoot selects the production table; it does not consume a token or bind a variable.
ruleEntry :: [RulePart] -> (Maybe String, [RulePart])
ruleEntry (EntryRoot name : parts) = (Just name, parts)
ruleEntry parts = (Nothing, parts)

data TemplatePattern a = AnyPattern | VariablePattern String | ConstructorPattern Bool a [String]
    deriving (Eq, Ord, Read, Show, Functor, Foldable, Traversable)

data TemplateBranch a = TemplateBranch (TemplatePattern a) (Template a)
    deriving (Eq, Ord, Read, Show, Functor, Foldable, Traversable)

data TemplateLevel = UNumber Integer | UNamed String | UHole
    | UOffset TemplateLevel Integer | UMaximum TemplateLevel TemplateLevel
    deriving (Eq, Ord, Read, Show)

data TemplateFunction a = TemplateFunction String [(Bool, [String], Maybe (Template a))] (Maybe String) (Template a) (Template a)
    deriving (Eq, Ord, Read, Show, Functor, Foldable, Traversable)

data Template a
    = TReference Bool a
    | TVariable String
    | TApply (Template a) (Template a)
    | TAbstraction Bool Bool String (Maybe (Template a)) (Template a)
    | TLet String (Maybe (Template a)) (Template a) (Template a)
    | TArrow (Template a) (Template a)
    | TCast (Template a) (Template a)
    | TSort String
    | TNumber Integer
    | TBlockName Bool String
    | TProjection (Template a) a
    | TCase (Template a) (Maybe String) (Maybe (TemplatePattern a)) (Maybe (Template a)) [TemplateBranch a]
    | TFix [TemplateFunction a] (Maybe String)
    | TInstance Bool a [TemplateLevel]
    | TUniverse TemplateLevel
    | TSlotScopes [(String, [String])] (Template a)
    | TFormat String (Template a)
    | TRecursion (Template a)
    deriving (Eq, Ord, Read, Show, Functor, Foldable, Traversable)

data Usage = BothWays | ParsingOnly | PrintingOnly | ReservedSyntax deriving (Eq, Ord, Read, Show)
data RuleTarget a = TermTarget a | TacticTarget String
    | RocqTarget (Maybe String) [String] Usage (Template a) deriving (Eq, Ord, Read, Show)

data SyntaxLocality = DefaultSyntax | LocalSyntax | GlobalSyntax deriving (Eq, Show)

data ScopeClass a = SortClass | FunClass | ReferenceClass a
    deriving (Eq, Ord, Read, Show, Functor, Foldable, Traversable)

data ScopePlacement = ReplaceScopes | AddTop | AddBottom deriving (Eq, Ord, Read, Show)

data NotationSelector = PatternSelector String | AliasSelector String | EveryNotation deriving (Eq, Ord, Read, Show)

data Activation = Activation Bool Usage Bool NotationSelector (Maybe String) (Maybe String) deriving (Eq, Ord, Read, Show)

activationText :: [String] -> Activation -> String
activationText interpretation (Activation enabled mode many selector scope entry) = unwords (command ++ destination ++ interpretation ++ opts ++ owner) ++ "." where
    command = [if enabled then "Enable" else "Disable","Notation"]
    destination = case selector of { PatternSelector pat -> [quoted pat]; AliasSelector n -> [n]; EveryNotation -> [] }
    fields = ["all" | many] ++ ["only parsing" | mode == ParsingOnly] ++ ["only printing" | mode == PrintingOnly] ++ maybe [] (\e -> [if null e then "in constr" else "in custom " ++ e]) entry
    opts = ["(" ++ foldr1 (\a b -> a ++ ", " ++ b) fields ++ ")" | not (null fields)]
    owner = maybe [] (\n -> [":",if null n then "no scope" else n]) scope

data ScopeAction a = DeclareCustomEntry String | DeclareScope String | DelimitScope String String
    | OpenScope String | CloseScope String | UndelimitScope String
    | ToggleNotation Activation | ToggleInterpretation Activation [String] (Template a)
    | BindScope String ScopePlacement [ScopeClass a] deriving (Eq, Ord, Read, Show, Functor, Foldable, Traversable)

-- Rebuild declaration-time argument scope policies in explicit module text.
-- A public step consumes one event of the module's exported grammar history.
data SyntaxStep a = PublicSyntax | ScopeLookup a | PrivateScope (ScopeAction a) | ArgumentStep Bool a [Bool] (Maybe [[String]]) | SectionStep a Int [Bool] [[String]]
    deriving (Eq, Show, Functor, Foldable, Traversable)

data SyntaxRule a = SyntaxRule [RulePart] Integer String (RuleTarget a) deriving (Eq, Ord, Read, Show)

data Command
    = CDefinition Span String Name [Binder] Term Term
    | CAxiom Span Name Term
    | CCheck Span Term
    | CCompute Span Term
    | CSearch Span [(Bool, SearchItem)] SearchScope
    | CPrint Span Name
    | CPrintAssumptions Span Name
    | CInductive Span [IndBody]
    | CFixpoint Span [FixBody]
    | CSetArguments Span SyntaxLocality Name [ArgSpec] [Name]
    | CInfix Span Name Name Integer (Maybe Name)
    | CNotation Span Bool (SyntaxRule Name)
    | CRocqNotation Span SyntaxLocality [RulePart] Integer String (Maybe String) [String] Usage (Maybe String) Term
    | CWhere Span Command [Command]
    | CScope Span SyntaxLocality (ScopeAction Name)
    | CSelectNotation Span SyntaxLocality Activation [String] Term
    | CNumerals Span Name Name
    | CImport Span Name
    | CSection Span Name
    | CContext Span [Binder]
    | CEnd Span Name
    | CUniverses Span (Maybe UniverseDecl) Command
    | CTemplate Span Command
    | CPrimitive Span Bool [Name] Command
    | COrdinaryRecord Span [(Name, Int)] Command
    | CRecordDefinitions Span Bool Command [RecordDefinition]
    deriving (Eq, Show)

-- The usual accessor, its original declaration over all previous real
-- fields, the names of those fields in order, and the count of computed
-- fields bound by leading lets. If an earlier real field has no accessor,
-- its variable remains available while the original definition is checked.
data RecordDefinition = RecordDefinition Command Command [Name] Int deriving (Eq, Show)

pattern CArguments :: Span -> Name -> [ArgSpec] -> [Name] -> Command
pattern CArguments pos name args opts <- CSetArguments pos _ name args opts where
    CArguments pos name args opts = CSetArguments pos DefaultSyntax name args opts

commandSpan :: Command -> Span
commandSpan command = case command of
    CDefinition location _ _ _ _ _ -> location
    CAxiom location _ _ -> location
    CCheck location _ -> location
    CCompute location _ -> location
    CSearch location _ _ -> location
    CPrint location _ -> location
    CPrintAssumptions location _ -> location
    CInductive location _ -> location
    CFixpoint location _ -> location
    CArguments location _ _ _ -> location
    CInfix location _ _ _ _ -> location
    CNotation location _ _ -> location
    CRocqNotation location _ _ _ _ _ _ _ _ _ -> location
    CWhere location _ _ -> location
    CSelectNotation location _ _ _ _ -> location
    CScope location _ _ -> location
    CNumerals location _ _ -> location
    CImport location _ -> location
    CSection location _ -> location
    CContext location _ -> location
    CEnd location _ -> location
    CUniverses location _ _ -> location
    CTemplate location _ -> location
    CPrimitive location _ _ _ -> location
    COrdinaryRecord location _ _ -> location
    CRecordDefinitions location _ _ _ -> location

commandKind :: Command -> String
commandKind command = case command of
    CDefinition _ kind _ _ _ _ -> kind
    CAxiom {} -> "Axiom"
    CCheck {} -> "Check"
    CCompute {} -> "Compute"
    CSearch {} -> "Search"
    CPrint {} -> "Print"
    CPrintAssumptions {} -> "Print Assumptions"
    CInductive {} -> "Inductive"
    CFixpoint {} -> "Fixpoint"
    CArguments {} -> "Arguments"
    CInfix {} -> "Infix"
    CNotation {} -> "Notation"
    CRocqNotation {} -> "Notation"
    CWhere _ cmd _ -> commandKind cmd
    CSelectNotation {} -> "Notation"
    CScope {} -> "Scope"
    CNumerals {} -> "Numerals"
    CImport {} -> "Import"
    CSection {} -> "Section"
    CContext {} -> "Context"
    CEnd {} -> "End"
    CUniverses _ _ inner -> "Polymorphic " ++ commandKind inner
    CTemplate _ inner -> commandKind inner
    CPrimitive {} -> "Record"
    COrdinaryRecord {} -> "Record"
    CRecordDefinitions _ _ inner _ -> commandKind inner

data FrontError
    = FrontError
        { frontSpan :: Span
        , frontKind :: String
        , frontCode :: String
        , frontText :: String
        }
    deriving (Eq, Show)

data Token
    = Token
        { tokenSpan :: Span
        , tokenKind :: String
        , tokenText :: String
        }
    deriving (Eq, Show)

tokenName :: Token -> Name
tokenName token = Name (tokenSpan token) (tokenText token)

application :: Term -> Term -> Term
application function argument = Term (termSpan function <> termSpan argument) (SApp function argument)

arrowTo :: Term -> Term -> Term
arrowTo domain body = Term (termSpan domain <> termSpan body) (SArrow domain body)

castTo :: Term -> Term -> Term
castTo value annotation = Term (termSpan value <> termSpan annotation) (SAnnotation value annotation)

-- The type is a full term. When operators precede the colon, only the
-- current notation environment can say which of their operands is cast.
castOperators :: (Term, [(Name, Term)]) -> Span -> Term -> Term
castOperators (first, []) _ annotation = castTo first annotation
castOperators (first, reversed) colon annotation = operators (first, (Name colon ":", annotation) : reversed)

-- A `let` that writes no type and whose value is a cast takes the type of
-- that cast, and its value is the term of the cast: `let x := (t : T) in u`
-- is `let x : T := t in u`, as the grammar of Rocq reads it.
letIn :: Name -> Maybe Term -> Term -> Term -> TermForm
letIn name annotation value body = case (annotation, written value) of
    (Nothing, Just (term, typ)) -> SLet name (Just typ) term body
    _ -> SLet name annotation value body
    where
        written term = case termForm term of
            SParen inner -> written inner
            SAnnotation inner typ -> Just (inner, typ)
            _ -> Nothing

-- An operator sequence stays flat, in the order written. The parser collects
-- its operands in reverse.
operators :: (Term, [(Name, Term)]) -> Term
operators (first, reversed) = case reversed of
    [] -> first
    (_, final) : _ -> Term (termSpan first <> termSpan final) (SOperators first (reverse reversed))

-- In a real field's domain the preceding computed fields are local lets.
-- A let may precede some of the real binders now in scope; hide precisely
-- those newer names while reading its original type and value. The indices
-- themselves stay in place. The constructor has one argument per real field.
data RecordField
    = Assumption Name Term
    | Computed Name (Maybe Term) Term
    deriving (Eq, Show)

recordDeclaration :: Bool -> Span -> Name -> Maybe UniverseDecl -> [Binder] -> Maybe Term -> Maybe Name -> [RecordField] -> Command
recordDeclaration nonrecursive at family universes parameters annotation supplied sourceFields
    | null definitions = ordinary
    | otherwise = CRecordDefinitions at nonrecursive ordinary definitions
    where
        fields
            | nonrecursive = map scoped sourceFields
            | otherwise = sourceFields
        scoped (Assumption name domain) = Assumption name (outside domain)
        scoped field@Computed {} = field
        outside expr = Term (termSpan expr) (SWithout family expr)
        constructor = maybe (Name (nameSpan family) ("Build_" ++ nameText family)) id supplied
        arity = maybe (Term (nameSpan family) SInferredType) id annotation
        arguments = concatMap binderVars parameters
        bound depth = [Term (nameSpan arg) (SBound index) | (arg, index) <- zip arguments (reverse [depth .. depth + length arguments - 1])]
        global name args = foldl (\function argument -> Term at (SApp function argument)) (Term (nameSpan name) (SDeclared name)) args
        typ depth = global family (bound depth)
        real = [(name, domain) | Assumption name domain <- fields]
        ordinary = COrdinaryRecord at (assumptions 0 fields) (scheme (CInductive at [IndBody at family parameters arity [Constructor at constructor signature]]))
        -- Each real field's domain starts with this many computed-field lets.
        assumptions _ [] = []
        assumptions count (Computed {} : rest) = assumptions (count + 1) rest
        assumptions count (Assumption name _ : rest) = (name, count) : assumptions count rest
        scheme cmd = maybe cmd (\levels -> CUniverses at (Just levels) cmd) universes
        signature = Term at (SForall (domains 0 [] fields) (typ (length real)))
        domains _ _ [] = []
        domains count preceding (Computed name annotation value : rest) = domains count (preceding ++ [(count, name, annotation, value)]) rest
        domains count preceding (Assumption name domain : rest) = Binder (nameSpan name <> termSpan domain) [name] (Just (locals count preceding domain)) False : domains (count + 1) preceding rest
        locals count preceding expr = foldr local expr (zip [0 ..] preceding) where
            local (depth, (old, given, annotation, value)) body = Term (nameSpan given <> termSpan body) (SLet given (fmap masked annotation) (masked value) body) where
                masked expr
                    | old == count = expr
                    | otherwise = Term (termSpan expr) (SMask depth (count - old) expr)
        -- Computed projections are checked definitions. Bind the preceding
        -- fields in declaration order, using the same lexical context as the
        -- constructor. The extra receiver cannot shadow a source identifier.
        receiver = Binder at [Name at "$record"] (Just (global (recordAlias family) (bound 0))) False
        definitions = derive [] fields
        derive _ [] = []
        derive earlier (field : rest) = named ++ derive (earlier ++ [field]) rest where
            named = case field of
                Assumption {} -> []
                Computed name annotation value -> [RecordDefinition accessor original assumed (length computed)] where
                    definition binders wrap = scheme (CDefinition at "Definition" name binders (maybe (Term (nameSpan name) SHole) wrap annotation) (wrap value))
                    accessor = definition (parameters ++ [receiver]) surrounded
                    original = definition (parameters ++ [receiver] ++ domains 0 [] earlier) (locals (length assumed) computed)
                    assumed = [given | Assumption given _ <- earlier]
                    computed = [(length [() | Assumption {} <- take i earlier], given, typ, term) | (i, Computed given typ term) <- zip [0 ..] earlier]
            surrounded expr = foldr bind expr (zip [0 ..] earlier)
            bind (depth, previous) body = case previous of
                Assumption name domain -> local name (Just domain) (global (recordAlias name) (bound (depth + 1) ++ [Term at (SBound depth)]))
                Computed name annotation value -> local name annotation value
                where
                    local name annotation value = Term (nameSpan name <> termSpan body) (SLet name annotation value body)

-- A derived accessor uses these private bindings for the field names it
-- generates. Source names also see the family and the earlier local fields.
recordAlias :: Name -> Name
recordAlias name = name { nameText = "$record." ++ nameText name }

maskLocals :: (a -> a) -> Int -> Int -> [a] -> [a]
maskLocals hide prefix count scope = kept ++ map hide hidden ++ rest where
    (kept, tail') = splitAt prefix scope
    (hidden, rest) = splitAt count tail'
