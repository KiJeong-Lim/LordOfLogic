{-# LANGUAGE PatternSynonyms #-}
module LoL.Object where

import Control.Monad (foldM, unless)
import Data.Char (isDigit, isSpace)
import Data.List (sort)
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.Word (Word8)
import LoL.Core
import qualified LoL.Env as Env
import qualified LoL.Front.Fixity as Fixity
import qualified LoL.Front.Notation as Notation
import LoL.Front.Syntax (SyntaxStep (..), RulePart (..), repeatOperand, PatternEntry (..), RuleTarget (..), Span (..), SyntaxRule (..), Template (..), TemplateLevel (..), TemplatePattern (..), TemplateBranch (..), TemplateFunction (..), Usage (..), ScopeAction (..), Activation (..), NotationSelector (..), ScopeClass (..), ScopePlacement (..))
import LoL.Hol.Session (Kernel, Limits)
import qualified LoL.Pretty as Pretty
import qualified Z.Hash as Hash

-- Only explicit syntax crosses this boundary. No verdict, oracle cache or
-- inductive Info is saved; loading always goes through Env.declare again.
data ObjectFile
    = ObjectData
        { objectModule  :: String
        , objectImports :: [(String, String)]
        , objectEntries :: [StoredDecl]
        , objectOffsets :: [Int]
        , objectSyntax  :: Wire
        }
    deriving (Eq, Show)

-- In v3–v6 every direct import precedes the first declaration.
pattern ObjectFile :: String -> [(String, String)] -> [StoredDecl] -> Wire -> ObjectFile
pattern ObjectFile name imports entries syntax <- ObjectData name imports entries _ syntax where
    ObjectFile name imports entries syntax = ObjectData name imports entries [] syntax

-- Number of local declarations preceding each import in the source.
-- Keep the canonical encoding of modules whose imports are all at the top.
withImportOffsets :: [Int] -> ObjectFile -> ObjectFile
withImportOffsets offsets object = object { objectOffsets = if any (> 0) offsets then offsets else [] }

-- Partition declarations at the points where additional imports enter scope.
importGroups :: ObjectFile -> [a] -> [([String], [a])]
importGroups object = groups 0 [] positions where
    positions = zip (objectOffsets object ++ repeat 0) (map fst (objectImports object))
    groups _ names [] entries = [(names, entries)]
    groups start names rest@((offset, _) : _) entries =
        [(names, before) | not (null names && null before)] ++ groups offset (map snd same) later after
        where
            (same, later) = span ((== offset) . fst) rest
            (before, after) = splitAt (offset - start) entries

data StoredDecl
    = StoredDecl
        { storedName         :: String
        , storedForm         :: Wire
        , storedDependencies :: [String]
        }
    deriving (Eq, Show)

data Wire
    = Node [Wire]
    | Word String
    | Text String
    | Number Integer
    deriving (Eq, Show)

data ObjectFailure
    = ObjectFormat String
    | ObjectRejected String Env.Refusal Env.Env
    deriving (Eq, Show)

tag :: String -> [Wire] -> Wire
tag name parts = Node (Word name : parts)

qualified :: String -> Bool
qualified = Pretty.qualified

localName :: String -> Bool
localName = Pretty.identifier

require :: Bool -> String -> Either String ()
require condition message = unless condition (Left message)

naturalInt :: Integer -> Either String Int
naturalInt value = do
    require (value >= 0 && value <= toInteger (maxBound :: Int)) "an object index is outside the Int range"
    return (fromInteger value)

-- The limits bound parsing work, not the mathematical universe hierarchy.
-- Integers are read as Integer; machine indices are range checked separately.
objectTextLimit :: Int
objectTextLimit = 16 * 1024 * 1024

parseWire :: String -> Either String Wire
parseWire input = do
    require (null (drop objectTextLimit input)) ("object text exceeds " ++ show objectTextLimit ++ " characters")
    frames <- walk 0 0 [[]] input
    case frames of
        [[result]] -> Right result
        _ -> Left "the object must contain exactly one expression"
    where
        walk :: Int -> Int -> [[Wire]] -> String -> Either String [[Wire]]
        walk depth count frames source
            | count > 1000000 = Left "object text exceeds one million nodes"
            | otherwise = case dropWhile isSpace source of
                [] -> if depth == 0 then Right frames else Left "unterminated object expression"
                '(' : rest -> do
                    let nested = depth + nesting (head frames)
                    require (nested <= 8192) "object nesting exceeds 8192 levels"
                    walk nested (count + 1) ([] : frames) rest
                ')' : rest -> case frames of
                    current : parent : older -> walk (depth - nesting parent) count ((Node (reverse current) : parent) : older) rest
                    _ -> Left "unexpected closing parenthesis in object"
                text@('"' : _) -> case reads text :: [(String, String)] of
                    [(value, rest)] -> add depth count frames (Text value) rest
                    _ -> Left "invalid object string"
                text -> do
                    let (atom, rest) = span (\c -> not (isSpace c) && c /= '(' && c /= ')' && c /= '"') text
                    require (not (null atom)) "invalid object token"
                    value <- if all isDigit atom || (head atom == '-' && length atom > 1 && all isDigit (tail atom)) then
                        case reads atom :: [(Integer, String)] of
                            [(number, "")] -> Right (Number number)
                            _ -> Left "invalid object integer"
                    else Right (Word atom)
                    add depth count frames value rest
        -- Count an application's argument spine as a sequence. The completed
        -- function can itself take implicit parameters. Its nesting has already
        -- been checked. The whole sequence still consumes the node budget.
        nesting [Node _, Word "app"] = 0
        nesting _ = 1
        add depth count (current : older) value rest = walk depth (count + 1) ((value : current) : older) rest
        add _ _ [] _ _ = Left "invalid object parser state"

renderWire :: Wire -> ShowS
renderWire wire
    = case wire of
        Node parts -> showChar '(' . sequenceParts parts . showChar ')'
        Word word -> showString word
        Text text -> shows text
        Number number -> shows number
    where
        sequenceParts [] = id
        sequenceParts [part] = renderWire part
        sequenceParts (part : rest) = renderWire part . showChar ' ' . sequenceParts rest

-- A file without reduction metadata has exactly its v3 encoding and digest.
syntaxVersion :: Wire -> Integer
syntaxVersion (Node (Word "syntax" : entries))
    | any v1 entries = 8
    | any notation entries = 6
    | any never entries = 4
    where
        v1 (Node (Word k : more)) = k `elem` ["scope", "syntax-schedule", "argument-scopes", "default-scopes", "bind-scope", "activate", "activate-rhs", "custom-entry", "delimiter", "undelimit-scope", "open-scope", "close-scope", "rocq"] || any v1 more
        v1 _ = False
        notation (Node (Word "notation" : _)) = True
        notation _ = False
        never (Node (Word "simpl-never" : _)) = True
        never _ = False
syntaxVersion _ = 3

-- Old modules keep their exact encoding and dependency pins. An object that
-- only consumes a projected field also needs the new term vocabulary.
objectVersion :: Wire -> [Wire] -> Integer
objectVersion syntax declarations
    | syntaxVersion syntax >= 6 = syntaxVersion syntax
    | beta syntax || any beta declarations = 5
    | otherwise = syntaxVersion syntax
    where
        beta (Node (Word name : args)) = name `elem` ["family-beta", "proj", "pfield", "projection-parameters", "template-level"] || any beta args
        beta (Node args) = any beta args
        beta _ = False

encodeObject :: ObjectFile -> String
encodeObject object = renderWire wire "\n" where
    version = max (if null (objectOffsets object) then 3 else 7) (objectVersion (objectSyntax object) (map storedForm (objectEntries object)))
    pin (name, digest) offset = tag "import" ([Text name, Text digest] ++ [Number (toInteger offset) | version >= 7])
    wire = tag "LoLObject" [Number version, Text (objectModule object), tag "imports" (zipWith pin (objectImports object) (objectOffsets object ++ repeat 0)), tag "declarations" (map entry (objectEntries object)), objectSyntax object]
    entry stored = tag "entry" [Text (storedName stored), storedForm stored, tag "dependencies" (map Text (storedDependencies stored))]

decodeObject :: String -> Either String ObjectFile
decodeObject source = do
    wire <- parseWire source
    case wire of
        Node [Word "LoLObject", Number version, Text name, Node (Word "imports" : imported), Node (Word "declarations" : entries), syntax]
            | version == 7 && objectVersion syntax entries < 8 || version == objectVersion syntax entries -> do
                require (qualified name) "invalid object module name"
                pins <- mapM (dependency version) imported
                let (imports, offsets) = unzip pins
                require ((version /= 7 || any (> 0) offsets) && and (zipWith (<=) offsets (drop 1 offsets)) && all (<= length entries) offsets) "invalid import positions in object"
                require (validImports name imports) "invalid or repeated object import"
                declarations <- mapM entry entries
                return (withImportOffsets offsets (ObjectFile name imports declarations syntax))
        Node (Word "LoLObject" : Number version : _)
            | version `elem` [3, 4, 5, 6, 7, 8] -> Left ("invalid LoL object version " ++ show version ++ " structure")
        Node (Word "LoLObject" : Number 2 : _) -> Left "legacy LoL object format; recompile the source"
        Node (Word "LoLObject" : Number 1 : _) -> Left "legacy LoL object format; recompile the source"
        Node (Word "LoLBundle" : _) -> Left "legacy LoL bundle format; recompile the source"
        Node (Word "LoLObject" : Number _ : _) -> Left "unsupported LoL object version; recompile the source"
        _ -> Left "invalid LoL object header"
    where
        string (Text text) = Right text
        string _ = Left "expected an object name"
        dependency version (Node [Word "import", Text name, Text digest, Number offset]) | version >= 7 = (,) (name, digest) <$> naturalInt offset
        dependency version (Node [Word "import", Text name, Text digest])
            | version < 7 = Right ((name, digest), 0)
        dependency _ _ = Left "expected an object import with its content hash"
        entry (Node [Word "entry", Text name, form, Node (Word "dependencies" : uses)]) = do
            require (localName name) "invalid local declaration name in object"
            dependencies <- mapM string uses
            require (all qualified dependencies && strictlyIncreasing dependencies) "object dependencies must be distinct sorted names"
            return (StoredDecl name form dependencies)
        entry _ = Left "invalid object declaration"

validFingerprint :: String -> Bool
validFingerprint value = length value == 64 && all (`elem` "0123456789abcdef") value

strictlyIncreasing :: Ord a => [a] -> Bool
strictlyIncreasing xs = and (zipWith (<) xs (drop 1 xs))

validImports :: String -> [(String, String)] -> Bool
validImports name imports = all (\(given, digest) -> qualified given && validFingerprint digest) imports && length names == Set.size (Set.fromList names) && name `notElem` names where
    names = map fst imports

-- A content identity, never evidence that a declaration was checked. The
-- canonical wire includes opaque bodies, syntax and direct dependency pins.
fingerprint :: ObjectFile -> String
fingerprint = sha256 . utf8 . encodeObject

-- These names remain available to object-format clients; Hol's program cache
-- uses the shared utility without depending on any LoL module.
utf8 :: String -> [Word8]
utf8 = Hash.utf8

sha256 :: [Word8] -> String
sha256 = Hash.sha256

globalNames :: Env.Env -> Map.Map Global String
globalNames env = Map.fromList [(global, name) | (identity, entry) <- Map.toAscList (Env.envDecls env), (name, global) <- Env.declGlobals identity (Env.entryName entry) (Env.entryDecl entry)]

captureObject :: String -> [(String, String)] -> [ConstId] -> Env.Env -> Either String ObjectFile
captureObject name imports identities env = captureNamedObject name imports (Map.map ((name ++ ".") ++) (globalNames env)) identities env

ownedArguments :: Set.Set Global -> Env.Syntax -> Env.Syntax -> Env.Syntax
ownedArguments own source exported = exported { Env.syntaxArgPrefixes = Map.restrictKeys (Env.syntaxArgPrefixes source) own, Env.syntaxDefaults = Map.restrictKeys (Env.syntaxDefaults source) own, Env.syntaxArgScopes = Map.restrictKeys (Env.syntaxArgScopes source) own, Env.syntaxArguments = Map.restrictKeys (Env.syntaxArguments source) own, Env.syntaxNever = Set.intersection own (Env.syntaxNever source), Env.syntaxProjectionParameters = Map.restrictKeys (Env.syntaxProjectionParameters source) own }

captureNamedObject :: String -> [(String, String)] -> Map.Map Global String -> [ConstId] -> Env.Env -> Either String ObjectFile
captureNamedObject name imports names identities env = do
    require (qualified name) "invalid module name while saving object"
    require (validImports name imports) "invalid or repeated object import"
    require (strictlyIncreasing identities) "object declarations are not in dependency order"
    entries <- mapM stored identities
    let own = Set.fromList [global | identity <- identities, Just entry <- [Map.lookup identity (Env.envDecls env)], (_, global) <- Env.declGlobals identity (Env.entryName entry) (Env.entryDecl entry)]
        syntax = ownedArguments own (Env.envSyntax env) (Env.envSyntax env)
    metadata <- saveSyntax names syntax
    return (ObjectFile name imports entries metadata)
    where
        saveOwner (Number owner) = named names (GlobalInd owner 0)
        saveOwner _ = Left "invalid internal template universe owner"
        stored identity = do
            entry <- maybe (Left "an object declaration is absent from its environment") Right (Map.lookup identity (Env.envDecls env))
            declaration <- saveDecl names (Env.entryDecl entry)
            form <- universeOwners saveOwner (if Env.entryUniverses entry == emptyUniverses then declaration else tag "scheme" [saveUniverses (Env.entryUniverses entry), declaration])
            let own = Set.fromList [name ++ "." ++ local | (local, _) <- Env.declGlobals identity (Env.entryName entry) (Env.entryDecl entry)]
                uses = Set.toAscList (references form `Set.difference` own)
            return (StoredDecl (Env.entryName entry) form uses)

named :: Map.Map Global String -> Global -> Either String Wire
named names global = maybe (Left ("no object name for " ++ show global)) (Right . Text) (Map.lookup global names)

-- Runtime declaration numbers are local to a loader. The canonical wire
-- always names a template level by its owning family and coordinate.
universeOwners :: (Wire -> Either String Wire) -> Wire -> Either String Wire
universeOwners resolve wire = case wire of
    Node [Word "template-level", owner, slot] -> (\name -> tag "template-level" [name, slot]) <$> resolve owner
    Node children -> Node <$> traverse (universeOwners resolve) children
    _ -> Right wire

saveLevel :: Level -> Wire
saveLevel level = case level of
    Closed number -> Number number
    DefaultLevel owner slot -> tag "template-level" [Number owner, Number (toInteger slot)]
    Parameter index -> tag "parameter" [Number (toInteger index)]
    Successor inner -> tag "successor" [saveLevel inner]
    Maximum left right -> tag "maximum" (map saveLevel [left, right])

loadLevel :: Wire -> Either String Level
loadLevel wire = case wire of
    Number number -> Closed number <$ require (number >= 0) "negative object universe"
    Node [Word "template-level", Number owner, Number slot] -> DefaultLevel owner <$> naturalInt slot
    Node [Word "parameter", Number index] -> Parameter <$> naturalInt index
    Node [Word "successor", inner] -> Successor <$> loadLevel inner
    Node [Word "maximum", left, right] -> Maximum <$> loadLevel left <*> loadLevel right
    _ -> Left "invalid object universe expression"

saveInstance :: UniverseInstance -> [Wire]
saveInstance [] = []
saveInstance instance_ = [tag "instance" (map saveLevel instance_)]

loadInstance :: [Wire] -> Either String UniverseInstance
loadInstance [] = Right []
loadInstance [Node (Word "instance" : levels)] = mapM loadLevel levels
loadInstance _ = Left "invalid object universe instance"

saveUniverses :: UniverseContext -> Wire
saveUniverses context = tag "universes" [tag "names" (map Text (universeNames context)), tag "constraints" (map constraint (universeConstraints context))] where
    constraint (UniverseLe left right) = tag "le" (map saveLevel [left, right])
    constraint (UniverseEq left right) = tag "eq" (map saveLevel [left, right])

loadScheme :: Wire -> Either String (UniverseContext, Wire)
loadScheme (Node [Word "scheme", Node [Word "universes", Node (Word "names" : hints), Node (Word "constraints" : constraints)], declaration]) = do
    names <- mapM hint hints
    relations <- mapM constraint constraints
    return (UniverseContext names relations, declaration)
    where
        hint (Text name) = Right name
        hint _ = Left "invalid object universe binder"
        constraint (Node [Word "le", left, right]) = UniverseLe <$> loadLevel left <*> loadLevel right
        constraint (Node [Word "eq", left, right]) = UniverseEq <$> loadLevel left <*> loadLevel right
        constraint _ = Left "invalid object universe constraint"
loadScheme (Node (Word "scheme" : _)) = Left "invalid object universe scheme"
loadScheme declaration = Right (emptyUniverses, declaration)

saveTerm :: Map.Map Global String -> Term -> Either String Wire
saveTerm names term
    = case term of
        Prop -> Right (tag "prop" [])
        Type level -> Right (tag "type" [saveLevel level])
        Cst c instance_ -> tag "const" . (: saveInstance instance_) <$> named names (GlobalCst c)
        Ind b i instance_ -> tag "ind" . (: saveInstance instance_) <$> named names (GlobalInd b i)
        Con b i j instance_ -> tag "con" . (: saveInstance instance_) <$> named names (GlobalCon b i j)
        PField b i us -> tag "pfield" . (: saveInstance us) <$> named names (GlobalProj b i)
        Proj b i term' -> do
            field <- named names (GlobalProj b i)
            receiver <- saveTerm names term'
            return (tag "proj" [field, receiver])
        Var index -> Right (tag "var" [Number (toInteger index)])
        Pi hint a b -> binary "pi" hint a b
        Lam hint a b -> binary "lam" hint a b
        Let hint value a body -> tag "let" . (Text hint :) <$> mapM (saveTerm names) [value, a, body]
        Cast value a -> tag "cast" <$> mapM (saveTerm names) [value, a]
        App function argument -> tag "app" <$> mapM (saveTerm names) [function, argument]
        Case block family instance_ parameters hints predicate subject branches -> do
            familyName <- named names (GlobalInd block family)
            values <- mapM (saveTerm names) parameters
            result <- saveTerm names predicate
            argument <- saveTerm names subject
            cases <- mapM (\(bound, body) -> tag "branch" . (tag "binders" (map Text bound) :) . pure <$> saveTerm names body) branches
            return (tag "case" ([familyName, Node values, tag "binders" (map Text hints), result, argument, Node cases] ++ saveInstance instance_))
        Fix selected functions -> tag "fix" . (Number (toInteger selected) :) <$> mapM saveFunction functions
        Hole _ -> Left "an object cannot contain an unresolved hole"
    where
        binary constructor hint a b = tag constructor . (Text hint :) <$> mapM (saveTerm names) [a, b]
        saveFunction function = tag "function" . ([Text (functionName function), Number (toInteger (functionArgN function))] ++) <$> mapM (saveTerm names) [functionType function, functionBody function]

saveDecl :: Map.Map Global String -> Env.Decl -> Either String Wire
saveDecl names declaration
    = case declaration of
        Env.Axiom a -> tag "axiom" . pure <$> saveTerm names a
        Env.Definition a t -> tag "definition" <$> mapM (saveTerm names) [a, t]
        Env.Theorem a t -> tag "theorem" <$> mapM (saveTerm names) [a, t]
        Env.Inductive parameters families -> tag "inductive" . (Number (toInteger parameters) :) <$> mapM family families
    where
        family item = do
            arity <- saveTerm names (Env.familyType item)
            constructors <- mapM (\(name, term) -> tag "constructor" . (Text name :) . pure <$> saveTerm names term) (Env.familyCons item)
            let body = arity : constructors
                name = Text (Env.familyName item)
                mode = Word (if Env.familyTemplate item then "template" else "full")
            case Env.familyRecord item of
                Nothing
                    | not (Env.familyTemplate item) -> return (tag "family" (name : body))
                    | otherwise -> return (tag "family-beta" (name : mode : tag "ordinary" [] : body))
                Just info -> do
                    let fields = tag (if Env.recordEta info then "record" else "recursive-record") (map Text (Env.recordFields info))
                    return (tag "family-beta" (name : mode : fields : body))

familyWire :: Wire -> Either String (String, Bool, Maybe Env.RecordInfo, Wire, [Wire])
familyWire (Node (Word "family" : Text name : arity : constructors)) =
    Right (name, False, Nothing, arity, constructors)
familyWire (Node (Word "family-beta" : Text name : Word mode : Node (Word form : fields) : arity : constructors)) = do
    require (mode `elem` ["full", "template"]) "invalid universe mode in object family"
    record <- case (form, fields) of
        ("ordinary", []) -> Nothing <$ require (mode == "template") "redundant object family attributes"
        _ -> do
            require (form `elem` ["record", "recursive-record"]) "invalid object record kind"
            fieldNames <- mapM field fields
            return (Just (Env.RecordInfo (form == "record") fieldNames))
    return (name, mode == "template", record, arity, constructors)
    where
        field (Text value)
            | localName value = Right value
        field _ = Left "invalid object projection name"
familyWire _ = Left "invalid object family"

references :: Wire -> Set.Set String
references wire
    = case wire of
        Node (Word kind : Text name : rest)
            | kind `elem` ["const", "ind", "con", "case", "pfield", "proj", "template-level"] -> Set.insert name (Set.unions (map references rest))
        Node parts -> Set.unions (map references parts)
        _ -> Set.empty

loadTerm :: Map.Map String Global -> Wire -> Either String Term
loadTerm names wire
    = case wire of
        Node [Word "prop"] -> Right Prop
        Node [Word "type", level] -> Type <$> loadLevel level
        Node (Word "const" : Text name : instance_) -> reference name asConstant <*> loadInstance instance_
        Node (Word "ind" : Text name : instance_) -> reference name asInductive <*> loadInstance instance_
        Node (Word "con" : Text name : instance_) -> reference name asConstructor <*> loadInstance instance_
        Node [Word "proj", Text name, receiver] -> reference name (projection Proj) <*> loadTerm names receiver
        Node (Word "pfield" : Text name : levels) -> reference name (projection PField) <*> loadInstance levels
        Node [Word "var", Number index] -> Var <$> naturalInt index
        Node [Word "pi", Text hint, a, b] -> Pi hint <$> loadTerm names a <*> loadTerm names b
        Node [Word "lam", Text hint, a, b] -> Lam hint <$> loadTerm names a <*> loadTerm names b
        Node [Word "let", Text hint, value, a, body] -> Let hint <$> loadTerm names value <*> loadTerm names a <*> loadTerm names body
        Node [Word "cast", value, a] -> Cast <$> loadTerm names value <*> loadTerm names a
        Node [Word "app", function, argument] -> App <$> loadTerm names function <*> loadTerm names argument
        Node (Word "case" : Text name : Node parameters : bound : predicate : subject : Node branches : instance_) -> do
            global <- maybe (Left ("unknown object family " ++ name)) Right (Map.lookup name names)
            (block, family) <- case global of
                GlobalInd b i -> Right (b, i)
                _ -> Left ("object case references a non-family: " ++ name)
            Case block family <$> loadInstance instance_ <*> mapM (loadTerm names) parameters <*> hints bound <*> loadTerm names predicate <*> loadTerm names subject <*> mapM branch branches
        Node (Word "fix" : Number selected : functions) -> do
            index <- naturalInt selected
            require (index < length functions) "object fix selects an absent function"
            Fix index <$> mapM function functions
        _ -> Left "invalid explicit Core term in object"
    where
        reference name accept = maybe (Left ("unknown or wrongly tagged object reference: " ++ name)) Right (Map.lookup name names >>= accept)
        projection build global = case global of
            GlobalProj b i -> Just (build b i)
            _ -> Nothing
        asConstant global = case global of
            GlobalCst c -> Just (Cst c)
            _ -> Nothing
        asInductive global = case global of
            GlobalInd b i -> Just (Ind b i)
            _ -> Nothing
        asConstructor global = case global of
            GlobalCon b i j -> Just (Con b i j)
            _ -> Nothing
        hints (Node (Word "binders" : values)) = mapM binderText values
        hints _ = Left "invalid object binders"
        binderText value = case value of
            Text hint -> Right hint
            _ -> Left "invalid object binder"
        branch (Node [Word "branch", bound, body]) = (,) <$> hints bound <*> loadTerm names body
        branch _ = Left "invalid object branch"
        function (Node [Word "function", Text hint, Number index, a, body]) = Function hint <$> naturalInt index <*> loadTerm names a <*> loadTerm names body
        function _ = Left "invalid object function"

localGlobals :: ConstId -> String -> Wire -> Either String [(String, Global)]
localGlobals identity name wire
    = case wire of
        Node [Word "scheme", _, inner] -> localGlobals identity name inner
        Node (Word "inductive" : Number _ : families) -> concat <$> sequence [family i item | (i, item) <- zip [0 ..] families]
        Node (Word kind : _)
            | kind `elem` ["axiom", "definition", "theorem"] -> Right [(name, GlobalCst identity)]
        _ -> Left "invalid object declaration kind"
    where
        family i wire' = do
            (name', _, record, _, constructors) <- familyWire wire'
            require (localName name') "invalid object family name"
            cons <- sequence [constructor i j item | (j, item) <- zip [0 ..] constructors]
            let fields = [(field, GlobalProj identity j) | Just info <- [record], (j, field) <- zip [0 ..] (Env.recordFields info)]
            return ((name', GlobalInd identity i) : cons ++ fields)
        constructor i j (Node [Word "constructor", Text name', _]) = (,) name' (GlobalCon identity i j) <$ require (localName name') "invalid object constructor name"
        constructor _ _ _ = Left "invalid object constructor"

loadDecl :: Map.Map String Global -> Wire -> Either String Env.Decl
loadDecl names wire
    = case wire of
        Node [Word "axiom", a] -> Env.Axiom <$> loadTerm names a
        Node [Word "definition", a, t] -> Env.Definition <$> loadTerm names a <*> loadTerm names t
        Node [Word "theorem", a, t] -> Env.Theorem <$> loadTerm names a <*> loadTerm names t
        Node (Word "inductive" : Number parameters : families) -> Env.Inductive <$> naturalInt parameters <*> mapM family families
        _ -> Left "invalid object declaration"
    where
        family wire' = do
            (name, template, record, arity, constructors) <- familyWire wire'
            value <- Env.Family name <$> loadTerm names arity <*> mapM constructor constructors
            return value { Env.familyTemplate = template, Env.familyRecord = record }
        constructor (Node [Word "constructor", Text name, term]) = (,) name <$> loadTerm names term
        constructor _ = Left "invalid object constructor"

replayObject :: Kernel -> Limits -> Env.Env -> ObjectFile -> IO (Either ObjectFailure Env.Env)
replayObject kernel limits initial object
    | null (objectOffsets object) = replayGroups kernel limits initial object (\env _ -> return (Right env))
    | otherwise = return (Left (ObjectFormat "interleaved imports require a module resolver"))

replayGroups :: Kernel -> Limits -> Env.Env -> ObjectFile -> (Env.Env -> [String] -> IO (Either ObjectFailure Env.Env)) -> IO (Either ObjectFailure Env.Env)
replayGroups kernel limits initial object activate = do
    result <- foldM group (Right initial) (importGroups object (objectEntries object))
    case result of
        Left failure -> return (Left failure)
        Right env -> case loadSyntaxWith (objectModule object) (Env.envSyntax env) (Env.envNames env) (objectSyntax object) of
            Left message -> return (Left (ObjectFormat message))
            Right syntax -> do
                let owned = Set.fromList [global | (identity, entry) <- Map.toList (Env.envDecls env), identity >= Env.envFresh initial, (_, global) <- Env.declGlobals identity (Env.entryName entry) (Env.entryDecl entry)]
                let masks = [(global, toInteger (length flags), "Arguments mask") | (global, flags) <- Map.toList (Env.syntaxArguments syntax)]
                    required slots = maximum (0 : [n | (n, []) <- zip [1..] slots])
                    scopeMasks = [(g, required slots, "Arguments scopes") | (g, slots) <- Map.toList (Env.syntaxArgScopes syntax)] ++ [(g, toInteger (length slots), "default argument scopes") | (g, slots) <- Map.toList (Env.syntaxDefaults syntax)]
                    accessors = [(global, toInteger count + 1, "projection receiver") | (global, count) <- Map.toList (Env.syntaxProjectionParameters syntax)]
                    schedule = Env.syntaxSchedule syntax
                    scheduledMasks = [(g, max (toInteger (length fs)) (maybe 0 required slots), "scheduled Arguments") | (_, _, ArgumentStep _ g fs slots) <- schedule] ++ [(g, max (toInteger (length fs)) (required slots), "section Arguments") | (_, _, SectionStep g _ fs slots) <- schedule]
                valid <- validateArguments owned env (masks ++ scopeMasks ++ accessors ++ scheduledMasks)
                return $ do
                    valid
                    unless (all (\(i, d, _) -> i <= length (objectImports object) && d <= length (objectEntries object)) schedule) (Left (ObjectFormat "syntax schedule position outside its module"))
                    unless (Env.syntaxNever syntax `Set.isSubsetOf` owned) (Left (ObjectFormat "simpl never must name a constant of this module"))
                    merged <- either (Left . ObjectFormat . snd) Right (joinSyntax (Env.envSyntax env) syntax)
                    Right (Env.withSyntax merged env)
    where
        group (Left failure) _ = return (Left failure)
        group (Right env) (imports, declarations) = do
            scoped <- if null imports then return (Right env) else activate env imports
            foldM step scoped declarations
        validateArguments _ _ [] = return (Right ())
        validateArguments owned env ((global, required, description) : rest)
            | Set.notMember global owned = return (Left (ObjectFormat "object Arguments metadata may only name this module's declarations"))
            | otherwise = do
                arity <- Env.argumentArity kernel limits env global
                let name = case [given | (given, found) <- Map.toList (Env.envNames env), found == global] of
                        given : _ -> given
                        [] -> show global
                case arity of
                    Left problem -> return (Left (ObjectRejected ("Arguments " ++ name) problem env))
                    Right count
                        | required > toInteger count -> return (Left (ObjectFormat ("object " ++ description ++ " exceeds the arity of " ++ name)))
                        | otherwise -> validateArguments owned env rest
        step (Left failure) _ = return (Left failure)
        step (Right env) stored = case prepare env stored of
            Left message -> return (Left (ObjectFormat message))
            Right (visible, universes, declaration, aliases) -> do
                admitted <- Env.declareWithUniverses kernel limits visible (storedName stored) universes declaration
                return $ case admitted of
                    Left failure -> Left (ObjectRejected (storedName stored) failure visible)
                    Right (_, next) -> Right (Env.withNames (Map.union (Map.fromList aliases) (Env.envNames next)) next)
        loadOwner env (Text name) | Just (GlobalInd owner 0) <- Map.lookup name (Env.envNames env) = Right (Number owner)
        loadOwner _ _ = Left "unknown or invalid template universe owner"
        prepare env stored = do
            require (localName (storedName stored)) "invalid local declaration name in object"
            (universes, form) <- universeOwners (loadOwner env) (storedForm stored) >>= loadScheme
            globals <- localGlobals (Env.envFresh env) (storedName stored) (storedForm stored)
            require (not (null globals) && length globals == Set.size (Set.fromList (map fst globals))) "empty or duplicate object declaration names"
            let canonical = [(objectModule object ++ "." ++ name, global) | (name, global) <- globals]
                own = Set.fromList (map fst canonical)
                dependencies = Set.toAscList (references (storedForm stored) `Set.difference` own)
            require (dependencies == storedDependencies stored) "object dependency names do not match its Core terms"
            require (all (\(name, _) -> Map.notMember name (Env.envNames env)) canonical) "an object redeclares a name in its module"
            let visibleNames = foldr Map.delete (Env.envNames env) (map fst globals)
                local = case form of
                    Node (Word "inductive" : _) -> Map.fromList (canonical ++ globals)
                    _ -> Map.empty
            declaration <- loadDecl (Map.union local visibleNames) form
            require (all (wellScopedUniverses (length (universeNames universes)) 0) (Env.declTerms declaration)) "object Core term has an unbound or invalid index"
            return (Env.withNames visibleNames env, universes, declaration, canonical)

scheduled :: Env.Syntax -> Bool
scheduled syntax = not (Map.null (Env.syntaxDefaults syntax) && Map.null (Env.syntaxArgScopes syntax) && Map.null (Env.syntaxBindings syntax)) || any usesScopes (Env.syntaxSchedule syntax) where
    usesScopes (_, _, ScopeLookup _) = True
    usesScopes (_, _, PrivateScope BindScope {}) = True
    usesScopes (_, _, ArgumentStep _ _ _ (Just _)) = True
    usesScopes _ = False

saveSyntax :: Map.Map Global String -> Env.Syntax -> Either String Wire
saveSyntax names syntax = do
    arguments <- mapM (\(global, flags) -> tag "arguments" . (: map (Word . show) flags) <$> named names global) (Map.toAscList (Env.syntaxArguments syntax))
    infixes <- mapM (\(operator, (global, level, associativity)) -> (\name -> tag "infix" [Text operator, name, Number level, Text associativity]) <$> named names global) (Map.toAscList (Env.syntaxInfix syntax))
    numerals <- case Env.syntaxNumerals syntax of
        Nothing -> Right []
        Just (zero, successor) -> pure . tag "numerals" <$> mapM (named names) [zero, successor]
    never <- mapM (fmap (tag "simpl-never" . pure) . named names) (Set.toAscList (Env.syntaxNever syntax))
    fields <- mapM (\(target, count) -> (\name -> tag "projection-parameters" [name, Number (toInteger count)]) <$> named names target) (Map.toAscList (Env.syntaxProjectionParameters syntax))
    let scopes kind (g, slots) = (\label -> tag kind (label : map (Node . map Text) slots)) <$> named names g
    prefixes <- mapM (\(g, n) -> (\name -> tag "automatic-prefix" [name, Number (toInteger n)]) <$> named names g) (Map.toAscList (Env.syntaxArgPrefixes syntax))
    argScopes <- mapM (scopes "argument-scopes") (Map.toAscList (Env.syntaxArgScopes syntax))
    defaults <- mapM (scopes "default-scopes") (Map.toAscList (Env.syntaxDefaults syntax))
    rules <- mapM save [r | r@(SyntaxRule _ _ _ target) <- sort (Env.syntaxRules syntax), case target of { RocqTarget {} -> False; _ -> True }]
    v1 <- mapM (either scopeWire save) (reverse (Env.syntaxHistory syntax))
    timeline <- if scheduled syntax then mapM saveStep (reverse (Env.syntaxSchedule syntax)) else Right []
    return (tag "syntax" (arguments ++ argScopes ++ prefixes ++ defaults ++ infixes ++ numerals ++ never ++ fields ++ rules ++ v1 ++ [tag "syntax-schedule" timeline | not (null timeline)]))
    where
        saveStep (imports, offset, event) = do
            value <- case event of
                PublicSyntax -> Right (Word "public")
                ScopeLookup g -> tag "scope-lookup" . pure <$> named names g
                PrivateScope op -> tag "private" . pure <$> scopeWire op
                SectionStep g count flags slots -> do
                    n <- named names g
                    Right (tag "section-args" [n, Number (toInteger count), Node (map (Word . show) flags), Node (map (Node . map Text) slots)])
                ArgumentStep local g flags policies -> do
                    n <- named names g
                    Right (tag "args" [Word (show local), n, Node (map (Word . show) flags), Node [Node (map (Node . map Text) slots) | Just slots <- [policies]]])
            Right (Node [Number (toInteger imports), Number (toInteger offset), value])
        scopeWire (BindScope name placement classes) = tag "bind-scope" . (Text name :) . (Word (show placement) :) <$> mapM classWire classes
        scopeWire (ToggleInterpretation setting names' query) = do
            activation <- scopeWire (ToggleNotation setting)
            refs <- traverse (named names) query
            Right (tag "activate-rhs" [activation,Node (map Text names'),writeTemplate refs])
        scopeWire (ToggleNotation (Activation on mode many selector scope entry)) = Right (tag "activate" [Word (show on),Word (show mode),Word (show many),target,key scope,key entry])
            where
                key = maybe (Word "any") Text
                target = case selector of { EveryNotation -> Word "all"; AliasSelector name -> tag "alias" [Text name]; PatternSelector pat -> tag "pattern" [Text pat] }
        scopeWire action = Right $ case action of
            DeclareCustomEntry n -> tag "custom-entry" [Text n]
            DeclareScope n -> tag "scope" [Text n]
            DelimitScope n k -> tag "delimiter" [Text n,Text k]
            OpenScope n -> tag "open-scope" [Text n]
            UndelimitScope n -> tag "undelimit-scope" [Text n]
            CloseScope n -> tag "close-scope" [Text n]
        classWire SortClass = Right (Word "sort")
        classWire FunClass = Right (Word "function")
        classWire (ReferenceClass g) = named names g
        save rule@(SyntaxRule pattern' level direction target) = do
            reference <- case target of
                TermTarget global -> tag "term" . pure <$> named names global
                TacticTarget tactic -> Right (tag "tactic" [Text tactic])
                RocqTarget scope vars usage body -> do
                    refs <- traverse (named names) body
                    Right (tag "rocq" [Text (maybe "" id scope), tag "vars" (map Text vars), Word (show usage), writeTemplate refs])
            (_, Span (row, column) (lastRow, lastColumn)) <- maybe (Left "missing source location for notation") Right (Map.lookup rule (Env.syntaxRuleSites syntax))
            return (tag "notation" [tag "pattern" (map part pattern'), Number level, Text direction, reference, tag "span" (map (Number . toInteger) [row, column, lastRow, lastColumn])])
        part (Literal literal) = Text literal
        part TermSlot = Word "term"
        part (AliasHead n) = tag "alias-head" [Text n]
        part (AliasArg sc) = tag "alias-argument" [Text (maybe "" id sc)]
        part BinderSlot = Word "binder"
        part NameSlot = Word "name"
        part (ScopedSlot slot) = tag "body" [Number (toInteger slot)]
        part (PatternSlot (OtherPattern name) strict level) = tag "as-pattern" [Word (show strict),part (EntrySlot name level)]
        part (PatternSlot mode strict level) = tag "pattern-slot" [Word (show (mode == CurrentPattern)), Word (show strict), Node (map Number (maybe [] pure level))]
        part (TokenSlot k) = tag "token-slot" [Text k]
        part (LevelSlot n) = tag "level" [Number n]
        part (EntryRoot name) = tag "production-entry" [Text name]
        part (AsNameSlot strict name strength) = tag "as-name" [Word (show strict),part (EntrySlot name strength)]
        part (EntrySlot name strength) = tag "argument-entry" [Text (maybe "" id name), Node (maybe [] (pure . Number) strength)]
        part (RepeatSlot sep item)
            | if null sep then item == BinderSlot else item == TermSlot = tag "repeat" [Text sep]
            | otherwise = tag "repeat-of" [Text sep, part item]
        part TacticSlot = Word "tactic"

writeTemplate :: Template Wire -> Wire
writeTemplate expr = case expr of
    TReference explicit name -> tag "global" [Word (show explicit),name]
    TVariable name -> tag "var" [Text name]
    TNumber n -> tag "number" [Number n]
    TSort name -> tag "sort" [Text name]
    TApply f x -> binary "app" f x
    TCast x ty -> binary "cast" x ty
    TArrow a b -> binary "arrow" a b
    TAbstraction prod impl name ty body -> tag "binder" [Word (show prod),Word (show impl),Text name,optional ty,writeTemplate body]
    TLet name ty val body -> tag "let" [Text name,optional ty,writeTemplate val,writeTemplate body]
    TSlotScopes scopes body -> tag "slot-scopes" [Node [Node (Text n : map Text keys) | (n, keys) <- scopes], writeTemplate body]
    TFormat fmt body -> tag "format" [Text fmt,writeTemplate body]
    TBlockName {} -> Word "unresolved-recursive-notation"
    TProjection val field -> tag "project" [writeTemplate val,field]
    TUniverse u -> tag "universe" [level u]
    TInstance e n us -> tag "instance" [Word (show e),n, Node (map level us)]
    TCase v alias family motive bs -> tag "match" [writeTemplate v,opt Text alias,opt patternWire family,optional motive,Node (map branch bs)]
    TFix fs chosen -> tag "fix" [Node (map function fs),opt Text chosen]
    TRecursion body -> tag "iteration" [writeTemplate body]
    where
        opt f = maybe (Word "none") f
        level (UNumber n) = Number n
        level (UNamed n) = Text n
        level UHole = Word "hole"
        level (UOffset u n) = tag "offset" [level u,Number n]
        level (UMaximum a b) = tag "max" [level a,level b]
        patternWire AnyPattern = Word "wildcard"
        patternWire (VariablePattern n) = tag "variable-pattern" [Text n]
        patternWire (ConstructorPattern e n vs) = tag "constructor" [Word (show e),n,Node (map Text vs)]
        branch (TemplateBranch pat b) = Node [patternWire pat,writeTemplate b]
        function (TemplateFunction n bs arg ty rhs) = Node [Text n,Node (map binder bs),opt Text arg,writeTemplate ty,writeTemplate rhs]
        binder (impl,vs,ty) = Node [Word (show impl),Node (map Text vs),optional ty]
        binary name a b = tag name [writeTemplate a,writeTemplate b]
        optional = maybe (Word "none") writeTemplate

readTemplate :: Wire -> Either String (Template String)
readTemplate wire = case wire of
    Node [Word "global", flag, Text name] -> TReference <$> boolean flag <*> pure name
    Node [Word "var", Text name] -> Right (TVariable name)
    Node [Word "number", Number n] | n >= 0 -> Right (TNumber n)
    Node [Word "sort", Text name] -> Right (TSort name)
    Node [Word "app", f, x] -> TApply <$> readTemplate f <*> readTemplate x
    Node [Word "cast", x, ty] -> TCast <$> readTemplate x <*> readTemplate ty
    Node [Word "arrow", a, b] -> TArrow <$> readTemplate a <*> readTemplate b
    Node [Word "binder", prod, impl, Text n, ty, b] -> TAbstraction <$> boolean prod <*> boolean impl <*> pure n <*> optional ty <*> readTemplate b
    Node [Word "let", Text n, ty, v, b] -> TLet n <$> optional ty <*> readTemplate v <*> readTemplate b
    Node [Word "project",v,Text n] -> flip TProjection n <$> readTemplate v
    Node [Word "universe",u] -> TUniverse <$> level u
    Node [Word "instance",e,Text n,Node us] -> TInstance <$> boolean e <*> pure n <*> mapM level us
    Node [Word "match",v,alias,family,motive,Node bs] -> TCase <$> readTemplate v <*> opt label alias <*> opt patternWire family <*> optional motive <*> mapM branch bs
    Node [Word "fix",Node fs,chosen] | not (null fs) -> TFix <$> mapM function fs <*> opt label chosen
    Node [Word "iteration", inner] -> TRecursion <$> readTemplate inner
    _ -> Left "invalid notation interpretation"
    where
        opt _ (Word "none") = Right Nothing
        opt f v = Just <$> f v
        label (Text n) | n == "_" || qualified n = Right n
        label _ = Left "invalid notation identifier"
        level (Number n) | n >= 0 = Right (UNumber n)
        level v@(Text _) = UNamed <$> label v
        level (Word "hole") = Right UHole
        level (Node [Word "offset",u,Number n]) | n >= 0 = flip UOffset n <$> level u
        level (Node [Word "max",a,b]) = UMaximum <$> level a <*> level b
        level _ = Left "invalid notation universe"
        patternWire (Word "wildcard") = Right AnyPattern
        patternWire (Node [Word "variable-pattern", Text n]) = Right (VariablePattern n)
        patternWire (Node [Word "constructor",e,Text n,Node vs]) = ConstructorPattern <$> boolean e <*> pure n <*> mapM label vs
        patternWire _ = Left "invalid notation pattern"
        branch (Node [p,b]) = TemplateBranch <$> patternWire p <*> readTemplate b
        branch _ = Left "invalid notation branch"
        function (Node [n,Node bs,arg,ty,rhs]) = TemplateFunction <$> label n <*> mapM binder bs <*> opt label arg <*> readTemplate ty <*> readTemplate rhs
        function _ = Left "invalid notation fixpoint"
        binder (Node [impl,Node vs,ty]) | not (null vs) = (,,) <$> boolean impl <*> mapM label vs <*> optional ty
        binder _ = Left "invalid notation binder"
        optional (Word "none") = Right Nothing
        optional value = Just <$> readTemplate value
        boolean (Word "True") = Right True
        boolean (Word "False") = Right False
        boolean _ = Left "invalid notation flag"

loadSyntax :: Map.Map String Global -> Wire -> Either String Env.Syntax
loadSyntax = loadSyntaxOf ""

loadSyntaxOf :: String -> Map.Map String Global -> Wire -> Either String Env.Syntax
loadSyntaxOf owner = loadSyntaxWith owner (Env.Syntax Map.empty Map.empty Nothing Set.empty)

loadSyntaxWith :: String -> Env.Syntax -> Map.Map String Global -> Wire -> Either String Env.Syntax
loadSyntaxWith owner imported names wire
    = case wire of
        Node (Word "syntax" : entries) -> do
            let isSchedule (Node (Word "syntax-schedule" : _)) = True
                isSchedule _ = False
            require (not (any isSchedule (drop 1 (reverse entries)))) "syntax schedule must follow the public grammar"
            foldM entry blank entries
        _ -> Left "invalid object syntax metadata"
    where
        blank = (Env.Syntax Map.empty Map.empty Nothing Set.empty) { Env.syntaxOwner = owner }
        own n = if null owner then n else owner ++ "." ++ n
        entryRef syntax n
            | '.' `elem` n = known n
            | Map.member (own n) (Env.syntaxEntries syntax) = Right (own n)
            | _:_:_ <- Notation.entryCandidates (Env.syntaxReader imported) n = Left ("Ambiguous legacy custom entry " ++ n ++ "; recompile the module from source")
            | otherwise = known (Notation.entryPath (Env.syntaxReader imported) n)
            where
                known path
                    | any (Map.member path . Env.syntaxEntries) [syntax, imported] = Right path
                    | otherwise = Left ("Unknown custom entry in object: " ++ n)
        global name = maybe (Left ("unknown object syntax reference: " ++ name)) Right (Map.lookup name names)
        boolean (Word "True") = Right True
        boolean (Word "False") = Right False
        boolean _ = Left "invalid object implicit flag"
        variable (Text n) | localName n = Right n
        variable _ = Left "invalid notation variable"
        part _ (Text literal) = Right (Literal literal)
        part syntax (Node [Word "production-entry", Text name]) | qualified name = EntryRoot <$> entryRef syntax name
        part syntax (Node [Word mode,flag,wire@(Node [Word "argument-entry",_,_])]) | mode `elem` ["as-name","as-pattern"] = do
            strict <- boolean flag
            entry <- part syntax wire
            case entry of
                EntrySlot e n | mode == "as-pattern" -> Right (PatternSlot (OtherPattern e) strict n)
                EntrySlot e n -> Right (AsNameSlot strict e n)
                _ -> Left "invalid notation name entry"
        part syntax (Node [Word "argument-entry", Text name, Node levels]) | null name || qualified name = do
            strength <- case levels of
                [] -> Right Nothing
                [Number n] | Notation.validLevel n -> Right (Just n)
                _ -> Left "invalid custom entry argument level"
            entryId <- if null name then Right Nothing else Just <$> entryRef syntax name
            Right (EntrySlot entryId strength)
        part _ (Word "term") = Right TermSlot
        part _ (Node [Word "alias-head", Text n]) | localName n = Right (AliasHead n)
        part _ (Node [Word "alias-argument", Text n]) | null n || localName n = Right (AliasArg (if null n then Nothing else Just n))
        part _ (Word "binder") = Right BinderSlot
        part _ (Word "name") = Right NameSlot
        part _ (Node [Word "repeat", Text sep]) = Right (RepeatSlot sep (if null sep then BinderSlot else TermSlot))
        part syntax (Node [Word "repeat-of", Text sep, item]) = do
            let atomic = case item of
                    Node (Word kind : _) -> kind `elem` ["level", "argument-entry", "token-slot"]
                    Word kind -> kind `elem` ["term", "binder"]
                    _ -> False
            require atomic "invalid recursive notation entry"
            operand <- part syntax item
            require (repeatOperand operand) "invalid recursive notation operand"
            Right (RepeatSlot sep operand)
        part _ (Node [Word "pattern-slot", as, strict, Node levels]) = do
            strength <- case levels of
                [] -> Right Nothing
                [Number n] | Notation.validLevel n -> Right (Just n)
                _ -> Left "invalid notation pattern level"
            termSlot <- boolean as
            PatternSlot (if termSlot then CurrentPattern else NativePattern) <$> boolean strict <*> pure strength
        part _ (Node [Word "token-slot", Text k]) = Right (TokenSlot k)
        part _ (Node [Word "level", Number n]) = Right (LevelSlot n)
        part _ (Word "tactic") = Right TacticSlot
        part _ (Node [Word "body", Number slot]) = ScopedSlot <$> naturalInt slot
        part _ _ = Left "invalid object notation slot"
        activation syntax (Node [Word "activate",state,Word direction,allMatches,selection,sc,table]) = do
            on <- boolean state
            many <- boolean allMatches
            mode <- case direction of { "BothWays" -> Right BothWays; "ParsingOnly" -> Right ParsingOnly; "PrintingOnly" -> Right PrintingOnly; _ -> Left "invalid activation direction" }
            selector <- case selection of
                Word "all" -> Right EveryNotation
                Node [Word "alias",Text n] | qualified n -> Right (AliasSelector n)
                Node [Word "pattern",Text pat] | not (null pat) && '"' `notElem` pat -> Right (PatternSelector pat)
                _ -> Left "invalid activation selector"
            let optionalName (Word "any") = Right Nothing
                optionalName (Text n) | null n || localName n = Right (Just n)
                optionalName _ = Left "invalid scope or entry"
                optionalEntry (Text n) | not (null n) && qualified n = Just <$> entryRef syntax n
                optionalEntry other = optionalName other
            Activation on mode many selector <$> optionalName sc <*> optionalEntry table
        activation _ _ = Left "invalid notation activation"
        entry syntax (Node (Word "syntax-schedule" : steps)) = do
            require (null (Env.syntaxSchedule syntax) && not (null steps)) "invalid or repeated syntax schedule"
            schedule <- readSteps (Env.syntaxEntries syntax) steps
            let ordered (i, d, _) (j, e, _) = i <= j && d <= e
            require (and (zipWith ordered schedule (drop 1 schedule))) "unordered syntax schedule"
            require (length [() | (_, _, PublicSyntax) <- schedule] == length (Env.syntaxHistory syntax)) "syntax schedule does not cover its public grammar"
            Right syntax { Env.syntaxSchedule = reverse schedule }
            where
                readSteps _ [] = Right []
                readSteps known (Node [Number i, Number n, tag] : more) = do
                    one@(_, _, action) <- (,,) <$> naturalInt i <*> naturalInt n <*> step known tag
                    let next = case action of
                            PrivateScope (DeclareCustomEntry name) -> Map.insert name True known
                            _ -> known
                    (one :) <$> readSteps next more
                readSteps _ _ = Left "invalid syntax schedule step"
                step _ (Word "public") = Right PublicSyntax
                step _ (Node [Word "scope-lookup", Text n]) = ScopeLookup <$> global n
                step known (Node [Word "private", form@(Node (Word tag : _))])
                    | tag `notElem` ["syntax-schedule", "notation"] = do
                    local <- entry (if tag == "custom-entry" then blank else blank { Env.syntaxEntries = known }) form
                    case Env.syntaxHistory local of
                        [Left action] -> Right (PrivateScope action)
                        _ -> Left "invalid local scope event"
                step _ (Node [Word "section-args", Text n, Number k, Node fs, Node ss]) = do
                    count <- naturalInt k
                    slots <- mapM slot ss
                    require (count > 0 && count <= length slots && all null (take count slots)) "invalid discharged argument scope schedule"
                    SectionStep <$> global n <*> pure count <*> mapM boolean fs <*> pure slots
                step _ (Node [Word "args", hidden, Text n, Node fs, Node ps]) = do
                    local <- boolean hidden
                    g <- global n
                    flags <- mapM boolean fs
                    policies <- case ps of
                        [] -> Right Nothing
                        [Node slots] -> Just <$> mapM slot slots
                        _ -> Left "invalid scheduled argument scopes"
                    Right (ArgumentStep local g flags policies)
                step _ _ = Left "invalid syntax schedule event"
                slot (Node keys) = mapM variable keys
                slot _ = Left "invalid argument scope position"
        entry syntax (Node [Word "notation", Node (Word "pattern" : parts), Number level, Text direction, destination, Node [Word "span", Number row, Number col, Number endRow, Number endCol]]) = do
            pattern' <- mapM (part syntax) parts
            target <- case destination of
                Node [Word "term", Text name] -> do
                    require (qualified name && '.' `elem` name) "object notation must refer to a qualified global"
                    TermTarget <$> global name
                Node [Word "rocq", Text sc, Node (Word "vars" : vs), Word use, body] -> do
                    vars <- mapM variable vs
                    usage <- case use of
                        "ReservedSyntax" -> Right ReservedSyntax
                        "BothWays" -> Right BothWays
                        "PrintingOnly" -> Right PrintingOnly
                        "ParsingOnly" -> Right ParsingOnly
                        _ -> Left "invalid notation usage"
                    let scoped (Node [Word "slot-scopes", Node pairs, inner]) = do
                            policies <- mapM slotPolicy pairs
                            let keys = map fst policies
                            require (all (`elem` vars) keys && length keys == Set.size (Set.fromList keys)) "invalid notation slot scope names"
                            TSlotScopes policies <$> readTemplate inner
                        scoped inner = readTemplate inner
                        slotPolicy (Node (n : keys)) | not (null keys) = (,) <$> variable n <*> mapM variable keys
                        slotPolicy _ = Left "invalid scope policy for a notation slot"
                    template <- case body of
                        Node [Word "format", Text fmt, inner] -> TFormat fmt <$> scoped inner
                        _ -> scoped body
                    resolved <- traverse (\n -> if qualified n && '.' `elem` n then global n else Left "unqualified notation reference") template
                    Right (RocqTarget (if null sc then Nothing else Just sc) vars usage resolved)
                Node [Word "tactic", Text tactic] -> Right (TacticTarget tactic)
                _ -> Left "invalid object notation target"
            start <- (,) <$> naturalInt row <*> naturalInt col
            end <- (,) <$> naturalInt endRow <*> naturalInt endCol
            require (minimum [row, col, endRow, endCol] >= 1 && start <= end) "invalid object notation span"
            let rule = SyntaxRule pattern' level direction target
            case target of
                RocqTarget {} -> Right ()
                _ -> require (Map.notMember rule (Env.syntaxRuleSites syntax)) "repeated object notation"
            Fixity.installRule (owner, Span start end) rule syntax
        entry syntax (Node (Word "bind-scope" : Text name : Word position : classes)) | localName name, not (null classes) = do
            placement <- case position of
                "ReplaceScopes" -> Right ReplaceScopes
                "AddTop" -> Right AddTop
                "AddBottom" -> Right AddBottom
                _ -> Left "invalid scope binding position"
            targets <- mapM classValue classes
            Fixity.applyScope (BindScope name placement targets) syntax
            where
                classValue (Word "sort") = Right SortClass
                classValue (Word "function") = Right FunClass
                classValue (Text n) | qualified n, '.' `elem` n = ReferenceClass <$> global n
                classValue _ = Left "invalid object scope class"
        entry syntax (Node [Word "automatic-prefix", Text n, Number len]) = do
            g <- global n
            prefix <- naturalInt len
            let slots = Map.findWithDefault [] g (Env.syntaxArgScopes syntax)
            require (prefix > 0 && prefix <= length slots && all null (take prefix slots) && Map.notMember g (Env.syntaxArgPrefixes syntax)) "invalid automatic section argument prefix"
            Right syntax { Env.syntaxArgPrefixes = Map.insert g prefix (Env.syntaxArgPrefixes syntax) }
        entry syntax (Node (Word marker : Text name : slots)) | marker `elem` ["argument-scopes", "default-scopes"] = do
            target <- global name
            let auto = marker == "default-scopes"
            require (Map.notMember target ((if auto then Env.syntaxDefaults else Env.syntaxArgScopes) syntax)) "repeated object argument scopes"
            scopes <- mapM (\slot -> case slot of { Node keys -> mapM variable keys; _ -> Left "invalid argument scopes" }) slots
            return (if auto then syntax { Env.syntaxDefaults = Map.insert target scopes (Env.syntaxDefaults syntax) } else syntax { Env.syntaxArgScopes = Map.insert target scopes (Env.syntaxArgScopes syntax) })
        entry syntax wire@(Node (Word "activate" : _)) = activation syntax wire >>= flip Fixity.applyScope syntax . ToggleNotation
        entry syntax (Node [Word "activate-rhs",action,Node parameters,query]) = do
            setting <- activation syntax action
            vars <- mapM variable parameters
            unresolved <- readTemplate query
            resolved <- traverse (\n -> if qualified n && '.' `elem` n then global n else Left "unqualified activation reference") unresolved
            Fixity.applyScope (ToggleInterpretation setting vars resolved) syntax
        entry syntax (Node [Word "custom-entry", Text name]) | qualified name = do
            let canonical = if '.' `elem` name then name else own name
                local = reverse (takeWhile (/= '.') (reverse canonical))
            require (canonical == own local && Map.notMember canonical (Env.syntaxEntries syntax)) "invalid or duplicate custom entry owner"
            Fixity.applyScope (DeclareCustomEntry canonical) syntax
        entry syntax (Node [Word "scope", Text name]) | localName name = Fixity.applyScope (DeclareScope name) syntax
        entry syntax (Node [Word "delimiter", Text name, Text key]) | localName name && localName key = Fixity.applyScope (DelimitScope name key) syntax
        entry syntax (Node [Word "undelimit-scope", Text name]) | localName name = Right (Fixity.replayScope (UndelimitScope name) syntax)
        entry syntax (Node [Word "close-scope", Text name]) | localName name = Right (Fixity.replayScope (CloseScope name) syntax)
        entry syntax (Node [Word "open-scope", Text name]) | localName name = Right (Fixity.replayScope (OpenScope name) syntax)
        entry syntax (Node (Word "arguments" : Text name : flags)) = do
            target <- global name
            require (Map.notMember target (Env.syntaxArguments syntax)) "repeated object Arguments metadata"
            values <- mapM boolean flags
            return syntax { Env.syntaxArguments = Map.insert target values (Env.syntaxArguments syntax) }
        entry syntax (Node [Word "projection-parameters", Text name, Number count]) = do
            target <- global name
            case target of
                GlobalCst _ -> Right ()
                _ -> Left "ordinary projection syntax requires a constant"
            parameters <- naturalInt count
            require (Map.notMember target (Env.syntaxProjectionParameters syntax)) "repeated object projection metadata"
            return syntax { Env.syntaxProjectionParameters = Map.insert target parameters (Env.syntaxProjectionParameters syntax) }
        entry syntax (Node [Word "simpl-never", Text name]) = do
            target <- global name
            case target of
                GlobalCst _ -> Right ()
                GlobalProj {} -> Right ()
                _ -> Left "simpl never requires a constant or projection"
            require (Set.notMember target (Env.syntaxNever syntax)) "repeated object simpl never metadata"
            return syntax { Env.syntaxNever = Set.insert target (Env.syntaxNever syntax) }
        entry syntax (Node [Word "infix", Text operator, Text name, Number level, Text associativity]) = do
            target <- global name
            require (Env.validOperator operator && level >= 0 && level <= 200 && associativity `elem` ["left", "right", "no"]) "invalid object infix metadata"
            require (Fixity.infixOverlap operator (target, level, associativity) syntax == Nothing) "infix conflicts with object notation"
            require (Map.notMember operator (Env.syntaxInfix syntax)) "repeated object Infix metadata"
            return syntax { Env.syntaxInfix = Map.insert operator (target, level, associativity) (Env.syntaxInfix syntax) }
        entry syntax (Node [Word "numerals", Text zero, Text successor]) = do
            require (Env.syntaxNumerals syntax == Nothing) "repeated object Numerals metadata"
            pair <- (,) <$> global zero <*> global successor
            return syntax { Env.syntaxNumerals = Just pair }
        entry _ _ = Left "invalid object syntax entry"

mergeSyntax :: Env.Syntax -> Env.Syntax -> Env.Syntax
mergeSyntax old new = old
    { Env.syntaxArgPrefixes = Map.union (Env.syntaxArgPrefixes new) (Env.syntaxArgPrefixes old)
    , Env.syntaxDefaults = Map.union (Env.syntaxDefaults new) (Env.syntaxDefaults old)
    , Env.syntaxArgScopes = Map.union (Env.syntaxArgScopes new) (Env.syntaxArgScopes old)
    , Env.syntaxArguments = Map.union (Env.syntaxArguments new) (Env.syntaxArguments old)
    , Env.syntaxInfix = Map.union (Env.syntaxInfix new) (Env.syntaxInfix old)
    , Env.syntaxScopes = Set.union (Env.syntaxScopes new) (Env.syntaxScopes old)
    , Env.syntaxKeys = Map.union (Env.syntaxKeys new) (Env.syntaxKeys old)
    , Env.syntaxOpen = Env.syntaxOpen new ++ filter (`notElem` Env.syntaxOpen new) (Env.syntaxOpen old)
    , Env.syntaxNumerals = numerals
    , Env.syntaxNever = Set.union (Env.syntaxNever new) (Env.syntaxNever old)
    , Env.syntaxProjectionParameters = Map.union (Env.syntaxProjectionParameters new) (Env.syntaxProjectionParameters old)
    } where
    numerals = case Env.syntaxNumerals new of
        Just values -> Just values
        Nothing -> Env.syntaxNumerals old

joinSyntax :: Env.Syntax -> Env.Syntax -> Either (String, String) Env.Syntax
joinSyntax old new
    | any (\(symbol, value) -> maybe False (/= value) (Map.lookup symbol (Env.syntaxInfix old))) (Map.toList (Env.syntaxInfix new)) = Left ("H-Infix", "conflicting declarations of the same infix symbol")
    | Just first <- Env.syntaxNumerals old, Just second <- Env.syntaxNumerals new, first /= second = Left ("H-Numeral", "conflicting Numerals declarations")
    | symbol : _ <- [operator | (operator, fixity) <- Map.toList (Env.syntaxInfix new), Just _ <- [Fixity.infixOverlap operator fixity old]] = Left ("H-Notation", "imported infix conflicts with notation: " ++ symbol)
    | otherwise = do
        base <- foldM install (mergeSyntax old new) [r | r@(SyntaxRule _ _ _ target) <- Env.syntaxRules new, case target of { RocqTarget {} -> False; _ -> True }]
        foldM replay base (reverse (Env.syntaxHistory new))
    where
        replay syntax (Left op) = Right (Fixity.replayScope op syntax)
        replay syntax (Right rule) = install syntax rule
        install syntax rule = do
            site <- maybe (Left ("H-Notation", "missing location for imported notation")) Right (Map.lookup rule (Env.syntaxRuleSites new))
            either (Left . (,) "H-Notation") Right (Fixity.installRule site rule syntax)
