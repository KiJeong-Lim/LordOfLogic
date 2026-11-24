module LoL.Front.Grammar where

import Control.Monad (ap, when)
import Data.Bifunctor (first)
import Data.Maybe (listToMaybe)
import LoL.Front.Syntax

-- Recursive occurrences re-enter the document's expression grammar. The
-- fixed productions consume their own delimiters, including nested scopes.
data Grammar = Grammar
    { expression        :: Parser Term
    , groupedExpression :: Parser Term
    , reservedBinder    :: String -> Bool
    }
data Problem = Unexpected (Maybe Token) | Association Token deriving (Eq, Show)

problemToken :: Problem -> Maybe Token
problemToken (Unexpected unexpected) = unexpected
problemToken (Association token) = Just token

newtype Parser a = Parser { runParser :: Grammar -> [Token] -> Either Problem (a, [Token]) } deriving ()

instance Functor Parser where
    fmap f parser = Parser $ \grammar input -> do
        (value, rest) <- runParser parser grammar input
        Right (f value, rest)

instance Applicative Parser where
    pure value = Parser $ \_ input -> Right (value, input)
    (<*>) = ap

instance Monad Parser where
    parser >>= next = Parser $ \grammar input -> do
        (value, rest) <- runParser parser grammar input
        runParser (next value) grammar rest

peek :: Parser (Maybe Token)
peek = Parser $ \_ input -> Right (listToMaybe input, input)

bad :: Parser a
bad = Parser $ \_ input -> Left (Unexpected (listToMaybe input))

takeIf :: (Token -> Bool) -> Parser Token
takeIf predicate = Parser $ \_ input -> case input of
    first : rest
        | predicate first -> Right (first, rest)
    _ -> Left (Unexpected (listToMaybe input))

takeToken :: Parser Token
takeToken = takeIf (const True)

want :: String -> Parser Token
want kind = takeIf ((== kind) . tokenKind)

ahead :: Parser String
ahead = maybe "" tokenKind <$> peek

whenKind :: String -> Parser a -> Parser (Maybe a)
whenKind kind parser = do
    next <- ahead
    if next == kind then Just <$> parser else pure Nothing

after :: String -> Parser a -> Parser (Maybe a)
after kind parser = whenKind kind (want kind >> parser)

series :: (String -> Bool) -> Parser a -> Parser [a]
series accepts parser = do
    next <- ahead
    if accepts next then (:) <$> parser <*> series accepts parser else pure []

identifier :: String -> Bool
identifier kind = kind `elem` ["ident", "Assumptions", "associativity", "at", "left", "level", "no", "right"]

namedBy :: (String -> Bool) -> Parser Name
namedBy accepts = tokenName <$> takeIf (accepts . tokenKind)

ident, qname, variable :: Parser Name
ident = namedBy identifier
qname = namedBy (\kind -> kind == "qualid" || identifier kind)
variable = boundName variableKind

boundName :: (String -> Bool) -> Parser Name
boundName accepts = Parser $ \grammar -> runParser (tokenName <$> takeIf (allowed grammar)) grammar where
    allowed grammar token = accepts (tokenKind token) && not (reservedBinder grammar (tokenText token))

boundIdent :: Parser Name
boundIdent = boundName identifier

variableKind :: String -> Bool
variableKind kind = kind == "_" || identifier kind

startsAtom :: String -> Bool
startsAtom kind = identifier kind || kind `elem` ["qualid", "@", "Prop", "Set", "Type", "numeral", "_", "("]

fixed :: Grammar
fixed = Grammar fixedTerm fixedTerm (const False)

parseRaw :: [Token] -> Either (Maybe Token) (Either Term [Command])
parseRaw = parseRawWith fixed

parseRawWith :: Grammar -> [Token] -> Either (Maybe Token) (Either Term [Command])
parseRawWith grammar = first problemToken . readRaw grammar

readRaw :: Grammar -> [Token] -> Either Problem (Either Term [Command])
readRaw grammar input = do
    (result, rest) <- runParser start grammar input
    case rest of
        [] -> Right result
        next : _ -> Left (Unexpected (Just next))
    where
        start = case input of
            [] -> pure (Right [])
            first : _
                | startsCommand (tokenKind first) -> Right <$> series startsCommand command
            _ -> Left <$> term
        startsCommand kind = kind `elem` words "record-command Polymorphic Definition Theorem Lemma Axiom Check Compute Print Inductive Fixpoint Arguments Infix Numerals Import"

term :: Parser Term
term = Parser $ \grammar -> runParser (expression grammar) grammar

-- Only the trailing body of an open binder inherits an outer notation's
-- delimiter. A binder domain or a let value has its own closing token.
groupedTerm :: Parser Term
groupedTerm = Parser $ \grammar -> runParser (groupedExpression grammar) grammar

base :: Parser Term
base = do
    next <- ahead
    case next of
        "forall" -> abstraction SForall ","
        "fun" -> abstraction SLambda "=>"
        "let" -> do
            start <- takeToken
            name <- boundIdent
            typ <- after ":" groupedTerm
            value <- want ":=" >> groupedTerm
            body <- want "in" >> term
            pure (Term (tokenSpan start <> termSpan body) (letIn name typ value body))
        "fix" -> do
            start <- takeToken
            first <- fixFunction
            rest <- series (== "with") (want "with" >> fixFunction)
            selected <- after "for" ident
            let functions = first : rest
                FixBody end _ _ _ _ _ = last functions
            pure (Term (tokenSpan start <> maybe end nameSpan selected) (SFix functions selected))
        "match" -> do
            start <- takeToken
            scrutinee <- term
            alias <- after "as" variable
            family <- after "in" patternP
            motive <- after "return" term
            branches <- want "with-match" >> series (== "|") branch
            end <- want "end"
            pure (Term (tokenSpan start <> tokenSpan end) (SMatch scrutinee alias family motive branches))
        _ -> atom
    where
        abstraction build delimiter = do
            start <- takeToken
            binders <- abstractionBinders
            body <- want delimiter >> term
            pure (Term (tokenSpan start <> termSpan body) (build binders body))
        branch = do
            start <- want "|"
            pat <- patternP
            body <- want "=>" >> term
            pure (Branch (tokenSpan start <> termSpan body) pat body)

fixedTerm :: Parser Term
fixedTerm = do
    first <- base
    if openPrefix first then pure first else applications first >>= \lhs -> spine lhs []
    where
        spine first reversed = do
            next <- ahead
            case next of
                "operator" -> do
                    op <- tokenName <$> takeToken
                    arg <- base
                    value <- if openPrefix arg then pure arg else applications arg
                    spine first ((op, value) : reversed)
                "->" -> arrowTo (operators (first, reversed)) <$> (want "->" >> term)
                ":" -> do
                    colon <- takeToken
                    castOperators (first, reversed) (tokenSpan colon) <$> term
                _ -> pure (operators (first, reversed))
        applications value = do
            next <- ahead
            if startsAtom next then atom >>= applications . application value else pure value

openPrefix :: Term -> Bool
openPrefix value = case termForm value of
    SForall {} -> True
    SLambda {} -> True
    SLet {} -> True
    SFix _ Nothing -> True
    _ -> False

atom :: Parser Term
atom = do
    next <- ahead
    case next of
        "Prop" -> simple SProp
        "Set" -> simple SSet
        "_" -> simple SHole
        "Type" -> do
            start <- takeToken
            universe <- after "@{" level
            value <- case universe of
                Nothing -> pure (Term (tokenSpan start) SInferredType)
                Just lev -> do
                    end <- want "}"
                    let form = case levelForm lev of
                            LNumber n -> SType n
                            _ -> SUniverse lev
                    pure (Term (tokenSpan start <> tokenSpan end) form)
            projectionTail value
        "numeral" -> do
            n <- takeToken
            projectionTail (Term (tokenSpan n) (SNumeral (read (tokenText n))))
        "(" -> do
            start <- takeToken
            inner <- groupedTerm
            end <- want ")"
            projectionTail (Term (tokenSpan start <> tokenSpan end) (SParen inner))
        _ -> do
            mark <- whenKind "@" takeToken
            name <- qname
            let start = maybe (nameSpan name) tokenSpan mark
                explicit = maybe False (const True) mark
            instance' <- whenKind "@{" (takeToken >> series levelStart level)
            value <- case instance' of
                Nothing -> pure (Term (start <> nameSpan name) (if explicit then SExplicit name else SName name))
                Just levels -> do
                    end <- want "}"
                    pure (Term (start <> tokenSpan end) (SInstance explicit name levels))
            projectionTail value
    where
        simple form = takeToken >>= projectionTail . flip Term form . tokenSpan

projectionTail :: Term -> Parser Term
projectionTail value = do
    next <- ahead
    if next /= ".(" then pure value else do
        field <- takeToken >> qname
        end <- want ")"
        projectionTail (Term (termSpan value <> tokenSpan end) (SProjection value field))

patternP :: Parser Pattern
patternP = do
    next <- ahead
    if next == "_" then WildPattern . tokenSpan <$> takeToken else do
        mark <- whenKind "@" takeToken
        name <- qname
        vars <- series variableKind variable
        let start = maybe (nameSpan name) tokenSpan mark
        pure (Pattern (start <> nameSpan (last (name : vars))) (maybe False (const True) mark) name vars)

levelStart :: String -> Bool
levelStart kind = identifier kind || kind `elem` ["qualid", "numeral", "_", "Set", "("]

level :: Parser LevelSyntax
level = do
    next <- ahead
    x <- case next of
        "(" -> do
            open <- takeToken
            inner <- level
            close <- want ")"
            pure inner { levelSpan = tokenSpan open <> tokenSpan close }
        "numeral" -> do
            n <- takeToken
            pure (LevelSyntax (tokenSpan n) (LNumber (read (tokenText n))))
        "_" -> leaf LHole
        "Set" -> leaf (LNumber 0)
        _ -> do
            name <- qname
            open <- ahead
            if nameText name /= "max" || open /= "(" then pure (LevelSyntax (nameSpan name) (LName name)) else do
                a <- takeToken >> level
                b <- want "," >> level
                end <- want ")"
                pure (LevelSyntax (nameSpan name <> tokenSpan end) (LMaximum name a b))
    token <- peek
    case token of
        Just plus
            | tokenKind plus == "operator", tokenText plus == "+" -> do
                n <- takeToken >> want "numeral"
                pure (LevelSyntax (levelSpan x <> tokenSpan n) (LOffset x (tokenName plus) (read (tokenText n))))
        _ -> pure x
    where
        leaf value = flip LevelSyntax value . tokenSpan <$> takeToken

binderStart :: String -> Bool
binderStart kind = variableKind kind || kind == "(" || kind == "{"

binder :: Parser Binder
binder = do
    next <- ahead
    if variableKind next then do
        name <- variable
        pure (untyped name)
    else do
        open <- takeIf (\t -> tokenKind t `elem` ["(", "{"])
        first <- variable
        others <- series variableKind variable
        domain <- want ":" >> groupedTerm
        let implicit = tokenKind open == "{"
        close <- want (if implicit then "}" else ")")
        pure (Binder (tokenSpan open <> tokenSpan close) (first : others) (Just domain) implicit)

untyped :: Name -> Binder
untyped name = Binder (nameSpan name) [name] Nothing False

abstractionBinders :: Parser [Binder]
abstractionBinders = do
    next <- ahead
    if variableKind next then do
        first <- variable
        others <- series variableKind variable
        let names = first : others
        domain <- after ":" groupedTerm
        case domain of
            Just typ -> pure [Binder (nameSpan first <> termSpan typ) names (Just typ) False]
            Nothing -> (map untyped names ++) <$> series binderStart binder
    else (:) <$> binder <*> series binderStart binder

fixFunction :: Parser FixBody
fixFunction = boundIdent >>= fixAfterName

fixAfterName :: Name -> Parser FixBody
fixAfterName name = do
    first <- binder
    (rest, structural) <- tailBinders
    typ <- want ":" >> groupedTerm
    body <- want ":=" >> term
    pure (FixBody (nameSpan name <> termSpan body) name (first : rest) structural typ body)
    where
        tailBinders = do
            structural <- Parser $ \_ input -> Right (map tokenKind (take 2 input) == ["{", "struct"], input)
            next <- ahead
            if structural then do
                variable' <- takeToken >> takeToken >> ident
                _ <- want "}"
                pure ([], Just variable')
            else if binderStart next then do
                b <- binder
                (bs, marker) <- tailBinders
                pure (b : bs, marker)
            else pure ([], Nothing)

optionalUniverses :: Parser (Maybe UniverseDecl)
optionalUniverses = after "@{" $ do
    names <- series identifier ident
    constraints <- after "|" relations
    _ <- want "}"
    pure (UniverseDecl names (maybe True (const False) constraints) (maybe [] id constraints))
    where
        relations = do
            next <- ahead
            if next == "}" then pure [] else do
                left <- level
                op <- tokenName <$> want "operator"
                right <- level
                rest <- after "," relations
                pure ((left, op, right) : maybe [] id rest)

command :: Parser Command
command = do
    poly <- whenKind "Polymorphic" takeToken
    start <- case poly of
        Just _ -> takeIf (\t -> tokenKind t `elem` ["Definition", "Theorem", "Lemma", "Axiom", "Inductive", "Fixpoint"])
        Nothing -> takeToken
    let kind = tokenKind start
        finish make = do
            end <- want "."
            pure (make (tokenSpan start <> tokenSpan end))
        named action = do
            name <- boundIdent
            universes <- maybe (pure Nothing) (const optionalUniverses) poly
            result <- action name >>= finish
            case poly of
                Nothing -> pure result
                Just prefix -> pure (CUniverses (tokenSpan prefix <> commandSpan result) universes result)
        query make = term >>= \value -> finish (\at -> make at value)
        definition name = do
            binders <- series binderStart binder
            typ <- want ":" >> term
            body <- want ":=" >> term
            pure (\at -> CDefinition at kind name binders typ body)
    case kind of
        "Definition" -> named definition
        "Lemma" -> named definition
        "Theorem" -> named definition
        "Axiom" -> named $ \name -> do
            typ <- want ":" >> term
            pure (\at -> CAxiom at name typ)
        "Inductive" -> named $ \name -> do
            first <- family name
            rest <- series (== "with") (takeToken >> boundIdent >>= family)
            pure (\at -> CInductive at (first : rest))
        "Fixpoint" -> named $ \name -> do
            first <- fixAfterName name
            rest <- series (== "with") (takeToken >> fixFunction)
            pure (\at -> CFixpoint at (first : rest))
        "record-command" -> do
            name <- boundIdent
            universes <- optionalUniverses
            binders <- series binderStart binder
            arity <- after ":" term
            _ <- want ":="
            next <- ahead
            ctor <- case next of
                "|" -> Just <$> (takeToken >> boundIdent)
                "{" -> pure Nothing
                _ -> Just <$> boundIdent
            fields <- want "{" >> recordFields
            _ <- want "}"
            finish (\at -> recordDeclaration (tokenText start == "Record") at name universes binders arity ctor fields)
        "Check" -> query CCheck
        "Compute" -> query CCompute
        "Print" -> do
            first <- qname
            next <- ahead
            case nameText first of
                "Assumptions"
                    | next /= "." -> qname >>= \name -> finish (\at -> CPrintAssumptions at name)
                _ -> finish (\at -> CPrint at first)
        "Import" -> qname >>= \name -> finish (\at -> CImport at name)
        "Numerals" -> do
            zero <- qname
            successor <- qname
            finish (\at -> CNumerals at zero successor)
        "Infix" -> do
            symbol <- tokenName <$> want "string"
            target <- want ":=" >> qname
            n <- want "(" >> want "at" >> want "level" >> want "numeral"
            direction <- after "," $ do
                assoc <- takeIf (\t -> tokenKind t `elem` ["left", "right", "no"])
                end <- want "associativity"
                pure (Name (tokenSpan assoc <> tokenSpan end) (tokenText assoc))
            _ <- want ")"
            finish (\at -> CInfix at symbol target (read (tokenText n)) direction)
        "Arguments" -> do
            target <- qname
            specs <- series (\k -> identifier k || k == "{") argument
            options <- after ":" $ do
                key <- ident
                value <- namedBy (\k -> k == "numeral" || identifier k)
                pure [key, value]
            when (null specs && options == Nothing) bad
            finish (\at -> CArguments at target specs (maybe [] id options))
        _ -> bad
    where
        family name = do
            binders <- series binderStart binder
            typ <- want ":" >> term
            assign <- want ":="
            ctors <- series (== "|") constructor
            let end = case reverse ctors of
                    Constructor at _ _ : _ -> at
                    [] -> tokenSpan assign
            pure (IndBody (nameSpan name <> end) name binders typ ctors)
        constructor = do
            open <- want "|"
            name <- boundIdent
            typ <- want ":" >> term
            pure (Constructor (tokenSpan open <> termSpan typ) name typ)
        recordFields = do
            next <- ahead
            if next == "}" then pure [] else do
                name <- boundIdent
                typ <- after ":" term
                field <- case typ of
                    Nothing -> Computed name Nothing <$> (want ":=" >> term)
                    Just domain -> maybe (Assumption name domain) (Computed name typ) <$> after ":=" term
                rest <- after ";" recordFields
                pure (field : maybe [] id rest)
        argument = do
            next <- ahead
            if next == "{" then do
                start <- takeToken
                name <- ident
                end <- want "}"
                pure (ArgSpec (tokenSpan start <> tokenSpan end) True name)
            else do
                name <- ident
                pure (ArgSpec (nameSpan name) False name)
