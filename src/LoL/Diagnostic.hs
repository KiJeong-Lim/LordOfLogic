module LoL.Diagnostic where

import qualified Hol.V2.Embedding as Hol
import Hol.V2.Embedding (SLoc (..))
import LoL.Front.Syntax (Span (..), FrontError (..))
import qualified LoL.Core as Core
import qualified LoL.Env as Env
import LoL.Hol.Embed (Report (..), ReportValue (..))
import qualified LoL.Pretty as Pretty
import qualified Z.Doc as Doc

data Diagnostic
    = Diagnostic
        { diagnosticSpan :: Span
        , diagnosticKind :: String
        , diagnosticCode :: String
        , diagnosticText :: String
        , diagnosticBody :: [String]
        }
    deriving (Eq, Show)

fromFrontError :: FrontError -> Diagnostic
fromFrontError failure = Diagnostic (frontSpan failure) (frontKind failure) (frontCode failure) (frontText failure) []

-- This only prints the kernel's terms. A declaration rejected before entering
-- Env may have no global name yet; a stable placeholder identifies that slot.
reportTerms :: Env.Env -> Report -> [String]
reportTerms env = reportTermsAt env []

reportTermsAt :: Env.Env -> [Core.Hint] -> Report -> [String]
reportTermsAt env universes report = zipWith3 shown (roles ++ fields) (reportArgs report) (reportCore report) where
    regular = Pretty.naming env
    names = regular { Pretty.namingGlobal = \global -> Just (maybe (anonymous global) id (Pretty.globalName env global)), Pretty.namingUniverses = universes }
    roles = case reportRule report of
        "T-Conv" -> ["term", "has type", "expected"]
        "T-App" -> ["function", "has type"]
        "T-Proj" -> ["receiver", "has type"]
        "T-Ind" -> ["inductive family"]
        "T-Const" -> ["constant"]
        "T-Constr" -> ["constructor"]
        "T-Var" -> ["variable"]
        "T-Match" -> repeat "branch"
        "I-Univ" -> ["constructor field type", "field sort", "inductive sort"]
        "I-Elim-Prop" -> ["inductive family", "return sort"]
        "T-Record-Elim" -> ["record family"]
        "I-Template-Default" -> ["template family"]
        "I-Uniform" -> ["constructor result"]
        "I-Index" -> ["constructor result"]
        "I-Con" -> ["constructor type"]
        "I-Params" -> ["parameter telescope"]
        "I-Arity" -> ["arity"]
        "F-Guard" -> repeat "recursive definition"
        "E-NotFunction" -> ["source", "has type"]
        "E-Arity" -> ["source", "has type"]
        "E-Unsolved" -> "source" : repeat "unresolved term"
        "E-Unify" -> "source" : fields
        _ -> fields
    fields = ["operand " ++ show n | n <- [1 :: Int ..]]
    shown fallback original value = case value of
        Just (ReportField role field) -> shown role original field
        Just (ReportConstraint named role constraint) -> role ++ ": " ++ relation (if null named then names else names { Pretty.namingUniverses = named }) constraint
        _ -> fallback ++ ": " ++ either (const ("kernel encoding: " ++ original)) id (rendered value)
    rendered value = case value of
        Just (ReportTerm locals term) -> Pretty.renderOpen names locals term
        Just (ReportBinders locals binders term) -> Pretty.renderClosure names locals binders term
        Just (ReportHole name locals) -> Right ("_ (* unsolved " ++ name ++ (if null locals then "" else "; observed binders: " ++ unwords locals) ++ " *)")
        _ -> Left "no decoded term"
    relation labels constraint = case constraint of
        Core.UniverseLe (Core.Successor left) right -> relationText labels left " < " right
        Core.UniverseLe left right -> relationText labels left " <= " right
        Core.UniverseEq left right -> relationText labels left " = " right
    relationText labels left operator right = Pretty.levelText Pretty.Surface labels left (operator ++ Pretty.levelText Pretty.Surface labels right "")
    anonymous global = case global of
        Core.GlobalCst c -> "_constant_" ++ show c
        Core.GlobalInd b i -> "_family_" ++ show b ++ "_" ++ show i
        Core.GlobalProj b j -> "_field_" ++ show b ++ "_" ++ show j
        Core.GlobalCon b i j -> "_constructor_" ++ show b ++ "_" ++ show i ++ "_" ++ show j

-- What LoL does not support.
unsupported :: Span -> String -> Diagnostic
unsupported position syntax = Diagnostic position "LoL-Unsupported" "M2-Unsupported" ("not supported yet: " ++ syntax) []

-- `{struct x}` names one binder. LoL does not pick the first of two.
ambiguousStruct :: Span -> String -> Diagnostic
ambiguousStruct position name = Diagnostic position "LoL-ScopeError" "H-Name" ("two binders have the name of the struct argument: " ++ name) [name]

renderDiagnostic :: FilePath -> String -> Diagnostic -> String
renderDiagnostic path source failure
    | null source = unlines ((path ++ ": error: [" ++ diagnosticKind failure ++ "]") : heading "" : map ("  " ++) (diagnosticBody failure))
    | otherwise = Hol.diagnosticWithModule Hol.DiagnosticTest (diagnosticKind failure) (Just path) (Just (lines source)) location body
    where
        position = diagnosticSpan failure
        location = SLoc (spanFrom position) (spanTill position)
        code = diagnosticCode failure
        heading = (if null code then id else showChar '[' . showString code . showString "] ") . showString (diagnosticText failure)
        terms = if null (diagnosticBody failure) then [sourceAt source position] else diagnosticBody failure
        body = Doc.text (heading "") : [Doc.text ("  " ++ term) | term <- terms, not (null term)]

sourceAt :: String -> Span -> String
sourceAt source (Span (row, column) (lastRow, lastColumn)) = unlines (zipWith slice [row ..] selected) where
    selected = take (max 1 (lastRow - row + 1)) (drop (max 0 (row - 1)) (lines source))
    slice current line = take (max 0 (end - start + 1)) (drop (start - 1) line) where
        start = if current == row then max 1 column else 1
        end = if current == lastRow then lastColumn else length line
