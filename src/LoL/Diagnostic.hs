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
reportTerms env report = zipWith shown (reportArgs report) (reportCore report) where
    names = (Pretty.naming env) { Pretty.namingGlobal = \global -> Just (maybe (anonymous global) id (Pretty.globalName env global)) }
    shown original Nothing = "kernel encoding: " ++ original
    shown original (Just value) = either (const ("kernel encoding: " ++ original)) id rendered where
        rendered = case value of
            ReportTerm locals term -> Pretty.renderOpen names locals term
            ReportBinders locals binders term -> Pretty.renderClosure names locals binders term
            ReportHole name locals -> Right ("_ (* unsolved " ++ name ++ (if null locals then "" else "; observed binders: " ++ unwords locals) ++ " *)")
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
renderDiagnostic path source failure = Hol.diagnosticWithModule Hol.DiagnosticTest (diagnosticKind failure) (Just path) (Just (lines source)) location body where
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
