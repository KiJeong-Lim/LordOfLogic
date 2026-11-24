module LoL.ObjectReport (checkedObject) where

import Control.Applicative ((<|>))
import Data.List (intercalate)
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import LoL.Core (Global (GlobalCst))
import qualified LoL.Env as Env
import qualified LoL.Module as Module
import qualified LoL.Object as Object
import qualified LoL.Pretty as Pretty

-- Only a successful kernel replay supplies a Loaded value to this report.
-- The object file's own dependency lists are not evidence about assumptions.
checkedObject :: Module.Loaded -> Either String ([String], Bool)
checkedObject loaded = do
    declarations <- concat <$> mapM reportUnit (Module.loadedOrder loaded)
    axioms <- mapM qualified axiomIds
    return (("Checked object " ++ Module.loadedMain loaded ++ ".") : declarations ++ ["Axioms in checked modules: " ++ list axioms], not (null axioms))
    where
        env = Module.loadedEnv loaded
        entries = Env.envDecls env
        names = Module.canonicalNames loaded
        base = Pretty.naming env
        axiomIds = [c | (c, entry) <- Map.toAscList entries, Env.Axiom {} <- [Env.entryDecl entry]]
        inherited = if null axiomIds then Map.empty else Env.assumptionTable env
        list [] = "none"
        list xs = intercalate ", " xs
        reportUnit moduleName = case Map.lookup moduleName (Module.loadedUnits loaded) of
            Nothing -> Left ("Missing checked module " ++ moduleName)
            Just unit -> (("Module " ++ moduleName ++ ".") :) . concat <$> mapM signature (Module.unitLocals unit)
        signature identity = do
            entry <- maybe (Left "Missing checked declaration") Right (Map.lookup identity entries)
            let decl = Env.entryDecl entry
                own = Map.fromList [(global, name) | (name, global) <- Env.declGlobals identity (Env.entryName entry) decl]
                naming = base { Pretty.namingGlobal = \global -> Map.lookup global own <|> Map.lookup global names }
            line <- case Pretty.commandBodies (Pretty.printerOf Pretty.Surface) False False Pretty.Surface naming identity entry of
                Right (_, rendered) -> Right rendered
                Left _ -> coreSignature entry
            case decl of
                Env.Theorem {} -> do
                    dependencies <- mapM qualified (Set.toAscList (Map.findWithDefault Set.empty identity inherited))
                    Right [line, "  Assumptions: " ++ list dependencies]
                _ -> Right [line]
        qualified ident = maybe (Left "Missing qualified name for a checked axiom") Right (Map.lookup (GlobalCst ident) names)
        -- Some valid Core universe expressions have no surface spelling.
        -- Retain those signatures, including their constraints, in the object's notation.
        coreSignature entry = do
            let decl = Env.entryDecl entry
            body <- case decl of
                Env.Axiom a -> Object.tag "axiom" . pure <$> Object.saveTerm names a
                Env.Definition a _ -> Object.tag "definition" . pure <$> Object.saveTerm names a
                Env.Theorem a _ -> Object.tag "theorem" . pure <$> Object.saveTerm names a
                Env.Inductive {} -> Object.saveDecl names decl
            let core = Object.tag "signature" [Object.Text (Env.entryName entry), Object.saveUniverses (Env.entryUniverses entry), body]
            Right ("Core " ++ Object.renderWire core "")
