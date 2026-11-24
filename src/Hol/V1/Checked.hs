-- A validation witness for the immutable full program. The constructor stays
-- private: consuming this witness can avoid another structural traversal.
module Hol.V1.Checked (CheckedProgram, checkedProgram, checkedSections, checkedMetadata, checkProgram, restoreCheckedArtifact) where

import Hol.V1.FullBytecode
import qualified Data.IntMap.Strict as IntMap

type StoredMetadata = (Maybe String, Maybe StoredType, Maybe ((Int, Int), (Int, Int)))

data CheckedProgram = CheckedProgram !FullProgram !FullSections ![StoredMetadata] deriving ()

checkedProgram :: CheckedProgram -> FullProgram
checkedProgram (CheckedProgram program _ _) = program

checkedSections :: CheckedProgram -> FullSections
checkedSections (CheckedProgram _ sections _) = sections

checkedMetadata :: CheckedProgram -> [StoredMetadata]
checkedMetadata (CheckedProgram _ _ metadata) = metadata

checkProgram :: FullProgram -> Either String CheckedProgram
checkProgram = verify True Nothing

restoreCheckedArtifact :: FullArtifact -> Either String CheckedProgram
restoreCheckedArtifact artifact@(FullArtifact _ _ _ _ metadata _ _ _) = restoreFullFields artifact >>= verify False (Just metadata)

-- Restored DTO fields have already been validated. Both paths check exactly
-- the same graph, while retaining its sections instead of splitting them
-- again when the compiler restores indices and source projections.
verify :: Bool -> Maybe [StoredMetadata] -> FullProgram -> Either String CheckedProgram
verify fields metadata program = do
    requireTypedProgram program
    sections <- fullSections (fullWords program)
    validateSectionsWith fields (const False) 0 0 program sections
    return (CheckedProgram program sections (maybe (map storeMetadata (IntMap.elems (fullMetadata program))) id metadata))
