module Main

import DeterministicOrdering
import GenerationMonotonic
import HeavyAppendLoad
import NoReadersReclaimsEverything
import NWritersMReaders
import ReaderAtGeneration3
import ReaderDoesNotPinAncientGenerations
--import ReadSnapshotStable
import RegisterThreadReuse
import ReplayProducesExpectedVector
import RetiredSnapshotCreated
import RotateTransfersOwnership

main : IO ()
main = do
  () <- test_RegisterThreadReuse
  () <- test_RotateTransfersOwnership
  () <- test_DeterministicOrdering
  () <- test_ReplayProducesExpectedVector
  () <- test_GenerationMonotonic
  () <- test_RetiredSnapshotCreated
  () <- test_NoReadersReclaimsEverything
  () <- test_ReaderAtGeneration3
  () <- test_ReaderDoesNotPinAncientGenerations
  --() <- test_ReadSnapshotStable
  () <- test_HeavyAppendLoad
  test_NWritersMReaders_run
