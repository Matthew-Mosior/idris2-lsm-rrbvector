module Main

import DeterministicOrdering
import GenerationMonotonic
import HeavyAppendLoad
import Hedgehog
import NoReadersReclaimsEverything
import NWritersMReaders
import SortThenReplayDeterministic
import ReaderAtGeneration3
import ReaderDoesNotPinAncientGenerations
import ReadSnapshotStable
import RegisterThreadReuse
import ReplayProducesExpectedVector
import RetiredSnapshotCreated
import RotateTransfersOwnership
import RRBVector

main : IO ()
main = do
  _  <- test [ props
             ]
  () <- test_RegisterThreadReuse
  () <- test_RotateTransfersOwnership
  () <- test_DeterministicOrdering
  () <- test_ReplayProducesExpectedVector
  () <- test_GenerationMonotonic
  () <- test_RetiredSnapshotCreated
  () <- test_NoReadersReclaimsEverything
  () <- test_ReaderAtGeneration3
  () <- test_ReaderDoesNotPinAncientGenerations
  () <- test_ReadSnapshotStable
  () <- test_HeavyAppendLoad
  () <- test_SortThenReplayDeterministic
  test_NWritersMReaders
