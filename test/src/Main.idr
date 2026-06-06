module Main

import Hedgehog
import LSMRRBVector.DeterministicOrdering
import LSMRRBVector.GenerationMonotonic
import LSMRRBVector.HeavyAppendLoad
import LSMRRBVector.NoReadersReclaimsEverything
import LSMRRBVector.NWritersMReaders
import LSMRRBVector.SortThenReplayDeterministic
import LSMRRBVector.ReaderAtGeneration3
import LSMRRBVector.ReaderDoesNotPinAncientGenerations
import LSMRRBVector.ReadSnapshotStable
import LSMRRBVector.RegisterThreadReuse
import LSMRRBVector.ReplayProducesExpectedVector
import LSMRRBVector.RetiredSnapshotCreated
import LSMRRBVector.RotateTransfersOwnership
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
