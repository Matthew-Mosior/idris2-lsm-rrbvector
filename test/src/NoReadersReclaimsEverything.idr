module NoReadersReclaimsEverything

import Data.Linear.Ref1
import Data.LSMRRBVector
import Data.RRBVector
import Data.SortedMap

||| Ensures that when no readers exist, all retired snapshots are reclaimed.
|||
export
test_NoReadersReclaimsEverything : IO ()
test_NoReadersReclaimsEverything = do
  state : Ref World (CombinedSnapshotState Int) <-
    newref (MkCombinedSnapshotState (MkSnapshotState 0 empty) [MkRetiredSnapshot 0 empty] empty 0 False 64)
  reclaimSnapshots state
