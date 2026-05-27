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
  let s0 : SnapshotState Int
      s0 = MkSnapshotState 0 empty
  state  <- newref (MkCombinedSnapshotState s0 [MkRetiredSnapshot 0 empty] empty 0 False 64)
  runIO (reclaimSnapshots state)
