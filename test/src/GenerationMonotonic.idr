module GenerationMonotonic

import Data.Linear.Ref1
import Data.LSMRRBVector
import Data.SortedMap

||| Ensures snapshot generation strictly increases on publish.
|||
||| This guarantees:
||| - Readers can detect stale snapshots.
||| - Correctness of reclamation.
|||
export
test_GenerationMonotonic : IO ()
test_GenerationMonotonic = do
  state : Ref World (CombinedSnapshotState Int) <-
    newref (MkCombinedSnapshotState (MkSnapshotState 0 empty) [] empty 0 False 64)
  g1 <- publishSnapshot state []
  g2 <- publishSnapshot state []
  g3 <- publishSnapshot state []
  when (not (g1 < g2 && g2 < g3)) $
    putStrLn "test_GenerationMonotonic: generation not monotonic"
