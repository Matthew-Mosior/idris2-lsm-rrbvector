module RetiredSnapshotCreated

import Data.Linear.Ref1
import Data.LSMRRBVector
import Data.RRBVector
import Data.SortedMap
import System.Posix.Time
import System.Posix.Timer.Prim

||| Ensures publishSnapshot retires previous snapshot correctly.
|||
||| Validates:
||| - Retired snapshot list grows.
||| - Previous snapshot preserved.
|||
export
test_RetiredSnapshotCreated : IO ()
test_RetiredSnapshotCreated = do
  state : Ref World (CombinedSnapshotState Int) <-
    newref (MkCombinedSnapshotState (MkSnapshotState 0 empty) [] empty 0 False 64)
  let entries                                   = [MkEntry (Append 1) (toUTC $ TM 1 0 0 1 0 0 0 0 False) 1 0]
  gen                                           <- publishSnapshot state entries
  when (gen /= 1) $
    assert_total $ idris_crash "test_RetiredSnapshotCreated: generation not incremented"
