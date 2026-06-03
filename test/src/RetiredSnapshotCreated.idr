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
    putStrLn "test_RetiredSnapshotCreated: generation not incremented"
  css <- readref state
  when (length css.retiredsnapshots /= 1) $
    putStrLn "test_RetiredSnapshotCreated: retired snapshot missing"
  case css.retiredsnapshots of
    [snap] =>
      when (snap.generation /= 0) $
        putStrLn "test_RetiredSnapshotCreated: incorrect retired generation"
    _ =>
      putStrLn "test_RetiredSnapshotCreated: unexpected retired snapshot count"
