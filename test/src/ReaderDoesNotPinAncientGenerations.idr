module ReaderDoesNotPinAncientGenerations

import Data.Linear.Ref1
import Data.LSMRRBVector
import Data.RRBVector
import Data.SortedMap

||| Ensures old readers do not prevent modern snapshot reclamation once they leave.
|||
export
test_ReaderDoesNotPinAncientGenerations : IO ()
test_ReaderDoesNotPinAncientGenerations = do
  state : Ref World (CombinedSnapshotState Int) <-
    newref (MkCombinedSnapshotState (MkSnapshotState 10 Empty) [MkRetiredSnapshot 1 Empty, MkRetiredSnapshot 2 Empty] empty 0 False 64)
  runIO (leaveGeneration state 1)
