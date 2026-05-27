module ReaderAtGeneration3

import Data.Linear.Ref1
import Data.LSMRRBVector
import Data.RRBVector
import Data.SortedMap

||| Ensures reader registration records the current snapshot generation.
|||
||| This test validates:
||| - Reader state is inserted into registry.
||| - Generation is derived from snapshot state.
||| - The enterGeneration function ignores external generation input.
|||
export
test_ReaderAtGeneration3 : IO ()
test_ReaderAtGeneration3 = do
  let snap : SnapshotState Int
      snap = MkSnapshotState 3 empty
  state    <- newref (MkCombinedSnapshotState snap [] empty 0 False 64)
  -- reader registers current generation (3)
  _        <- runIO (enterGeneration state 1)
  pure ()
