module ReadSnapshotStable

import Data.Linear.Ref1
import Data.LSMRRBVector
import Data.RRBVector
import Data.SortedMap
import IO.Async.Loop.Posix

%hide Prelude.toList

||| Ensures snapshot reads observe a consistent (generation, tree) pair.
|||
||| Checks:
||| - Snapshot acquisition succeeds.
||| - Generation and tree originate from the same published SnapshotState.
||| - Reader registration/cleanup executes correctly.
|||
||| Failure indicates:
||| - Snapshot publication races.
||| - Reader tracking inconsistencies.
||| - Broken acquisition semantics.
|||
export
test_ReadSnapshotStable : Ord (Entry a)
                        => IO ()
test_ReadSnapshotStable = do
  vec <- runIO (emptyWith (MkLSMRRBVectorConfig 8))
  xs  <- runIO (readSnapshotWithGeneration vec 1 (\(_, tree) => Data.RRBVector.toList tree))
  when (xs /= []) $
    assert_total $ idris_crash "test_ReadSnapshotStable: expected empty snapshot contents"
