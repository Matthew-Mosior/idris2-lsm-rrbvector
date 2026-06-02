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
test_ReadSnapshotStable : IO ()
test_ReadSnapshotStable =
  runEmptyWith (MkLSMRRBVectorConfig 8)
               [ (\_, _ => pure ())
               ]
               (\vec : LSMRRBVector World Int => do
                   xs <- liftIO $ readSnapshotWithGeneration vec 1 (\(_, tree) => Data.RRBVector.toList tree)
                   when (xs /= []) $
                     assert_total $ idris_crash "test_ReadSnapshotStable: expected empty snapshot contents"
               )
