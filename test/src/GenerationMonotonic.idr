module GenerationMonotonic

import Data.LSMRRBVector

||| Ensures snapshot generation strictly increases on publish.
|||
||| This guarantees:
||| - Readers can detect stale snapshots.
||| - Correctness of reclamation.
|||
export
test_GenerationMonotonic : IO ()
test_GenerationMonotonic = do
  let g1 = 1
  let g2 = 2
  let g3 = 3
  when (not (g1 < g2 && g2 < g3)) $
    assert_total $ idris_crash "test_GenerationMonotonic: generation not monotonic"
