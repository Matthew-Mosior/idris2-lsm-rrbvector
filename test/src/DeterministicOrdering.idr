module DeterministicOrdering

import Data.Linear.Ref1
import Data.List
import Data.LSMRRBVector
import Data.SortedMap
import System.Posix.Time
import System.Posix.Timer.Prim

||| Ensures that Entry sorting is deterministic: identical inputs always produce identical ordering.
|||
||| This guarantees replay stability across rebuild cycles.
|||
export
test_DeterministicOrdering : IO ()
test_DeterministicOrdering = do
  let e1      = MkEntry (Append 1) (toUTC $ TM 0 0 0 1 0 0 0 0 False) 1 0
  let e2      = MkEntry (Append 2) (toUTC $ TM 1 0 0 1 0 0 0 0 False) 1 1
  let e3      = MkEntry (Append 3) (toUTC $ TM 2 0 0 1 0 0 0 0 False) 2 0
  let input   = [e3, e1, e2]
  let sorted1 = sortEntries input
  let sorted2 = sortEntries input
  when (sorted1 /= [e1, e2, e3]) $
    putStrLn "test_DeterministicOrdering: incorrect ordering"
