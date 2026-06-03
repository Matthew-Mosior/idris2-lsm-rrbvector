module SortThenReplayDeterministic

import Data.LSMRRBVector
import Data.RRBVector
import System.Posix.Time
import System.Posix.Timer.Prim

%hide Prelude.Ops.infixl.(|>)
%hide Prelude.Ops.infixr.(<|)

||| Verifies that the rebuild pipeline's ordering stage produces a deterministic replay result regardless of input ordering.
|||
||| This test exercises:
||| - Entry timestamp ordering.
||| - sortEntries.
||| - replayEntries.
||| - Final vector contents.
|||
||| The input list is intentionally shuffled relative to the logical mutation order.
||| After sorting and replaying, the resulting vector must match the order implied by Entry ordering:
|||
|||   e1 -> Append 1
|||   e2 -> Append 2
|||   e3 -> Append 3
|||
||| Expected result:
|||
|||   Empty |> 1 |> 2 |> 3
|||
||| Failure indicates:
||| - Broken Entry Ord implementation.
||| - Non-deterministic sorting.
||| - Replay ordering bugs.
||| - Rebuild pipeline corruption.
|||
export
test_SortThenReplayDeterministic : IO ()
test_SortThenReplayDeterministic = do
  let e1 =
        MkEntry
          (Append 1)
          (toUTC $ TM 1 0 0 1 0 0 0 0 False)
          1
          0
  let e2 =
        MkEntry
          (Append 2)
          (toUTC $ TM 2 0 0 1 0 0 0 0 False)
          2
          0
  let e3 =
        MkEntry
          (Append 3)
          (toUTC $ TM 3 0 0 1 0 0 0 0 False)
          1
          1
  -- intentionally shuffled
  let unsorted =
        [ e3
        , e1
        , e2
        ]
  let sorted =
        sortEntries unsorted
  when (sorted /= [e1, e2, e3]) $
    putStrLn "test_SortThenReplayDeterministic: sortEntries produced incorrect ordering"
  let result =
        replayEntries
          sorted
          (the (RRBVector Int) Empty)
  let expected =
        Empty |> 1 |> 2 |> 3
  when (result /= expected) $
    putStrLn "test_SortThenReplayDeterministic: replay produced incorrect vector"
  when (Data.RRBVector.toList result /= [1,2,3]) $
    putStrLn "test_SortThenReplayDeterministic: final contents mismatch"
