module HeavyAppendLoad

import Data.List
import Data.LSMRRBVector
import Data.RRBVector
import Data.SortedMap
import System.Posix.Time
import System.Posix.Timer.Prim

||| Stress test:
||| - Many appends.
||| - Ensures no crash, no loss of structure.
|||
export
test_HeavyAppendLoad : IO ()
test_HeavyAppendLoad = do
  let entries = Prelude.Interfaces.map (\i => MkEntry (Append 1) (toUTC $ TM (cast i) 0 0 1 0 0 0 0 False) 1 i) [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19]
      result  = replayEntries entries (the (RRBVector Int) empty)
  when (Prelude.toList result /= replicate 20 1) $
    putStrLn "test_HeavyAppendLoad: replay contents incorrect"
