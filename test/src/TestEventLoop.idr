module TestEventLoop

import IO.Async.Loop
import Data.Linear.Ref1
import Data.SortedMap
import Data.Nat

public export
record TestEventLoop where
  constructor MkTestEventLoop
  queue : Ref World (List (FbrState TestEventLoop))

public export
EventLoop TestEventLoop where
  spawn el fbr =
    runIO (runFbr el fbr)
  limit = 1000
