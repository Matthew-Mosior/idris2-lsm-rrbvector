module LSMRRBVector.ReplayProducesExpectedVector

import Data.LSMRRBVector
import Data.RRBVector
import System.Posix.Time
import System.Posix.Timer.Prim

%hide Prelude.Ops.infixl.(|>)
%hide Prelude.Ops.infixr.(<|)

||| Verifies that replaying buffered operations produces correct final vector.
|||
||| This ensures:
||| - Operation semantics are correct.
||| - Replay is order-preserving.
|||
export
test_ReplayProducesExpectedVector : IO ()
test_ReplayProducesExpectedVector = do
  let v0       = Empty
  let e1       = MkEntry (Append 1) (toUTC $ TM 1 0 0 1 0 0 0 0 False) 1 0
  let e2       = MkEntry (Append 2) (toUTC $ TM 2 0 0 1 0 0 0 0 False) 1 1
  let e3       = MkEntry (Prepend 0) (toUTC $ TM 3 0 0 1 0 0 0 0 False) 2 0
  let result   = replayEntries [e1, e2, e3] v0
  let expected = 0 <| (Empty |> 1 |> 2)
  when (result /= expected) $
    assert_total $ idris_crash "test_ReplayProducesExpectedVector: replay mismatch"
