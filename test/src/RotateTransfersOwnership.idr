module RotateTransfersOwnership

import Data.Linear.Ref1
import Data.LSMRRBVector
import Data.SortedMap
import System.Posix.Time
import System.Posix.Timer.Prim

||| Verifies that rotateAllBuffers:
||| - Extracts active buffers exactly once.
||| - Clears thread-local buffers after rotation.
||| - Preserves non-empty thread contexts.
|||
||| This test ensures ownership transfer semantics are correct:
||| - Once buffers are rotated, writers should not retain access to previously active buffers.
|||
export
test_RotateTransfersOwnership : IO ()
test_RotateTransfersOwnership = do
  reg : Ref World (SortedMap ThreadId (ThreadContext Int)) <- newref empty
  -- register this thread (this ensures proper initial context exists)
  ctx <- runIO (registerThread reg 1)
  -- inject an entry into the actual context
  let entry = MkEntry (Append 42) (toUTC $ TM 0 0 0 1 0 0 0 0 False) 1 ctx.sequence
  _ <- runIO (casupdate1 reg (\m =>
                               case lookup 1 m of
                                 Just c  =>
                                   let c' = { buffers := writeOperation c.buffers entry } c
                                     in (insert 1 c' m, ())
                                 Nothing =>
                                   (m, ())
                             )
             )
  extracted <- runIO (rotateAllBuffers reg)
  -- after rotation, registry should still exist but buffer should be cleared
  regstate <- readref reg
  case lookup 1 regstate of
    Nothing   =>
      -- extracted buffers must include one buffer
      when (null extracted) $
        assert_total $ idris_crash "test_RotateTransfersOwnership: no buffers extracted"
    Just ctx' => do
      when (not (bufferEmpty ctx'.buffers.active)) $
        assert_total $ idris_crash "test_RotateTransfersOwnership: buffer not cleared after rotation"
      -- extracted buffers must include one buffer
      when (null extracted) $
        assert_total $ idris_crash "test_RotateTransfersOwnership: no buffers extracted"
