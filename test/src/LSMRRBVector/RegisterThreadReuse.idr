module LSMRRBVector.RegisterThreadReuse

import Data.Linear.Ref1
import Data.LSMRRBVector
import Data.SortedMap

||| Verifies that registering the same thread id repeatedly
||| reuses the existing ThreadContext instead of creating
||| duplicate registrations.
|||
||| Checks:
||| - Same ThreadId returns same context.
||| - Sequence state is preserved.
||| - Registry contains exactly one entry.
|||
||| Failure indicates:
||| - Duplicate thread registration.
||| - Lost thread-local state.
||| - Registry growth bugs.
|||
export
test_RegisterThreadReuse : IO ()
test_RegisterThreadReuse = do
  reg : Ref World (SortedMap ThreadId (ThreadContext Int))
    <- newref empty
  ctx1 <- registerThread reg 1
  ctx2 <- registerThread reg 1
  when (ctx1.threadid /= ctx2.threadid || ctx1.sequence /= ctx2.sequence) $
    assert_total $ idris_crash "testRegisterThreadReuse: duplicate ThreadContext created"
  registry <- readref reg
  when (length (keys registry) /= 1) $
    assert_total $ idris_crash "test_RegisterThreadReuse: registry contains duplicate entries"
