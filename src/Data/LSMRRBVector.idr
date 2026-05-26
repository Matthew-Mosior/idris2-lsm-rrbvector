||| Log-Structured Merge RRB Vectors (LSMRRBVector)
module Data.LSMRRBVector

import public Data.LSMRRBVector.Internal
import Data.RRBVector

import Control.Monad.Elin
import Control.Monad.MCancel
import Control.Monad.ST
import Data.Array
import Data.Array.Core
import Data.Array.Index
import Data.Array.Indexed
import Data.Bits
import Data.Linear.Ref1
import Data.List
import Data.List1
import Data.Maybe
import Data.RRBVector
import Data.SortedMap
import Data.SnocList
import Data.Vect
import Data.Zippable
import IO.Async
import IO.Async.Service
import Syntax.T1 as T1
import System.Concurrency
import System.Posix.Timer
import System.Posix.Timer.Prim

%hide Control.Monad.Elin.Elin.(.run)
%hide Prelude.null
%hide Prelude.Ops.infixr.(<|)
%hide Prelude.Ops.infixl.(|>)

%default total

--------------------------------------------------------------------------------
--          Buffer Utilities
--------------------------------------------------------------------------------

||| Empty mutation buffer.
|||
export
emptyBuffer : Buffer a
emptyBuffer =
  MkBuffer [<] 0

--------------------------------------------------------------------------------
--          Write Buffer Utilities
--------------------------------------------------------------------------------

||| Empty buffer state.
|||
export
emptyWriteBuffers : WriteBuffers a
emptyWriteBuffers =
  MkWriteBuffers emptyBuffer

--------------------------------------------------------------------------------
--          Metrics Utilities
--------------------------------------------------------------------------------

||| Empty rebuild metrics.
|||
||| Properties:
||| - No rebuilds observed.
||| - Average batch size is effectively zero.
|||
export
initialRebuildMetrics : RebuildMetrics
initialRebuildMetrics =
  MkRebuildMetrics
    0
    0
    0

--------------------------------------------------------------------------------
--          Rebuild Service Utilities
--------------------------------------------------------------------------------

||| Initial rebuild service state.
|||
||| Properties:
||| - Service begins idle.
||| - No rebuild failures recorded.
|||
export
initialRebuildServiceState : RebuildServiceState
initialRebuildServiceState =
  MkRebuildServiceState
    Sleeping
    Nothing
    initialRebuildMetrics

--------------------------------------------------------------------------------
--          Metrics
--------------------------------------------------------------------------------

||| Updates rebuild metrics after a successful rebuild cycle.
|||
||| Parameters:
||| - batchsize: Number of entries processed in this cycle.
|||
||| Properties:
||| - O(1).
||| - Pure deterministic update.
|||
export
updateMetrics :  RebuildMetrics
              -> Nat
              -> RebuildMetrics
updateMetrics m batchsize =
  { lastbatchsize  := batchsize
  , totalbatchsize $= (`plus` batchsize)
  , rebuildcount   $= S
  } m

||| Computes average rebuild batch size.
|||
||| Returns:
||| - 0 when no rebuilds have occurred.
|||
export
averageBatchSize :  RebuildMetrics
                 -> Nat
averageBatchSize m =
  case m.rebuildcount of
    Z =>
      0
    S _ =>
      m.totalbatchsize `div` m.rebuildcount

--------------------------------------------------------------------------------
--          Registering Threads
--------------------------------------------------------------------------------

||| Registers a thread if necessary and returns its thread context.
|||
||| Behavior:
||| - Existing registrations are reused.
||| - Missing registrations allocate fresh thread state.
|||
||| Properties:
||| - One ThreadContext per ThreadId.
||| - Preserves existing mutation state.
|||
export
registerThread :  Ref s (SortedMap ThreadId (ThreadContext a))
               -> ThreadId
               -> F1 s (ThreadContext a)
registerThread regref tid t =
  casupdate1 regref (\m =>
                      case lookup tid m of
                        Just ctx =>
                          (m, ctx)
                        Nothing  =>
                          let ctx = MkThreadContext
                                      tid
                                      0
                                      emptyWriteBuffers
                            in (insert tid ctx m, ctx)
                    ) t

--------------------------------------------------------------------------------
--          Generation Utilities
--------------------------------------------------------------------------------

||| Announces that a thread has entered a snapshot read section.
|||
||| Behavior:
||| - Registers the generation currently being read.
||| - Replaces any previous generation announcement.
|||
||| Properties:
||| - O(log n).
||| - One active generation per thread.
||| - Used by reclamation safety checks.
|||
export
enterGeneration :  Ref s (CombinedSnapshotState a)
                -> ThreadId
                -> Generation
                -> F1' s
enterGeneration combinedsnapshotstate tid gen t =
  casmod1 combinedsnapshotstate (\s =>
                                  { readerstate $= insert tid (MkReaderState gen)
                                  } s
                                ) t

||| Announces that a thread has completed a snapshot read section.
|||
||| Behavior:
||| - Removes thread participation state.
||| - Indicates thread no longer references a snapshot.
|||
||| Properties:
||| - O(log n).
||| - Enables reclamation progress.
|||
export
leaveGeneration :  Ref s (CombinedSnapshotState a)
                -> ThreadId
                -> F1' s
leaveGeneration combinedsnapshotstate tid t =
  casmod1 combinedsnapshotstate (\s =>
                                  { readerstate $= delete tid
                                  } s
                                ) t

||| Finds oldest active generation.
|||
||| Returns:
||| - Nothing when no readers exist.
||| - Just generation otherwise.
|||
||| Properties:
||| - O(n).
|||
export
minimumGeneration :  SortedMap ThreadId ReaderState
                  -> Maybe Generation
minimumGeneration rs =
    case map generation (values rs) of
      []    =>
        Nothing
      x::xs =>
        Just (foldl min x xs)

--------------------------------------------------------------------------------
--          Mutation Utilities
--------------------------------------------------------------------------------

||| Appends an Entry onto the end of a mutation buffer.
|||
||| Properties:
||| - O(1).
||| - Preserves insertion ordering.
|||
export
appendEntry :  Buffer a
            -> Entry a
            -> Buffer a
appendEntry (MkBuffer es n) e =
  MkBuffer (es :< e) (S n)

||| Appends a deferred mutation into the active write buffer.
|||
||| Properties:
||| - Frozen buffer remains unchanged.
||| - O(1) amortized.
|||
export
writeOperation :  WriteBuffers a
               -> Entry a
               -> WriteBuffers a
writeOperation (MkWriteBuffers active) e =
  MkWriteBuffers
    (appendEntry active e)

||| Converts an operation into an Entry and appends it into the owning thread's active mutation buffer.
|||
||| Steps:
||| - Acquire current timestamp.
||| - Register thread if necessary.
||| - Allocate Entry.
||| - Increment sequence counter.
||| - Append into active write buffer.
||| - Increment global write pressure.
||| - Mark rebuild work as pending.
|||
||| Properties:
||| - O(log n) registry update.
||| - O(1) buffer append.
||| - Deterministic replay ordering.
||| - Adaptive batching pressure is globally visible atomically.
|||
export
enqueueOperation :  Ref World (SortedMap ThreadId (ThreadContext a))
                 -> Ref World (CombinedSnapshotState a)
                 -> ThreadId
                 -> Operation a
                 -> F1 World Bool
enqueueOperation regref snapshotref tid op t =
  let now # t := ioToF1 (runElinIO grabTime) t
    in case now of
         Left err   =>
           (assert_total $ idris_crash "Data.LSMRRBVector.enqueueOperation: \{show err}") # t
         Right now' =>
           let ctx           # t := registerThread regref tid t
               ()            # t := casmod1 regref (\m =>
                                                     let entry = MkEntry
                                                                   op
                                                                   now'
                                                                   tid
                                                                   ctx.sequence
                                                         ctx'  = { sequence := S ctx.sequence
                                                                 , buffers  := writeOperation ctx.buffers entry
                                                                 } ctx
                                                       in insert tid ctx' m
                                                   ) t
               shouldtrigger # t := casupdate1 snapshotref (\s =>
                                                             let pressure' = S s.writepressure
                                                                 pending'  = pressure' >= s.batchwindow
                                                                 s'        = { writepressure := pressure'
                                                                             , rebuildpending := pending'
                                                                             } s
                                                               in (s', pending')
                                                           ) t
             in shouldtrigger # t
  where
    grabTime : Elin World [Errno] (IClock CLOCK_REALTIME)
    grabTime = getTime CLOCK_REALTIME

--------------------------------------------------------------------------------
--          Rebuild Trigger
--------------------------------------------------------------------------------

||| Sends a rebuild notification to the background rebuilder.
|||
||| Behavior:
||| - Requests background progression toward snapshot publication.
||| - Multiple requests may be coalesced.
||| - Triggering occurs only after adaptive batching thresholds indicate sufficient accumulated write pressure.
|||
||| Notes:
||| - Does not guarantee immediate rebuild execution.
||| - Does not guarantee publication.
|||
export
triggerRebuild :  LSMRRBVector s e a
               -> F1 s (Async e [] ())
triggerRebuild v t =
  let shouldsend # t := casupdate1 v.rebuildscheduled (\scheduled =>
                                                        case scheduled of
                                                          True  =>
                                                            (True, False)
                                                          False =>
                                                            (True, True)
                                                      ) t
    in case shouldsend of
         True  =>
           let action : Async e [] ()
               action = do
                 svc <- v.rebuilder.run
                 send svc Trigger
             in action # t
         False =>
           pure () # t

--------------------------------------------------------------------------------
--          Scheduling Helper
--------------------------------------------------------------------------------

||| Schedules rebuild work if adaptive batching has reached its target.
|||
||| Behavior:
||| - Checks whether the current write accumulation has crossed the adaptive batch threshold.
||| - Coalesces multiple concurrent scheduling attempts.
|||
||| Properties:
||| - O(1).
||| - Avoids duplicate rebuild requests.
|||
export
scheduleIfNeeded :  LSMRRBVector World e a
                 -> Bool
                 -> F1 World (Async e [] ())
scheduleIfNeeded v shouldTrigger t =
  case shouldTrigger of
    True =>
      triggerRebuild v t
    False =>
      pure () # t

--------------------------------------------------------------------------------
--          Mutation Operations
--------------------------------------------------------------------------------

||| Appends a value onto the logical end of the vector.
|||
||| Effect:
||| - Adds an Append operation to the thread-local buffer.
|||
export
append :  LSMRRBVector World e a
       -> ThreadId
       -> a
       -> F1' World
append v tid x t =
  let shouldtrigger # t := enqueueOperation v.buffers v.combinedsnapshotstate tid (Append x) t
      _             # t := scheduleIfNeeded v shouldtrigger t
    in () # t

||| Prepends a value onto the logical beginning of the vector.
|||
||| Effect:
||| - Adds a Prepend operation to the thread-local buffer.
|||
export
prepend :  LSMRRBVector World e a
        -> ThreadId
        -> a
        -> F1' World
prepend v tid x t =
  let shouldtrigger # t := enqueueOperation v.buffers v.combinedsnapshotstate tid (Prepend x) t
      _             # t := scheduleIfNeeded v shouldtrigger t
    in () # t

||| Inserts a value at a specified logical index.
|||
||| Effect:
||| - Adds an Insert operation to the thread-local buffer.
|||
export
insert :  LSMRRBVector World e a
       -> ThreadId
       -> Nat
       -> a
       -> F1' World
insert v tid i x t =
  let shouldtrigger # t := enqueueOperation v.buffers v.combinedsnapshotstate tid (Insert i x) t
      _             # t := scheduleIfNeeded v shouldtrigger t
    in () # t

||| Removes a value at a specified logical index.
|||
||| Effect:
||| - Adds a Delete operation to the thread-local buffer.
|||
export
delete :  LSMRRBVector World e a
       -> ThreadId
       -> Nat
       -> F1' World
delete v tid i t =
  let shouldtrigger # t := enqueueOperation v.buffers v.combinedsnapshotstate tid (Delete i) t
      _             # t := scheduleIfNeeded v shouldtrigger t
    in () # t

||| Replaces a value at a specified logical index.
|||
||| Effect:
||| - Adds an Update operation to the thread-local buffer.
|||
export
update :  LSMRRBVector World e a
       -> ThreadId
       -> Nat
       -> a
       -> F1' World
update v tid i x t =
  let shouldtrigger # t := enqueueOperation v.buffers v.combinedsnapshotstate tid (Update i x) t
      _             # t := scheduleIfNeeded v shouldtrigger t
    in () # t

--------------------------------------------------------------------------------
--          Buffer Rotation
--------------------------------------------------------------------------------

||| Extract active buffer ownership for rebuilding.
|||
||| Returns:
||| - Updated thread context with empty active buffer
||| - Extracted buffer now owned by rebuilder
|||
export
rotateBuffers :  ThreadContext a
              -> (ThreadContext a, Buffer a)
rotateBuffers ctx =
  let active = ctx.buffers.active
      ctx'   = { buffers :=
                   MkWriteBuffers
                     emptyBuffer
               } ctx
    in (ctx', active) 

--------------------------------------------------------------------------------
--          Registry Rotation
--------------------------------------------------------------------------------

||| Atomically extracts active buffers from all registered threads.
|||
||| Behavior:
||| - Replaces every thread's active buffer with an empty buffer.
||| - Transfers ownership of the previous active buffers to the rebuilder.
||| - Writers immediately continue appending into fresh active buffers.
|||
||| Returns:
||| - A list of extracted buffers now exclusively owned by the rebuilder.
|||
||| Properties:
||| - Each buffered operation is extracted exactly once.
||| - Extracted buffers cannot be observed or modified by writers.
||| - No buffered operations are duplicated or lost.
||| - Atomic across the entire thread registry.
||| - O(number of registered threads)
|||
||| Notes:
||| - Extraction performs ownership transfer rather than copying.
||| - Returned buffers are intended for a single rebuild cycle.
||| - Once extracted, buffers should be consumed exactly once.
|||
export
rotateAllBuffers :  Ref s (SortedMap ThreadId (ThreadContext a))
                 -> F1 s (List (Buffer a))
rotateAllBuffers regref t =
  casupdate1 regref (\m =>
                      let rotated   = map rotateBuffers m
                          contexts  = map fst rotated
                          extracted = map snd (values rotated)
                        in (contexts, extracted)
                    ) t

--------------------------------------------------------------------------------
--          Entry Collection
--------------------------------------------------------------------------------

||| Converts a buffer into a list of contained entries.
|||
||| Behavior:
||| - Preserves insertion order.
||| - Extracts buffered mutation events for rebuild processing.
|||
||| Properties:
||| - O(n).
||| - Does not modify buffer ownership.
||| - Pure projection operation.
|||
||| Notes:
||| - Intended for rebuild entry collection.
|||
export
bufferEntries :  Buffer a
              -> List (Entry a)
bufferEntries (MkBuffer es _) =
  cast es

||| Collects entries from multiple extracted buffers.
|||
||| Behavior:
||| - Traverses all buffers.
||| - Concatenates their entries into a single list.
|||
||| Properties:
||| - O(total entries).
||| - Preserves per-buffer ordering.
||| - Does not perform global ordering.
|||
||| Notes:
||| - Intended as a preprocessing step before sorting.
|||
export
collectEntries :  List (Buffer a)
               -> List (Entry a)
collectEntries =
  concatMap bufferEntries

||| Produces a deterministic global ordering of buffered entries.
|||
||| Ordering:
||| - timestamp
||| - thread id
||| - sequence number
|||
||| Properties:
||| - O(n log n).
||| - Deterministic across rebuild cycles.
|||
||| Notes:
||| - Required before replay to ensure stable behavior under concurrent writes.
|||
export
sortEntries :  Ord (Entry a)
            => List (Entry a)
            -> List (Entry a)
sortEntries =
  sort

--------------------------------------------------------------------------------
--          Replay
--------------------------------------------------------------------------------

export
applyOperation :  Operation a
               -> RRBVector a
               -> RRBVector a
applyOperation (Append x)   v =
  v |> x
applyOperation (Prepend x)  v =
  x <| v
applyOperation (Insert i x) v =
  insertAt i x v
applyOperation (Delete i)   v =
  deleteAt i v
applyOperation (Update i x) v =
  update i x v

export
replayEntries :  List (Entry a)
              -> RRBVector a
              -> RRBVector a
replayEntries es v =
  foldl (\acc, e => applyOperation e.operation acc) v es

--------------------------------------------------------------------------------
--          Reading
--------------------------------------------------------------------------------

||| Reads the current immutable snapshot under generation tracking.
|||
||| Steps:
||| - Atomically acquires the currently published snapshot.
||| - Registers the calling thread as observing that generation.
||| - Applies the supplied function to the snapshot tree.
||| - Removes reader participation after evaluation completes.
|||
||| Properties:
||| - Snapshot acquisition and generation announcement occur atomically.
||| - Readers observe a consistent immutable snapshot.
||| - Prevents reclamation of snapshots while actively referenced.
||| - Reader cleanup occurs even if evaluation fails or is canceled.
||| - Does not block writers or rebuild activity.
|||
||| Notes:
||| - The supplied function operates on a stable immutable snapshot.
||| - Concurrent writes or publications do not affect the observed tree.
||| - Reader registration exists only for the duration of this operation.
|||
||| Complexity:
||| - O(log n) for reader registration/removal.
||| - Snapshot access itself is O(1).
|||
readSnapshot :  LSMRRBVector World e a
             -> ThreadId
             -> (RRBVector a -> b)
             -> F1 World b
readSnapshot rrbvector tid f t =
  let res # t := ioToF1 (runElinIO readSnapshot') t
    in case res of
         Right res' =>
           res' # t
         Left err   =>
           (assert_total $ idris_crash "Data.LSMRRBVector.readSnapshot: \{show err}") # t
  where
    acquire : F1 World (SnapshotState a)
    acquire t =
      casupdate1 rrbvector.combinedsnapshotstate (\s =>
                                                   ( { readerstate $= insert tid (MkReaderState s.currentsnapshot.generation)
                                                     } s
                                                   , s.currentsnapshot
                                                   )
                                                 ) t
    use :  SnapshotState a
        -> F1 World b
    use snapshot t = f snapshot.tree # t
    release :  SnapshotState a
            -> F1' World
    release _ t =
      leaveGeneration rrbvector.combinedsnapshotstate tid t
    readSnapshot' : Elin World [Errno] b
    readSnapshot' =
      bracket (runIO acquire) (\snapshot => runIO (use snapshot)) (\snapshot => runIO (release snapshot))

--------------------------------------------------------------------------------
--          Read Operations
--------------------------------------------------------------------------------

||| Converts the current published snapshot into a list.
|||
||| Behavior:
||| - Reads the current immutable snapshot.
||| - Converts the snapshot contents into a List.
|||
||| Properties:
||| - Observes a consistent snapshot.
||| - Does not block writers or rebuild activity.
||| - Reader participation is cleaned up automatically.
|||
||| Notes:
||| - Concurrent writes published after acquisition are not visible.
|||
||| Complexity:
||| - Snapshot acquisition: O(1)
||| - Conversion: O(n)
|||
export
toList :  LSMRRBVector World e a
       -> ThreadId
       -> F1 World (List a)
toList rrbvector tid t =
  readSnapshot rrbvector tid Data.RRBVector.toList t

||| Returns the number of elements in the current published snapshot.
|||
||| Behavior:
||| - Reads the current immutable snapshot.
||| - Returns its logical length.
|||
||| Properties:
||| - Observes a consistent snapshot.
||| - Does not block writers or rebuild activity.
||| - Reader participation is cleaned up automatically.
|||
||| Notes:
||| - Concurrent writes published after acquisition are not visible.
|||
||| Complexity:
||| - O(1)
|||
export
length :  LSMRRBVector World e a
       -> ThreadId
       -> F1 World Nat
length rrbvector tid t =
  readSnapshot rrbvector tid Data.RRBVector.length t

||| Returns the element at a given index.
|||
||| Behavior:
||| - Reads the current immutable snapshot.
||| - Retrieves the element at the specified index.
|||
||| Properties:
||| - Observes a consistent snapshot.
||| - Does not block writers or rebuild activity.
||| - Reader participation is cleaned up automatically.
|||
||| Notes:
||| - Out-of-bounds behavior matches RRBVector.index.
||| - Concurrent writes published after acquisition are not visible.
|||
||| Complexity:
||| - O(log n)
|||
export
index :  LSMRRBVector World e a
      -> ThreadId
      -> Nat
      -> F1 World a
index rrbvector tid i t =
  readSnapshot rrbvector tid (\v => Data.RRBVector.index i v) t

||| Looks up an element by index.
|||
||| Behavior:
||| - Reads the current immutable snapshot.
||| - Returns Nothing if the index is out of bounds.
|||
||| Properties:
||| - Observes a consistent snapshot.
||| - Does not block writers or rebuild activity.
||| - Reader participation is cleaned up automatically.
|||
||| Notes:
||| - Concurrent writes published after acquisition are not visible.
|||
||| Complexity:
||| - O(log n)
|||
export
lookup :  LSMRRBVector World e a
       -> ThreadId
       -> Nat
       -> F1 World (Maybe a)
lookup rrbvector tid i t =
  readSnapshot rrbvector tid (\v => Data.RRBVector.lookup i v) t

||| Tests whether the current published snapshot is empty.
|||
||| Behavior:
||| - Reads the current immutable snapshot.
||| - Returns True when no elements exist.
|||
||| Properties:
||| - Observes a consistent snapshot.
||| - Does not block writers or rebuild activity.
||| - Reader participation is cleaned up automatically.
|||
||| Notes:
||| - Concurrent writes published after acquisition are not visible.
|||
||| Complexity:
||| - O(1)
|||
export
null :  LSMRRBVector World e a
     -> ThreadId
     -> F1 World Bool
null rrbvector tid t =
  readSnapshot rrbvector tid Data.RRBVector.null t

--------------------------------------------------------------------------------
--          Metrics Queries
--------------------------------------------------------------------------------

||| Returns current rebuild metrics.
|||
||| Properties:
||| - O(1)
||| - Snapshot of current service state
|||
export
rebuildMetrics :  RebuildServiceState
               -> RebuildMetrics
rebuildMetrics st =
  st.rebuildmetrics

||| Returns average rebuild batch size.
|||
||| Properties:
||| - O(1)
|||
export
averageRebuildBatchSize :  RebuildServiceState
                        -> Nat
averageRebuildBatchSize st =
  averageBatchSize st.rebuildmetrics

--------------------------------------------------------------------------------
--          Adaptive Batching
--------------------------------------------------------------------------------

||| Adjusts adaptive batching window according to observed write pressure.
|||
||| Rules:
||| - Pressure above the current window expands the window.
||| - Pressure below half the current window shrinks the window.
||| - Window never shrinks below 1.
|||
||| Properties:
||| - Pure deterministic policy function.
||| - Does not affect correctness.
||| - Only influences rebuild batching behavior.
|||
export
adjustBatchWindow :  Nat
                  -> Nat
                  -> Nat
adjustBatchWindow pressure window =
  case pressure > window of
    True  =>
      window * 2
    False =>
      case pressure < (window `div` 2) of
        True  =>
          max 1 (window `div` 2)
        False =>
          window

--------------------------------------------------------------------------------
--          Publication
--------------------------------------------------------------------------------

||| Atomically publishes a rebuilt snapshot and advances adaptive batching state.
|||
||| Steps:
||| - Publish rebuilt immutable tree.
||| - Increment snapshot generation.
||| - Retire previous snapshot.
||| - Reset accumulated write pressure.
||| - Clear rebuild pending state.
||| - Adaptively adjust batching window.
|||
||| Properties:
||| - Snapshot publication is atomic.
||| - Readers always observe a consistent snapshot/generation pair.
||| - Adaptive batching state transitions are globally visible atomically.
||| - Previous snapshots become eligible for reclamation.
|||
||| Notes:
||| - Adaptive batching decisions are based on write pressure observed since the previous successful publication.
|||
export
publishSnapshot :  Ref s (CombinedSnapshotState a)
                -> List (Entry a)
                -> F1 s Generation
publishSnapshot combinedsnapshotstateref entries t =
  casupdate1 combinedsnapshotstateref (\(MkCombinedSnapshotState snapshot retired readers writepressure rebuildpending batchwindow) =>
                                        let rebuilt    = replayEntries entries snapshot.tree
                                            newgen     = S snapshot.generation
                                            snapshot'  = MkSnapshotState newgen rebuilt
                                            retired'   = MkRetiredSnapshot snapshot.generation snapshot.tree :: retired                      
                                            nextwindow = adjustBatchWindow writepressure batchwindow
                                          in ( MkCombinedSnapshotState snapshot' retired' readers 0 False nextwindow
                                             , newgen
                                             )
                                      ) t

--------------------------------------------------------------------------------
--          Reclamation
--------------------------------------------------------------------------------

||| Reclaims retired snapshots that are no longer visible to readers.
|||
||| Rules:
||| - If no readers exist: reclaim everything.
||| - Otherwise: reclaim snapshots older than oldest active generation.
|||
||| Properties:
||| - Safe generation-based reclamation.
||| - O(number of retired snapshots)
|||
export
reclaimSnapshots :  Ref s (CombinedSnapshotState a)
                 -> F1' s
reclaimSnapshots combinedsnapshotstate t =
  casmod1 combinedsnapshotstate (\(MkCombinedSnapshotState snapshot retired readers writepressure rebuildpending batchwindow) =>
                                  let survivors = case minimumGeneration readers of
                                                    Nothing     =>
                                                      []
                                                    Just mingen =>
                                                      filter (\snap =>
                                                               snap.generation >= mingen
                                                             ) retired
                                    in MkCombinedSnapshotState snapshot survivors readers writepressure rebuildpending batchwindow
                                ) t

--------------------------------------------------------------------------------
--          Single Rebuild Cycle
--------------------------------------------------------------------------------

||| Executes one rebuild pass.
|||
||| Steps:
||| - Rotate all active buffers.
||| - Collect extracted entries.
||| - Sort entries deterministically.
||| - Publish rebuilt snapshot.
||| - Reclaim retired snapshots.
|||
||| Returns:
||| - Published generation when work exists.
||| - 0 when no publication occurred.
||| - Whether any entries were processed.
|||
||| Notes:
||| - Performs exactly one ownership-transfer cycle.
||| - Does not guarantee complete draining.
|||
export covering
rebuildOnce :  Ord (Entry a)
            => Ref World (SortedMap Int (ThreadContext a))
            -> Ref World (CombinedSnapshotState a)
            -> RebuildServiceState
            -> Async e [] (RebuildServiceState, Generation, Bool)
rebuildOnce buffers combinedsnapshotstate st = do
  -- RotatingBuffers
  let st1        : RebuildServiceState
      st1        = { rebuildphase := RotatingBuffers } st
  extracted      <- liftIO (runIO (rotateAllBuffers buffers))
  -- CollectingEntries
  let st2        : RebuildServiceState
      st2        = { rebuildphase := CollectingEntries } st1
      entries    = collectEntries extracted
      batchsize  = length entries
  case isNil entries of
    True  => do
      let st' = { rebuildphase := Sleeping } st2
      pure (st', 0, False)
    False => do
      -- SortingEntries
      let st3 : RebuildServiceState
          st3 = { rebuildphase := SortingEntries
                } st2
          sorted = sortEntries entries
      -- PublishingSnapshot
      let st4    : RebuildServiceState
          st4    = { rebuildphase := PublishingSnapshot } st3
      generation <- liftIO (runIO (publishSnapshot combinedsnapshotstate sorted))
      liftIO (runIO (reclaimSnapshots combinedsnapshotstate))
      let st5    : RebuildServiceState
          st5    = { rebuildphase := Sleeping
                   , rebuildmetrics := updateMetrics st4.rebuildmetrics batchsize
                   } st4
      pure (st5, generation, True)

--------------------------------------------------------------------------------
--          Flush Until Empty
--------------------------------------------------------------------------------

||| Repeatedly performs rebuild cycles until no buffered work remains.
|||
||| Properties:
||| - Ensures Flush observes all writes that arrived before completion.
||| - Writers may continue concurrently.
||| - Terminates once a rotation extracts no entries.
|||
||| Returns:
||| - Final rebuild state.
||| - Last published generation.
|||
export covering
flushUntilEmpty :  Ord (Entry a)
                => Ref World (SortedMap Int (ThreadContext a))
                -> Ref World (CombinedSnapshotState a)
                -> RebuildServiceState
                -> Async e [] (RebuildServiceState, Generation)
flushUntilEmpty buffers combinedsnapshotstate st =
  let loop :  RebuildServiceState
           -> Generation
           -> Async e [] (RebuildServiceState, Generation)
      loop st lastgen = do
        (st', gen, hadentries) <- rebuildOnce buffers combinedsnapshotstate st
        case hadentries of
          True  =>
            loop st' gen
          False =>
            pure (st', gen)
    in loop st 0

--------------------------------------------------------------------------------
--          Rebuilder Service
--------------------------------------------------------------------------------

||| Processes a rebuild request issued by the LSM write system.
|||
||| This service is responsible for advancing the immutable snapshot from the accumulated thread-local mutation buffers.
|||
||| Two modes of operation exist:
|||
||| Trigger:
||| - Requests background progression toward publication.
||| - May coalesce multiple requests.
||| - Performs at most one rebuild cycle.
||| - May or may not publish a new snapshot.
|||
||| Flush:
||| - Repeatedly performs rebuild cycles until all buffered writes observed at invocation time are incorporated.
||| - Guarantees that all prior writes are reflected in the returned snapshot generation.
||| - May perform multiple rotations and publications internally.
|||
||| Concurrency guarantees:
||| - Writers may continue appending during rebuild.
||| - Flush only guarantees completeness relative to a quiescent cut of buffer rotation visibility.
|||
||| Return values:
||| - Trigger returns unit acknowledgement.
||| - Flush returns the final snapshot generation after draining.
|||
||| State transitions:
||| Sleeping → RotatingBuffers → CollectingEntries → SortingEntries → PublishingSnapshot → Sleeping
|||
||| Notes:
||| - Empty rebuild cycles do not advance generation.
||| - Flush drains until a cycle produces no entries.
||| - Trigger is a bounded operation, Flush is unbounded (but finite under quiescent assumptions).
|||
export covering
handleRebuildRequest :  Ord (Entry a)
                     => Ref World (SortedMap Int (ThreadContext a))
                     -> Ref World (CombinedSnapshotState a)
                     -> Ref World Bool
                     -> RebuildServiceState
                     -> (req : RebuildRequest)
                     -> Async e [] (RebuildServiceState, RebuildResponse req)
handleRebuildRequest buffers combinedsnapshotstate rebuildscheduled st Trigger = do
  (_, _, _) <- rebuildOnce buffers combinedsnapshotstate st
  liftIO (runIO (casmod1 rebuildscheduled (const False)))
  let st' = { rebuildphase := Sleeping
            , rebuildfailure := Nothing
            } st
  pure (st', ())
handleRebuildRequest buffers combinedsnapshotstate rebuildscheduled st Flush = do
  (_, generation) <- flushUntilEmpty buffers combinedsnapshotstate st
  liftIO (runIO (casmod1 rebuildscheduled (const False)))  
  let st' = { rebuildphase := Sleeping
            , rebuildfailure := Nothing
            } st
  pure (st', generation)

--------------------------------------------------------------------------------
--          Spawn Rebuilder
--------------------------------------------------------------------------------

||| Creates and starts the background rebuild actor service.
|||
||| The returned service owns:
||| - rebuild state
||| - request mailbox
||| - worker thread
|||
||| Lifecycle:
|||
||| Trigger
|||     ↓
||| pending := True
|||     ↓
||| rebuild
|||     ↓
||| publish snapshot
|||     ↓
||| increment generation
|||
export covering
spawnRebuilderService :  Ord (Entry a)
                      => Ref World (SortedMap Int (ThreadContext a))
                      -> Ref World (CombinedSnapshotState a)
                      -> Ref World Bool
                      -> Async e [] (Service e [] RebuildRequest RebuildResponse)
spawnRebuilderService buffers combinedsnapshotstate rebuildscheduled =
  service RebuildResponse
          initialRebuildServiceState
          ( handleRebuildRequest
              buffers
              combinedsnapshotstate
              rebuildscheduled
          )

--------------------------------------------------------------------------------
--          Default Config
--------------------------------------------------------------------------------

||| Default LSMRRBVector configuration.
|||
||| Current defaults favor balanced throughput and latency.
|||
export
defaultConfig : LSMRRBConfig
defaultConfig = MkLSMRRBConfig 64

--------------------------------------------------------------------------------
--          Creating Log-Structured Merge RRB-Vectors
--------------------------------------------------------------------------------

||| Empty log-structured merge vector using a user-provided configuration.
|||
||| Parameters:
||| - initialbatchwindow: Starting adaptive batching target.
|||
||| Notes:
||| - Smaller values rebuild more aggressively.
||| - Larger values favor write throughput.
|||
export covering
emptyWith :  Ord (Entry a)
          => LSMRRBConfig
          -> F1 World (LSMRRBVector World e a)
emptyWith config t =
  let buffers               # t := ref1 Data.SortedMap.empty t
      combinedsnapshotstate # t := ref1 (MkCombinedSnapshotState (MkSnapshotState Z Empty) [] Data.SortedMap.empty 0 False config.initialbatchwindow) t
      rebuildscheduled      # t := ref1 False t
      rebuilder                 := spawnRebuilderService buffers combinedsnapshotstate rebuildscheduled
    in MkLSMRRBVector buffers combinedsnapshotstate rebuildscheduled (MkManagedService rebuilder) # t

||| The empty log-structured merge vector. O(1)
|||
export covering
empty :  Ord (Entry a)
      => F1 World (LSMRRBVector World e a)
empty t =
  emptyWith defaultConfig t

||| Empty LSMRRBVector tuned for high sustained write throughput.
|||
||| Configuration:
||| - Initial adaptive batch window: 512
|||
||| Behavior:
||| - Favors larger rebuild batches.
||| - Reduces rebuild frequency under heavy write load.
||| - May increase visibility latency for newly written values.
|||
||| Notes:
||| - Intended for write-heavy workloads.
|||
export covering
fastWritesEmpty : F1 World (LSMRRBVector World e Int)
fastWritesEmpty =
  emptyWith (MkLSMRRBConfig 512)

||| Empty LSMRRBVector tuned for low publication latency.
|||
||| Configuration:
||| - Initial adaptive batch window: 16
|||
||| Behavior:
||| - Favors frequent rebuild cycles.
||| - Reduces time between writes and publication.
||| - May increase rebuild overhead under heavy load.
|||
||| Notes:
||| - Intended for latency-sensitive workloads.
|||
export covering
lowLatencyEmpty : F1 World (LSMRRBVector World e Int)
lowLatencyEmpty =
  emptyWith (MkLSMRRBConfig 16)

||| Singleton log-structured merge vector using a user-provided configuration.
|||
||| Parameters:
||| - initialbatchwindow: Starting adaptive batching target.
|||
||| Notes:
||| - Smaller values rebuild more aggressively.
||| - Larger values favor write throughput.
|||
export covering
singletonWith :  Ord (Entry a)
              => LSMRRBConfig
              -> a
              -> F1 World (LSMRRBVector World e a)
singletonWith config x t =
  let buffers               # t := ref1 Data.SortedMap.empty t
      combinedsnapshotstate # t := ref1 (MkCombinedSnapshotState (MkSnapshotState Z (Root 1 0 (Leaf $ A 1 $ fill 1 x))) [] Data.SortedMap.empty 0 False config.initialbatchwindow) t
      rebuildscheduled      # t := ref1 False t
      rebuilder                 := spawnRebuilderService buffers combinedsnapshotstate rebuildscheduled
    in MkLSMRRBVector buffers combinedsnapshotstate rebuildscheduled (MkManagedService rebuilder) # t

||| A log-structured merge vector with a single element. O(1)
|||
export covering
singleton :  Ord (Entry a)
          => a
          -> F1 World (LSMRRBVector World e a)
singleton x t =
  singletonWith defaultConfig x t
