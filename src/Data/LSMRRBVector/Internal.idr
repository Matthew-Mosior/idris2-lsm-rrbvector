||| Log-Structured Merge RRB Vectors Internals
module Data.LSMRRBVector.Internal

import public Data.LSMRRBVector.Types
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
import IO.Async.Core
import IO.Async.Loop.Poller
import IO.Async.Loop.Posix
import IO.Async.Posix
import IO.Async.Service
import IO.Async.Util
import Syntax.T1 as T1
import System.Concurrency
import System.Posix.Timer
import System.Posix.Timer.Prim

%hide Control.Monad.Elin.Elin.(.run)
%hide Control.Monad.Elin.Elin.run
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
--          Thread Context Utilities
--------------------------------------------------------------------------------

||| Determines whether a buffer contains pending entries.
|||
||| Returns:
||| - True when no buffered operations exist.
||| - False otherwise.
|||
||| Properties:
||| - O(1).
|||
export
bufferEmpty :  Buffer a
            -> Bool
bufferEmpty b =
  b.length == 0

||| Determines whether a thread context contains buffered work.
|||
||| Returns:
||| - True when all thread-local mutation state is empty.
||| - False otherwise.
|||
||| Properties:
||| - O(1).
|||
||| Notes:
||| - Sequence numbers are ignored.
||| - Historical sequence advancement does not imply pending work.
|||
export
threadContextEmpty :  ThreadContext a
                   -> Bool
threadContextEmpty ctx =
  bufferEmpty ctx.buffers.active

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
registerThread :  Ref World (SortedMap ThreadId (ThreadContext a))
               -> ThreadId
               -> IO (ThreadContext a)
registerThread regref tid =
  update regref (\m =>
                  case lookup tid m of
                    Just ctx =>
                      (m, ctx)
                    Nothing  =>
                      let ctx = MkThreadContext
                                  tid
                                  0
                                  emptyWriteBuffers
                        in (insert tid ctx m, ctx)
                )

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
enterGeneration :  Ref World (CombinedSnapshotState a)
                -> ThreadId
                -> IO (SnapshotState a)
enterGeneration combinedsnapshotstate tid =
  update combinedsnapshotstate (\s =>
                                 ( { readerstate $= insert tid (MkReaderState s.currentsnapshot.generation)
                                   } s
                                 , s.currentsnapshot
                                 )
                               )

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
leaveGeneration :  Ref World (CombinedSnapshotState a)
                -> ThreadId
                -> IO ()
leaveGeneration combinedsnapshotstate tid =
  mod combinedsnapshotstate (\s =>
                              { readerstate $= delete tid
                              } s
                            )

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
                 -> IO Bool
enqueueOperation regref snapshotref tid op = do
  now <- runElinIO grabTime
  case now of
    Left err   =>
      assert_total $ idris_crash "Data.LSMRRBVector.enqueueOperation: \{show err}"
    Right now' => do
      ctx <- registerThread regref tid
      mod regref (\m =>
                   let entry = MkEntry
                                 op
                                 now'
                                 tid
                                 ctx.sequence
                       ctx'  = { sequence := S ctx.sequence
                               , buffers  := writeOperation ctx.buffers entry
                               } ctx
                     in insert tid ctx' m
                 )
      update snapshotref (\s =>
                           let pressure' = S s.writepressure
                               pending'  = pressure' >= s.batchwindow
                               s'        = { writepressure := pressure'
                                           , rebuildpending := pending'
                                           } s
                             in (s', pending')
                         )
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
triggerRebuild :  LSMRRBVector World a
               -> RebuildService Poll
               -> Async Poll [Errno] ()
triggerRebuild lsmrrbvector svc = do
  shouldsend <- update lsmrrbvector.rebuildscheduled (\scheduled =>
                                                       case scheduled of
                                                         True  =>
                                                           (True, False)
                                                         False =>
                                                           (True, True)
                                                     )
  case shouldsend of
    True  => do
      run svc Trigger
    False =>
      pure ()

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
scheduleIfNeeded :  LSMRRBVector World a
                 -> RebuildService Poll
                 -> Bool
                 -> Async Poll [Errno] ()
scheduleIfNeeded lsmrrbvector svc shouldtrigger =
  case shouldtrigger of
    True =>
      triggerRebuild lsmrrbvector svc
    False =>
      pure ()

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
||| - Replaces active buffers with empty buffers.
||| - Transfers ownership of previous active buffers.
||| - Removes thread registrations whose post-rotation state contains no pending work.
|||
||| Lifecycle:
||| - Thread registrations are cleaned up automatically during rebuild.
||| - Explicit thread unregistration is unnecessary.
|||
||| Properties:
||| - Extracted entries appear exactly once.
||| - Prevents unbounded registry growth.
||| - O(number of registered threads).
|||
export
rotateAllBuffers :  Ref World (SortedMap ThreadId (ThreadContext a))
                 -> IO (List (Buffer a))
rotateAllBuffers regref = do
  update regref (\m =>
                  let rotated : SortedMap ThreadId (ThreadContext a, Buffer a)
                      rotated = map rotateBuffers m
                      extracted : List (Buffer a)
                      extracted = map snd (values rotated)
                      survivors : SortedMap ThreadId (ThreadContext a)
                      survivors = foldl (\acc, (tid, (ctx, _)) =>
                                          case threadContextEmpty ctx of
                                            True =>
                                              acc
                                            False =>
                                              insert tid ctx acc
                                        )
                                        Data.SortedMap.empty
                                        (Data.SortedMap.toList rotated)
                    in (survivors, extracted)
                )

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

||| Reads the current immutable snapshot together with its generation.
|||
||| Behavior:
||| - Atomically captures the current SnapshotState.
||| - Registers the thread as an active reader of that generation.
||| - Passes (generation, snapshot tree) to the user function.
||| - Ensures reader registration is cleaned up after evaluation.
|||
||| Key property:
||| - The generation and tree are consistent and taken from the same CAS snapshot.
|||
||| This enables:
||| - Precise visibility reasoning.
||| - Safe interaction with reclamation.
||| - Deterministic debugging of snapshot lag.
|||
||| Complexity:
||| - O(log n) for reader registration/removal.
||| - O(1) snapshot access.
|||
export
readSnapshotWithGeneration :  LSMRRBVector World a
                           -> ThreadId
                           -> ((Generation, RRBVector a) -> b)
                           -> IO b
readSnapshotWithGeneration rrbvector tid f = do
  res <- runElinIO readSnapshotWithGeneration'
  case res of
    Right res' =>
      pure res'
    Left err   =>
      assert_total $ idris_crash "Data.LSMRRBVector.readSnapshotWithGeneration: \{show err}"
  where
    acquire : F1 World (SnapshotState a)
    acquire = ioToF1 (enterGeneration rrbvector.combinedsnapshotstate tid)
    use :  SnapshotState a
        -> F1 World b
    use snapshot t =
      let gen := snapshot.generation
        in f (gen, snapshot.tree) # t
    release :  SnapshotState a
            -> F1' World
    release _ = ioToF1 (leaveGeneration rrbvector.combinedsnapshotstate tid)
    readSnapshotWithGeneration' : Elin World [Errno] b
    readSnapshotWithGeneration' =
      bracket (runIO acquire)
              (\snapshot => runIO (use snapshot))
              (\snapshot => runIO (release snapshot))

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
publishSnapshot :  Ref World (CombinedSnapshotState a)
                -> List (Entry a)
                -> IO Generation
publishSnapshot combinedsnapshotstateref entries =
  update combinedsnapshotstateref (\(MkCombinedSnapshotState snapshot retired readers writepressure rebuildpending batchwindow) =>
                                    let rebuilt    = replayEntries entries snapshot.tree
                                        newgen     = S snapshot.generation
                                        snapshot'  = MkSnapshotState newgen rebuilt
                                        retired'   = MkRetiredSnapshot snapshot.generation snapshot.tree :: retired
                                        nextwindow = adjustBatchWindow writepressure batchwindow
                                      in ( MkCombinedSnapshotState snapshot' retired' readers 0 False nextwindow
                                         , newgen
                                         )
                                  )

--------------------------------------------------------------------------------
--          Reclamation Utilities
--------------------------------------------------------------------------------

||| Computes the newest retired generation that may safely be reclaimed.
|||
||| Behavior:
||| - Determines the oldest snapshot generation currently referenced by active readers.
||| - Finds the highest retired generation strictly older than that reader boundary.
||| - Returns Nothing when no reclaimable generation exists.
|||
||| Returns:
||| - Nothing: No readers exist, or no retired snapshots can be reclaimed.
|||
||| - Just g: Every retired snapshot with generation <= g may safely be reclaimed.
|||
||| Safety rules:
||| - Readers observing generation G may still require snapshot G.
||| - Readers may also require all newer generations.
||| - Only snapshots strictly older than the oldest active reader generation are reclaimable.
|||
||| Example:
|||
||| Retired              <-> [1,2,3,4,5]
||| Active readers       <-> [4,7]
||| oldest active reader <-> 4
||| Safe reclamation     <-> [1,2,3]
||| Result               <-> Just 3
|||
||| Properties:
||| - O(number of retired snapshots + number of readers).
||| - Never reclaims a snapshot visible to any active reader.
||| - Computes a maximal safe reclamation boundary.
|||
export
reclamationCutoff :
     List (RetiredSnapshot a)
  -> SortedMap ThreadId ReaderState
  -> Maybe Generation
reclamationCutoff retired readers =
  case minimumGeneration readers of
    Nothing =>
      Nothing
    Just oldest =>
      case map generation ( filter
                             (\snap =>
                               snap.generation < oldest)
                            retired
                          ) of

        []      =>
          Nothing
        x :: xs =>
          Just (foldl max x xs)

--------------------------------------------------------------------------------
--          Reclamation
--------------------------------------------------------------------------------

||| Reclaims retired snapshots no longer visible to active readers.
|||
||| Rules:
||| - No readers: Reclaim everything.
||| - Readers exist: retain snapshots at or newer than the oldest active reader boundary.
|||
||| Properties:
||| - Safe generation-based reclamation.
||| - Keeps only snapshots potentially observable by readers.
||| - O(number of retired snapshots + number of readers).
|||
export
reclaimSnapshots :  Ref World (CombinedSnapshotState a)
                 -> IO ()
reclaimSnapshots combinedsnapshotstate =
  mod combinedsnapshotstate (\(MkCombinedSnapshotState snapshot retired readers writepressure rebuildpending batchwindow) =>
                              let survivors = case reclamationCutoff retired readers of
                                                Nothing     =>
                                                  case minimumGeneration readers of
                                                    Nothing =>
                                                      []
                                                    Just _  =>
                                                      retired
                                                Just cutoff =>
                                                  filter (\snap =>
                                                           snap.generation > cutoff
                                                         ) retired
                                in MkCombinedSnapshotState snapshot survivors readers writepressure rebuildpending batchwindow
                            )

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
            -> Async Poll [Errno] (RebuildServiceState, Generation, Bool)
rebuildOnce buffers combinedsnapshotstate st = do
  -- RotatingBuffers
  let st1        : RebuildServiceState
      st1        = { rebuildphase := RotatingBuffers } st
  extracted      <- liftIO (rotateAllBuffers buffers)
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
      generation <- liftIO (publishSnapshot combinedsnapshotstate sorted)
      liftIO (reclaimSnapshots combinedsnapshotstate)
      let st5    : RebuildServiceState
          st5    = { rebuildphase := Sleeping
                   , rebuildmetrics := updateMetrics st4.rebuildmetrics batchsize
                   } st4
      pure (st5, generation, True)

--------------------------------------------------------------------------------
--          Flush Until Empty
--------------------------------------------------------------------------------

||| Repeatedly performs rebuild cycles until a rotation extracts no work.
|||
||| Behavior:
||| - Executes rebuild cycles in sequence.
||| - Each cycle atomically rotates ownership of active buffers.
||| - Extracted entries are rebuilt into a published snapshot.
||| - Terminates once a rotation produces no extracted entries.
|||
||| Visibility guarantees:
||| - Flush establishes a quiescent visibility boundary at buffer rotation.
||| - All writes already present in rotated buffers are incorporated before completion.
||| - Writes arriving concurrently may appear either before or after completion depending on timing.
||| - Flush does not stop writers or establish a global synchronization barrier.
|||
||| Concurrency properties:
||| - Writers continue appending during rebuild execution.
||| - Multiple rebuild cycles may be required if writes continue arriving.
||| - Progress remains lock-free for writers.
|||
||| Returns:
||| - Final rebuild state.
||| - Most recently published generation.
|||
||| Notes:
||| - Completion means no buffered work was visible during the final rotation.
||| - This is weaker than "all writes before return".
||| - Stronger linearizable flush semantics would require an explicit epoch or barrier mechanism.
|||
export covering
flushUntilEmpty :  Ord (Entry a)
                => Ref World (SortedMap Int (ThreadContext a))
                -> Ref World (CombinedSnapshotState a)
                -> RebuildServiceState
                -> Async Poll [Errno] (RebuildServiceState, Generation)
flushUntilEmpty buffers combinedsnapshotstate st =
  let loop :  RebuildServiceState
           -> Generation
           -> Async Poll [Errno] (RebuildServiceState, Generation)
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
||| - Guarantees that all writes visible in rotated buffers during draining are reflected in the returned generation.
||| - Concurrent writes may be incorporated either before or after completion.
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
                     => LSMRRBVector World a
                     -> RebuildServiceState
                     -> (req : RebuildRequest)
                     -> Async Poll [Errno] ()
handleRebuildRequest lsmrrbvector st Trigger = do
  (_, _, _) <- rebuildOnce lsmrrbvector.buffers lsmrrbvector.combinedsnapshotstate st
  liftIO (mod lsmrrbvector.rebuildscheduled (const False))
  let st' : RebuildServiceState
      st' = { rebuildphase := Sleeping
            } st
  pure ()
handleRebuildRequest lsmrrbvector st Flush = do
  (_, generation) <- flushUntilEmpty lsmrrbvector.buffers lsmrrbvector.combinedsnapshotstate st
  liftIO (mod lsmrrbvector.rebuildscheduled (const False))
  let st' : RebuildServiceState
      st' = { rebuildphase := Sleeping
            } st
  pure ()

--------------------------------------------------------------------------------
--          Rebuild Service
--------------------------------------------------------------------------------

export covering
rebuilderService :  Ord (Entry a)
                 => LSMRRBVector World a
                 -> RebuildServiceState
                 -> List (LSMRRBVector World a -> RebuildService Poll -> Async Poll [Errno] ())
                 -> Async Poll [Errno] ()
rebuilderService lsmrrbvector st actions = do
  rebuilderservice <-
    rebuilder
      (\req => handleRebuildRequest lsmrrbvector st req)
  ignore $
    parTraverse (\action => action lsmrrbvector rebuilderservice) actions

--------------------------------------------------------------------------------
--          LSMRRBVector Service
--------------------------------------------------------------------------------

export covering
lsmrrbvectorService :  LSMRRBVector World a
                    -> List (LSMRRBVector World a -> Async Poll [Errno] ())
                    -> Async Poll [Errno] ()
lsmrrbvectorService lsmrrbvector actions =
  ignore $
    parTraverse (\action => action lsmrrbvector) actions

--------------------------------------------------------------------------------
--          Rebuild And LSMRRBVector Service
--------------------------------------------------------------------------------

export covering
rebuilderAndLSMRRBVectorService :  Async Poll [Errno] ()
                                -> Async Poll [Errno] ()
                                -> Async Poll [Errno] ()
rebuilderAndLSMRRBVectorService rebuilderservice lsmrrbvectorservice =
  ignore $
    par [ -- writers
         rebuilderservice
        , -- readers
          lsmrrbvectorservice
        ]
