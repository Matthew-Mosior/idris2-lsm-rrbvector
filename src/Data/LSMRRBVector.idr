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
export
emptyBuffer : Buffer a
emptyBuffer =
  MkBuffer [<] 0

--------------------------------------------------------------------------------
--          Write Buffer Utilities
--------------------------------------------------------------------------------

||| Empty double-buffer state.
export
emptyWriteBuffers : WriteBuffers a
emptyWriteBuffers =
  MkWriteBuffers emptyBuffer emptyBuffer

--------------------------------------------------------------------------------
--          Rebuild Service Utilities
--------------------------------------------------------------------------------

||| Initial rebuild state.
export
initialRebuildServiceState : RebuildServiceState
initialRebuildServiceState =
  MkRebuildServiceState
    Sleeping
    0
    False

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
writeOperation (MkWriteBuffers active frozen) e =
  MkWriteBuffers
    (appendEntry active e)
    frozen

||| Converts an operation into an Entry and appends it into the owning thread's active mutation buffer.
|||
||| Steps:
||| - Acquire current timestamp.
||| - Register thread if necessary.
||| - Allocate Entry.
||| - Increment sequence counter.
||| - Update thread registry.
|||
||| Properties:
||| - O(log n) registry update.
||| - O(1) buffer append.
||| - Deterministic replay ordering.
|||
export
enqueueOperation :  Ref World (SortedMap ThreadId (ThreadContext a))
                 -> ThreadId
                 -> Operation a
                 -> F1' World
enqueueOperation regref tid op t =
  let now # t := ioToF1 (runElinIO grabTime) t
    in case now of
         Left err   =>
           (assert_total $ idris_crash "Data.LSMRRBVector.enqueueOperation: \{show err}") # t
         Right now' =>
           casmod1 regref (\m =>
                            case lookup tid m of
                              Nothing  =>
                                let ctx   = MkThreadContext
                                              tid
                                              0
                                              emptyWriteBuffers
                                    entry = MkEntry
                                              op
                                              now'
                                              tid
                                              ctx.sequence
                                    ctx'  = { sequence := S ctx.sequence
                                            , buffers  :=
                                                writeOperation ctx.buffers entry
                                            } ctx
                                  in insert tid ctx' m
                              Just ctx =>
                                let entry = MkEntry
                                              op
                                              now'
                                              tid
                                              ctx.sequence
                                    ctx'  = { sequence := S ctx.sequence
                                            , buffers  :=
                                                writeOperation ctx.buffers entry
                                            } ctx
                                  in insert tid ctx' m
                          ) t
  where
    grabTime : Elin World [Errno] (IClock CLOCK_REALTIME)
    grabTime = getTime CLOCK_REALTIME

--------------------------------------------------------------------------------
--          Operations
--------------------------------------------------------------------------------

||| Appends a value onto the logical end of the vector.
|||
||| Effect:
||| - Adds an Append operation to the thread-local buffer.
|||
export
append :  Ref World (SortedMap ThreadId (ThreadContext a))
       -> ThreadId
       -> a
       -> F1' World
append regref tid x =
  enqueueOperation regref tid (Append x)

||| Prepends a value onto the logical beginning of the vector.
|||
||| Effect:
||| - Adds a Prepend operation to the thread-local buffer.
|||
export
prepend :  Ref World (SortedMap ThreadId (ThreadContext a))
        -> ThreadId
        -> a
        -> F1' World
prepend regref tid x =
  enqueueOperation regref tid (Prepend x)

||| Inserts a value at a specified logical index.
|||
||| Effect:
||| - Adds an Insert operation to the thread-local buffer.
|||
export
insert :  Ref World (SortedMap ThreadId (ThreadContext a))
       -> ThreadId
       -> Nat
       -> a
       -> F1' World
insert regref tid i x =
  enqueueOperation regref tid (Insert i x)

||| Removes a value at a specified logical index.
|||
||| Effect:
||| - Adds a Delete operation to the thread-local buffer.
|||
export
delete :  Ref World (SortedMap ThreadId (ThreadContext a))
       -> ThreadId
       -> Nat
       -> F1' World
delete regref tid i =
  enqueueOperation regref tid (Delete i)

||| Replaces a value at a specified logical index.
|||
||| Effect:
||| - Adds an Update operation to the thread-local buffer.
|||
export
update :  Ref World (SortedMap ThreadId (ThreadContext a))
       -> ThreadId
       -> Nat
       -> a
       -> F1' World
update regref tid i x =
  enqueueOperation regref tid (Update i x)

--------------------------------------------------------------------------------
--          Rebuild Trigger
--------------------------------------------------------------------------------

||| Sends a rebuild notification to the background rebuilder.
|||
||| Notes:
||| - Multiple Trigger requests may be coalesced.
||| - Does not guarantee an immediate rebuild.
||| - Returns after the request has been accepted by the service.
|||
export
triggerRebuild :  LSMRRBVector s e a
               -> F1 s (Async e [] ())
triggerRebuild v t =
  let action : Async e [] ()
      action = do
        svc <- v.rebuilder.run
        send svc Trigger
    in action # t

--------------------------------------------------------------------------------
--          Buffer Rotation
--------------------------------------------------------------------------------

||| Swap active/frozen and clear active.
|||
export
rotateBuffers :  ThreadContext a
              -> ThreadContext a
rotateBuffers ctx =
  let bufs = ctx.buffers
    in { buffers :=
           MkWriteBuffers
             emptyBuffer
             bufs.active
       } ctx

--------------------------------------------------------------------------------
--          Registry Rotation
--------------------------------------------------------------------------------

||| Rotate every registered thread's buffers.
|||
||| Returns all frozen buffers to rebuild from.
|||
export
rotateAllBuffers :  Ref s (SortedMap ThreadId (ThreadContext a))
                 -> F1 s (List (Buffer a))
rotateAllBuffers regref t =
  casupdate1 regref (\m =>
                      let m'      = map rotateBuffers m
                          frozen' =
                            map (\ctx => ctx.buffers.frozen)
                                (values m')
                        in (m', frozen')
                    ) t

--------------------------------------------------------------------------------
--          Entry Collection
--------------------------------------------------------------------------------

export
bufferEntries :  Buffer a
              -> List (Entry a)
bufferEntries (MkBuffer es _) =
  cast es

export
collectEntries :  List (Buffer a)
               -> List (Entry a)
collectEntries =
  concatMap bufferEntries

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
--          Publication
--------------------------------------------------------------------------------

||| Atomically publishes a newly rebuilt immutable snapshot.
|||
||| Steps:
||| - Replace the currently visible tree.
||| - Increment snapshot generation.
||| - Publish both together atomically.
|||
||| Properties:
||| - Readers never observe mismatched (generation,tree) pairs.
||| - Publication is linearizable.
||| - O(1).
|||
||| Notes:
||| - The rebuild service is the sole writer.
||| - CAS protects against races with concurrent readers.
|||
export
publishSnapshot :  Ref s (SnapshotState a)
                -> RRBVector a
                -> F1' s
publishSnapshot snapshotref new t =
  casmod1 snapshotref (\snapshot =>
                        { generation := S snapshot.generation
                        , tree := new
                        } snapshot
                      ) t

--------------------------------------------------------------------------------
--          Rebuilder Service
--------------------------------------------------------------------------------

||| Processes a rebuild request and updates rebuild state.
|||
||| Trigger:
||| - Marks pending work.
||| - Starts rebuild if idle.
|||
||| Flush:
||| - Forces processing of all buffered writes.
||| - Returns only after publication completes.
|||
export covering
handleRebuildRequest  :  Ord (Entry a)
                      => Ref World (SortedMap Int (ThreadContext a))
                      -> Ref World (SnapshotState a)
                      -> RebuildServiceState
                      -> (req : RebuildRequest)
                      -> Async e [] (RebuildServiceState, RebuildResponse req)
handleRebuildRequest buffers snapshot st Trigger = do
  let st1     = { rebuildphase := RotatingBuffers
                , rebuildpending := True
                } st
  frozen      <- liftIO (runIO (rotateAllBuffers buffers))
  let st2     = { rebuildphase := CollectingEntries
                } st1
      entries = collectEntries frozen
      st3     = { rebuildphase := SortingEntries
                } st2
      sorted  = sortEntries entries
      st4     = { rebuildphase := ApplyingOperations
                } st3
  oldsnapshot <- liftIO (runIO (read1 snapshot))
  let rebuilt = replayEntries sorted oldsnapshot.tree
      st5     = { rebuildphase := PublishingSnapshot
                } st4
  liftIO (runIO (publishSnapshot snapshot rebuilt))
  pure
    ( { rebuildphase := Sleeping
      , rebuildpending := False
      , rebuildgeneration :=
          S st.rebuildgeneration
      } st5
    , ()
    )
handleRebuildRequest buffers snapshot st Flush   =
  handleRebuildRequest buffers
                       snapshot
                       st
                       Trigger

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
                      -> Ref World (SnapshotState a)
                      -> F1 World (Async e [] (Service e [] RebuildRequest RebuildResponse))
spawnRebuilderService buffers snapshot t =
  service RebuildResponse
          initialRebuildServiceState
          ( handleRebuildRequest
              buffers
              snapshot
          ) # t

--------------------------------------------------------------------------------
--          Creating Log-Structured Merge RRB-Vectors
--------------------------------------------------------------------------------

||| The empty log-structured merge vector. O(1)
export covering
empty :  Ord (Entry a)
      => F1 World (LSMRRBVector World e a)
empty t =
  let buffers    # t := ref1 Data.SortedMap.empty t
      snapshot   # t := ref1 (MkSnapshotState Z Empty) t
      rebuilder  # t := spawnRebuilderService buffers snapshot t
    in MkLSMRRBVector buffers snapshot (MkManagedService rebuilder) # t

||| A log-structured merge vector with a single element. O(1)
export covering
singleton :  Ord (Entry a)
          => a
          -> F1 World (LSMRRBVector World e a)
singleton x t =
  let buffers    # t := ref1 Data.SortedMap.empty t
      snapshot   # t := ref1 (MkSnapshotState Z (Root 1 0 (Leaf $ A 1 $ fill 1 x))) t
      rebuilder  # t := spawnRebuilderService buffers snapshot t
    in MkLSMRRBVector buffers snapshot (MkManagedService rebuilder) # t
