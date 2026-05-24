||| LSM RRB Vector Internals
module Data.LSMRRBVector.Internal

import Data.Array
import Data.Array.Core
import Data.Array.Index
import Data.Array.Indexed
import Data.Bits
import Data.List
import Data.Nat
import Data.Linear.Ref1
import Data.RRBVector
import Data.RRBVector.Internal
import Data.SortedMap
import Data.String
import Derive.Prelude
import IO.Async
import IO.Async.Service
import System.Concurrency
import System.Posix.Timer
import System.Posix.Timer.Prim

%default total
%language ElabReflection

--------------------------------------------------------------------------------
--          Generation
--------------------------------------------------------------------------------

||| Snapshot generation identifier.
|||
||| Represents the logical version of the currently published
||| immutable snapshot.
|||
||| Properties:
||| - Monotonically increasing.
||| - Incremented only after successful publication.
||| - Readers may compare generations to detect snapshot changes.
|||
||| Notes:
||| - Does not encode time.
||| - Exists purely for ordering and visibility.
|||
public export
Generation : Type
Generation = Nat

--------------------------------------------------------------------------------
--          ThreadId
--------------------------------------------------------------------------------

||| A wrapper over Int for thread ids.
|||
public export
ThreadId : Type
ThreadId = Int

--------------------------------------------------------------------------------
--          Buffered Operations
--------------------------------------------------------------------------------

||| Operation represents a deferred vector mutation.
|||
||| Rather than mutating the underlying RRBVector immediately, all user
||| modifications are first converted into Operations and appended into
||| thread-indexed shared state.
|||
||| Variants:
||| - Prepend a
|||   Insert a value at the logical beginning.
||| - Append a
|||   Insert a value at the logical end.
||| - Insert Nat a
|||   Insert a value at a specified index.
||| - Delete Nat
|||   Remove a value at a specified index.
||| - Update Nat a
|||   Replace a value at a specified index.
|||
||| Role in LSM design:
||| - Forms the deferred mutation layer.
||| - Enables batching.
||| - Prevents writers from mutating snapshots.
|||
||| Notes:
||| Indices are interpreted relative to the visible snapshot together with preceding replayed operations.
|||
public export
data Operation a
  = Prepend a
  | Append a
  | Insert Nat a
  | Delete Nat
  | Update Nat a

%runElab derive "Operation" [Show,Eq]

--------------------------------------------------------------------------------
--          Write Buffer Entries
--------------------------------------------------------------------------------

||| Entry represents a deferred mutation event.
|||
||| Every user write becomes an Entry before entering a thread buffer.
|||
||| Fields:
||| - operation <-> Deferred mutation
||| - timestamp <-> Wall-clock ordering hint
||| - threadid  <-> Originating thread
||| - sequence  <-> Monotonic per-thread counter
|||
||| Ordering:
||| - Entries are sorted using (timestamp, threadid, sequence).
||| - This guarantees deterministic replay even when timestamps collide.
|||
||| Role in LSM design:
||| - Unit of deferred work.
||| - Supports deterministic rebuild.
|||
public export
record Entry a where
  constructor MkEntry
  operation : Operation a
  timestamp : IClock CLOCK_REALTIME
  threadid  : Int
  sequence  : Nat

public export
Eq a => Eq (Entry a) where
  (MkEntry op1 ts1 tid1 seq1) == (MkEntry op2 ts2 tid2 seq2) =
       op1   == op2
    && ts1   == ts2
    && tid1  == tid2
    && seq1  == seq2

public export
Eq (Entry a) => Ord (Entry a) where
  compare x y =
    case compare x.timestamp y.timestamp of
      LT =>
        LT
      GT =>
        GT
      EQ =>
        case compare x.threadid y.threadid of
          LT =>
            LT
          GT =>
            GT
          EQ =>
            compare x.sequence y.sequence

--------------------------------------------------------------------------------
--          Single Buffer
--------------------------------------------------------------------------------

||| Single append-efficient mutation log.
|||
||| Represents one physical mutation buffer.
|||
public export
record Buffer a where
  constructor MkBuffer
  entries : SnocList (Entry a)
  length  : Nat

--------------------------------------------------------------------------------
--          Double Buffered Mutation State
--------------------------------------------------------------------------------

||| Thread-local double buffered mutation state.
|||
||| Writers append only to active.
|||
||| During rebuild:
||| - active ↔ frozen
|||
||| After rotation:
||| - Writers immediately continue using a fresh active buffer.
||| - Rebuild processes frozen asynchronously.
|||
||| Layout:
||| - active: Buffer currently receiving writes
||| - frozen: Snapshot of buffered writes currently under rebuild
|||
||| Properties:
||| - O(1) amortized append.
||| - No stop-the-world pauses.
||| - Continuous snapshot construction.
|||
public export
record WriteBuffers a where
  constructor MkWriteBuffers
  active : Buffer a
  frozen : Buffer a

--------------------------------------------------------------------------------
--          Thread Context
--------------------------------------------------------------------------------

||| ThreadContext stores per-thread mutation state.
|||
||| Ownership:
||| - One ThreadContext exists per registered thread.
|||
||| Fields:
||| - threadid <-> Unique thread identifier
||| - sequence <-> Monotonically increasing local counter used for deterministic ordering
||| - buffers  <-> Thread-owned double-buffer state
|||
||| Properties:
||| - Per-thread logical ownership.
||| - Shared registry storage.
||| - Low-contention write path.
|||
public export
record ThreadContext a where
  constructor MkThreadContext
  threadid : Int
  sequence : Nat
  buffers  : WriteBuffers a

--------------------------------------------------------------------------------
--          Background Rebuild State
--------------------------------------------------------------------------------

||| RebuildState represents rebuild thread progress.
|||
||| Lifecycle:
|||
||| Sleeping
|||      ↓
||| RotatingBuffers
|||      ↓
||| CollectingEntries
|||      ↓
||| SortingEntries
|||      ↓
||| ApplyingOperations
|||      ↓
||| BuildingSnapshot
|||      ↓
||| PublishingSnapshot
|||      ↓
||| Sleeping
|||
public export
data RebuildState
  = Sleeping
  | RotatingBuffers
  | CollectingEntries
  | SortingEntries
  | ApplyingOperations
  | BuildingSnapshot
  | PublishingSnapshot

%runElab derive "RebuildState" [Show,Eq]

--------------------------------------------------------------------------------
--          Rebuild Service Messages
--------------------------------------------------------------------------------

||| Requests sent to the rebuild service.
|||
||| Trigger:
||| - Indicates new buffered work exists.
||| - Marks rebuild work as pending.
||| - Does not initiate rebuild.
|||
||| Flush:
||| - Forces all pending writes into a published snapshot.
|||
public export
data RebuildRequest
  = Trigger
  | Flush

%runElab derive "RebuildRequest" [Show,Eq]

--------------------------------------------------------------------------------
--          Rebuild Service Responses
--------------------------------------------------------------------------------

||| Response produced by the rebuild service.
|||
||| Trigger:
||| - Acknowledges notification that buffered work exists.
||| - Does not imply that a rebuild occurred.
||| - Multiple Trigger requests may be coalesced.
|||
||| Flush:
||| - Indicates that all currently buffered writes have been incorporated into a published snapshot.
|||
||| Notes:
||| - Responses currently contain no payload.
||| - Dependent typing preserves request/response correspondence.
||| - Future extensions may return rebuild metrics or generation numbers.
|||
public export
RebuildResponse : RebuildRequest -> Type
RebuildResponse Trigger = ()
RebuildResponse Flush   = Generation

--------------------------------------------------------------------------------
--          Rebuild Failure
--------------------------------------------------------------------------------

||| Failure encountered during rebuild.
|||
||| Failures are persisted into service state so callers can observe rebuild health.
|||
public export
data RebuildFailure
  = SnapshotReadFailure String
  | SnapshotPublishFailure String
  | ReplayFailure String

%runElab derive "RebuildFailure" [Show,Eq]

--------------------------------------------------------------------------------
--          Rebuild Service State
--------------------------------------------------------------------------------

||| Internal state owned exclusively by the rebuild service.
|||
||| Properties:
||| - Exists only inside rebuilder.
||| - Sequentially updated.
||| - Never shared.
|||
public export
record RebuildServiceState where
  constructor MkRebuildServiceState
  rebuildphase   : RebuildState
  rebuildpending : Bool
  rebuildfailure : Maybe RebuildFailure

%runElab derive "RebuildServiceState" [Show]

--------------------------------------------------------------------------------
--          Registration
--------------------------------------------------------------------------------

||| Result of thread registration lookup.
|||
||| Existing:
||| - Thread already has registered state.
||| - Reuses existing ThreadContext.
|||
||| New:
||| - Thread was not previously registered.
||| - Requires creation and insertion of ThreadContext.
|||
||| Notes:
||| - Distinguishes allocation from lookup.
||| - Avoids duplicate registration logic.
|||
public export
data Registration a
  = Existing a
  | New a

--------------------------------------------------------------------------------
--          Snapshot State
--------------------------------------------------------------------------------

||| Immutable published snapshot state.
|||
||| Represents the currently visible version of the vector.
|||
||| Fields:
||| - generation <-> Monotonic snapshot version identifier
||| - tree       <-> Immutable published RRB snapshot
|||
||| Publication properties:
||| - Tree and generation are published atomically.
||| - Readers always observe a consistent snapshot pair.
||| - Eliminates visibility races between tree updates and generation updates.
|||
||| Lifecycle:
|||
||| rebuild
|||     ↓
||| new snapshot tree
|||     ↓
||| increment generation
|||     ↓
||| atomic publication
|||     ↓
||| visible to readers
|||
||| Notes:
||| - SnapshotState is immutable once constructed.
||| - Publication occurs by replacing the whole record.
|||
public export
record SnapshotState a where
  constructor MkSnapshotState
  generation : Generation
  tree       : RRBVector a

--------------------------------------------------------------------------------
--          ManagedService
--------------------------------------------------------------------------------

||| A managed effectful resource that can be started inside Async,
||| but stored purely in data structures.
|||
public export
record ManagedService (e : Type) (req : Type) (resp : req -> Type) where
  constructor MkManagedService
  run : Async e [] (Service e [] req resp)

--------------------------------------------------------------------------------
--          Log Structured Merge RRB Vector
--------------------------------------------------------------------------------

||| Concurrent LSM-style vector built from:
||| - Thread-local mutation logs
||| - Immutable RRB snapshots
||| - Continuous background rebuild
|||
||| Write path:
|||
||| Thread
|||    ↓
||| ThreadContext
|||    ↓
||| active buffer
|||    ↓
||| Entry append
|||
||| Rebuild path:
|||
||| Rotate active/frozen
|||        ↓
||| Collect frozen buffers
|||        ↓
||| Sort Entries
|||        ↓
||| Apply Operations
|||        ↓
||| Build snapshot
|||        ↓
||| Publish snapshot
|||
||| Fields:
||| - buffers    <-> Thread registry
||| - tree       <-> Current immutable snapshot
||| - generation <-> Monotonically increasing snapshot version
||| - rebuilder  <-> Background rebuild service
|||
||| Properties:
||| - O(1) amortized writes.
||| - Continuous rebuilding.
||| - No stop-the-world pauses.
||| - Read-stable snapshots.
|||
public export
record LSMRRBVector s e a where
  constructor MkLSMRRBVector
  buffers    : Ref s (SortedMap ThreadId (ThreadContext a))
  snapshot   : Ref s (SnapshotState a)
  rebuilder  : ManagedService e RebuildRequest RebuildResponse
