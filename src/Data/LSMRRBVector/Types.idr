||| Log-Structured Merge RRB Vector Types
module Data.LSMRRBVector.Types

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
import IO.Async.Core
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
Show a => Show (Entry a) where
  show (MkEntry operation timestamp threadid sequence) =
    "MkEntry "                    ++
    (show operation)              ++
    " "                           ++
    (asctime $ fromUTC timestamp) ++
    " "                           ++
    (show threadid)               ++
    " "                           ++
    (show sequence)

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

%runElab derive "Buffer" [Show,Eq]

--------------------------------------------------------------------------------
--          Double Buffered Mutation State
--------------------------------------------------------------------------------

||| Thread-local mutation state.
|||
||| Writers append only to active.
|||
||| During rebuild:
||| - Active buffers are extracted atomically.
||| - Ownership transfers to the rebuilder.
||| - Writers immediately continue on a fresh buffer.
|||
||| Properties:
||| - O(1) amortized append.
||| - No stop-the-world pauses.
||| - No shared rebuild ownership.
|||
public export
record WriteBuffers a where
  constructor MkWriteBuffers
  active : Buffer a

%runElab derive "WriteBuffers" [Show,Eq]

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

%runElab derive "ThreadContext" [Show,Eq]

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
--          Rebuild Metrics
--------------------------------------------------------------------------------

||| Runtime rebuild statistics.
|||
||| Metrics are updated after successful rebuild cycles and provide lightweight visibility into rebuild behavior.
|||
||| Fields:
||| - lastbatchsize  <-> Number of entries processed during most recent rebuild.
||| - totalbatchsize <-> Total number of entries processed across all rebuilds.
||| - rebuildcount   <-> Number of successful rebuild cycles.
|||
||| Derived values:
||| - average batch size: totalbatchsize / rebuildcount
|||
||| Properties:
||| - Updated only by the rebuild worker.
||| - Does not affect correctness.
||| - Intended for observability and adaptive tuning.
|||
public export
record RebuildMetrics where
  constructor MkRebuildMetrics
  lastbatchsize  : Nat
  totalbatchsize : Nat
  rebuildcount   : Nat

%runElab derive "RebuildMetrics" [Show,Eq]

--------------------------------------------------------------------------------
--          Rebuild Service State
--------------------------------------------------------------------------------

||| Controls execution of rebuild-cycle progress.
|||
||| Fields:
||| - rebuildphase: Current phase of the rebuild pipeline.
||| - rebuildmetrics: Runtime rebuild statistics.
|||
||| Properties:
||| - Local service execution state only.
||| - Mutable only by the rebuild worker.
||| - Represents execution progress rather than global vector state.
|||
||| Notes:
||| - Pending rebuild work is tracked globally through CombinedSnapshotState.rebuildpending.
||| - Failure state is intentionally omitted.
||| - Current rebuild operations are total and crash on unrecoverable runtime failures rather than persisting structured errors.
|||
public export
record RebuildServiceState where
  constructor MkRebuildServiceState
  rebuildphase   : RebuildState
  rebuildmetrics : RebuildMetrics

%runElab derive "RebuildServiceState" [Show,Eq]

--------------------------------------------------------------------------------
--          Reader State
--------------------------------------------------------------------------------

||| Reader participation in generation tracking.
|||
||| Readers announce the snapshot generation currently being observed.
|||
||| Properties:
||| - Updated only when entering/leaving a snapshot read section.
||| - Used by reclamation to determine oldest active generation.
||| - One entry per participating thread.
|||
public export
record ReaderState where
  constructor MkReaderState
  generation : Generation

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
--          Retired Snapshot
--------------------------------------------------------------------------------

||| Snapshot awaiting reclamation.
|||
||| A snapshot becomes retired after publication of a newer snapshot.
|||
||| Properties:
||| - Immutable after retirement.
||| - Safe to reclaim once no reader references its generation.
|||
public export
record RetiredSnapshot a where
  constructor MkRetiredSnapshot
  generation : Generation
  tree       : RRBVector a

--------------------------------------------------------------------------------
--          Combined Snapshot State
--------------------------------------------------------------------------------

||| Combined snapshot publication, reclamation, and batching state.
|||
||| Fields:
||| - currentsnapshot: Current published immutable snapshot.
||| - retiredsnapshots: Older snapshots awaiting reclamation.
||| - readerstate: Active reader generation announcements.
||| - writepressure: Number of writes accumulated since the last rebuild cycle.
||| - rebuildpending: Indicates whether buffered work exists requiring rebuild.
||| - batchwindow: Current adaptive rebuild target controlling how many writes are accumulated before rebuild behavior expands or contracts.
|||
||| Properties:
||| - Updated atomically through CAS.
||| - Shared between readers, writers, and rebuilder.
||| - Adaptive batching decisions observe a globally consistent state.
|||
public export
record CombinedSnapshotState a where
  constructor MkCombinedSnapshotState
  currentsnapshot  : SnapshotState a
  retiredsnapshots : List (RetiredSnapshot a)
  readerstate      : SortedMap ThreadId ReaderState
  writepressure    : Nat
  rebuildpending   : Bool
  batchwindow      : Nat

--------------------------------------------------------------------------------
--          Snapshot-Rebuilding Service
--------------------------------------------------------------------------------

public export
record RebuildService (0 e : Type) where
  constructor MkRebuildService
  run : RebuildRequest -> Async e [Errno] ()

export covering
rebuilder :  (sendrebuildrequest : RebuildRequest -> Async e [Errno] ())
          -> Async e es (RebuildService e)
rebuilder sendrebuildrequest = do
  srv <- stateless (const ()) sendRebuildRequest
  pure $ MkRebuildService (send srv)
  where
    sendRebuildRequest :  RebuildRequest
                       -> Async e [Errno] ()
    sendRebuildRequest req = sendrebuildrequest req

--------------------------------------------------------------------------------
--          Log Structured Merge RRB Vector
--------------------------------------------------------------------------------

public export
record LSMRRBVector s a where
  constructor MkLSMRRBVector
  buffers               : Ref s (SortedMap ThreadId (ThreadContext a))
  combinedsnapshotstate : Ref s (CombinedSnapshotState a)
  rebuildscheduled      : Ref s Bool

--------------------------------------------------------------------------------
--          Configuration
--------------------------------------------------------------------------------

||| Configuration controlling rebuild and adaptive batching behavior.
|||
||| Fields:
||| - initialbatchwindow: Initial adaptive batching target used before runtime adjustments occur.
|||
||| Properties:
||| - Does not affect correctness.
||| - Influences rebuild latency/throughput tradeoffs.
||| - Serves as the starting point for adaptive window adjustment.
|||
||| Typical values:
||| - 16–64: Lower latency, more frequent rebuilds.
||| - 64–256: Balanced throughput and latency.
||| - 256+: Higher throughput under sustained write load.
|||
public export
record LSMRRBVectorConfig where
  constructor MkLSMRRBVectorConfig
  initialbatchwindow : Nat
