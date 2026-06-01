||| Log-Structured Merge RRB Vectors (LSMRRBVector)
module Data.LSMRRBVector

import public Data.LSMRRBVector.Internal
import public Data.LSMRRBVector.Types
import public Data.RRBVector

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
--          Mutation Operations
--------------------------------------------------------------------------------

||| Appends a value onto the logical end of the vector.
|||
||| Effect:
||| - Adds an Append operation to the thread-local buffer.
|||
export
append :  LSMRRBVector World a
       -> RebuildService Poll
       -> ThreadId
       -> a
       -> Async Poll [Errno] ()
append lsmrrbvector svc tid x = do
  shouldtrigger <- liftIO (enqueueOperation lsmrrbvector.buffers lsmrrbvector.combinedsnapshotstate tid (Append x))
  scheduleIfNeeded lsmrrbvector svc shouldtrigger
  
||| Prepends a value onto the logical beginning of the vector.
|||
||| Effect:
||| - Adds a Prepend operation to the thread-local buffer.
|||
export
prepend :  LSMRRBVector World a
        -> RebuildService Poll
        -> ThreadId
        -> a
        -> Async Poll [Errno] ()
prepend lsmrrbvector svc tid x = do
  shouldtrigger <- liftIO (enqueueOperation lsmrrbvector.buffers lsmrrbvector.combinedsnapshotstate tid (Prepend x))
  scheduleIfNeeded lsmrrbvector svc shouldtrigger

||| Inserts a value at a specified logical index.
|||
||| Effect:
||| - Adds an Insert operation to the thread-local buffer.
|||
export
insert :  LSMRRBVector World a
       -> RebuildService Poll
       -> ThreadId
       -> Nat
       -> a
       -> Async Poll [Errno] ()
insert lsmrrbvector svc tid i x = do
  shouldtrigger <- liftIO (enqueueOperation lsmrrbvector.buffers lsmrrbvector.combinedsnapshotstate tid (Insert i x))
  scheduleIfNeeded lsmrrbvector svc shouldtrigger

||| Removes a value at a specified logical index.
|||
||| Effect:
||| - Adds a Delete operation to the thread-local buffer.
|||
export
delete :  LSMRRBVector World a
       -> RebuildService Poll
       -> ThreadId
       -> Nat
       -> Async Poll [Errno] ()
delete lsmrrbvector svc tid i = do
  shouldtrigger <- liftIO (enqueueOperation lsmrrbvector.buffers lsmrrbvector.combinedsnapshotstate tid (Delete i))
  scheduleIfNeeded lsmrrbvector svc shouldtrigger

||| Replaces a value at a specified logical index.
|||
||| Effect:
||| - Adds an Update operation to the thread-local buffer.
|||
export
update :  LSMRRBVector World a
       -> RebuildService Poll
       -> ThreadId
       -> Nat
       -> a
       -> Async Poll [Errno] ()
update lsmrrbvector svc tid i x = do
  shouldtrigger <- liftIO (enqueueOperation lsmrrbvector.buffers lsmrrbvector.combinedsnapshotstate tid (Update i x))
  scheduleIfNeeded lsmrrbvector svc shouldtrigger

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
toList :  LSMRRBVector World a
       -> ThreadId
       -> IO (List a)
toList lsmrrbvector tid =
  readSnapshotWithGeneration lsmrrbvector tid (\(_, v) => Data.RRBVector.toList v)

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
length :  LSMRRBVector World a
       -> ThreadId
       -> IO Nat
length lsmrrbvector tid =
  readSnapshotWithGeneration lsmrrbvector tid (\(_, v) => Data.RRBVector.length v)

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
index :  LSMRRBVector World a
      -> ThreadId
      -> Nat
      -> IO a
index lsmrrbvector tid i =
  readSnapshotWithGeneration lsmrrbvector tid (\(_, v) => Data.RRBVector.index i v)

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
lookup :  LSMRRBVector World a
       -> ThreadId
       -> Nat
       -> IO (Maybe a)
lookup lsmrrbvector tid i =
  readSnapshotWithGeneration lsmrrbvector tid (\(_, v) => Data.RRBVector.lookup i v)

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
null :  LSMRRBVector World a
     -> ThreadId
     -> IO Bool
null lsmrrbvector tid =
  readSnapshotWithGeneration lsmrrbvector tid (\(_, v) => Data.RRBVector.null v)

--------------------------------------------------------------------------------
--          Default Config
--------------------------------------------------------------------------------

||| Default LSMRRBVector configuration.
|||
||| Current defaults favor balanced throughput and latency.
|||
export
defaultconfig : LSMRRBVectorConfig
defaultconfig = MkLSMRRBVectorConfig 64

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
runEmptyWith :  Ord (Entry a)
             => Show (SortedMap Int (ThreadContext a))
             => Show (List (Buffer a))
             => LSMRRBVectorConfig
  --           -> (LSMRRBVector World a -> RebuildService Poll -> IO ())
             -> (LSMRRBVector World a -> RebuildService Poll -> Async Poll [Errno] ())
             -> (LSMRRBVector World a -> IO ())
             -> IO ()
runEmptyWith config rebuilderaction lsmrrbvectoraction = do
  buffers                 <- newref Data.SortedMap.empty
  combinedsnapshotstate   <- newref (MkCombinedSnapshotState (MkSnapshotState Z Empty) [] Data.SortedMap.empty 0 False config.initialbatchwindow)
  rebuildscheduled        <- newref False
  let lsmrrbvector        = MkLSMRRBVector buffers combinedsnapshotstate rebuildscheduled
  let rebuilderservice    = rebuilderService lsmrrbvector initialRebuildServiceState rebuilderaction
  let lsmrrbvectorservice = lsmrrbvectorService lsmrrbvector lsmrrbvectoraction
  app (Element (the Nat 2) %search) [SIGINT] posixPoller $ handle handlers (rebuilderAndLSMRRBVectorService rebuilderservice lsmrrbvectorservice)
  where
    handlers : All (Handler () Poll) [Errno]
    handlers = [\x => stderrLn "Error: \{errorText x} (\{errorName x})"]

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
runFastWritesEmpty :  Ord (Entry a)
                   => Show (SortedMap Int (ThreadContext a))
                   => Show (List (Buffer a))
            --       => (LSMRRBVector World a -> RebuildService Poll -> IO ())
                   => (LSMRRBVector World a -> RebuildService Poll -> Async Poll [Errno] ())
                   -> (LSMRRBVector World a -> IO ())
                   -> IO ()
runFastWritesEmpty rebuilderaction lsmrrbvectoraction =
  runEmptyWith (MkLSMRRBVectorConfig 512) rebuilderaction lsmrrbvectoraction

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
runLowLatencyEmpty :  Ord (Entry a)
                   => Show (SortedMap Int (ThreadContext a))
                   => Show (List (Buffer a))
               --    => (LSMRRBVector World a -> RebuildService Poll -> IO ())
                   => (LSMRRBVector World a -> RebuildService Poll -> Async Poll [Errno] ())
                   -> (LSMRRBVector World a -> IO ())
                   -> IO ()
runLowLatencyEmpty rebuilderaction lsmrrbvectoraction =
  runEmptyWith (MkLSMRRBVectorConfig 16) rebuilderaction lsmrrbvectoraction

||| The empty log-structured merge vector. O(1)
|||
export covering
runEmpty :  Ord (Entry a)
         => Show (SortedMap Int (ThreadContext a))
         => Show (List (Buffer a))
--         => (LSMRRBVector World a -> RebuildService Poll -> IO ())
         => (LSMRRBVector World a -> RebuildService Poll -> Async Poll [Errno] ())
         -> (LSMRRBVector World a -> IO ())
         -> IO ()
runEmpty rebuilderaction lsmrrbvectoraction = 
  runEmptyWith defaultconfig rebuilderaction lsmrrbvectoraction
