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
import Data.String
import Derive.Prelude
import Syntax.T1 as T1
import System.Concurrency
import System.Posix.Time

%default total
%language ElabReflection

--------------------------------------------------------------------------------
--          Internal Utility
--------------------------------------------------------------------------------

||| Convenience interface for bitSize that doesn't use an implicit parameter.
private
bitSizeOf :  (ty : Type)
          -> FiniteBits ty
          => Nat
bitSizeOf ty = bitSize {a = ty}

--------------------------------------------------------------------------------
--          Internals
--------------------------------------------------------------------------------

public export
Shift : Type
Shift = Nat

||| The number of bits used per level.
export
blockshift : Shift
blockshift = 4

||| The maximum size of a block.
export
blocksize : Nat
blocksize = integerToNat $ 1 `shiftL` blockshift

||| The mask used to extract the index into the array.
export
blockmask : Nat
blockmask = minus blocksize 1

export
up :  Shift
   -> Shift
up sh = plus sh blockshift

export
down :  Shift
     -> Shift
down sh = minus sh blockshift

export
radixIndex :  Nat
           -> Shift
           -> Nat
radixIndex i sh = integerToNat ((natToInteger i) `shiftR` sh .&. (natToInteger blockmask))

export
relaxedRadixIndex :  Array Nat
                  -> Nat
                  -> Shift
                  -> (Nat, Nat)
relaxedRadixIndex sizes i sh =
  let guess  = radixIndex i sh -- guess <= idx
      idx    = loop sizes guess
      subIdx = case idx == 0 of
                 True  =>
                   i
                 False =>
                   let idx' = case tryNatToFin $ minus idx 1 of
                                Nothing    =>
                                  assert_total $ idris_crash "Data.RRBVector.Unsized.Internal.relaxedRadixIndex: index out of bounds"
                                Just idx'' =>
                                  idx''
                     in minus i (at sizes.arr idx')
    in (idx, subIdx)
  where
    loop :  Array Nat
         -> Nat
         -> Nat
    loop sizes idx =
      let current = case tryNatToFin idx of
                      Nothing       =>
                        assert_total $ idris_crash "Data.RRBVector.Unsized.Internal.relaxedRadixIndex.loop: index out of bounds"
                      Just idx' =>
                        at sizes.arr idx' -- idx will always be in range for a well-formed tree
        in case i < current of
             True  =>
               idx
             False =>
               assert_total $ loop sizes (plus idx 1)

--------------------------------------------------------------------------------
--          Internal Tree Representation
--------------------------------------------------------------------------------

||| An internal tree representation.
public export
data Tree a = Balanced (Array (Tree a))
            | Unbalanced (Array (Tree a)) (Array Nat)
            | Leaf (Array a)

--------------------------------------------------------------------------------
--          Query (Tree)
--------------------------------------------------------------------------------

||| Is the tree empty? O(1)
private
null :  Tree a
     -> Bool
null (Balanced arr)     =
  null arr
null (Unbalanced arr _) =
  null arr
null (Leaf arr)         =
  null arr

--------------------------------------------------------------------------------
--          Folds (Tree)
--------------------------------------------------------------------------------

private
foldl :  (b -> a -> b)
      -> b
      -> Tree a
      -> b
foldl f acc tree =
  foldlTree acc tree
  where
    foldlTree :  b
              -> Tree a
              -> b
    foldlTree acc' (Balanced arr)     =
      assert_total $ foldl foldlTree acc' arr
    foldlTree acc' (Unbalanced arr _) =
      assert_total $ foldl foldlTree acc' arr
    foldlTree acc' (Leaf arr)         =
      assert_total $ foldl f acc' arr

private
foldr :  (a -> b -> b)
      -> b
      -> Tree a
      -> b
foldr f acc tree =
  foldrTree tree acc
  where
    foldrTree :  Tree a
              -> b
              -> b
    foldrTree (Balanced arr) acc'     =
      assert_total $ foldr foldrTree acc' arr
    foldrTree (Unbalanced arr _) acc' =
      assert_total $ foldr foldrTree acc' arr
    foldrTree (Leaf arr) acc'         =
      assert_total $ foldr f acc' arr

--------------------------------------------------------------------------------
--          Creating Lists from Trees
--------------------------------------------------------------------------------

export
toList :  Tree a
       -> List a
toList (Balanced arr)     =
  assert_total $ concat (map toList (toList arr))
toList (Unbalanced arr _) =
  assert_total $ concat (map toList (toList arr))
toList (Leaf arr)         =
  toList arr

--------------------------------------------------------------------------------
--          Interfaces (Tree)
--------------------------------------------------------------------------------

public export
Show a => Show (Tree a) where
  show (Balanced arr)     =
    assert_total $ "Balanced " ++ show arr
  show (Unbalanced arr _) =
    assert_total $ "Unbalanced " ++ show arr
  show (Leaf arr)         =
    "Leaf " ++ show arr

public export
Foldable Tree where
  foldl f z = Data.LSMRRBVector.Internal.foldl f z
  foldr f z = Data.LSMRRBVector.Internal.foldr f z
  toList    = Data.LSMRRBVector.Internal.toList
  null      = Data.LSMRRBVector.Internal.null

public export
Eq a => Eq (Tree a) where
  (Balanced arr1) == (Balanced arr2)         =
    assert_total $ arr1 == arr2
  (Unbalanced arr1 _) == (Unbalanced arr2 _) =
    assert_total $ arr1 == arr2
  (Leaf arr1) == (Leaf arr2)                 =
    arr1 == arr2
  _                        == _              =
    False

public export
Ord a => Ord (Tree a) where
  compare tree1 tree2 =
    compare (Data.LSMRRBVector.Internal.toList tree1) (Data.LSMRRBVector.Internal.toList tree2)

--------------------------------------------------------------------------------
--          Show Utilities (Tree)
--------------------------------------------------------------------------------

public export
showTreeRep :  Show a
            => Show (Tree a)
            => Tree a
            -> String
showTreeRep (Balanced trees)     =
  assert_total $ "Balanced " ++ (show $ toList trees)
showTreeRep (Unbalanced trees _) =
  assert_total $ "Unbalanced " ++ (show $ toList trees)
showTreeRep (Leaf elems)         =
  assert_total $ "Leaf " ++ (show $ toList elems)

--------------------------------------------------------------------------------
--          Tree Utilities
--------------------------------------------------------------------------------

export
singleton :  a
          -> Array a
singleton x =
  A 1 $ fill 1 x

export
treeToArray :  Tree a
            -> Array (Tree a)
treeToArray (Balanced arr)     =
  arr
treeToArray (Unbalanced arr _) =
  arr
treeToArray (Leaf _)           =
  assert_total $ idris_crash "Data.RRBVector.Unsized.Internal.treeToArray: leaf"

export
treeBalanced :  Tree a
             -> Bool
treeBalanced (Balanced _)     =
  True
treeBalanced (Unbalanced _ _) =
  False
treeBalanced (Leaf _)         =
  True

||| Computes the size of a tree with shift.
export
treeSize :  Shift
         -> Tree a
         -> Nat
treeSize = go 0
  where
    go :  Shift
       -> Shift
       -> Tree a
       -> Nat
    go acc _  (Leaf arr)             =
      plus acc arr.size
    go acc _  (Unbalanced arr sizes) =
      let i = case tryNatToFin $ minus arr.size 1 of
                Nothing =>
                  assert_total $ idris_crash "Data.RRBVector.Unsized.Internal.treeSize: index out of bounds"
                Just i' =>
                  i'
        in plus acc (at sizes.arr i)
    go acc sh (Balanced arr)         =
      let i  = minus arr.size 1
          i' = case tryNatToFin i of
                 Nothing  =>
                   assert_total $ idris_crash "Data.RRBVector.Unsized.Internal.treeSize: index out of bounds"
                 Just i'' =>
                   i''
        in go (plus acc (mult i (integerToNat (1 `shiftL` sh))))
              (down sh)
              (assert_smaller arr (at arr.arr i'))

||| Turns an array into a tree node by computing the sizes of its subtrees.
||| sh is the shift of the resulting tree.
export
computeSizes :  Shift
             -> Array (Tree a)
             -> Tree a
computeSizes sh arr =
  case isBalanced of
    True  =>
      Balanced arr
    False =>
      let arrnat = unsafeAlloc arr.size (loop sh 0 0 arr.size (toList arr))
        in Unbalanced arr arrnat
  where
    loop :  (sh,cur,acc,n : Nat)
         -> List (Tree a)
         -> WithMArray n Nat (Array Nat)
    loop sh _   acc n []        r = T1.do
      res <- unsafeFreeze r
      pure $ A n res
    loop sh cur acc n (x :: xs) r =
      case tryNatToFin cur of
        Nothing   =>
          assert_total $ idris_crash "Data.RRBVector.Unsized.Internal.computeSizes.go: can't convert Nat to Fin"
        Just cur' =>
          let acc' = plus acc (treeSize (down sh) x)
            in T1.do set r cur' acc'
                     assert_total $ loop sh (S cur) acc' n xs r
    maxsize : Integer
    maxsize = 1 `shiftL` sh -- the maximum size of a subtree
    len : Nat
    len = arr.size
    lenM1 : Nat
    lenM1 = minus len 1
    isBalanced : Bool
    isBalanced = go 0
      where
        go :  Nat
           -> Bool
        go i =
          let subtree = case tryNatToFin i of
                          Nothing =>
                            assert_total $ idris_crash "Data.RRBVector.Unsized.Internal.computeSizes.isBalanced: can't convert Nat to Fin"
                          Just i' =>
                            at arr.arr i'
            in case i < lenM1 of
                 True  =>
                   assert_total $ (natToInteger $ treeSize (down sh) subtree) == maxsize && go (plus i 1)
                 False =>
                   treeBalanced subtree

export
countTrailingZeros :  Nat
                   -> Nat
countTrailingZeros x =
  go 0
  where
    w : Nat
    w = bitSizeOf Int
    go : Nat -> Nat
    go i =
      case i >= w of
        True  =>
          i
        False =>
          case tryNatToFin i of
            Nothing =>
              assert_total $ idris_crash "Data.RRBVector.Unsized.Internal.countTrailingZeros: can't convert Nat to Fin"
            Just i' =>
              case testBit (the Int (cast x)) i' of
                True  =>
                  i
                False =>
                  assert_total $ go (plus i 1)

||| Nat log base 2.
export
log2 :  Nat
     -> Nat
log2 x =
  let bitSizeMinus1 = minus (bitSizeOf Int) 1
    in minus bitSizeMinus1 (countLeadingZeros x)
  where
    countLeadingZeros : Nat -> Nat
    countLeadingZeros x =
      minus (minus w 1) (go (minus w 1))
      where
        w : Nat
        w = bitSizeOf Int
        go : Nat -> Nat
        go i =
          case i < 0 of
            True  =>
              i
            False =>
              case tryNatToFin i of
                Nothing =>
                  assert_total $ idris_crash "Data.RRBVector.Unsized.Internal.log2: can't convert Nat to Fin"
                Just i' =>
                  case testBit (the Int (cast x)) i' of
                    True  =>
                      i
                    False =>
                      assert_total $ go (minus i 1)

--------------------------------------------------------------------------------
--          Write Buffer Entries (Entry)
--------------------------------------------------------------------------------

||| A timestamped write entry stored inside WriteBuffers.
|||
||| Each logical mutation to the LSMRRBVector is first converted into an Entry
||| before being placed into a striped WriteBuffers structure.
|||
||| Fields:
||| - value:
|||   - The actual value being written.
||| - timestamp:
|||   - A logical timestamp used to impose a deterministic global ordering
|||     across concurrent writes.
|||   - This is expressed using `Tm`, a structured time representation
|||     (calendar time), rather than a monotonic counter.
|||
||| Ordering model:
||| - Entries are ordered during flush by timestamp.
||| - If two entries share identical timestamps, tie-breaking is implementation
|||   defined (typically stripe order or stable list order).
|||
||| Role in LSM pipeline:
||| - Produced at write time (append/prepend).
||| - Buffered in WriteBuffers.
||| - Sorted and merged during flush into the RRBVector.
|||
||| Note:
||| - Timestamp is used for merge ordering, not for indexing inside the tree.
||| - The RRBVector itself remains free of timestamp metadata.
|||
public export
record Entry a where
  constructor MkEntry
  value     : a
  timestamp : Tm

%runElab derive "Entry" [Show]

--------------------------------------------------------------------------------
--          Write buffers (WriteBuffers)
--------------------------------------------------------------------------------

||| WriteBuffers represent the deferred write layer of an LSM-style vector.
|||
||| Instead of immediately applying mutations to the underlying RRB tree,
||| writes are first accumulated into in-memory buffers.
|||
||| This structure is now used in a striped concurrency model:
||| - Multiple independent WriteBuffers exist (one per stripe).
||| - Each stripe reduces contention by allowing concurrent writes to
|||   different buffers without interference.
|||
||| Each buffer stores timestamped entries:
||| - prependbuffer : List (Entry a)
||| - appendbuffer  : SnocList (Entry a)
|||
||| Directional buffers:
||| - prependbuffer:
|||   - Stores logically front-inserted values.
||| - appendbuffer:
|||   - Stores logically back-appended values.
|||
||| Length fields:
||| - prependlen / appendlen track buffer sizes explicitly to avoid O(n)
||| - recomputation and to support deterministic flush thresholds.
|||
||| Invariant:
||| - prependlen == length prependbuffer
||| - appendlen  == length appendbuffer
|||
||| Concurrency model:
||| - Each WriteBuffers instance is protected by a Mutex at the LSM level.
||| - Multiple stripes may be written concurrently.
||| - Each buffer is only mutated inside a controlled critical section.
|||
||| Flush policy:
||| - When a buffer exceeds a configured block size (e.g. 16 entries),
|||   it becomes eligible for flushing.
||| - Flushing is performed by a dedicated thread or coordinated flush path
|||   under a global LSMRRBVector mutex.
|||
||| Merge semantics:
||| - During flush, entries from all stripes are collected.
||| - Entries are ordered using their timestamp (Tm).
||| - Ordered entries are then merged into the RRBVector.
|||
public export
record WriteBuffers a where
  constructor MkWriteBuffers
  prependbuffer : List a
  prependlen    : Nat
  appendbuffer  : SnocList a
  appendlen     : Nat
  
%runElab derive "WriteBuffers" [Show]

--------------------------------------------------------------------------------
--          Relaxed Radix Balanced Vector (RRBVector)
--------------------------------------------------------------------------------

||| RRBVector is the immutable core data structure representing a relaxed
||| radix balanced vector.
|||
||| This is the "stable snapshot" layer of the LSM design. Once writes are
||| flushed from WriteBuffers, they are materialized into this structure.
|||
||| Fields:
||| - size  : Total number of elements stored in the tree.
||| - shift : The current tree height indicator (used for radix indexing).
|||           It determines how many levels of branching exist in the tree.
||| - tree  : The actual RRB tree structure storing elements in a
|||           balanced, indexed layout with relaxed constraints for efficient
|||           concatenation and updates.
|||
||| Properties:
||| - Supports O(log n) indexed access.
||| - Supports efficient concatenation compared to strict vectors.
||| - Maintains balance via relaxed block sizes rather than strict fullness.
|||
||| Role in LSM design:
||| - Serves as the stable read snapshot.
||| - Updated only during flush/rebuild operations.
||| - Replaced atomically under a Mutex (not CAS).
|||
||| Concurrency model:
||| - Protected by LSMRRBVector-level Mutex.
||| - Reads are lock-free (snapshot reads).
||| - Writes never mutate it directly.
||| - Flush operations create a new RRBVector and swap it under lock.
|||
||| Consistency model:
||| - Readers always observe a consistent snapshot.
||| - Buffered writes may not be visible until next flush.
|||
public export
data RRBVector a = Root Nat   -- size
                        Shift -- shift (blockshift * height)
                        (Tree a)
                 | Empty
  
%runElab derive "RRBVector" [Show]

--------------------------------------------------------------------------------
--          Log-Structured Merge RRB Vectors (LSMRRBVector)
--------------------------------------------------------------------------------

||| LSMRRBVector is a concurrent log-structured vector built from:
||| - striped write buffers (WriteBuffers)
||| - an immutable RRB snapshot tree (RRBVector)
||| - a global mutex controlling flush and rebuild operations
|||
||| Architecture:
||| - Write path:
|||   - Writes are distributed across multiple striped buffers.
|||   - Each write is converted into an Entry (value + timestamp).
|||   - Writes are fast and require only short critical sections.
||| - Read path:
|||   - Reads primarily consult the RRBVector snapshot.
|||   - Buffered writes may not yet be visible until flushed.
||| - Flush / merge path:
|||   - Triggered when buffers exceed a threshold or by a background thread.
|||   - A single Mutex is acquired to ensure exclusive rebuild.
|||   - All buffers are drained and merged.
|||   - Entries are ordered by timestamp (Tm).
|||   - A new RRBVector is constructed and swapped in atomically.
|||
||| Concurrency model:
||| - buffers :
|||   - Array (Ref s (WriteBuffers a))
|||     → striped write hot path
||| - tree :
|||   - Ref s (RRBVector a)
|||     → immutable snapshot, replaced under mutex
||| - lock :
|||   - Mutex
|||     → ensures only one flush/rebuild occurs at a time
|||
||| Key properties:
||| - High write throughput via striping
||| - Low contention via buffer isolation
||| - Deterministic global ordering via timestamps
||| - Consistent snapshots via mutex-protected rebuild
|||
||| Trade-offs:
||| - Writes are fast but not immediately visible
||| - Flush operations are expensive but serialized
||| - Ordering depends on timestamp correctness
|||
||| This design is optimized for write-heavy workloads with periodic batch
||| compaction into a balanced immutable structure.
|||
public export
record LSMRRBVector s a where
  constructor MkLSMRRBVector
  buffers : Array (Ref s (WriteBuffers a))
  tree    : Ref s (RRBVector a)
  lock    : Mutex
