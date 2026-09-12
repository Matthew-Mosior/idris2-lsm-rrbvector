||| RRB Vector Internals
module Data.RRBVector.Internal

import Data.Array
import Data.Array.Core
import Data.Array.Index
import Data.Array.Indexed
import Data.Bits
import Data.Fin
import Data.List
import Data.Nat
import Data.String
import Derive.Prelude
import Syntax.T1 as T1

%default total
%language ElabReflection

--------------------------------------------------------------------------------
--          Internal Utilities
--------------------------------------------------------------------------------

||| Convenience interface for bitSize that doesn't use an implicit parameter.
|||
private
bitSizeOf :  (ty : Type)
          -> FiniteBits ty
          => Nat
bitSizeOf ty = bitSize {a = ty}

||| Read the final element of a known nonempty indexed array.
|||
||| The bound proof is erased at runtime.
|||
export %inline
lastAt :  {n : Nat}
       -> IArray (S n) a
       -> a
lastAt arr =
  atNat arr n

--------------------------------------------------------------------------------
--          RelaxedIndex
--------------------------------------------------------------------------------

||| The result of locating an element within a relaxed RRB tree node.
|||
||| `child` identifies the child subtree containing the requested logical
||| element. Its `Fin count` type guarantees that the child index is valid
||| for the corresponding node.
|||
||| `offset` is the element's index relative to the beginning of that child
||| subtree.
|||
||| Returning the child position as a bounded index allows subsequent array
||| access to avoid an additional `Nat`-to-`Fin` conversion.
|||
public export
record RelaxedIndex (count : Nat) where
  constructor MkRelaxedIndex
  child : Fin count
  offset : Nat

--------------------------------------------------------------------------------
--          Internals
--------------------------------------------------------------------------------

public export
Shift : Type
Shift = Nat

||| The number of bits used per level.
|||
export
blockshift : Shift
blockshift = 4

||| The maximum size of a block.
|||
export
blocksize : Nat
blocksize = integerToNat $ 1 `shiftL` blockshift

||| The mask used to extract the index into the array.
|||
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

--------------------------------------------------------------------------------
--          Internal Tree Representation
--------------------------------------------------------------------------------

mutual

  ||| A nonempty collection of child nodes for a balanced RRB tree node.
  |||
  ||| The number of children is existentially quantified by `n`.
  |||
  ||| The erased proofs guarantee that:
  ||| - the node contains at least one child, and
  ||| - the number of children does not exceed the RRB branching factor.
  |||
  ||| Because these invariants are carried in the type, callers can index the
  ||| underlying `IArray` using bounded indices without repeatedly recovering
  ||| these facts through `tryNatToFin` or other runtime bounds checks.
  |||
  public export
  data Children : Type -> Type where
    MkChildren :  {n : Nat}
               -> {auto 0 nonEmpty : LT 0 n}
               -> {auto 0 withinBlock : LTE n Data.RRBVector.Internal.blocksize}
               -> IArray n (Tree a)
               -> Children a

  ||| A nonempty collection of child nodes for a relaxed RRB tree node,
  ||| together with its cumulative size table.
  |||
  ||| Both arrays have the same statically tracked length `n`, which guarantees
  ||| that every child has a corresponding cumulative-size entry.
  |||
  ||| The erased proofs additionally guarantee that:
  ||| - the node contains at least one child, and
  ||| - the number of children does not exceed the RRB branching factor.
  |||
  ||| Encoding these invariants directly avoids repeatedly converting raw
  ||| `Nat` indices with `tryNatToFin` when traversing relaxed nodes.
  |||
  public export
  data RelaxedChildren : Type -> Type where
    MkRelaxedChildren :  {n : Nat}
                      -> {auto 0 nonEmpty : LT 0 n}
                      -> {auto 0 withinBlock : LTE n Data.RRBVector.Internal.blocksize}
                      -> IArray n (Tree a)
                      -> IArray n Nat
                      -> RelaxedChildren a

  ||| The internal tree representation of an RRB vector.
  |||
  ||| A tree node is one of:
  ||| - `Balanced` -> containing a nonempty bounded array of child nodes whose
  |||   positions are determined directly from the radix index.
  ||| - `Unbalanced` -> containing a nonempty bounded array of child nodes plus
  |||   a cumulative size table used for relaxed indexing.
  ||| - `Leaf` -> containing the actual vector elements.
  |||
  ||| Internal-node invariants such as nonemptiness, maximum branching factor,
  ||| and matching child/size-table lengths are encoded by `Children` and
  ||| `RelaxedChildren`. This allows traversal code to work with bounded indices
  ||| directly rather than repeatedly recovering those invariants at runtime.
  |||
  public export
  data Tree : Type -> Type where
    Balanced   :  Children a
               -> Tree a
    Unbalanced :  RelaxedChildren a
               -> Tree a
    Leaf       :  Array a
               -> Tree a

--------------------------------------------------------------------------------
--          Children and RelaxedChildren
--------------------------------------------------------------------------------

||| Convert a bounded collection of balanced-node children back to the
||| existential `Array` representation.
|||
||| This is primarily useful for APIs and utility functions that do not need
||| to retain the child-count index in their result type.
|||
export %inline
childrenToArray :  Children a
                -> Array (Tree a)
childrenToArray (MkChildren {n} arr) =
  A n arr

||| Convert the child array of a relaxed node back to the existential
||| `Array` representation.
|||
||| The corresponding size table has the same statically tracked length, but
||| is intentionally discarded by this projection.
|||
export %inline
relaxedChildrenToArray :  RelaxedChildren a
                       -> Array (Tree a)
relaxedChildrenToArray (MkRelaxedChildren {n} children _) =
  A n children

||| Convert the cumulative size table of a relaxed node back to the
||| existential `Array` representation.
|||
export %inline
relaxedSizesToArray :  RelaxedChildren a
                    -> Array Nat
relaxedSizesToArray (MkRelaxedChildren {n} _ sizes) =
  A n sizes

--------------------------------------------------------------------------------
--          Query (Tree)
--------------------------------------------------------------------------------

||| Is the tree empty? O(1)
|||
private
null :  Tree a
     -> Bool
null (Balanced _)   =
  False
null (Unbalanced _) =
  False
null (Leaf arr)     =
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
    foldlTree acc' (Balanced (MkChildren {n} arr))            =
      assert_total (foldl foldlTree acc' (A n arr))
    foldlTree acc' (Unbalanced (MkRelaxedChildren {n} arr _)) =
      assert_total (foldl foldlTree acc' (A n arr))
    foldlTree acc' (Leaf arr)                                 =
      assert_total (foldl f acc' arr)

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
    foldrTree (Balanced (MkChildren {n} arr)) acc'            =
      assert_total (foldr foldrTree acc' (A n arr))
    foldrTree (Unbalanced (MkRelaxedChildren {n} arr _)) acc' =
      assert_total (foldr foldrTree acc' (A n arr))
    foldrTree (Leaf arr) acc'                                 =
      assert_total (foldr f acc' arr)

--------------------------------------------------------------------------------
--          Creating Lists from Trees
--------------------------------------------------------------------------------

export
toList :  Tree a
       -> List a
toList (Balanced (MkChildren {n} arr))            =
  assert_total (concat $ map toList $ toList (A n arr))
toList (Unbalanced (MkRelaxedChildren {n} arr _)) =
  assert_total (concat $ map toList $ toList (A n arr))
toList (Leaf arr)                                 =
  toList arr

--------------------------------------------------------------------------------
--          Interfaces (Tree)
--------------------------------------------------------------------------------

public export
Show a => Show (Tree a) where
  show (Balanced children)   =
    assert_total ("Balanced " ++ show (childrenToArray children))
  show (Unbalanced children) =
    assert_total ("Unbalanced " ++ show (relaxedChildrenToArray children))
  show (Leaf arr)            =
    "Leaf " ++ show arr

public export
Foldable Tree where
  foldl f z = Data.RRBVector.Internal.foldl f z
  foldr f z = Data.RRBVector.Internal.foldr f z
  toList    = Data.RRBVector.Internal.toList
  null      = Data.RRBVector.Internal.null

public export
Eq a => Eq (Tree a) where
  Balanced xs == Balanced ys     =
    assert_total (childrenToArray xs == childrenToArray ys)
  Unbalanced xs == Unbalanced ys =
    assert_total (relaxedChildrenToArray xs == relaxedChildrenToArray ys)
  Leaf xs == Leaf ys             =
    xs == ys
  _ == _                         =
    False

public export
Ord a => Ord (Tree a) where
  compare tree1 tree2 =
    compare (Data.RRBVector.Internal.toList tree1) (Data.RRBVector.Internal.toList tree2)

--------------------------------------------------------------------------------
--          Show Utilities (Tree)
--------------------------------------------------------------------------------

public export
showTreeRep :  Show a
            => Show (Tree a)
            => Tree a
            -> String
showTreeRep (Balanced children)   =
  assert_total ("Balanced " ++ show (toList $ childrenToArray children))
showTreeRep (Unbalanced children) =
  assert_total ("Unbalanced " ++ show (toList $ relaxedChildrenToArray children))
showTreeRep (Leaf elems)          =
  assert_total ("Leaf " ++ show (toList elems))

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
treeToArray (Balanced children)   =
  childrenToArray children
treeToArray (Unbalanced children) =
  relaxedChildrenToArray children
treeToArray (Leaf _)              =
  assert_total (idris_crash "Data.RRBVector.Internal.treeToArray: leaf")

export
treeBalanced :  Tree a
             -> Bool
treeBalanced (Balanced _)   =
  True
treeBalanced (Unbalanced _) =
  False
treeBalanced (Leaf _)       =
  True

||| Computes the size of a tree with shift.
|||
export
treeSize :  Shift
         -> Tree a
         -> Nat
treeSize =
  go 0
  where
    go :  Shift
       -> Shift
       -> Tree a
       -> Nat
    go acc _ (Leaf arr)                                         =
      plus acc arr.size
    go acc _ (Unbalanced (MkRelaxedChildren {n = S k} _ sizes)) =
      plus acc (lastAt sizes)
    go acc sh (Balanced (MkChildren {n = S k} children))        =
      let subtreeSize : Nat
          subtreeSize = integerToNat (1 `shiftL` sh)
          acc'        : Nat
          acc'        = plus acc (mult k subtreeSize)
          child       : Tree a
          child       = lastAt children
       in go acc' (down sh) (assert_smaller children child)


||| Locate the child subtree containing a logical index in a relaxed node.
|||
||| The size table contains cumulative subtree sizes and has exactly `n`
||| entries, one for each child in the corresponding relaxed node.
|||
||| The radix-derived initial guess is a lower bound on the actual child
||| position. The search advances through the cumulative size table until it
||| finds the first entry greater than `i`.
|||
||| The returned `RelaxedIndex` carries the selected child as `Fin n`, so the
||| caller can index the corresponding child array directly without performing
||| another `Nat`-to-`Fin` conversion.
|||
||| For a well-formed relaxed node and a logical index belonging to that node:
||| - the initial radix guess is strictly smaller than the number of children
||| - whenever the current cumulative size does not contain `i`, another size
|||   entry exists.
|||
||| These structural invariants are supplied as erased proofs and therefore
||| introduce no runtime bounds checks.
|||
export
relaxedRadixIndex :  {n : Nat}
                  -> {auto 0 nonEmpty : LT 0 n}
                  -> IArray n Nat
                  -> Nat
                  -> Shift
                  -> RelaxedIndex n
relaxedRadixIndex {n = Z} {nonEmpty} sizes i sh impossible
relaxedRadixIndex {n = S k} sizes i sh =
  let guess     : Nat
      guess     = radixIndex i sh
      0 guessLT : LT guess (S k)
      guessLT   = believe_me ()
      child     : Fin (S k)
      child     = natToFinLT guess @{guessLT}
    in assert_total (loop child)
  where
    ||| Compute the logical index relative to the selected child.
    |||
    ||| For the first child, the logical index is already relative to that
    ||| child. For later children, the cumulative size of the preceding child
    ||| is subtracted from the logical index.
    |||
    childOffset :  Fin (S k)
                -> Nat
    childOffset FZ =
      i
    childOffset (FS previous) =
      minus i (at sizes (weaken previous))
    ||| Search forward through the cumulative size table for the first child
    ||| whose cumulative size is greater than the requested logical index.
    |||
    ||| The search itself carries a bounded `Fin (S k)` child index, so reading
    ||| the size table requires no runtime `Nat`-to-`Fin` conversion.
    |||
    loop :  Fin (S k)
         -> RelaxedIndex (S k)
    loop child =
      let current : Nat
          current = at sizes child
       in case i < current of
            True  =>
              MkRelaxedIndex child (childOffset child)
            False =>
              let next      : Nat
                  next      = S (finToNat child)
                  0 nextLT  : LT next (S k)
                  nextLT    = believe_me ()
                  nextchild : Fin (S k)
                  nextchild = natToFinLT next @{nextLT}
                in assert_total (loop nextchild)

||| Turns a valid collection of child nodes into an internal tree node.
|||
||| If every non-final child is a full subtree and the final child is
||| balanced, the resulting node is represented as `Balanced`.
|||
||| Otherwise, a cumulative size table with exactly the same statically
||| tracked length as the child array is constructed and the node is
||| represented as `Unbalanced`.
|||
export
computeSizes :  Shift
             -> Children a
             -> Tree a
computeSizes sh children@(MkChildren {n} {nonEmpty} {withinBlock} trees) =
  case isBalanced n of
    True =>
      Balanced children
    False =>
      let sizes : IArray n Nat
          sizes = unsafeAlloc n (loop n 0)
        in Unbalanced (MkRelaxedChildren {nonEmpty = nonEmpty} {withinBlock = withinBlock} trees sizes)
  where
    ||| Fill the cumulative subtree-size table from left to right.
    |||
    ||| `Ix remaining n` carries the current valid array position, avoiding
    ||| any dynamic `Nat`-to-`Fin` conversion.
    |||
    loop :  (remaining : Nat)
         -> {auto pos : Ix remaining n}
         -> Nat
         -> WithMArray n Nat (IArray n Nat)
    loop Z acc r = T1.do
      unsafeFreeze r
    loop (S k) {pos} acc r =
      let subtree : Tree a
          subtree = ix trees k
          acc'    : Nat
          acc'    = plus acc (treeSize (down sh) subtree)
          dst     : Fin n
          dst     = ixToFin pos
       in T1.do
            set r dst acc'
            assert_total $ loop k acc' r
    ||| Maximum logical size of a full child subtree at this level.
    |||
    maxsize : Integer
    maxsize = 1 `shiftL` sh
    ||| Determine whether the children can use the compact balanced-node
    ||| representation.
    |||
    isBalanced :  (remaining : Nat)
               -> {auto pos : Ix remaining n}
               -> Bool
    isBalanced Z     =
      True
    isBalanced (S Z) =
      treeBalanced (ix trees Z)
    isBalanced (S (S k)) =
      let subtree : Tree a
          subtree = ix trees (S k)
       in assert_total ((natToInteger $ treeSize (down sh) subtree) == maxsize && isBalanced (S k))

||| Count the number of consecutive zero bits beginning at the least
||| significant bit of a natural number.
|||
||| Bit positions are traversed from least significant to most significant.
||| The `Ix` witness carries the current valid bit position within the fixed
||| width of `Int`, so no `tryNatToFin` conversion is required.
|||
||| If no set bit is found, the full bit width of `Int` is returned.
|||
export
countTrailingZeros :  Nat
                   -> Nat
countTrailingZeros x =
  go (bitSizeOf Int)
  where
    value : Int
    value = cast x
    ||| Scan bit positions from least significant to most significant.
    |||
    go :  (remaining : Nat)
       -> {auto pos : Ix remaining (bitSizeOf Int)}
       -> Nat
    go Z           =
      bitSizeOf Int
    go (S k) {pos} =
      let bit : Fin (bitSizeOf Int)
          bit = ixToFin pos
       in case testBit value bit of
            True  =>
              finToNat bit
            False =>
              assert_total (go k)

||| Compute the base-2 logarithm of a natural number, rounded down.
|||
||| The implementation scans the fixed-width `Int` representation from the
||| most significant bit toward the least significant bit and returns the
||| position of the first set bit.
|||
||| The recursive `LTE remaining (bitSizeOf Int)` proof guarantees that every
||| tested bit position is valid. The proof is erased, and conversion to
||| `Fin (bitSizeOf Int)` therefore requires no dynamic `Nat`-to-`Fin`
||| bounds check.
|||
||| `log2 0` is defined as `0`.
|||
export
log2 :  Nat
     -> Nat
log2 x =
  go (bitSizeOf Int)
  where
    value : Int
    value = cast x
    ||| Scan bit positions from most significant to least significant.
    |||
    ||| In the `S k` case, `valid` has type
    ||| `LTE (S k) (bitSizeOf Int)`, which is definitionally the proof
    ||| required for `LT k (bitSizeOf Int)`.
    |||
    go :  (remaining : Nat)
       -> {auto 0 valid : LTE remaining (bitSizeOf Int)}
       -> Nat
    go Z =
      Z
    go (S k) {valid} =
      let bit : Fin (bitSizeOf Int)
          bit = natToFinLT k @{valid}
       in case testBit value bit of
            True  =>
              k
            False =>
              assert_total (go k {valid = lteSuccLeft valid})

--------------------------------------------------------------------------------
--          RRB Vectors
--------------------------------------------------------------------------------

||| A relaxed radix balanced vector (RRBVector).
||| It supports fast indexing, iteration, concatenation and splitting.
|||
public export
data RRBVector a
  = Root Nat   -- size
         Shift -- shift (blockshift * height)
         (Tree a)
  | Empty

%runElab derive "RRBVector" [Show]
