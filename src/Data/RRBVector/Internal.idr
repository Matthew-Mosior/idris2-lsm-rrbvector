||| RRB Vector Internals
module Data.RRBVector.Internal

import Data.Array
import Data.Array.Core
import Data.Array.Index
import Data.Array.Indexed
import Data.Bits
import Data.List
import Data.Nat
import Data.String
import Derive.Prelude
import Syntax.T1 as T1

%default total
%language ElabReflection

--------------------------------------------------------------------------------
--          Internal Utility
--------------------------------------------------------------------------------

||| Convenience interface for bitSize that doesn't use an implicit parameter.
|||
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

export
relaxedRadixIndex :  Array Nat
                  -> Nat
                  -> Shift
                  -> Maybe (Nat, Nat)
relaxedRadixIndex sizes i sh =
  let guess        = radixIndex i sh -- guess <= idx
      Just idx     = loop sizes guess
        | Nothing =>
            Nothing
      subidx       = case idx == 0 of
                       True  =>
                         Just i
                       False =>
                         let idx'       = tryNatToFin $ minus idx 1
                             Just idx'' = idx'
                               | Nothing =>
                                   Nothing
                           in Just $ minus i (at sizes.arr idx'')
      Just subidx' = subidx
        | Nothing =>
            Nothing
    in Just (idx, subidx')
  where
    loop :  Array Nat
         -> Nat
         -> Maybe Nat
    loop sizes idx =
      let Just idx' = tryNatToFin idx
            | Nothing =>
                Nothing
          current   = at sizes.arr idx'
          False     = i < current
            | True =>
                Just idx
        in assert_total $ loop sizes (plus idx 1)

--------------------------------------------------------------------------------
--          Internal Tree Representation
--------------------------------------------------------------------------------

||| An internal tree representation.
|||
public export
data Tree a
  = Balanced (Array (Tree a))
  | Unbalanced (Array (Tree a)) (Array Nat)
  | Leaf (Array a)

--------------------------------------------------------------------------------
--          Query (Tree)
--------------------------------------------------------------------------------

||| Is the tree empty? O(1)
|||
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
  foldl f z = Data.RRBVector.Internal.foldl f z
  foldr f z = Data.RRBVector.Internal.foldr f z
  toList    = Data.RRBVector.Internal.toList
  null      = Data.RRBVector.Internal.null

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
    compare (Data.RRBVector.Internal.toList tree1) (Data.RRBVector.Internal.toList tree2)

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
            -> Maybe (Array (Tree a))
treeToArray (Balanced arr)     =
  Just arr
treeToArray (Unbalanced arr _) =
  Just arr
treeToArray (Leaf _)           =
  Nothing

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
|||
export
treeSize :  Shift
         -> Tree a
         -> Maybe Nat
treeSize = go 0
  where
    go :  Shift
       -> Shift
       -> Tree a
       -> Maybe Nat
    go acc _  (Leaf arr)             =
      Just $ plus acc arr.size
    go acc _  (Unbalanced arr sizes) =
      let i       = tryNatToFin $ minus arr.size 1
          Just i' = i
            | Nothing =>
                Nothing
        in Just $ plus acc (at sizes.arr i')
    go acc sh (Balanced arr)         =
      let i        = minus arr.size 1
          i'       = tryNatToFin i
          Just i'' = i'
            | Nothing =>
                Nothing
        in go (plus acc (mult i (integerToNat (1 `shiftL` sh))))
              (down sh)
              (assert_smaller arr (at arr.arr i''))

||| Turns an array into a tree node by computing the sizes of its subtrees.
||| sh is the shift of the resulting tree.
|||
export
computeSizes :  Shift
             -> Array (Tree a)
             -> Maybe (Tree a)
computeSizes sh arr =
  let Just isbalanced = isBalanced
        | Nothing =>
            Nothing
      False           = isbalanced
        | True =>
            Just $ Balanced arr
      arrnat          = unsafeAlloc arr.size (loop sh 0 0 arr.size (toList arr))
      Just arrnat'    = arrnat
        | Nothing =>
            Nothing
    in Just $ Unbalanced arr arrnat'
  where
    loop :  (sh,cur,acc,n : Nat)
         -> List (Tree a)
         -> WithMArray n Nat (Maybe (Array Nat))
    loop sh _   acc n []        r = T1.do
      res <- unsafeFreeze r
      pure $ Just $ A n res
    loop sh cur acc n (x :: xs) r =
      let Just cur'     = tryNatToFin cur
            | Nothing =>
                pure Nothing
          Just treesize = treeSize (down sh) x
            | Nothing =>
                pure Nothing
          acc'          = plus acc treesize
        in T1.do set r cur' acc'
                 assert_total $ loop sh (S cur) acc' n xs r
    maxsize : Integer
    maxsize = 1 `shiftL` sh -- the maximum size of a subtree
    len : Nat
    len = arr.size
    lenM1 : Nat
    lenM1 = minus len 1
    isBalanced : Maybe Bool
    isBalanced = go 0
      where
        go :  Nat
           -> Maybe Bool
        go i =
          let Just subtree = tryNatToFin i
                | Nothing =>
                    Nothing
              subtree'     = at arr.arr subtree
              False        = i < lenM1
                | True =>
                    let Just treesize = treeSize (down sh) subtree'
                          | Nothing =>
                              Nothing
                        go'           = assert_total $ go (plus i 1)
                        Just go''     = go'
                          | Nothing =>
                              Nothing
                      in assert_total $ Just ((natToInteger treesize) == maxsize && go'')
            in Just $ treeBalanced subtree'

export
countTrailingZeros :  Nat
                   -> Maybe Nat
countTrailingZeros x =
  go 0
  where
    w : Nat
    w = bitSizeOf Int
    go :  Nat
       -> Maybe Nat
    go i =
      case i >= w of
        True  =>
          Just i
        False =>
          let Just i' = tryNatToFin i
                | Nothing =>
                    Nothing
              False   = testBit (the Int (cast x)) i'
                | True =>
                    Just i
            in assert_total $ go (plus i 1) 

||| Nat log base 2.
|||
export
log2 :  Nat
     -> Maybe Nat
log2 x =
  let bitSizeMinus1          = minus (bitSizeOf Int) 1
      Just countleadingzeros = countLeadingZeros x
        | Nothing =>
            Nothing
      countleadingzeros'     = minus bitSizeMinus1 countleadingzeros
    in Just countleadingzeros'
  where
    countLeadingZeros :  Nat
                      -> Maybe Nat
    countLeadingZeros x =
      let Just go' = go (minus w 1)
            | Nothing =>
                Nothing
        in Just $ minus (minus w 1) go'
      where
        w : Nat
        w = bitSizeOf Int
        go :  Nat
           -> Maybe Nat
        go i =
          case i < 0 of
            True  =>
              Just i
            False =>
              let Just i' = tryNatToFin i
                    | Nothing =>
                        Nothing
                  False   = testBit (the Int (cast x)) i'
                    | True =>
                        Just i
                in assert_total $ go (minus i 1)

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
