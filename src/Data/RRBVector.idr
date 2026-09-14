||| Relaxed Radix Balanced Vectors (RRBVector)
module Data.RRBVector

import public Data.RRBVector.Internal

import Data.Array
import Data.Array.Core
import Data.Array.Index
import Data.Array.Indexed
import Data.Bits
import Data.Linear.Ref1
import Data.Linear.Traverse1
import Data.List
import Data.List1
import Data.Maybe
import Data.SnocList
import Data.Vect
import Data.Zippable
import Syntax.T1 as T1

%hide Prelude.null
%hide Prelude.Ops.infixr.(<|)
%hide Prelude.Ops.infixl.(|>)

%default total

--------------------------------------------------------------------------------
--          Fixity
--------------------------------------------------------------------------------

export
infixr 5 ><

export
infixr 5 <|

export
infixl 5 |>

--------------------------------------------------------------------------------
--          Utilities
--------------------------------------------------------------------------------

||| Transport an indexed array across an equality of its lengths.
|||
||| The equality proof is erased at runtime, so this introduces no runtime
||| conversion or allocation.
|||
private
%inline
castIArray :  {m, n : Nat}
           -> (0 prf : m = n)
           -> IArray m a
           -> IArray n a
castIArray Refl arr =
  arr

||| Reflexivity of `LTE` for natural numbers.
|||
||| This proof is erased at runtime.
|||
private
0 lteReflNat :  (n : Nat)
             -> LTE n n
lteReflNat Z     =
  LTEZero
lteReflNat (S n) =
  LTESucc (lteReflNat n)

||| Adding one on the right of a natural number is its successor.
|||
private
0 plusOneRight :  (n : Nat)
               -> plus n 1 = S n
plusOneRight Z     =
  Refl
plusOneRight (S n) =
  cong S (plusOneRight n)

||| Construct a bounded child collection by appending one child to an indexed
||| array.
|||
||| The resulting collection is statically nonempty. The equality between
||| `n + 1` and `S n` is proved and erased at runtime.
|||
private
childrenSnoc :  {n : Nat}
             -> IArray n (Tree a)
             -> Tree a
             -> Children a
childrenSnoc {n} xs x =
  let arr  : IArray (plus n 1) (Tree a)
      arr  = append xs (fill 1 x)
      arr' : IArray (S n) (Tree a)
      arr' = castIArray (plusOneRight n) arr
    in MkChildren {n = S n} {nonEmpty = LTESucc LTEZero} {withinBlock = believe_me ()} arr'

||| Construct a bounded child collection by prepending one child to an indexed
||| array.
|||
||| The resulting collection is statically nonempty, and the child count is
||| carried directly in the resulting `Children`.
|||
||| The branching-factor proof is erased at runtime.
|||
private
childrenCons :  {n : Nat}
             -> Tree a
             -> IArray n (Tree a)
             -> Children a
childrenCons {n} x xs =
  MkChildren {n = S n} {nonEmpty = LTESucc LTEZero} {withinBlock = believe_me ()} (append (fill 1 x) xs)

||| Construct a bounded nonempty child collection from an internal array.
|||
||| Callers must maintain the RRB invariant that the array is nonempty and
||| contains no more than `blocksize` children. The branching-factor proof is
||| erased at runtime.
|||
private
childrenFromArray :  Array (Tree a)
                  -> Children a
childrenFromArray (A Z _) =
  assert_total (idris_crash "Data.RRBVector.childrenFromArray: empty child array")
childrenFromArray (A (S n) arr) =
  MkChildren {nonEmpty = LTESucc LTEZero} {withinBlock = believe_me ()} arr

||| The final valid index of a statically nonempty collection.
|||
private %inline
lastFin :  {n : Nat}
        -> Fin (S n)
lastFin {n = Z} =
  FZ
lastFin {n = S k} =
  FS lastFin

--------------------------------------------------------------------------------
--          Creating RRB-Vectors
--------------------------------------------------------------------------------

||| The empty vector. O(1)
|||
export
empty : RRBVector a
empty = Empty

||| A vector with a single element. O(1)
|||
export
singleton :  a
          -> RRBVector a
singleton x = Root 1 0 (Leaf $ A 1 $ fill 1 x)

||| Create a new vector from a list. O(n)
|||
||| Leaf and internal-node arrays are filled from left to right using `Ix`.
||| The `Ix remaining n` witness carries the current valid array position, so
||| writes require no dynamic `Nat`-to-`Fin` conversion.
|||
export
fromList :
     List a
  -> RRBVector a
fromList []  =
  Empty
fromList [x] =
  singleton x
fromList xs  =
  case nodes Leaf xs of
    [tree] =>
      Root (treeSize 0 tree) 0 tree
    xs' =>
      assert_smaller xs (iterateNodes blockshift xs')
  where
    ||| Build leaf-sized nodes from a list.
    |||
    ||| `remaining` is the number of writable array positions still available.
    ||| The `Ix remaining n` witness identifies the current forward position
    ||| and converts directly to `Fin n` through `ixToFin`.
    |||
    nodes :  (Array a -> Tree a)
          -> List a
          -> List (Tree a)
    nodes f trees =
      let (tree, rest) = unsafeAlloc blocksize (go {n = blocksize} blocksize f trees)
        in case rest of
            [] =>
              [tree]
            rest' =>
              tree :: nodes f (assert_smaller trees rest')
      where
        ||| Fill one array from left to right.
        |||
        ||| When the input list is exhausted before the array is full,
        ||| `ixToNat pos` is the number of positions that were written.
        |||
        ||| When `remaining` reaches zero, the array is full and the
        ||| unconsumed input list is returned for construction of the next
        ||| node.
        |||
        go :  {n : Nat}
           -> (remaining : Nat)
           -> {auto pos : Ix remaining n}
           -> (Array a -> Tree a)
           -> List a
           -> WithMArray n a (Tree a, List a)
        go {n} remaining {pos} f [] r      = T1.do
          res <- unsafeFreeze r
          let written : Nat
              written = ixToNat pos
          pure
            ( f $
                force $
                  take written $
                    A n res
            , []
            )
        go {n} Z         {pos} f xs        r = T1.do
          res <- unsafeFreeze r
          pure
            ( f $ A n res
            , xs
            )
        go {n} (S k)     {pos} f (x :: xs) r =
          let idx : Fin n
              idx = ixToFin pos
           in T1.do
                set r idx x
                assert_total (go {n} k {pos = IS pos} f xs r)
    ||| Build internal RRB nodes from a list of child trees.
    |||
    ||| As with `nodes`, array positions are represented by `Ix`, eliminating
    ||| dynamic `Nat`-to-`Fin` conversion while filling each child array.
    |||
    nodes' :  (Array (Tree a) -> Tree a)
           -> List (Tree a)
           -> List (Tree a)
    nodes' f trees =
      let (tree, rest) =
            unsafeAlloc blocksize (go {n = blocksize} blocksize f trees)
       in case rest of
            [] =>
              [tree]
            rest' =>
              tree :: nodes' f (assert_smaller trees rest')
      where
        ||| Fill one internal-node child array from left to right.
        |||
        go :  {n : Nat}
           -> (remaining : Nat)
           -> {auto pos : Ix remaining n}
           -> (Array (Tree a) -> Tree a)
           -> List (Tree a)
           -> WithMArray n (Tree a) (Tree a, List (Tree a))
        go {n} remaining {pos} f []        r = T1.do
          res <- unsafeFreeze r
          let written : Nat
              written = ixToNat pos
          pure
            ( f $
                force $
                  take written $
                    A n res
            , []
            )
        go {n} Z         {pos} f xs        r = T1.do
          res <- unsafeFreeze r
          pure
            ( f $ A n res
            , xs
            )
        go {n} (S k)     {pos} f (x :: xs) r =
          let idx : Fin n
              idx = ixToFin pos
           in T1.do
                set r idx x
                assert_total (go {n} k {pos = IS pos} f xs r)
    ||| Repeatedly group child trees into balanced internal nodes until only a
    ||| single root remains.
    |||
    iterateNodes :  Shift
                 -> List (Tree a)
                 -> RRBVector a
    iterateNodes sh trees =
      case nodes' (\arr => Balanced (childrenFromArray arr)) trees of
        [tree] =>
          Root (treeSize sh tree) sh tree
        trees' =>
          iterateNodes (up sh) (assert_smaller trees trees')

||| Creates a vector of length `n` with every element set to `x`. O(log n)
|||
export
replicate :  Nat
          -> a
          -> RRBVector a
replicate n x =
  case compare n 0 of
    LT =>
      Empty
    EQ =>
      Empty
    GT =>
      case compare n blocksize of
        LT =>
          Root n 0 (Leaf $ A n $ fill n x)
        EQ =>
          Root n 0 (Leaf $ A n $ fill n x)
        GT =>
          let size' = integerToNat $ (natToInteger $ minus n 1) .&. (natToInteger $ plus blockmask 1)
            in iterateNodes blockshift (Leaf $ A blocksize $ fill blocksize x) (Leaf $ A size' $ fill size' x)
  where
    iterateNodes :  Shift
                 -> Tree a
                 -> Tree a
                 -> RRBVector a
    iterateNodes sh full rest =
      let subtreesm1   = (natToInteger $ minus n 1) `shiftR` sh
          restsize     = integerToNat $ subtreesm1 .&. natToInteger blockmask
          restchildren : Children a
          restchildren = childrenSnoc (fill restsize full) rest
          rest'        : Tree a
          rest'        = Balanced restchildren
       in case compare subtreesm1 (natToInteger blocksize) of
            LT =>
              Root n sh rest'
            EQ =>
              let fullchildren : Children a
                  fullchildren = MkChildren {n = blocksize} {nonEmpty = believe_me ()} {withinBlock = lteReflNat blocksize} (fill blocksize full)
                  full'        = Balanced fullchildren
                in iterateNodes (up sh) (assert_smaller full full') (assert_smaller rest rest')
            GT =>
              let fullchildren : Children a
                  fullchildren = MkChildren {n = blocksize} {nonEmpty = believe_me ()} {withinBlock = lteReflNat blocksize} (fill blocksize full)
                  full'        = Balanced fullchildren
                in iterateNodes (up sh) (assert_smaller full full') (assert_smaller rest rest')

--------------------------------------------------------------------------------
--          Creating Lists from RRB-Vectors
--------------------------------------------------------------------------------

||| Convert a vector to a list. O(n)
|||
export
toList :  RRBVector a
       -> List a
toList Empty           =
  []
toList (Root _ _ tree) =
  treeToList tree
  where
    treeToList :  Tree a
               -> List a
    treeToList (Balanced (MkChildren {n} trees))            =
      assert_total (concat (map treeToList (toList (A n trees))))
    treeToList (Unbalanced (MkRelaxedChildren {n} trees _)) =
      assert_total (concat (map treeToList (toList (A n trees))))
    treeToList (Leaf arr)                                   =
      toList arr

--------------------------------------------------------------------------------
--          Folds
--------------------------------------------------------------------------------

export
foldl :  (b -> a -> b)
      -> b
      -> RRBVector a
      -> b
foldl f acc = go
  where
    foldlTree :  b
              -> Tree a
              -> b
    foldlTree acc' (Balanced (MkChildren {n} trees))            =
      assert_total (foldl foldlTree acc' (A n trees))
    foldlTree acc' (Unbalanced (MkRelaxedChildren {n} trees _)) =
      assert_total (foldl foldlTree acc' (A n trees))
    foldlTree acc' (Leaf arr)                                   =
      assert_total (foldl f acc' arr)
    go :  RRBVector a
       -> b
    go Empty           =
      acc
    go (Root _ _ tree) =
      assert_total (foldlTree acc tree)

export
foldr :  (a -> b -> b)
      -> b
      -> RRBVector a
      -> b
foldr f acc = go
  where
    foldrTree :  Tree a
              -> b
              -> b
    foldrTree (Balanced (MkChildren {n} trees))            acc' =
      assert_total (foldr foldrTree acc' (A n trees))
    foldrTree (Unbalanced (MkRelaxedChildren {n} trees _)) acc' =
      assert_total (foldr foldrTree acc' (A n trees))
    foldrTree (Leaf arr)                                   acc' =
      assert_total (foldr f acc' arr)
    go :  RRBVector a
       -> b
    go Empty           =
      acc
    go (Root _ _ tree) =
      assert_total (foldrTree tree acc)

--------------------------------------------------------------------------------
--          Query
--------------------------------------------------------------------------------

||| Is the vector empty? O(1)
|||
export
null :  RRBVector a
     -> Bool
null Empty = True
null _     = False

||| Return the size of a vector. O(1)
|||
export
length :  RRBVector a
       -> Nat
length Empty        = 0
length (Root s _ _) = s

--------------------------------------------------------------------------------
--          Indexing
--------------------------------------------------------------------------------

||| The element at the index or `Nothing` if the index is out of range. O(log n)
|||
export
lookup :  Nat
       -> RRBVector a
       -> Maybe a
lookup _ Empty               =
  Nothing
lookup i (Root size sh tree) =
  case i < size of
    False =>
      Nothing
    True =>
      Just (lookupTree i sh tree)
  where
    lookupTree :  Nat
               -> Shift
               -> Tree a
               -> a
    lookupTree i sh (Balanced (MkChildren {n} children))                           =
      let childidx : Nat
          childidx = radixIndex i sh
          0 childLT : LT childidx n
          childLT = believe_me ()
          child : Fin n
          child = natToFinLT childidx @{childLT}
        in assert_total (lookupTree i (down sh) (at children child))
    lookupTree i sh (Unbalanced (MkRelaxedChildren {n} {nonEmpty} children sizes)) =
      let MkRelaxedIndex child offset = relaxedRadixIndex {n} {nonEmpty} sizes i sh
        in assert_total (lookupTree offset (down sh) (at children child))
    lookupTree i _  (Leaf (A n elems))                                             =
      let leafidx  : Nat
          leafidx  = integerToNat ((natToInteger i) .&. natToInteger blockmask)
          0 leafLT : LT leafidx n
          leafLT   = believe_me ()
        in atNat elems leafidx @{leafLT}

||| A flipped version of lookup. O(log n)
|||
export
(!?) :  RRBVector a
     -> Nat
     -> Maybe a
(!?) = flip lookup

||| Update the element at the index with a new element.
|||
||| If the index is out of range, the original vector is returned. O(log n)
|||
export
update :  Nat
       -> a
       -> RRBVector a
       -> RRBVector a
update _ _ Empty                 =
  Empty
update i x v@(Root size sh tree) =
  case i < size of
    False =>
      v
    True =>
      Root size sh (updateTree i sh tree)
  where
    updateTree :  Nat
               -> Shift
               -> Tree a
               -> Tree a
    updateTree i sh (Balanced (MkChildren {n} {nonEmpty} {withinBlock} children))                =
      let childidx  : Nat
          childidx  = radixIndex i sh
          0 childLT : LT childidx n
          childLT   = believe_me ()
          child     : Fin n
          child     = natToFinLT childidx @{childLT}
          children' = updateAt child (updateTree i (down sh)) children
        in assert_total (Balanced (MkChildren {nonEmpty = nonEmpty} {withinBlock = withinBlock} children'))
    updateTree i sh (Unbalanced (MkRelaxedChildren {n} {nonEmpty} {withinBlock} children sizes)) =
      let MkRelaxedIndex child offset = relaxedRadixIndex {n} {nonEmpty} sizes i sh
          children'                   = updateAt child (updateTree offset (down sh)) children
        in assert_total (Unbalanced (MkRelaxedChildren {nonEmpty = nonEmpty} {withinBlock = withinBlock} children' sizes))
    updateTree i _  (Leaf (A n elems))                                                           =
      let leafidx  : Nat
          leafidx  = integerToNat ((natToInteger i) .&. natToInteger blockmask)
          0 leafLT : LT leafIdx n
          leafLT   = believe_me ()
          idx      : Fin n
          idx      = natToFinLT leafidx @{leafLT}
        in Leaf (A n (setAt idx x elems))

||| Adjust the element at the index by applying the function to it.
|||
||| If the index is out of range, the original vector is returned. O(log n)
|||
export
adjust :  Nat
       -> (a -> a)
       -> RRBVector a
       -> RRBVector a
adjust _ _ Empty                 =
  Empty
adjust i f v@(Root size sh tree) =
  case i < size of
    False =>
      v
    True  =>
      Root size sh (adjustTree i sh tree)
  where
    adjustTree :  Nat
               -> Shift
               -> Tree a
               -> Tree a
    adjustTree i sh (Balanced (MkChildren {n} {nonEmpty} {withinBlock} children))                =
      let childidx  : Nat
          childidx  = radixIndex i sh
          0 childLT : LT childidx n
          childLT   = believe_me ()
          child     : Fin n
          child     = natToFinLT childidx @{childLT}
          children' = updateAt child (adjustTree i (down sh)) children
        in assert_total (Balanced (MkChildren {nonEmpty = nonEmpty} {withinBlock = withinBlock} children'))
    adjustTree i sh (Unbalanced (MkRelaxedChildren {n} {nonEmpty} {withinBlock} children sizes)) =
      let MkRelaxedIndex child offset = relaxedRadixIndex {n} {nonEmpty} sizes i sh
          children'                   = updateAt child (adjustTree offset (down sh)) children
        in assert_total (Unbalanced (MkRelaxedChildren {nonEmpty = nonEmpty} {withinBlock = withinBlock} children' sizes))
    adjustTree i _  (Leaf (A n elems))                                                           =
      let leafidx  : Nat
          leafidx  = integerToNat ((natToInteger i) .&. natToInteger blockmask)
          0 leafLT : LT leafidx n
          leafLT   = believe_me ()
          idx      : Fin n
          idx      = natToFinLT leafidx @{leafLT}
        in Leaf (A n (updateAt idx f elems))

private
normalize :  RRBVector a
          -> RRBVector a
normalize (Root size sh (Balanced (MkChildren {n = 1} children)))            =
  assert_total (normalize (Root size (down sh) (at children FZ)))
normalize (Root size sh (Unbalanced (MkRelaxedChildren {n = 1} children _))) =
  assert_total (normalize (Root size (down sh) (at children FZ)))
normalize v =
  v

||| Retain the portion of a tree ending at logical index `i`.
|||
||| `i` is the index of the final element retained in the resulting tree.
|||
||| Internal child positions are derived from the RRB indexing rules and
||| represented with erased bounds proofs. No dynamic `Nat`-to-`Fin`
||| conversion is required.
|||
private
takeTree :  Nat
         -> Shift
         -> Tree a
         -> Tree a
takeTree i sh (Balanced (MkChildren {n} children))                           =
  let childidx  : Nat
      childidx  = radixIndex i sh
      0 childLT : LT childidx n
      childLT   = believe_me ()
      prefix'   : IArray (S childidx) (Tree a)
      prefix'   = force (take (S childidx) children @{childLT})
      prefix''  : IArray (S childidx) (Tree a)
      prefix''  = updateAt (lastFin {n = childidx}) (takeTree i (down sh)) prefix'
    in assert_total (Balanced (MkChildren {n = S childidx} {nonEmpty = LTESucc LTEZero} {withinBlock = believe_me ()} prefix''))
takeTree i sh (Unbalanced (MkRelaxedChildren {n} {nonEmpty} children sizes)) =
  let MkRelaxedIndex child subidx = relaxedRadixIndex {n} {nonEmpty} sizes i sh
      childidx    : Nat
      childidx    = finToNat child
      0 prefixLTE : LTE (S childidx) n
      prefixLTE   = believe_me ()
      prefix'     : IArray (S childidx) (Tree a)
      prefix'     = force (take (S childidx) children @{prefixLTE})
      prefix''    : IArray (S childidx) (Tree a)
      prefix''    = updateAt (lastFin {n = childidx}) (takeTree subidx (down sh)) prefix'
      bounded     : Children a
      bounded     = MkChildren {n = S childidx} {nonEmpty = LTESucc LTEZero} {withinBlock = believe_me ()} prefix''
    in assert_total (computeSizes sh bounded)
takeTree i _  (Leaf (A n elems))                                             =
  let leafidx    : Nat
      leafidx    = integerToNat ((natToInteger i) .&. natToInteger blockmask)
      count      : Nat
      count      = S leafidx
      0 countLTE : LTE count n
      countLTE   = believe_me ()
      elems'     : IArray count a
      elems'     = force (take count elems @{countLTE})
    in Leaf (A count elems')

||| Remove the first `n` logical elements from a tree.
|||
||| The selected child becomes the first child in the resulting node and is
||| recursively trimmed by the offset within that child.
|||
||| Since this function is called only when elements remain after the drop,
||| every resulting internal node is nonempty. Array positions therefore use
||| erased bounds evidence rather than dynamic `Nat`-to-`Fin` conversion.
|||
private
dropTree :  Nat
         -> Shift
         -> Tree a
         -> Tree a
dropTree i sh (Balanced (MkChildren {n} children))                           =
  let childidx            : Nat
      childidx            = radixIndex i sh
      remaining           : Nat
      remaining           = minus n childidx
      children'           : IArray remaining (Tree a)
      children'           = force (drop childidx children)
      0 remainingpositive : LT 0 remaining
      remainingpositive   = believe_me ()
      zero                : Fin remaining
      zero                = natToFinLT 0 @{remainingpositive}
      children''          : IArray remaining (Tree a)
      children''          = updateAt zero (dropTree i (down sh)) children'
      bounded             : Children a
      bounded             = MkChildren {n = remaining} {nonEmpty = remainingpositive} {withinBlock = believe_me ()} children''
    in assert_total (computeSizes sh bounded)
dropTree i sh (Unbalanced (MkRelaxedChildren {n} {nonEmpty} children sizes)) =
  let MkRelaxedIndex child subidx = relaxedRadixIndex {n} {nonEmpty} sizes i sh
      childidx                    : Nat
      childidx                    = finToNat child
      remaining                   : Nat
      remaining                   = minus n childidx
      children'                   : IArray remaining (Tree a)
      children'                   = force (drop childidx children)
      0 remainingpositive         : LT 0 remaining
      remainingpositive           = believe_me ()
      zero                        : Fin remaining
      zero                        = natToFinLT 0 @{remainingpositive}
      children''                  : IArray remaining (Tree a)
      children''                  = updateAt zero (dropTree subidx (down sh)) children'
      bounded                     : Children a
      bounded                     = MkChildren {n = remaining} {nonEmpty = remainingpositive} {withinBlock = believe_me ()} children''
    in assert_total (computeSizes sh bounded)
dropTree i _  (Leaf (A n elems))                                             =
  let offset    : Nat
      offset    = integerToNat ((natToInteger i) .&. natToInteger blockmask)
      remaining : Nat
      remaining = minus n offset
      elems'    : IArray remaining a
      elems'    = force (drop offset elems)
    in Leaf (A remaining elems')

||| The first i elements of the vector.
||| If the vector contains less than or equal to i elements, the whole vector is returned. O(log n)
|||
export
take :  Nat
     -> RRBVector a
     -> RRBVector a
take _ Empty                 =
  empty
take n v@(Root size sh tree) =
  case compare n 0 of
    LT =>
      empty
    EQ =>
      empty
    GT =>
      case compare n size of
        LT =>
          normalize $ Root n sh (takeTree (minus n 1) sh tree)
        EQ =>
          v
        GT =>
          v

||| The vector without the first i elements.
||| If the vector contains less than or equal to i elements, the empty vector is returned. O(log n)
|||
export
drop :  Nat
     -> RRBVector a
     -> RRBVector a
drop _ Empty                 =
  empty
drop n v@(Root size sh tree) =
  case compare n 0 of
    LT =>
      v
    EQ =>
      v
    GT =>
      case compare n size of
        LT =>
          normalize $ Root (minus size n) sh (dropTree n sh tree)
        EQ =>
          empty
        GT =>
          empty

||| Split the vector at the given index. O(log n)
|||
export
splitAt :  Nat
        -> RRBVector a
        -> (RRBVector a, RRBVector a)
splitAt _ Empty                 = (Empty, Empty)
splitAt n v@(Root size sh tree) =
  case compare n 0 of
    LT =>
      (empty, v)
    EQ =>
      (empty, v)
    GT =>
      case compare n size of
        LT =>
          let left  = normalize $ Root n sh (takeTree (minus n 1) sh tree)
              right = normalize $ Root (minus size n) sh (dropTree n sh tree)
            in (left, right)
        EQ =>
          (v, empty)
        GT =>
          (v, empty)

--------------------------------------------------------------------------------
--          Deconstruction
--------------------------------------------------------------------------------

||| The first element and the vector without the first element, or `Nothing` if the vector is empty. O(log n)
|||
export
viewl :  RRBVector a
      -> Maybe (a, RRBVector a)
viewl Empty             =
  Nothing
viewl v@(Root _ _ tree) =
  let tail = drop 1 v
    in Just ( headTree tree
            , tail
            )
  where
    headTree :  Tree a
             -> a
    headTree (Balanced (MkChildren {n = S k} children))            =
      assert_total (headTree (at children FZ))
    headTree (Unbalanced (MkRelaxedChildren {n = S k} children _)) =
      assert_total (headTree (at children FZ))
    headTree (Leaf (A Z _))                                        =
      assert_total (idris_crash "Data.RRBVector.viewl: empty leaf")
    headTree (Leaf (A (S k) elems))                                =
      at elems FZ

||| The vector without the last element and the last element, or `Nothing` if the vector is empty. O(log n)
|||
export
viewr :  RRBVector a
      -> Maybe (RRBVector a, a)
viewr Empty                =
  Nothing
viewr v@(Root size _ tree) =
  let init = take (minus size 1) v
    in Just ( init
            , lastTree tree
            )
  where
    lastTree :  Tree a
             -> a
    lastTree (Balanced (MkChildren {n = S k} children))            =
      assert_total (lastTree (at children lastFin))
    lastTree (Unbalanced (MkRelaxedChildren {n = S k} children _)) =
      assert_total (lastTree (at children lastFin))
    lastTree (Leaf (A Z _))                                        =
      assert_total (idris_crash "Data.RRBVector.viewr: empty leaf")
    lastTree (Leaf (A (S k) elems))                                =
      at elems lastFin

--------------------------------------------------------------------------------
--          Transformation
--------------------------------------------------------------------------------

||| Apply the function to every element. O(n)
|||
export
map :  (a -> b)
    -> RRBVector a
    -> RRBVector b
map _ Empty               =
  Empty
map f (Root size sh tree) =
  Root size sh (mapTree tree)
  where
    mapTree :  Tree a
            -> Tree b
    mapTree (Balanced (MkChildren {n} {nonEmpty} {withinBlock} children))                =
      assert_total (Balanced (MkChildren {n} {nonEmpty = nonEmpty} {withinBlock = withinBlock} (map mapTree children)))
    mapTree (Unbalanced (MkRelaxedChildren {n} {nonEmpty} {withinBlock} children sizes)) =
      assert_total (Unbalanced (MkRelaxedChildren {n} {nonEmpty = nonEmpty} {withinBlock = withinBlock} (map mapTree children) sizes))
    mapTree (Leaf arr)                                                                   =
      Leaf (map f arr)

||| Reverse the vector. O(n)
|||
export
reverse :  RRBVector a
        -> RRBVector a
reverse v =
  case compare (length v) 1 of
    LT =>
      v
    EQ =>
      v
    GT =>
      case fromList $ toList v of
        Nothing =>
          assert_total $ idris_crash "Data.RRBVector.reverse: can't convert to List1"
        Just v' =>
          fromList $ forget $ reverse v'

||| Take two vectors and return a vector of corresponding pairs.
||| If one input is longer, excess elements are discarded from the right end. O(min(n1,n2))
|||
export
zip :  RRBVector a
    -> RRBVector b
    -> RRBVector (a, b)
zip v1 v2 =
  case fromList $ toList v1 of
    Nothing  =>
      assert_total $ idris_crash "Data.RRBVector.zip: can't convert to List1"
    Just v1' =>
      case fromList $ toList v2 of
        Nothing  =>
          assert_total $ idris_crash "Data.RRBVector.zip: can't convert to List1"
        Just v2' =>
          fromList $ forget $ zip v1' v2'

--------------------------------------------------------------------------------
--          Concatenation
--------------------------------------------------------------------------------

||| Create a new single-child branch with shift `sh`.
|||
private
newBranch :  a
          -> Shift
          -> Tree a
newBranch x Z  =
  Leaf (singleton x)
newBranch x sh =
  assert_total (Balanced (MkChildren {n = 1} {nonEmpty = LTESucc LTEZero} {withinBlock = believe_me ()} (fill 1 (newBranch x (down sh)))))

||| Add an element to the left end of the vector. O(log n)
|||
export
(<|) :  a
     -> RRBVector a
     -> RRBVector a
x <| Empty             =
  singleton x
x <| Root size sh tree =
  case compare insertshift sh of
    LT =>
      Root (S size) sh (consTree sh tree)
    EQ =>
      Root (S size) sh (consTree sh tree)
    GT =>
      let children : IArray 2 (Tree a)
          children =
            array ( fromList
                      [ newBranch x sh
                      , tree
                      ]
                  )
          rootChildren : Children a
          rootChildren =
            MkChildren {n = 2} {nonEmpty = believe_me ()} {withinBlock = believe_me ()} children
        in Root (S size) insertshift (computeSizes insertshift rootChildren)
  where
    ||| Compute the shift at which the new branch must be inserted.
    |||
    computeShift :  Nat
                 -> Shift
                 -> Shift
                 -> Tree a
                 -> Shift
    computeShift sz sh min (Balanced _)                                             =
      let hishift  =
            let comp = mult (log2 (minus sz 1) `div` blockshift) blockshift
              in case compare comp 0 of
                   LT =>
                     0
                   EQ =>
                     0
                   GT =>
                     comp
          hi       = (natToInteger $ minus sz 1) `shiftR` hishift
          newshift = case compare hi (natToInteger blockmask) of
                       LT =>
                         hishift
                       EQ =>
                         plus hishift blockshift
                       GT =>
                         plus hishift blockshift
        in case compare newshift sh of
             LT =>
               newshift
             EQ =>
               newshift
             GT =>
               min
    computeShift _ sh min (Unbalanced (MkRelaxedChildren {n = S k} children sizes)) =
      let sz'     : Nat
          sz'     = at sizes FZ
          newtree : Tree a
          newtree = at children FZ
          newmin  : Shift
          newmin  = case compare (S k) blocksize of
                      LT =>
                        sh
                      EQ =>
                        min
                      GT =>
                        min
        in assert_total (computeShift sz' (down sh) newmin newtree)
    computeShift _ _ min (Leaf arr) =
      case compare arr.size blocksize of
        LT =>
          0
        EQ =>
          min
        GT =>
          min
    insertshift : Shift
    insertshift = computeShift size sh (up sh) tree
    consTree :  Shift
             -> Tree a
             -> Tree a
    consTree sh (Balanced (MkChildren {n = S k} {nonEmpty} {withinBlock} children))            =
      case compare sh insertshift of
        LT =>
          assert_total (computeSizes sh (MkChildren {n = S k} {nonEmpty = nonEmpty} {withinBlock = withinBlock} (updateAt FZ (consTree $ down sh) children)))
        EQ =>
          let children' = append (fill 1 (newBranch x $ down sh)) children
            in computeSizes sh (MkChildren {n = S (S k)} {nonEmpty = believe_me ()} {withinBlock = believe_me ()} children')
        GT =>
          assert_total (computeSizes sh (MkChildren {n = S k} {nonEmpty = nonEmpty} {withinBlock = withinBlock} (updateAt FZ (consTree $ down sh) children)))
    consTree sh (Unbalanced (MkRelaxedChildren {n = S k} {nonEmpty} {withinBlock} children _)) =
      case compare sh insertshift of
        LT =>
          assert_total (computeSizes sh (MkChildren {n = S k} {nonEmpty = nonEmpty} {withinBlock = withinBlock} (updateAt FZ (consTree $ down sh) children)))
        EQ =>
          let children' = append (fill 1 (newBranch x $ down sh)) children
            in computeSizes sh (MkChildren {n = S (S k)} {nonEmpty = believe_me ()} {withinBlock = believe_me ()} children')
        GT =>
          assert_total (computeSizes sh (MkChildren {n = S k} {nonEmpty = nonEmpty} {withinBlock = withinBlock} (updateAt FZ (consTree $ down sh) children)))
    consTree _ (Leaf arr)                                                                      =
      Leaf (A (S arr.size) (append (fill 1 x) arr.arr))

||| Add an element to the right end of the vector. O(log n)
|||
export
(|>) :  RRBVector a
     -> a
     -> RRBVector a
Empty |> x =
  singleton x
Root size sh tree |> x =
  case compare insertshift sh of
    LT =>
      Root (S size) sh (snocTree sh tree)
    EQ =>
      Root (S size) sh (snocTree sh tree)
    GT =>
      let children     : IArray 2 (Tree a)
          children     = array ( fromList
                                   [ tree
                                   , newBranch x sh
                                   ]
                               )
          rootChildren : Children a
          rootChildren = MkChildren {n = 2} {nonEmpty = believe_me ()} {withinBlock = believe_me ()} children
        in Root (S size) insertshift (computeSizes insertshift rootChildren)
  where
    ||| Compute the shift at which the new right-hand branch must be inserted.
    |||
    computeShift :  Nat
                 -> Shift
                 -> Shift
                 -> Tree a
                 -> Shift
    computeShift sz sh min (Balanced _)                                                  =
      let newshift = mult (countTrailingZeros sz `div` blockshift) blockshift
        in case compare newshift sh of
             LT =>
               newshift
             EQ =>
               newshift
             GT =>
               min
    computeShift _  sh min (Unbalanced (MkRelaxedChildren {n = 1} children sizes))       =
      let sz' : Nat
          sz' = lastAt sizes
          newtree : Tree a
          newtree = lastAt children
          newmin : Shift
          newmin = case compare 1 blocksize of
                     LT =>
                       sh
                     EQ =>
                       min
                     GT =>
                       min
        in assert_total (computeShift sz' (down sh) newmin newtree)
    computeShift _  sh min (Unbalanced (MkRelaxedChildren {n = S (S k)} children sizes)) =
      let totalsize   : Nat
          totalsize   = lastAt sizes
          previousidx : Fin (S (S k))
          previousidx = weaken (lastFin {n = k})
          previous    : Nat
          previous    = at sizes previousidx
          sz'         : Nat
          sz'         = minus totalsize previous
          newtree     : Tree a
          newtree     = lastAt children
          newmin      : Shift
          newmin      = case compare (S (S k)) blocksize of
                          LT =>
                            sh
                          EQ =>
                            min
                          GT =>
                            min
        in assert_total (computeShift sz' (down sh) newmin newtree)
    computeShift _  _  min (Leaf arr)                                                    =
      case compare arr.size blocksize of
        LT =>
          0
        EQ =>
          min
        GT =>
          min
    insertshift : Shift
    insertshift = computeShift size sh (up sh) tree
    snocTree :  Shift
             -> Tree a
             -> Tree a
    snocTree sh (Balanced (MkChildren {n = S k} {nonEmpty} {withinBlock} children))                =
      case compare sh insertshift of
        LT =>
          assert_total (Balanced (MkChildren {n = S k} {nonEmpty = nonEmpty} {withinBlock = withinBlock} (updateAt lastFin (snocTree $ down sh) children)))
        EQ =>
          let children' = append children (fill 1 (newBranch x (down sh)))
            in Balanced (MkChildren {n = plus (S k) 1} {nonEmpty = believe_me ()} {withinBlock = believe_me ()} children')
        GT =>
          assert_total (Balanced (MkChildren {n = S k} {nonEmpty = nonEmpty} {withinBlock = withinBlock} (updateAt lastFin (snocTree $ down sh) children)))
    snocTree sh (Unbalanced (MkRelaxedChildren {n = S k} {nonEmpty} {withinBlock} children sizes)) =
      case compare sh insertshift of
        LT =>
          let lastsize : Nat
              lastsize = plus (lastAt sizes) 1
            in assert_total (Unbalanced (MkRelaxedChildren {n = S k} {nonEmpty = nonEmpty} {withinBlock = withinBlock} (updateAt lastFin (snocTree $ down sh) children) (setAt lastFin lastsize sizes)))
        EQ =>
          let lastsize  : Nat
              lastsize  = plus (lastAt sizes) 1
              children' = append children (fill 1 (newBranch x (down sh)))
              sizes'    = append sizes (fill 1 lastsize)
            in Unbalanced (MkRelaxedChildren {n = plus (S k) 1} {nonEmpty = believe_me ()} {withinBlock = believe_me ()} children' sizes')
        GT =>
          let lastsize : Nat
              lastsize = plus (lastAt sizes) 1
            in assert_total (Unbalanced (MkRelaxedChildren {n = S k} {nonEmpty = nonEmpty} {withinBlock = withinBlock} (updateAt lastFin (snocTree $ down sh) children) (setAt lastFin lastsize sizes)))
    snocTree _  (Leaf arr)                                                                         =
      Leaf (A (plus arr.size 1) (append arr.arr (fill 1 x)))

||| Concatenates two vectors. O(log(max(n1,n2)))
|||
export
(><) :  RRBVector a
     -> RRBVector a
     -> RRBVector a
Empty                >< v                    = v
v                    >< Empty                = v
Root size1 sh1 tree1 >< Root size2 sh2 tree2 =
  let upmaxshift   = case compare sh1 sh2 of
                       LT =>
                         up sh2
                       EQ =>
                         up sh1
                       GT =>
                         up sh1
      newarr       = mergeTrees tree1 sh1 tree2 sh2
      rootchildren : Children a
      rootchildren = childrenFromArray newarr
    in normalize (Root (plus size1 size2) upmaxshift (computeSizes upmaxshift rootchildren))
  where
    ||| Remove and return the first child of a nonempty tree array.
    |||
    ||| Arrays passed here originate from internal tree nodes and are therefore
    ||| structurally nonempty.
    |||
    viewlArr :  Array (Tree a)
             -> (Tree a, Array (Tree a))
    viewlArr (A Z _)       =
      assert_total (idris_crash "Data.RRBVector.(><).viewlArr: empty internal array")
    viewlArr (A (S n) arr) =
      let tail : IArray (minus n 0) (Tree a)
          tail = force (drop 1 arr)
        in ( at arr FZ
           , A (minus n 0) tail
           )
    ||| Remove and return the final child of a nonempty tree array.
    |||
    ||| The final position is represented directly by `lastFin`, avoiding a
    ||| dynamic conversion of `size - 1`.
    |||
    viewrArr :  Array (Tree b)
             -> (Array (Tree b), Tree b)
    viewrArr (A Z _)       =
      assert_total (idris_crash "Data.RRBVector.(><).viewrArr: empty internal array")
    viewrArr (A (S n) arr) =
      let 0 initLTE : LTE n (S n)
          initLTE   = believe_me ()
          init      : IArray n (Tree b)
          init      = force (take n arr @{initLTE})
        in ( A n init
           , at arr (lastFin {n})
           )
    mergeRebalance' :  Shift
                    -> Array (Tree a)
                    -> Array (Tree a)
                    -> Array (Tree a)
                    -> (Tree a -> Array (Tree a))
                    -> (Array (Tree a) -> Tree a)
                    -> Array (Tree a)
    mergeRebalance' sh left center right extract construct =
      run1 $ \t =>
        let nodecounter    # t := ref1 Z t
            subtreecounter # t := ref1 Z t
            newnode        # t := ref1 Lin t
            newsubtree     # t := ref1 Lin t
            newroot        # t := ref1 Lin t
            ()             # t := mergeRebalanceSubtree' sh nodecounter subtreecounter newnode newsubtree newroot extract construct (toList left ++ toList center ++ toList right) t
            newnode'       # t := read1 newnode t
            ()             # t := casmod1 newsubtree (\y => y :< (construct $ A (SnocSize newnode')
                                                                                (snocConcat newnode'))
                                                     ) t                
            newsubtree'    # t := read1 newsubtree t
            ()             # t := casmod1 newroot (\y => y :< (computeSizes sh (childrenFromArray (fromList (cast {to=List (Tree a)} newsubtree'))))
                                                  ) t
            newroot'       # t := read1 newroot t
          in fromList (cast {to=List (Tree a)} newroot') # t
      where
        mergeRebalanceSubtreeNodeCounter :  Ref s Nat
                                         -> Ref s Nat
                                         -> Ref s (SnocList (Array (Tree a)))
                                         -> Ref s (SnocList (Tree a))
                                         -> (Array (Tree a) -> Tree a)
                                         -> F1' s
        mergeRebalanceSubtreeNodeCounter nodecounter subtreecounter newnode newsubtree construct t =
          let newnode' # t := read1 newnode t
              ()       # t := casmod1 newsubtree (\y => y :< (construct $ A (SnocSize newnode')
                                                                            (snocConcat newnode'))
                                                 ) t
              ()       # t := write1 newnode Lin t
              ()       # t := write1 nodecounter Z t
            in casmod1 subtreecounter (\y => y + 1) t
        mergeRebalanceRootSubtreeCounter :  Shift
                                         -> Ref s Nat
                                         -> Ref s (SnocList (Tree a))
                                         -> Ref s (SnocList (Tree a))
                                         -> F1' s
        mergeRebalanceRootSubtreeCounter sh subtreecounter newsubtree newroot t =
          let newsubtree' # t := read1 newsubtree t
              ()          # t := casmod1 newroot (\y => y :< (computeSizes sh (childrenFromArray (fromList (cast {to=List (Tree a)} newsubtree'))))
                                                 ) t
              ()          # t := write1 newsubtree Lin t
            in write1 subtreecounter Z t
        mergeRebalanceSubtree''' :  Shift
                                 -> Ref s Nat
                                 -> Ref s Nat
                                 -> Ref s (SnocList (Array (Tree a)))
                                 -> Ref s (SnocList (Tree a))
                                 -> Ref s (SnocList (Tree a))
                                 -> (Array (Tree a) -> Tree a)
                                 -> Tree a
                                 -> F1' s
        mergeRebalanceSubtree''' sh nodecounter subtreecounter newnode newsubtree newroot construct extractedsubtree t =
          let nodecounter'    # t := read1 nodecounter t
              ()              # t := when1 (nodecounter' == blocksize) (mergeRebalanceSubtreeNodeCounter nodecounter subtreecounter newnode newsubtree construct) t
              subtreecounter' # t := read1 subtreecounter t
              ()              # t := when1 (subtreecounter' == blocksize) (mergeRebalanceRootSubtreeCounter sh subtreecounter newsubtree newroot) t
              ()              # t := casmod1 newnode (\y => y :< (fill 1 extractedsubtree)
                                                     ) t
            in casmod1 nodecounter (\y => y + 1) t        
        mergeRebalanceSubtree'' :  Shift
                                -> Ref s Nat
                                -> Ref s Nat
                                -> Ref s (SnocList (Array (Tree a)))
                                -> Ref s (SnocList (Tree a))
                                -> Ref s (SnocList (Tree a))
                                -> (Tree a -> Array (Tree a))
                                -> (Array (Tree a) -> Tree a)
                                -> Tree a
                                -> F1' s
        mergeRebalanceSubtree'' sh nodecounter subtreecounter newnode newsubtree newroot extract construct subtree t =
          traverse1_ (mergeRebalanceSubtree''' sh nodecounter subtreecounter newnode newsubtree newroot construct) (extract subtree) t
        mergeRebalanceSubtree' :  Shift
                               -> Ref s Nat
                               -> Ref s Nat
                               -> Ref s (SnocList (Array (Tree a)))
                               -> Ref s (SnocList (Tree a))
                               -> Ref s (SnocList (Tree a))
                               -> (Tree a -> Array (Tree a))
                               -> (Array (Tree a) -> Tree a)
                               -> List (Tree a)
                               -> F1' s
        mergeRebalanceSubtree' sh nodecounter subtreecounter newnode newsubtree newroot extract construct leftcenterright t =
          traverse1_ (mergeRebalanceSubtree'' sh nodecounter subtreecounter newnode newsubtree newroot extract construct) leftcenterright t
    mergeRebalance'' :  Shift
                     -> Array (Tree a)
                     -> Array (Tree a)
                     -> Array (Tree a)
                     -> (Tree a -> Array a)
                     -> (Array a -> Tree a)
                     -> Array (Tree a)
    mergeRebalance'' sh left center right extract construct =
      run1 $ \t =>
        let nodecounter    # t := ref1 Z t
            subtreecounter # t := ref1 Z t
            newnode        # t := ref1 Lin t
            newsubtree     # t := ref1 Lin t
            newroot        # t := ref1 Lin t
            ()             # t := mergeRebalanceSubtree' sh nodecounter subtreecounter newnode newsubtree newroot extract construct (toList left ++ toList center ++ toList right) t
            newnode'       # t := read1 newnode t
            ()             # t := casmod1 newsubtree (\y => y :< (construct $ A (SnocSize newnode')
                                                                                (snocConcat newnode'))
                                                     ) t                
            newsubtree'    # t := read1 newsubtree t
            ()             # t := casmod1 newroot (\y => y :< (computeSizes sh (childrenFromArray (fromList (cast {to=List (Tree a)} newsubtree'))))
                                                  ) t
            newroot'       # t := read1 newroot t
          in fromList (cast {to=List (Tree a)} newroot') # t
      where
        mergeRebalanceSubtreeNodeCounter :  Ref s Nat
                                         -> Ref s Nat
                                         -> Ref s (SnocList (Array a))
                                         -> Ref s (SnocList (Tree a))
                                         -> (Array a -> Tree a)
                                         -> F1' s
        mergeRebalanceSubtreeNodeCounter nodecounter subtreecounter newnode newsubtree construct t =
          let newnode' # t := read1 newnode t
              ()       # t := casmod1 newsubtree (\y => y :< (construct $ A (SnocSize newnode')
                                                                            (snocConcat newnode'))
                                                 ) t
              ()       # t := write1 newnode Lin t
              ()       # t := write1 nodecounter Z t
            in casmod1 subtreecounter (\y => y + 1) t
        mergeRebalanceRootSubtreeCounter :  Shift
                                         -> Ref s Nat
                                         -> Ref s (SnocList (Tree a))
                                         -> Ref s (SnocList (Tree a))
                                         -> F1' s
        mergeRebalanceRootSubtreeCounter sh subtreecounter newsubtree newroot t =
          let newsubtree' # t := read1 newsubtree t
              ()          # t := casmod1 newroot (\y => y :< (computeSizes sh (childrenFromArray (fromList (cast {to=List (Tree a)} newsubtree'))))
                                                 ) t
              ()          # t := write1 newsubtree Lin t
            in write1 subtreecounter Z t
        mergeRebalanceSubtree''' :  Shift
                                 -> Ref s Nat
                                 -> Ref s Nat
                                 -> Ref s (SnocList (Array a))
                                 -> Ref s (SnocList (Tree a))
                                 -> Ref s (SnocList (Tree a))
                                 -> (Array a -> Tree a)
                                 -> a
                                 -> F1' s
        mergeRebalanceSubtree''' sh nodecounter subtreecounter newnode newsubtree newroot construct extractedsubtree t =
          let nodecounter'    # t := read1 nodecounter t
              ()              # t := when1 (nodecounter' == blocksize) (mergeRebalanceSubtreeNodeCounter nodecounter subtreecounter newnode newsubtree construct) t
              subtreecounter' # t := read1 subtreecounter t
              ()              # t := when1 (subtreecounter' == blocksize) (mergeRebalanceRootSubtreeCounter sh subtreecounter newsubtree newroot) t
              ()              # t := casmod1 newnode (\y => y :< (fill 1 extractedsubtree)
                                                     ) t
            in casmod1 nodecounter (\y => y + 1) t        
        mergeRebalanceSubtree'' :  Shift
                                -> Ref s Nat
                                -> Ref s Nat
                                -> Ref s (SnocList (Array a))
                                -> Ref s (SnocList (Tree a))
                                -> Ref s (SnocList (Tree a))
                                -> (Tree a -> Array a)
                                -> (Array a -> Tree a)
                                -> Tree a
                                -> F1' s
        mergeRebalanceSubtree'' sh nodecounter subtreecounter newnode newsubtree newroot extract construct subtree t =
          traverse1_ (mergeRebalanceSubtree''' sh nodecounter subtreecounter newnode newsubtree newroot construct) (extract subtree) t
        mergeRebalanceSubtree' :  Shift
                               -> Ref s Nat
                               -> Ref s Nat
                               -> Ref s (SnocList (Array a))
                               -> Ref s (SnocList (Tree a))
                               -> Ref s (SnocList (Tree a))
                               -> (Tree a -> Array a)
                               -> (Array a -> Tree a)
                               -> List (Tree a)
                               -> F1' s
        mergeRebalanceSubtree' sh nodecounter subtreecounter newnode newsubtree newroot extract construct leftcenterright t =
          traverse1_ (mergeRebalanceSubtree'' sh nodecounter subtreecounter newnode newsubtree newroot extract construct) leftcenterright t
    mergeRebalance :  Shift
                   -> Array (Tree a)
                   -> Array (Tree a)
                   -> Array (Tree a)
                   -> Array (Tree a)
    mergeRebalance sh left center right =
      case compare sh blockshift of
        LT =>
          assert_total (mergeRebalance' sh left center right treeToArray (\arr => computeSizes (down sh) (childrenFromArray arr)))
        EQ =>
          assert_total (mergeRebalance'' sh left center right (\(Leaf arr) => arr) Leaf)
        GT =>
          assert_total (mergeRebalance' sh left center right treeToArray (\arr => computeSizes (down sh) (childrenFromArray arr)))
    mergeTrees :  Tree a
               -> Nat
               -> Tree a
               -> Nat
               -> Array (Tree a)
    mergeTrees tree1@(Leaf arr1) _   tree2@(Leaf arr2) _   =
      case compare arr1.size blocksize of
        LT =>
          let arr' = A (plus arr1.size arr2.size) (append arr1.arr arr2.arr)
            in case compare arr'.size blocksize of
                 LT =>
                   singleton $ Leaf arr'
                 EQ =>
                   singleton $ Leaf arr'
                 GT =>
                   let (left, right) = (take blocksize arr',drop blocksize arr')
                       lefttree      = Leaf left
                       righttree     = Leaf right
                     in A 2 $ fromPairs 2 lefttree [(1,righttree)]
        EQ =>
          A 2 $ fromPairs 2 tree1 [(1,tree2)]
        GT =>
          let arr' = A (plus arr1.size arr2.size) (append arr1.arr arr2.arr)
            in case compare arr'.size blocksize of
                 LT =>
                   singleton $ Leaf arr'
                 EQ =>
                   singleton $ Leaf arr'
                 GT =>
                   let (left, right) = (take blocksize arr',drop blocksize arr')
                       lefttree      = Leaf left
                       righttree     = Leaf right
                     in A 2 $ fromPairs 2 lefttree [(1,righttree)]
    mergeTrees tree1             sh1 tree2             sh2 =
      case compare sh1 sh2 of
        LT =>
          let right                  = treeToArray tree2
              (righthead, righttail) = viewlArr right
              merged                 = assert_total $ mergeTrees tree1 sh1 righthead (down sh2)
            in mergeRebalance sh2 empty merged righttail
        GT =>
          let left                 = treeToArray tree1
              (leftinit, leftlast) = viewrArr left
              merged               = assert_total $ mergeTrees leftlast (down sh1) tree2 sh2
            in mergeRebalance sh1 leftinit merged empty
        EQ =>
          let left                   = treeToArray tree1
              right                  = treeToArray tree2
              (leftinit, leftlast)   = viewrArr left
              (righthead, righttail) = viewlArr right
              merged                 = assert_total $ mergeTrees leftlast (down sh1) righthead (down sh2)
            in mergeRebalance sh1 leftinit merged righttail

||| Insert an element at the given index, shifting the rest of the vector over.
||| If the index is negative, add the element to the left end of the vector.
||| If the index is bigger than or equal to the length of the vector, add the element to the right end of the vector. O(log n)
|||
export
insertAt :  Nat
         -> a
         -> RRBVector a
         -> RRBVector a
insertAt i x v =
  let (left, right) = splitAt i v
    in (left |> x) >< right

||| Delete the element at the given index.
||| If the index is out of range, return the original vector. O(log n)
|||
export
deleteAt :  Nat
         -> RRBVector a
         -> RRBVector a
deleteAt i v =
  let (left, right) = splitAt (plus i 1) v
    in take i left >< right

--------------------------------------------------------------------------------
--          Show Utilities (RRB-Vector)
--------------------------------------------------------------------------------

||| Show the full representation of the vector.
|||
export
showRRBVectorRep :  Show a
                 => Show (Tree a)
                 => Show (RRBVector a)
                 => RRBVector a
                 -> String
showRRBVectorRep Empty            =
  ""
showRRBVectorRep (Root size sh t) =
  "RRBVector "    ++
  "{ "            ++
  "Size = "       ++
  (show size)     ++
  ", Shift = "    ++
  (show sh)       ++
  ", Tree = "     ++
  (showTreeRep t) ++
  "}"

--------------------------------------------------------------------------------
--          Interfaces (RRBVector)
--------------------------------------------------------------------------------

export
Eq a => Eq (RRBVector a) where
  xs == ys = length xs == length ys && Data.RRBVector.toList xs == Data.RRBVector.toList ys

export
Ord a => Ord (RRBVector a) where
  compare xs ys = compare (Data.RRBVector.toList xs) (Data.RRBVector.toList ys)

export
Functor RRBVector where
  map f v = map f v

export
Foldable RRBVector where
  foldl f z           = Data.RRBVector.foldl f z
  foldr f z           = Data.RRBVector.foldr f z
  null                = null

export
Applicative RRBVector where
  pure      = singleton
  fs <*> xs = Data.RRBVector.foldl (\acc, f => acc >< map f xs) empty fs

export
Semigroup (RRBVector a) where
  (<+>) = (><)

export
Semigroup (RRBVector a) => Monoid (RRBVector a) where
  neutral = empty

export
Monad RRBVector where
  xs >>= f = Data.RRBVector.foldl (\acc, x => acc >< f x) empty xs
