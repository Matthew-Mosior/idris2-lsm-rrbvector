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
export
fromList :  List a
         -> Maybe (RRBVector a)
fromList []  =
  Just Empty
fromList [x] =
  Just (singleton x)
fromList xs  =
  let Just nodes'   = nodes Leaf xs
        | Nothing =>
            Nothing
      [tree]        = nodes'
        | xs' =>
            assert_smaller xs (iterateNodes blockshift xs')
      Just treesize = treeSize 0 tree
        | Nothing =>
            Nothing
    in Just (Root treesize 0 tree) -- tree is a single leaf
  where
    nodes :  (Array a -> Tree a)
          -> List a
          -> (Maybe (List (Tree a)))
    nodes f trees =
      let Just (trees', rest) = unsafeAlloc blocksize (go 0 blocksize f trees)
            | Nothing =>
                Nothing
          []                  = rest
            | rest' =>
                let Just nodes' = nodes f (assert_smaller trees rest')
                      | Nothing =>
                          Nothing
                  in Just (trees' :: nodes')
        in Just [trees']
      where
        go :  (cur,n : Nat)
           -> (Array a -> Tree a)
           -> List a
           -> WithMArray n a (Maybe (Tree a, List a))
        go cur n f []        r = T1.do
          res <- unsafeFreeze r
          pure (Just (f $ force $ take cur $ A n res,[]))
        go cur n f (x :: xs) r =
          case cur == n of
            True  => T1.do
              res <- unsafeFreeze r
              pure (Just (f $ A n res, x :: xs))
            False => T1.do
              let Just cur' = tryNatToFin cur
                    | Nothing =>
                        pure Nothing
              set r cur' x
              go (S cur) n f xs r
    nodes' :  (Array (Tree a) -> Tree a)
           -> List (Tree a)
           -> Maybe (List (Tree a))
    nodes' f trees =
      let Just (trees', rest) = unsafeAlloc blocksize (go 0 blocksize f trees)
            | Nothing =>
                Nothing
          []                  = rest
            | rest' =>
                let Just nodes'' = nodes' f (assert_smaller trees rest')
                      | Nothing =>
                          Nothing
                  in Just (trees' :: nodes'') 
        in Just [trees']
      where
        go :  (cur,n : Nat)
           -> (Array (Tree a) -> Tree a)
           -> List (Tree a)
           -> WithMArray n (Tree a) (Maybe (Tree a, List (Tree a)))
        go cur n f []        r = T1.do
          res <- unsafeFreeze r
          pure (Just (f $ force $ take cur $ A n res,[]))
        go cur n f (x :: xs) r =
          case cur == n of
            True  => T1.do
              res <- unsafeFreeze r
              pure (Just (f $ A n res, x :: xs))
            False => T1.do
              let Just cur' = tryNatToFin cur
                    | Nothing =>
                        pure Nothing
              set r cur' x
              go (S cur) n f xs r
    iterateNodes :  Nat
                 -> List (Tree a)
                 -> Maybe (RRBVector a)
    iterateNodes sh trees =
      let Just nodes''  = nodes' Balanced trees
            | Nothing =>
                Nothing
          [tree]        = nodes''
            | trees' =>
                iterateNodes (up sh) (assert_smaller trees trees')
          Just treesize = treeSize sh tree
            | Nothing =>
                Nothing
        in Just (Root treesize sh tree)

||| Creates a vector of length n with every element set to x. O(log n)
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
          let size' = integerToNat ((natToInteger $ minus n 1) .&. (natToInteger $ plus blockmask 1))
            in iterateNodes blockshift
                            (Leaf $ A blocksize $ fill blocksize x)
                            (Leaf $ A size' $ fill size' x)
  where
    iterateNodes :  Shift
                 -> Tree a
                 -> Tree a
                 -> RRBVector a
    iterateNodes sh full rest =
      let subtreesm1  = (natToInteger $ minus n 1) `shiftR` sh
          restsize    = integerToNat (subtreesm1 .&. (natToInteger blockmask))
          rest'       = Balanced $ A (plus restsize 1) $ append (fill restsize full) (fill 1 rest)
        in case compare subtreesm1 (natToInteger blocksize) of
             LT =>
               Root n sh rest'
             EQ =>
               let full' = Balanced (A blocksize $ fill blocksize full)
                 in iterateNodes (up sh) (assert_smaller full full') (assert_smaller rest rest')
             GT =>
               let full' = Balanced (A blocksize $ fill blocksize full)
                 in iterateNodes (up sh) (assert_smaller full full') (assert_smaller rest rest')

--------------------------------------------------------------------------------
--          Creating Lists from RRB-Vectors
--------------------------------------------------------------------------------

||| Convert a vector to a list. O(n)
|||
export
toList :  RRBVector a
       -> List a
toList Empty           = []
toList (Root _ _ tree) = treeToList tree
  where
    treeToList :  Tree a
               -> List a
    treeToList (Balanced trees)     = assert_total $ concat (map treeToList (toList trees))
    treeToList (Unbalanced trees _) = assert_total $ concat (map treeToList (toList trees))
    treeToList (Leaf arr)           = toList arr

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
    foldlTree acc' (Balanced arr)     = assert_total $ foldl foldlTree acc' arr
    foldlTree acc' (Unbalanced arr _) = assert_total $ foldl foldlTree acc' arr
    foldlTree acc' (Leaf arr)         = assert_total $ foldl f acc' arr
    go :  RRBVector a
       -> b
    go Empty           = acc
    go (Root _ _ tree) = assert_total $ foldlTree acc tree

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
    foldrTree (Balanced arr) acc'     = assert_total $ foldr foldrTree acc' arr
    foldrTree (Unbalanced arr _) acc' = assert_total $ foldr foldrTree acc' arr
    foldrTree (Leaf arr) acc'         = assert_total $ foldr f acc' arr
    go :  RRBVector a
       -> b
    go Empty           = acc
    go (Root _ _ tree) = assert_total $ foldrTree tree acc

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

||| The element at the index or Nothing if the index is out of range. O(log n)
|||
export
lookup :  Nat
       -> RRBVector a
       -> Maybe a
lookup _ Empty               = Nothing
lookup i (Root size sh tree) =
  case compare i 0 of
    LT =>
      Nothing -- index out of range
    GT =>
      case compare i size of
        EQ =>
          Nothing -- index out of range
        GT =>
          Nothing -- index out of range
        LT =>
          lookupTree i sh tree
    EQ =>
      case compare i size of
        EQ =>
          Nothing -- index out of range
        GT =>
          Nothing -- index out of range
        LT =>
          lookupTree i sh tree
  where
    lookupTree :  Nat
               -> Nat
               -> Tree a
               -> Maybe a
    lookupTree i sh (Balanced arr)         =
      let Just i' = tryNatToFin (radixIndex i sh)
            | Nothing =>
                Nothing
        in assert_total (lookupTree i (down sh) (at arr.arr i'))
    lookupTree i sh (Unbalanced arr sizes) =
      let Just (idx, subidx) = relaxedRadixIndex sizes i sh
            | Nothing =>
                Nothing
          Just idx'          = tryNatToFin idx
            | Nothing =>
                Nothing
        in assert_total (lookupTree subidx (down sh) (at arr.arr idx'))
    lookupTree i _ (Leaf arr)              =
      let i'       = integerToNat ((natToInteger i) .&. (natToInteger blockmask))
          Just i'' = tryNatToFin i'
            | Nothing =>
                Nothing
        in Just (at arr.arr i'')

||| A flipped version of lookup. O(log n)
|||
export
(!?) :  RRBVector a
     -> Nat
     -> Maybe a
(!?) = flip lookup

||| Update the element at the index with a new element.
||| If the index is out of range, the original vector is returned. O (log n)
|||
export
update :  Nat
       -> a
       -> RRBVector a
       -> Maybe (RRBVector a)
update _ _ Empty                 =
  Just Empty
update i x v@(Root size sh tree) =
  case compare i 0 of
    LT =>
      Just v -- index out of range
    GT =>
      case compare i size of
        EQ =>
          Just v -- index out of range
        GT =>
          Just v -- index out of range
        LT =>
          let Just updatedtree = updateTree i sh tree
                | Nothing =>
                    Nothing
            in Just (Root size sh updatedtree)
    EQ =>
      case compare i size of
        EQ =>
          Just v -- index out of range
        GT =>
          Just v -- index out of range
        LT =>
          let Just updatedtree = updateTree i sh tree
                | Nothing =>
                    Nothing
            in Just (Root size sh updatedtree)
  where
    updateTree :  Nat
               -> Nat
               -> Tree a
               -> Maybe (Tree a)
    updateTree i sh (Balanced arr)         =
      let Just i'          = tryNatToFin (radixIndex i sh)
            | Nothing =>
                Nothing
          Just updatedtree = assert_total $ updateTree i (down sh) (Balanced arr)
            | Nothing =>
                Nothing
        in Just (Balanced (A arr.size (setAt i' updatedtree arr.arr))) 
    updateTree i sh (Unbalanced arr sizes) =
      let Just (idx, subidx) = relaxedRadixIndex sizes i sh
            | Nothing =>
                Nothing
          Just idx'          = tryNatToFin idx
            | Nothing =>
                Nothing
          Just updatedtree   = assert_total $ updateTree subidx (down sh) (Unbalanced arr sizes)
            | Nothing =>
                Nothing
        in Just (Unbalanced (A arr.size (setAt idx' updatedtree arr.arr)) sizes)
    updateTree i _ (Leaf arr)              =
      let i'       = integerToNat ((natToInteger i) .&. (natToInteger blockmask))
          Just i'' = tryNatToFin i'
            | Nothing =>
                Nothing
        in Just (Leaf (A arr.size (setAt i'' x arr.arr)))

||| Adjust the element at the index by applying the function to it.
||| If the index is out of range, the original vector is returned. O(log n)
|||
export
adjust :  Nat
       -> (a -> a)
       -> RRBVector a
       -> Maybe (RRBVector a)
adjust _ _ Empty                 =
  Just Empty
adjust i f v@(Root size sh tree) =
  case compare i 0 of
    LT =>
      Just v -- index out of range
    GT =>
      case compare i size of
        EQ =>
          Just v -- index out of range
        GT =>
          Just v -- index out of range
        LT =>
          let Just adjustedtree = adjustTree i sh tree
                | Nothing =>
                    Nothing
            in Just (Root size sh adjustedtree)
    EQ =>
      case compare i size of
        EQ =>
          Just v -- index out of range
        GT =>
          Just v -- index out of range
        LT =>
          let Just adjustedtree = adjustTree i sh tree
                | Nothing =>
                    Nothing
            in Just (Root size sh adjustedtree)
  where
    adjustTree :  Nat
               -> Nat
               -> Tree a
               -> Maybe (Tree a)
    adjustTree i sh (Balanced arr)         =
      let Just i'      = tryNatToFin (radixIndex i sh)
            | Nothing =>
                Nothing
          Just adjustedtree = assert_total $ adjustTree i (down sh) (Balanced arr)
            | Nothing =>
                Nothing
        in Just (Balanced (A arr.size (setAt i' adjustedtree arr.arr)))
    adjustTree i sh (Unbalanced arr sizes) =
      let Just (idx, subidx) = relaxedRadixIndex sizes i sh
            | Nothing =>
                Nothing
          Just idx'          = tryNatToFin idx
            | Nothing =>
                Nothing
          Just adjustedtree  = assert_total $ adjustTree subidx (down sh) (Unbalanced arr sizes)
            | Nothing =>
                Nothing
        in Just (Unbalanced (A arr.size (setAt idx' adjustedtree arr.arr)) sizes)
    adjustTree i _ (Leaf arr)              =
      let i'       = integerToNat ((natToInteger i) .&. (natToInteger blockmask))
          Just i'' = tryNatToFin i'
            | Nothing =>
                Nothing
        in Just (Leaf (A arr.size (updateAt i'' f arr.arr)))

private
normalize :  RRBVector a
          -> Maybe (RRBVector a)
normalize v@(Root size sh (Balanced arr))     =
  case compare arr.size 1 of
    LT =>
      Just v
    EQ =>
      let Just i = tryNatToFin 0
            | Nothing =>
                Nothing
          Just normalized = assert_total $ normalize $ Root size (down sh) (at arr.arr i)
            | Nothing =>
                Nothing
        in Just normalized
    GT =>
      Just v
normalize v@(Root size sh (Unbalanced arr _)) =
  case compare arr.size 1 of
    LT =>
      Just v
    EQ =>
      let Just i = tryNatToFin 0
            | Nothing =>
                Nothing
          Just normalized = assert_total $ normalize $ Root size (down sh) (at arr.arr i)
            | Nothing =>
                Nothing
        in Just normalized
    GT =>
      Just v
normalize v                                   =
  Just v

||| The initial i is n - 1 (the index of the last element in the new tree).
|||
private
takeTree :  Nat
         -> Shift
         -> Tree a
         -> Maybe (Tree a)
takeTree i sh (Balanced arr) with (radixIndex i sh) | ((plus (radixIndex i sh) 1) <= arr.size) proof eq
  _ | i' | True  =
    let Just i''       = tryNatToFin i'
          | Nothing =>
              Nothing
        newarr         = force $ take (plus (radixIndex i sh) 1) arr.arr @{lteOpReflectsLTE _ _ eq}
        Just takentree = assert_total $ takeTree i (down sh) (Balanced (A (plus (radixIndex i sh) 1) newarr))
          | Nothing =>
              Nothing
      in assert_total $ Just (Balanced (A (plus (radixIndex i sh) 1) (setAt i'' takentree newarr)))
  _ | _  | False =
    Nothing
takeTree i sh (Unbalanced arr sizes) with (relaxedRadixIndex sizes i sh)
  _ | Nothing =
    Nothing
  _ | Just (idx, subidx) with ((plus idx 1) <= arr.size) proof eq
    _ | True =
      let Just idx'      = tryNatToFin idx
            | Nothing =>
                Nothing
          newarr         = force $ take (plus idx 1) arr.arr @{lteOpReflectsLTE _ _ eq}
          Just takentree = assert_total $ takeTree subidx (down sh) (Unbalanced (A (plus idx 1) newarr) sizes)
            | Nothing =>
                Nothing
        in assert_total $ computeSizes sh (A (plus idx 1) (setAt idx' takentree newarr))
    _ | False =
         Nothing 
takeTree i _ (Leaf arr) with (integerToNat (((natToInteger i) .&. (natToInteger blockmask)) + 1) <= arr.size) proof eq
  _ | True  =
    let newarr = force $ take (integerToNat (((natToInteger i) .&. (natToInteger blockmask)) + 1)) arr.arr @{lteOpReflectsLTE _ _ eq}
      in Just (Leaf (A (integerToNat (((natToInteger i) .&. (natToInteger blockmask)) + 1)) newarr))
  _ | False =
    Nothing

private
dropTree :  Nat
         -> Shift
         -> Tree a
         -> Maybe (Tree a)
dropTree n sh (Balanced arr)         =
  let Just zero        = tryNatToFin 0
        | Nothing =>
            Nothing
      newarr           = force $ drop (radixIndex n sh) arr.arr
      Just droppedtree = assert_total $ dropTree n (down sh) (Balanced (A (minus arr.size (radixIndex n sh)) newarr))
        | Nothing =>
            Nothing
    in assert_total $ computeSizes sh (A (minus arr.size (radixIndex n sh)) (setAt zero droppedtree newarr))
dropTree n sh (Unbalanced arr sizes) with (relaxedRadixIndex sizes n sh)
  _ | Nothing =
    Nothing
  _ | Just (idx, subidx) with (minus arr.size idx <= arr.size)
    _ | True = 
      let Just zero          = tryNatToFin 0
            | Nothing =>
                Nothing
          newarr             = force $ drop idx arr.arr
          Just droppedtree   = assert_total $ dropTree subidx (down sh) (Unbalanced (A (minus arr.size idx) newarr) sizes)
            | Nothing =>
                Nothing
        in assert_total $ computeSizes sh (A (minus arr.size idx) (setAt zero droppedtree newarr))
    _ | False =
      Nothing
dropTree n _  (Leaf arr)             =
  let n      = integerToNat ((natToInteger n) .&. (natToInteger blockmask))
      newarr = force $ drop n arr.arr
    in Just (Leaf (A (minus arr.size n) newarr))

||| The first i elements of the vector.
||| If the vector contains less than or equal to i elements, the whole vector is returned. O(log n)
|||
export
take :  Nat
     -> RRBVector a
     -> Maybe (RRBVector a)
take _ Empty                 =
  Just Empty
take n v@(Root size sh tree) =
  case compare n 0 of
    LT =>
      Just empty
    EQ =>
      Just empty
    GT =>
      case compare n size of
        LT =>
          let Just takentree = takeTree (minus n 1) sh tree
                | Nothing =>
                    Nothing
            in normalize $ Root n sh takentree
        EQ =>
          Just v
        GT =>
          Just v

||| The vector without the first i elements.
||| If the vector contains less than or equal to i elements, the empty vector is returned. O(log n)
|||
export
drop :  Nat
     -> RRBVector a
     -> Maybe (RRBVector a)
drop _ Empty                 =
  Just Empty
drop n v@(Root size sh tree) =
  case compare n 0 of
    LT =>
      Just v
    EQ =>
      Just v
    GT =>
      case compare n size of
        LT =>
          let Just droppedtree = dropTree n sh tree
                | Nothing =>
                    Nothing
            in normalize $ Root (minus size n) sh droppedtree
        EQ =>
          Just empty
        GT =>
          Just empty

||| Split the vector at the given index. O(log n)
|||
export
splitAt :  Nat
        -> RRBVector a
        -> Maybe (RRBVector a, RRBVector a)
splitAt _ Empty                 =
  Just (Empty, Empty)
splitAt n v@(Root size sh tree) =
  case compare n 0 of
    LT =>
      Just (empty, v)
    EQ =>
      Just (empty, v)
    GT =>
      case compare n size of
        LT =>
          let Just takentree   = takeTree (minus n 1) sh tree
                | Nothing =>
                    Nothing
              Just left        = normalize $ Root n sh takentree
                | Nothing =>
                    Nothing
              Just droppedtree = dropTree n sh tree
                | Nothing =>
                    Nothing
              Just right       = normalize $ Root (minus size n) sh droppedtree
                | Nothing =>
                    Nothing
            in Just (left, right)
        EQ =>
          Just (v, empty)
        GT =>
          Just (v, empty)

--------------------------------------------------------------------------------
--          Deconstruction
--------------------------------------------------------------------------------

||| The first element and the vector without the first element, or 'Nothing' if the vector is empty. O(log n)
|||
export
viewl :  RRBVector a
      -> Maybe (a, RRBVector a)
viewl Empty             =
  Nothing
viewl v@(Root _ _ tree) =
  let Just tail = drop 1 v
        | Nothing =>
            Nothing
      Just headedtree = headTree tree
        | Nothing =>
            Nothing
    in Just (headedtree, tail)
  where
    headTree :  Tree a
             -> Maybe a
    headTree (Balanced arr)     =
      let Just zero  = tryNatToFin 0
            | Nothing =>
                Nothing
        in assert_total $ headTree (at arr.arr zero)
    headTree (Unbalanced arr _) =
      let Just zero = tryNatToFin 0
            | Nothing =>
                Nothing
        in assert_total $ headTree (at arr.arr zero)
    headTree (Leaf arr)         =
      let Just zero = tryNatToFin 0
            | Nothing =>
                Nothing
        in Just (at arr.arr zero)

||| The vector without the last element and the last element, or 'Nothing' if the vector is empty. O(log n)
|||
export
viewr :  RRBVector a
      -> Maybe (RRBVector a, a)
viewr Empty                =
  Nothing
viewr v@(Root size _ tree) =
  let Just init = take (minus size 1) v
        | Nothing =>
            Nothing
      Just lastedtree = lastTree tree
        | Nothing =>
            Nothing
    in Just (init, lastedtree)
  where
    lastTree :  Tree a
             -> Maybe a
    lastTree (Balanced arr)     =
      let Just last = tryNatToFin (minus size 1)
            | Nothing =>
                Nothing
        in assert_total $ lastTree (at arr.arr last)
    lastTree (Unbalanced arr _) =
      let Just last = tryNatToFin (minus size 1)
            | Nothing =>
                Nothing
        in assert_total $ lastTree (at arr.arr last)
    lastTree (Leaf arr)         =
      let Just last = tryNatToFin (minus size 1)
            | Nothing =>
                Nothing
        in Just (at arr.arr last)

--------------------------------------------------------------------------------
--          Transformation
--------------------------------------------------------------------------------

||| Apply the function to every element. O(n)
|||
export
map :  (a -> b)
    -> RRBVector a
    -> RRBVector b
map _ Empty               = Empty
map f (Root size sh tree) = Root size sh (mapTree tree)
  where
    mapTree : Tree a -> Tree b
    mapTree (Balanced arr)         =
      assert_total $ Balanced (map mapTree arr)
    mapTree (Unbalanced arr sizes) =
      assert_total $ Unbalanced (map mapTree arr) sizes
    mapTree (Leaf arr)             =
      Leaf (map f arr)

||| Reverse the vector. O(n)
|||
export
reverse :  RRBVector a
        -> Maybe (RRBVector a)
reverse v =
  case compare (length v) 1 of
    LT =>
      Just v
    EQ =>
      Just v
    GT =>
      let Just v'  = Data.List1.fromList $ toList v
            | Nothing =>
                Nothing
          v''      = Data.List1.reverse v'
        in fromList $ forget v''

||| Take two vectors and return a vector of corresponding pairs.
||| If one input is longer, excess elements are discarded from the right end. O(min(n1,n2))
|||
export
zip :  RRBVector a
    -> RRBVector b
    -> Maybe (RRBVector (a, b))
zip v1 v2 =
  let Just v1' = Data.List1.fromList $ toList v1
        | Nothing =>
            Nothing
      Just v2' = Data.List1.fromList $ toList v2
        | Nothing =>
            Nothing
    in fromList $ forget $ zip v1' v2'

--------------------------------------------------------------------------------
--          Concatenation
--------------------------------------------------------------------------------

||| Create a new tree with shift sh.
|||
private
newBranch :  a
          -> Shift
          -> Tree a
newBranch x 0  = Leaf (singleton x)
newBranch x sh = assert_total $ Balanced (singleton $ newBranch x (down sh))

||| Add an element to the left end of the vector. O(log n)
|||
export
(<|) :  a
     -> RRBVector a
     -> Maybe (RRBVector a)
x <| Empty             =
  Just (singleton x)
x <| Root size sh tree =
  let Just insertshift' = insertshift
        | Nothing =>
            Nothing
    in case compare insertshift' sh of
         LT =>
           let Just consedtree = assert_total $ consTree sh tree
                 | Nothing =>
                     Nothing
             in Just (Root (plus size 1) sh consedtree)
         EQ =>
           let Just consedtree = assert_total $ consTree sh tree
                 | Nothing =>
                     Nothing
             in Just (Root (plus size 1) sh consedtree)
         GT =>
           let new               = A 2 $ array $ fromList [(newBranch x sh), tree]
               Just computesizes = computeSizes insertshift' new
                 | Nothing =>
                     Nothing
             in Just (Root (plus size 1) insertshift' computesizes)
  where
    -- compute the shift at which the new branch needs to be inserted (0 means there is space in the leaf)
    -- the size is computed for efficient calculation of the shift in a balanced subtree
    computeShift :  Nat
                 -> Nat
                 -> Nat
                 -> Tree a
                 -> Maybe Nat
    computeShift sz sh min (Balanced _)          =
      -- @sz - 1@ is the index of the last element
      let Just log2' = log2 ((minus sz 1) `div` blockshift)
            | Nothing =>
                Nothing
          hishift    = let comp = mult log2' blockshift  -- the shift of the root when normalizing
                         in case compare comp 0 of
                              LT =>
                                0
                              EQ =>
                                0
                              GT =>
                                comp
          hi       = (natToInteger $ minus sz 1) `shiftR` hishift -- the length of the root node when normalizing minus 1
          newshift = case compare hi (natToInteger blockmask) of
                       LT =>
                         hishift
                       EQ =>
                         plus hishift blockshift
                       GT =>
                         plus hishift blockshift
        in case compare newshift sh of
             LT =>
               Just newshift
             EQ =>
               Just newshift
             GT =>
               Just min
    computeShift _ sh min (Unbalanced arr sizes) =
      let sz'           = do let Just zero = tryNatToFin 0
                                   | Nothing =>
                                       Nothing
                             Just (at sizes.arr zero)
          Just sz''     = sz'
            | Nothing =>
                Nothing
          newtree       = do let Just zero = tryNatToFin 0
                                   | Nothing =>
                                       Nothing
                             Just (at arr.arr zero)
          Just newtree' = newtree
            | Nothing =>
                Nothing
          newmin        = case compare arr.size blocksize of
                            LT =>
                              sh
                            EQ =>
                              min
                            GT =>
                              min
        in assert_total $ computeShift sz'' (down sh) newmin newtree'
    computeShift _ _ min (Leaf arr)              =
      case compare arr.size blocksize of
        LT =>
          Just 0
        EQ =>
          Just min
        GT =>
          Just min
    insertshift : Maybe Nat
    insertshift = computeShift size sh (up sh) tree
    consTree :  Nat
             -> Tree a
             -> Maybe (Tree a)
    consTree sh (Balanced arr)         =
      let Just insertshift' = insertshift
            | Nothing =>
                Nothing
        in case compare sh insertshift' of
             LT =>
               let Just zero       = tryNatToFin 0
                     | Nothing =>
                         Nothing
                   Just consedtree = assert_total $ consTree (down sh) (Balanced arr)
                     | Nothing =>
                         Nothing
                 in assert_total $ computeSizes sh (A arr.size $ setAt zero consedtree arr.arr)
             EQ =>
               computeSizes sh (A (S arr.size) (append (fill 1 (newBranch x (down sh))) arr.arr))
             GT =>
               let Just zero       = tryNatToFin 0
                     | Nothing =>
                         Nothing
                   Just consedtree = assert_total $ consTree (down sh) (Balanced arr)
                     | Nothing =>
                         Nothing
                 in assert_total $ computeSizes sh (A arr.size $ setAt zero consedtree arr.arr)
    consTree sh (Unbalanced arr sizes) =
      let Just insertshift' = insertshift
            | Nothing =>
                Nothing
        in case compare sh insertshift' of
             LT =>
               let Just zero       = tryNatToFin 0
                     | Nothing =>
                         Nothing
                   Just consedtree = assert_total $ consTree (down sh) (Unbalanced arr sizes)
                     | Nothing =>
                         Nothing
                 in assert_total $ computeSizes sh (A arr.size $ setAt zero consedtree arr.arr)
             EQ =>
               computeSizes sh (A (S arr.size) (append (fill 1 (newBranch x (down sh))) arr.arr))
             GT =>
               let Just zero       = tryNatToFin 0
                     | Nothing =>
                         Nothing
                   Just consedtree = assert_total $ consTree (down sh) (Unbalanced arr sizes)
                     | Nothing =>
                         Nothing
                 in assert_total $ computeSizes sh (A arr.size $ setAt zero consedtree arr.arr)
    consTree _ (Leaf arr)              =
      Just (Leaf (A (S arr.size) (append (fill 1 x) arr.arr)))

||| Add an element to the right end of the vector. O(log n)
|||
export
(|>) :  RRBVector a
     -> a
     -> RRBVector a
Empty             |> x = singleton x
Root size sh tree |> x =
  case compare insertshift sh of
    LT =>
      Root (plus size 1) sh (snocTree sh tree)
    EQ =>
      Root (plus size 1) sh (snocTree sh tree)
    GT =>
      let new = A 2 $ array $ fromList [tree,(newBranch x sh)]
        in Root (plus size 1) insertshift (computeSizes insertshift new)
  where
    -- compute the shift at which the new branch needs to be inserted (0 means there is space in the leaf)
    -- the size is computed for efficient calculation of the shift in a balanced subtree
    computeShift :  Nat
                 -> Nat
                 -> Nat
                 -> Tree a
                 -> Nat
    computeShift sz sh min (Balanced _)          =
      -- @sz - 1@ is the index of the last element
      let newshift = mult (countTrailingZeros sz `div` blockshift) blockshift
        in case compare newshift sh of
             LT =>
               newshift
             EQ =>
               newshift
             GT =>
               min
    computeShift _ sh min (Unbalanced arr sizes) =
      let lastidx = minus arr.size 1
          sz'     = case tryNatToFin lastidx of
                      Nothing       =>
                        assert_total $ idris_crash "Data.RRBVector.(|>).computeShift.Unbalanced: can't convert Nat to Fin"
                      Just lastidx' =>
                        case tryNatToFin $ minus lastidx 1 of
                          Nothing        =>
                            assert_total $ idris_crash "Data.RRBVector.(|>).computeShift.Unbalanced: can't convert Nat to Fin"
                          Just lastidx'' =>
                            minus (at sizes.arr lastidx') (at sizes.arr lastidx'')
          newtree = case tryNatToFin lastidx of
                      Nothing       =>
                        assert_total $ idris_crash "Data.RRBVector.(|>).computeShift.Unbalanced: can't convert Nat to Fin"
                      Just lastidx' =>
                        at arr.arr lastidx'
          newmin  = case compare arr.size blocksize of
                      LT =>
                        sh
                      EQ =>
                        min
                      GT =>
                        min
        in assert_total $ computeShift sz' (down sh) newmin newtree
    computeShift _ _ min (Leaf arr)              =
      case compare arr.size blocksize of
        LT =>
          0
        EQ =>
          min
        GT =>
          min
    insertshift : Nat
    insertshift = computeShift size sh (up sh) tree
    snocTree :  Nat
             -> Tree a
             -> Tree a
    snocTree sh (Balanced arr) =
      case compare sh insertshift of
        LT =>
          case tryNatToFin $ minus arr.size 1 of
            Nothing   =>
              assert_total $ idris_crash "Data.RRBVector.(|>).snocTree.Balanced: can't convert Nat to Fin"
            Just lastidx =>
              assert_total $ Balanced (A arr.size $ updateAt lastidx (snocTree (down sh)) arr.arr)
        EQ =>
          Balanced (A (plus arr.size 1) (append arr.arr (fill 1 (newBranch x (down sh))))) -- the current subtree is fully balanced
        GT =>
          case tryNatToFin $ minus arr.size 1 of
            Nothing   =>
              assert_total $ idris_crash "Data.RRBVector.(|>).snocTree.Balanced: can't convert Nat to Fin"
            Just lastidx =>
              assert_total $ Balanced (A arr.size $ updateAt lastidx (snocTree (down sh)) arr.arr)
    snocTree sh (Unbalanced arr sizes) =
      case compare sh insertshift of
        LT =>
          case tryNatToFin $ minus arr.size 1 of
            Nothing       =>
              assert_total $ idris_crash "Data.RRBVector.(|>).snocTree.Unbalanced: can't convert Nat to Fin"
            Just lastidxa =>
              case tryNatToFin $ minus sizes.size 1 of
                Nothing       =>
                  assert_total $ idris_crash "Data.RRBVector.(|>).snocTree.Unbalanced: can't convert Nat to Fin"
                Just lastidxs =>
                  let lastsize = plus (at sizes.arr lastidxs) 1
                    in assert_total $ Unbalanced (A arr.size (updateAt lastidxa (snocTree (down sh)) arr.arr))
                                                 (A sizes.size (setAt lastidxs lastsize sizes.arr))
        EQ =>
          case tryNatToFin $ minus sizes.size 1 of
            Nothing      =>
              assert_total $ idris_crash "Data.RRBVector.(|>).snocTree.Unbalanced: can't convert Nat to Fin"
            Just lastidx =>
              let lastsize = plus (at sizes.arr lastidx) 1
                in assert_total $ Unbalanced (A (plus arr.size 1) (append arr.arr (fill 1 (newBranch x (down sh)))))
                                             (A (plus sizes.size 1) (append sizes.arr (fill 1 lastsize)))
        GT =>
          case tryNatToFin $ minus arr.size 1 of
            Nothing       =>
              assert_total $ idris_crash "Data.RRBVector.(|>).snocTree.Unbalanced: can't convert Nat to Fin"
            Just lastidxa =>
              case tryNatToFin $ minus sizes.size 1 of
                Nothing       =>
                  assert_total $ idris_crash "Data.RRBVector.(|>).snocTree.Unbalanced: can't convert Nat to Fin"
                Just lastidxs =>
                  let lastsize = plus (at sizes.arr lastidxs) 1
                    in assert_total $ Unbalanced (A arr.size (updateAt lastidxa (snocTree (down sh)) arr.arr))
                                                 (A sizes.size (setAt lastidxs lastsize sizes.arr))
    snocTree _ (Leaf arr) = Leaf (A (plus arr.size 1) (append arr.arr (fill 1 x)))

||| Concatenates two vectors. O(log(max(n1,n2)))
|||
export
(><) :  RRBVector a
     -> RRBVector a
     -> RRBVector a
Empty                >< v                    = v
v                    >< Empty                = v
Root size1 sh1 tree1 >< Root size2 sh2 tree2 =
  let upmaxshift = case compare sh1 sh2 of
                     LT =>
                       up sh2
                     EQ =>
                       up sh1
                     GT =>
                       up sh1
      newarr     = mergeTrees tree1 sh1 tree2 sh2
    in normalize $ Root (plus size1 size2) upmaxshift (computeSizes upmaxshift newarr)
  where
    viewlArr : Array (Tree a) -> (Tree a, Array (Tree a))
    viewlArr arr =
      case tryNatToFin 0 of
        Nothing   =>
          assert_total $ idris_crash "Data.RRBVector.(><).viewlArr: can't convert Nat to Fin"
        Just zero =>
          (at arr.arr zero, drop 1 arr)
    viewrArr : Array (Tree b) -> (Array (Tree b), Tree b)
    viewrArr arr =
      case tryNatToFin $ minus arr.size 1 of
        Nothing   =>
          assert_total $ idris_crash "Data.RRBVector.(><).viewrArr: can't convert Nat to Fin"
        Just last =>
          (take (minus arr.size 1) arr, at arr.arr last)
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
            ()             # t := casmod1 newroot (\y => y :< (computeSizes sh (fromList (cast {to=List (Tree a)} newsubtree')))
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
              ()          # t := casmod1 newroot (\y => y :< (computeSizes sh (fromList (cast {to=List (Tree a)} newsubtree')))
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
            ()             # t := casmod1 newroot (\y => y :< (computeSizes sh (fromList (cast {to=List (Tree a)} newsubtree')))
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
              ()          # t := casmod1 newroot (\y => y :< (computeSizes sh (fromList (cast {to=List (Tree a)} newsubtree')))
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
          assert_total $ mergeRebalance' sh left center right treeToArray (computeSizes (down sh))
        EQ =>
          assert_total $ mergeRebalance'' sh left center right (\(Leaf arr) => arr) Leaf
        GT =>
          assert_total $ mergeRebalance' sh left center right treeToArray (computeSizes (down sh))
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
