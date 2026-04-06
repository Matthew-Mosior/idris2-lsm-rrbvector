||| Log-Structured Merge RRB Vectors (LSMRRBVector)
module Data.LSMRRBVector

import public Data.LSMRRBVector.Internal

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
import Data.SnocList
import Data.Vect
import Data.Zippable
import Syntax.T1 as T1
import System.Concurrency

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
export
empty : F1 World (LSMRRBVector World a)
empty t =
  let buf1 # t := ref1 (MkWriteBuffers [] 0 Lin 0) t
      buf2 # t := ref1 (MkWriteBuffers [] 0 Lin 0) t
      buf3 # t := ref1 (MkWriteBuffers [] 0 Lin 0) t
      buf4 # t := ref1 (MkWriteBuffers [] 0 Lin 0) t
      bufarr   := fromList [buf1, buf2, buf3, buf4]
      mtx  # t := ioToF1 makeMutex t 
      rrb  # t := ref1 Empty t
    in MkLSMRRBVector bufarr rrb mtx # t

||| A vector with a single element. O(1)
export
singleton :  a
          -> F1 World (LSMRRBVector World a)
singleton x t =
  let buf1 # t := ref1 (MkWriteBuffers [] 0 Lin 0) t
      buf2 # t := ref1 (MkWriteBuffers [] 0 Lin 0) t
      buf3 # t := ref1 (MkWriteBuffers [] 0 Lin 0) t
      buf4 # t := ref1 (MkWriteBuffers [] 0 Lin 0) t
      bufarr   := fromList [buf1, buf2, buf3, buf4]
      mtx  # t := ioToF1 makeMutex t 
      rrb  # t := ref1 (Root 1 0 (Leaf $ A 1 $ fill 1 x)) t
    in MkLSMRRBVector bufarr rrb mtx # t
