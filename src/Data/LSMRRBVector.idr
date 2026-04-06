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
import Data.SortedMap
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
  let bufmap # t := ref1 Nothing t
      bufmtx # t := ioToF1 makeMutex t 
      rrb    # t := ref1 Empty t
      rrbmtx # t := ioToF1 makeMutex t 
    in MkLSMRRBVector (bufmtx, bufmap) (rrbmtx, rrb) # t

||| A vector with a single element. O(1)
export
singleton :  a
          -> F1 World (LSMRRBVector World a)
singleton x t =
  let bufmap # t := ref1 Nothing t
      bufmtx # t := ioToF1 makeMutex t 
      rrb    # t := ref1 (Root 1 0 (Leaf $ A 1 $ fill 1 x)) t
      rrbmtx # t := ioToF1 makeMutex t 
    in MkLSMRRBVector (bufmtx, bufmap) (rrbmtx, rrb) # t
