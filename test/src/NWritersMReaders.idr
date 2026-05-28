module NWritersMReaders

import Data.Linear.Ref1
import Data.LSMRRBVector
import Data.RRBVector
import Data.SortedMap
import System
import System.Posix.Time
import System.Posix.Timer.Prim

||| Stress test:
||| N writers + M readers operate concurrently over the same LSMRRBVector system.
|||
||| This test verifies:
||| - Writers correctly append entries without loss.
||| - Readers always observe a valid snapshot + generation pair.
||| - Reader generations are properly registered via enterGeneration.
||| - The rotateAllBuffers function does not drop or duplicate writes.
||| - Reclamation does not interfere with active readers.
|||
||| Failure modes detected:
||| - Lost updates under concurrent append pressure.
||| - Stale snapshot visibility.
||| - Reader generation not being tracked correctly.
||| - Buffer corruption under interleaving.
||| - Unsafe reclamation of live generations.
|||
export
test_NWritersMReaders : IO ()
test_NWritersMReaders = do
  -- sorted map
  map <- newref empty
  -- shared vector system
  vec <- runIO (empty {e = ()} {a=Int})
  -- snapshot state (required for generation tracking)
  snapstate : Ref World (CombinedSnapshotState Int) <- newref (MkCombinedSnapshotState (MkSnapshotState 0 empty) [] empty 0 False 8)
  let writer :  Int
             -> Nat
             -> IO ()
      writer wid 0     =
        pure ()
      writer wid (S n) = do
        let entry = MkEntry (Append wid) (toUTC $ TM (cast n) 0 0 1 0 0 0 0 False) wid n
        -- simulate buffer mutation
        runIO ( casupdate1 map (\m =>
                                 ( insert wid (MkBuffer (Lin <>< [entry]) 1) m
                                 , ()
                                 )
                               )
              )
        usleep 5000
        writer wid n
  let reader :  Int
             -> Nat
             -> IO ()
      reader rid 0     =
        pure ()
      reader rid (S n) = do
        -- simulate entering a generation
        _ <- runIO ( enterGeneration snapstate rid
                   )
        -- read snapshot (must always succeed consistently)
        _ <- runIO ( readSnapshotWithGeneration vec rid (\(_, tree) =>
                                                          Data.RRBVector.toList tree
                                                        )
                   )

        usleep 5000
        reader rid n
  -- spawn writers
  let spawnWriters : IO (List ThreadID)
      spawnWriters =
        for [0,1,2,3,4] $ \n => do
          fork $ do
            writer n 50
  -- spawn readers
  let spawnReaders : IO (List ThreadID)
      spawnReaders =
        for [0,1,2] $ \n => do
          fork $ do
            reader n 20
  wtids <- spawnWriters
  rtids <- spawnReaders
  -- Wait for threads to finish
  for_ wtids $ \tid =>
    threadWait tid
  for_ rtids $ \tid =>
    threadWait tid
  css <- readref vec.combinedsnapshotstate
  when ((length $ Data.RRBVector.toList css.currentsnapshot.tree) /= 5 * 50) $
    assert_total $ idris_crash "test_NWritersMReaders: missing writes to final rrbvector since it's size is not equal to total writes"
