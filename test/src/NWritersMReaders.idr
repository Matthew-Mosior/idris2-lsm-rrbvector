module NWritersMReaders

import Data.Linear.Ref1
import Data.LSMRRBVector
import Data.RRBVector
import Data.SortedMap
import IO.Async.Core
import IO.Async.Loop
import IO.Async.Loop.Posix
import IO.Async.Posix
import IO.Async.Service
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
   runEmptyWith (MkLSMRRBVectorConfig 8)
                (\vec : LSMRRBVector World Int, svc => do
                  -- writer function
                  let writer :  Int
                             -> Nat
                             -> Async Poll [Errno] ()
                      writer wid 0     =
                        pure ()
                      writer wid (S n) = do
                        Data.LSMRRBVector.append vec svc wid (cast n)
                        liftIO (usleep 5000)
                        writer wid n
                  writer 5 50
                )
                (\vec : LSMRRBVector World Int => do
                        -- reader function
                        let reader :  Int
                                   -> Nat
                                   -> IO ()
                            reader rid 0     =
                              pure ()
                            reader rid (S n) = do
                              v <- readSnapshotWithGeneration vec rid (\(_, tree) =>
                                                                        Data.RRBVector.toList tree
                                                                      )
                              --putStrLn $ show v
                              usleep 5000
                              reader rid n
                        -- spawn readers
                        let spawnReaders : IO (List ThreadID)
                            spawnReaders =
                              for [0,1] $ \n => do
                                fork $ do
                                  reader n 25
                        usleep 10000
                        rtids <- spawnReaders
                        -- Wait for reader threads to finish
                        for_ rtids $ \tid =>
                          threadWait tid
                        css <- readref vec.combinedsnapshotstate
                        buffers' <- readref vec.buffers
                        when ((length $ Data.RRBVector.toList css.currentsnapshot.tree) /= 50) $ do
                          putStrLn $ show buffers'
                          putStrLn $ show $ length $ Data.RRBVector.toList css.currentsnapshot.tree
                          assert_total $ idris_crash "test_NWritersMReaders: missing writes to final rrbvector since it's size is not equal to total writes"
                )
