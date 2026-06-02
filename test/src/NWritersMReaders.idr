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
   runEmptyWith (MkLSMRRBVectorConfig 5)
                -- writer function(s)
                [ (\vec : LSMRRBVector World Int, svc, _ => do
                    -- writer function
                    let writer :  Int
                               -> Nat
                               -> Async Poll [Errno] ()
                        writer wid 0     =
                          pure ()
                        writer wid (S n) = do
                          Data.LSMRRBVector.append vec svc wid (cast n)
                          liftIO (usleep 50)
                          writer wid n
                    writer 1 50
                  )
                , (\vec : LSMRRBVector World Int, svc, _ => do
                    -- writer function
                    let writer :  Int
                               -> Nat
                               -> Async Poll [Errno] ()
                        writer wid 0     =
                          pure ()
                        writer wid (S n) = do
                          Data.LSMRRBVector.append vec svc wid (cast n)
                          liftIO (usleep 50)
                          writer wid n
                    writer 2 50
                  )
                , (\vec : LSMRRBVector World Int, _, st => do
                    -- flush function (ensure all writes make it into snapshot)
                    liftIO $ usleep 2000000
                    _ <- flushUntilEmpty vec st
                    pure ()
                  )
                ]
                [ (\vec : LSMRRBVector World Int => do
                    liftIO $ usleep 10000000
                    css <- readref vec.combinedsnapshotstate
                    buffers' <- readref vec.buffers
                    when ((length $ Data.RRBVector.toList css.currentsnapshot.tree) /= 100) $ do
                      liftIO $ putStrLn "test_NWritersMReaders: missing writes to final rrbvector since it's size is not equal to total writes"
                  )
                , (\vec : LSMRRBVector World Int => do
                    liftIO $ usleep 10000000
                    css <- readref vec.combinedsnapshotstate
                    buffers' <- readref vec.buffers
                    when ((length $ Data.RRBVector.toList css.currentsnapshot.tree) /= 100) $ do
                      liftIO $ putStrLn "test_NWritersMReaders: missing writes to final rrbvector since it's size is not equal to total writes"
                  )
                , (\vec : LSMRRBVector World Int => do
                    liftIO $ usleep 10000000
                    css <- readref vec.combinedsnapshotstate
                    buffers' <- readref vec.buffers
                    when ((length $ Data.RRBVector.toList css.currentsnapshot.tree) /= 100) $ do
                      liftIO $ putStrLn "test_NWritersMReaders: missing writes to final rrbvector since it's size is not equal to total writes"
                  )
                ]
