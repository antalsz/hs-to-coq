module Locks where

import           Control.Concurrent.MVar

example :: IO ()
example = do
  m <- newMVar 42
  x <- takeMVar m
  return ()

deadlock :: IO ()
deadlock = do
  m <- newEmptyMVar :: IO (MVar Int)
  x <- takeMVar m
  return ()

t1 :: MVar Int -> MVar Int -> IO ()
t1 bal cost = do
  modifyMVar_ bal $ \x -> return (x + 5000)
  modifyMVar_ bal $ \x -> return (x + 1000)
  modifyMVar_ bal $ \x -> return (x * 2)
  return ()

t2 :: MVar Int -> MVar Int -> IO ()
t2 bal cost = do
  x <- readMVar bal
  if (x >= 1000) then
    do putMVar cost 100
  else do putMVar cost 0
