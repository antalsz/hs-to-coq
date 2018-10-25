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
