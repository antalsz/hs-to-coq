{-# LANGUAGE GADTs #-}

module InterpHs where

import           Control.Concurrent.MVar
import qualified IO

type IO' = IO.Freer (IO.MemEff MVar)

type Prog = IO' ()

interp :: Prog -> IO (Either () Prog)
interp (IO.Ret _)                   = return $ Left ()
interp (IO.Vis IO.NewMV k)          = Right . k <$> newEmptyMVar
interp (IO.Vis (IO.TakeMV m) k)     = Right . k <$> takeMVar m
interp (IO.Vis (IO.ReadMV m) k)     = Right . k <$> readMVar m
interp (IO.Vis (IO.PutMV m v) k)    = Right . k <$> putMVar m v
interp (IO.Vis (IO.TryTakeMV m) k)  = Right . k <$> tryTakeMVar m
interp (IO.Vis (IO.TryReadMV m) k)  = Right . k <$> tryReadMVar m
interp (IO.Vis (IO.TryPutMV m v) k) = Right . k <$> tryPutMVar m v
interp (IO.Vis (IO.IsEmptyMV m) k)  = Right . k <$> isEmptyMVar m
