{-# OPTIONS_GHC -fno-warn-orphans #-}

module HsToCoq.Util.GHC.Monad (module GhcMonad, mapGhcT) where

import GhcMonad
import Control.Monad.Trans

instance MonadTrans GhcT where
  lift = liftGhcT

mapGhcT :: (m a -> n b) -> GhcT m a -> GhcT n b
mapGhcT f m = GhcT $ f . unGhcT m
