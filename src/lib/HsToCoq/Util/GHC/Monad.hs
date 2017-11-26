{-# LANGUAGE MultiParamTypeClasses, FlexibleInstances, UndecidableInstances #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}

module HsToCoq.Util.GHC.Monad (module GhcMonad, mapGhcT) where

import GhcMonad
import HsToCoq.Util.GHC.DynFlags ()
import HsToCoq.Util.GHC.Exception ()
import Control.Monad.Trans

import Control.Monad.Reader.Class
import Control.Monad.Writer.Class
import Control.Monad.State.Class
import Control.Monad.RWS.Class
import Control.Monad.Error.Class
import Control.Monad.Cont.Class

import qualified Control.Monad.Trans.Identity      as I
import qualified Control.Monad.Trans.Maybe         as M
import qualified Control.Monad.Trans.Reader        as R
import qualified Control.Monad.Trans.Writer.Strict as WS
import qualified Control.Monad.Trans.Writer.Lazy   as WL
import qualified Control.Monad.Trans.State.Strict  as SS
import qualified Control.Monad.Trans.State.Lazy    as SL
import qualified Control.Monad.Trans.RWS.Strict    as RWSS
import qualified Control.Monad.Trans.RWS.Lazy      as RWSL
import qualified Control.Monad.Trans.Variables     as V

instance MonadTrans GhcT where
  lift = liftGhcT

instance MonadReader r m => MonadReader r (GhcT m) where
  ask    = lift      ask
  local  = mapGhcT . local
  reader = lift    . reader

instance MonadWriter w m => MonadWriter w (GhcT m) where
  writer = lift    . writer
  tell   = lift    . tell
  listen = mapGhcT   listen
  pass   = mapGhcT   pass

instance MonadState s m => MonadState s (GhcT m) where
  get   = lift   get
  put   = lift . put
  state = lift . state

instance MonadRWS r w s m => MonadRWS r w s (GhcT m)

instance MonadError e m => MonadError e (GhcT m) where
  throwError       = lift . throwError
  m `catchError` h = GhcT $ \session -> unGhcT m session `catchError` (flip unGhcT session . h)

instance MonadCont m => MonadCont (GhcT m) where
  callCC f = GhcT $ \session ->
    callCC (flip unGhcT session . f . ((GhcT . const) .)) 

instance GhcMonad m => GhcMonad (I.IdentityT m) where
  getSession = lift   getSession
  setSession = lift . setSession

instance GhcMonad m => GhcMonad (M.MaybeT m) where
  getSession = lift   getSession
  setSession = lift . setSession

instance GhcMonad m => GhcMonad (R.ReaderT r m) where
  getSession = lift   getSession
  setSession = lift . setSession

instance (GhcMonad m, Monoid w) => GhcMonad (WS.WriterT w m) where
  getSession = lift   getSession
  setSession = lift . setSession

instance (GhcMonad m, Monoid w) => GhcMonad (WL.WriterT w m) where
  getSession = lift   getSession
  setSession = lift . setSession

instance GhcMonad m => GhcMonad (SS.StateT s m) where
  getSession = lift   getSession
  setSession = lift . setSession

instance GhcMonad m => GhcMonad (SL.StateT s m) where
  getSession = lift   getSession
  setSession = lift . setSession

instance (GhcMonad m, Monoid w) => GhcMonad (RWSS.RWST r w s m) where
  getSession = lift   getSession
  setSession = lift . setSession

instance (GhcMonad m, Monoid w) => GhcMonad (RWSL.RWST r w s m) where
  getSession = lift   getSession
  setSession = lift . setSession

instance (GhcMonad m, Ord i) => GhcMonad (V.VariablesT i d m) where
  getSession = lift   getSession
  setSession = lift . setSession

mapGhcT :: (m a -> n b) -> GhcT m a -> GhcT n b
mapGhcT f m = GhcT $ f . unGhcT m
