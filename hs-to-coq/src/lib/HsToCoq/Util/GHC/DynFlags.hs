{-# LANGUAGE TupleSections #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}

module HsToCoq.Util.GHC.DynFlags (module DynFlags) where

import DynFlags

import qualified Control.Monad.Trans.Identity      as I
import qualified Control.Monad.Trans.Reader        as R
import qualified Control.Monad.Trans.Writer.Strict as WS
import qualified Control.Monad.Trans.Writer.Lazy   as WL
import qualified Control.Monad.Trans.State.Strict  as SS
import qualified Control.Monad.Trans.State.Lazy    as SL
import qualified Control.Monad.Trans.RWS.Strict    as RWSS
import qualified Control.Monad.Trans.RWS.Lazy      as RWSL
import qualified Control.Monad.Trans.Maybe         as M
import qualified Control.Monad.Trans.Except        as E
import qualified Control.Monad.Trans.List          as L
import qualified Control.Monad.Trans.Cont          as C

instance HasDynFlags m => HasDynFlags (I.IdentityT m) where
  getDynFlags = I.IdentityT getDynFlags

instance HasDynFlags m => HasDynFlags (R.ReaderT r m) where
  getDynFlags = R.ReaderT $ const getDynFlags

instance (HasDynFlags m, Functor m, Monoid w) => HasDynFlags (WS.WriterT w m) where
  getDynFlags = WS.WriterT $ (,mempty) <$> getDynFlags

instance (HasDynFlags m, Functor m, Monoid w) => HasDynFlags (WL.WriterT w m) where
  getDynFlags = WL.WriterT $ (,mempty) <$> getDynFlags

instance (HasDynFlags m, Functor m) => HasDynFlags (SS.StateT s m) where
  getDynFlags = SS.StateT $ \s -> (,s) <$> getDynFlags

instance (HasDynFlags m, Functor m) => HasDynFlags (SL.StateT s m) where
  getDynFlags = SL.StateT $ \s -> (,s) <$> getDynFlags

instance (HasDynFlags m, Functor m, Monoid w) => HasDynFlags (RWSS.RWST r w s m) where
  getDynFlags = RWSS.RWST $ \_ s -> (,s,mempty) <$> getDynFlags

instance (HasDynFlags m, Functor m, Monoid w) => HasDynFlags (RWSL.RWST r w s m) where
  getDynFlags = RWSL.RWST $ \_ s -> (,s,mempty) <$> getDynFlags

instance (HasDynFlags m, Functor m) => HasDynFlags (M.MaybeT m) where
  getDynFlags = M.MaybeT $ Just <$> getDynFlags

instance (HasDynFlags m, Functor m) => HasDynFlags (E.ExceptT e m) where
  getDynFlags = E.ExceptT $ Right <$> getDynFlags

instance (HasDynFlags m, Functor m) => HasDynFlags (L.ListT m) where
  getDynFlags = L.ListT $ pure <$> getDynFlags

instance (HasDynFlags m, Monad m) => HasDynFlags (C.ContT r m) where
  getDynFlags = C.ContT (getDynFlags >>=)
