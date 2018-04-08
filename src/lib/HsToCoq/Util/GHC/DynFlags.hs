{-# LANGUAGE TupleSections #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}

module HsToCoq.Util.GHC.DynFlags (module DynFlags) where

import DynFlags

import Control.Monad.Trans
import qualified Control.Monad.Trans.Identity           as I
import qualified Control.Monad.Trans.Writer.Strict      as WS
import qualified Control.Monad.Trans.State.Strict       as SS
import qualified Control.Monad.Trans.State.Lazy         as SL
import qualified Control.Monad.Trans.RWS.Strict         as RWSS
import qualified Control.Monad.Trans.RWS.Lazy           as RWSL
import qualified Control.Monad.Trans.Cont               as C
import qualified Control.Monad.Trans.Counter            as C
import qualified Pipes                                  as P

-- Existing instances: Reader, lazy Writer, Maybe, and Except

instance HasDynFlags m => HasDynFlags (I.IdentityT m) where
  getDynFlags = I.IdentityT getDynFlags

instance (HasDynFlags m, Functor m, Monoid w) => HasDynFlags (WS.WriterT w m) where
  getDynFlags = WS.WriterT $ (,mempty) <$> getDynFlags

instance (HasDynFlags m, Functor m) => HasDynFlags (SS.StateT s m) where
  getDynFlags = SS.StateT $ \s -> (,s) <$> getDynFlags

instance (HasDynFlags m, Functor m) => HasDynFlags (SL.StateT s m) where
  getDynFlags = SL.StateT $ \s -> (,s) <$> getDynFlags

instance (HasDynFlags m, Functor m, Monoid w) => HasDynFlags (RWSS.RWST r w s m) where
  getDynFlags = RWSS.RWST $ \_ s -> (,s,mempty) <$> getDynFlags

instance (HasDynFlags m, Functor m, Monoid w) => HasDynFlags (RWSL.RWST r w s m) where
  getDynFlags = RWSL.RWST $ \_ s -> (,s,mempty) <$> getDynFlags

instance (HasDynFlags m, Monad m) => HasDynFlags (C.ContT r m) where
  getDynFlags = C.ContT (getDynFlags >>=)

instance (HasDynFlags m, Monad m) => HasDynFlags (P.ListT m) where
  getDynFlags = P.lift getDynFlags

instance (HasDynFlags m, Monad m) => HasDynFlags (C.CounterT m) where
  getDynFlags = lift getDynFlags
