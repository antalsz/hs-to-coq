{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE UndecidableInstances #-}

module Control.Monad.Trans.Counter (CounterT(), runCounterT, Counter, runCounter, MonadCounter(..)) where

import Numeric.Natural
import Exception
import HsToCoq.Util.GHC.Exception ()
import Control.Monad.State.Strict

import Data.Functor.Identity
import Control.Applicative
import Control.Monad.Fail

import qualified Control.Monad.Reader.Class    as R
import qualified Control.Monad.Writer.Class    as W
import qualified Control.Monad.Error.Class     as E
import qualified Control.Monad.Cont.Class      as C

import qualified Control.Monad.Trans.Identity      as I
import qualified Control.Monad.Trans.Reader        as R
import qualified Control.Monad.Trans.Writer.Strict as WS
import qualified Control.Monad.Trans.Writer.Lazy   as WL
import qualified Control.Monad.Trans.State.Lazy    as SL
import qualified Control.Monad.Trans.RWS.Strict    as RWSS
import qualified Control.Monad.Trans.RWS.Lazy      as RWSL
import qualified Control.Monad.Trans.Maybe         as M
import qualified Control.Monad.Trans.Except        as E
import qualified Control.Monad.Trans.Cont          as C

--------------------------------------------------------------------------------
-- Transformer

newtype CounterT m a = CounterT (StateT Natural m a)
                   deriving ( Functor, Applicative, Monad
                            , Alternative, MonadPlus
                            , MonadFail, MonadFix, MonadIO
                            , R.MonadReader r, W.MonadWriter w, E.MonadError e, C.MonadCont
                            , MonadTrans
                            , ExceptionMonad
                            )

instance MonadState s m => MonadState s (CounterT m) where
    put   = lift . put
    get   = lift get
    state = lift . state

runCounterT :: Monad m => CounterT m a -> m a
runCounterT (CounterT m) = evalStateT m 0

--------------------------------------------------------------------------------
-- Monad

type Counter = CounterT Identity

runCounter :: Counter a -> a
runCounter = runIdentity . runCounterT

--------------------------------------------------------------------------------
-- Type Class

class Monad m => MonadCounter m where
  fresh :: m Natural

instance Monad m => MonadCounter (CounterT m) where
  fresh = CounterT . StateT $ \n -> pure (n, n + 1)

instance MonadCounter m             => MonadCounter (I.IdentityT m)     where fresh = lift fresh
instance MonadCounter m             => MonadCounter (R.ReaderT r m)     where fresh = lift fresh
instance (MonadCounter m, Monoid w) => MonadCounter (WS.WriterT w m)    where fresh = lift fresh
instance (MonadCounter m, Monoid w) => MonadCounter (WL.WriterT w m)    where fresh = lift fresh
instance MonadCounter m             => MonadCounter (StateT s m)        where fresh = lift fresh
instance MonadCounter m             => MonadCounter (SL.StateT s m)     where fresh = lift fresh
instance (MonadCounter m, Monoid w) => MonadCounter (RWSS.RWST r w s m) where fresh = lift fresh
instance (MonadCounter m, Monoid w) => MonadCounter (RWSL.RWST r w s m) where fresh = lift fresh
instance MonadCounter m             => MonadCounter (M.MaybeT m)        where fresh = lift fresh
instance MonadCounter m             => MonadCounter (E.ExceptT e m)     where fresh = lift fresh
instance MonadCounter m             => MonadCounter (C.ContT r m)       where fresh = lift fresh
