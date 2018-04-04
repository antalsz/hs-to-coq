{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE UndecidableInstances #-}
module Control.Monad.Trans.Counter (CounterT, withCounterT, CounterMonad(..)) where

import Control.Monad.State.Strict
import Control.Monad.Writer.Class
import Control.Monad.Writer.Lazy
import Control.Monad.Reader
import Control.Monad.Trans.Maybe
import Numeric.Natural

import Exception
import HsToCoq.Util.GHC.Exception ()

newtype CounterT m a = CounterT (StateT Natural m a)
  deriving (Functor, Applicative, Monad, MonadTrans, MonadReader s,
            MonadWriter s, MonadIO, ExceptionMonad)

withCounterT :: Monad m => CounterT m a -> m a
withCounterT (CounterT m) = evalStateT m 0

class Monad m => CounterMonad m where
    fresh :: m Natural

instance Monad m => CounterMonad (CounterT m) where
    fresh = CounterT $ StateT $ \n -> pure (n, n + 1)

instance MonadState s m => MonadState s (CounterT m) where
    put x   = lift (put x)
    get     = lift get
    state x = lift (state x)

instance (CounterMonad m, Monoid s) => CounterMonad (WriterT s m) where
    fresh = lift fresh

instance CounterMonad m => CounterMonad (ReaderT s m) where
    fresh = lift fresh

instance CounterMonad m => CounterMonad (MaybeT m) where
    fresh = lift fresh
