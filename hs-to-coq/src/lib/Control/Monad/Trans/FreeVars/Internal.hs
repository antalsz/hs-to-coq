{-# LANGUAGE MultiParamTypeClasses, FunctionalDependencies,
             FlexibleInstances, UndecidableInstances,
             GeneralizedNewtypeDeriving #-}

module Control.Monad.Trans.FreeVars.Internal (
  -- * The 'FreeVars' monad
  FreeVars, runFreeVars, execFreeVars,
  mapFreeVars,
  -- * The 'FreeVarsT' monad transformer
  FreeVarsT(..), runFreeVarsT, execFreeVarsT,
  mapFreeVarsT,
  -- * 'FreeVars' operations
  bind, bindAll,
  bound, allBound,
  occurrence, occurrences,
  -- ** Internal operations
  free, frees
  ) where

import Control.Applicative
import Control.Monad
import HsToCoq.Util.Monad
import Data.Functor.Identity
import Control.Monad.Reader
import Control.Monad.Writer.Strict
import Control.Monad.State  (MonadState(..))
import Control.Monad.Except (MonadError(..))
import Control.Monad.Cont   (MonadCont(..))

import Data.Set (Set)
import qualified Data.Set as S

newtype FreeVarsT i m a =
  FreeVarsT { getFreeVarsT :: ReaderT (Set i) (WriterT (Set i) m) a }
  deriving ( Functor
           , Applicative, Alternative
           , Monad, MonadPlus, MonadFix
           , MonadState s, MonadError e, MonadCont, MonadIO )

instance Ord i => MonadTrans (FreeVarsT i) where
  lift = FreeVarsT . lift . lift
  {-# INLINABLE lift #-}

instance (MonadReader r m, Ord i) => MonadReader r (FreeVarsT i m) where
  ask    = FreeVarsT $ lift ask
  local  = mapFreeVarsT . local
  reader = FreeVarsT . lift . reader
  {-# INLINABLE ask    #-}
  {-# INLINABLE local  #-}
  {-# INLINABLE reader #-}

instance (MonadWriter w m, Ord i) => MonadWriter w (FreeVarsT i m) where
  writer = FreeVarsT . lift . lift . writer
  tell   = FreeVarsT . lift . lift . tell
  listen = mapFreeVarsT $ fmap (\((a,fs),w)  -> ((a,w),fs)) . listen
  pass   = mapFreeVarsT $ pass . fmap (\((a,wf),fs) -> ((a,fs),wf))
  {-# INLINABLE writer #-}
  {-# INLINABLE tell   #-}
  {-# INLINABLE listen #-}
  {-# INLINABLE pass   #-}

runFreeVarsT :: FreeVarsT i m a -> m (a, Set i)
runFreeVarsT = runWriterT . flip runReaderT S.empty . getFreeVarsT
{-# INLINABLE runFreeVarsT #-}

execFreeVarsT :: Monad m => FreeVarsT i m () -> m (Set i)
execFreeVarsT = execWriterT . flip runReaderT S.empty . getFreeVarsT
{-# INLINABLE execFreeVarsT #-}

mapFreeVarsT :: (m (a, Set i) -> n (b, Set i)) -> FreeVarsT i m a -> FreeVarsT i n b
mapFreeVarsT f = FreeVarsT . mapReaderT (mapWriterT f) . getFreeVarsT
{-# INLINABLE mapFreeVarsT #-}

type FreeVars i = FreeVarsT i Identity

runFreeVars :: FreeVars i a -> (a, Set i)
runFreeVars = runIdentity . runFreeVarsT
{-# INLINABLE runFreeVars #-}

execFreeVars :: FreeVars i () -> Set i
execFreeVars = runIdentity . execFreeVarsT
{-# INLINABLE execFreeVars #-}

mapFreeVars :: ((a, Set i) -> (b, Set i)) -> FreeVars i a -> FreeVars i b
mapFreeVars f = FreeVarsT . mapReaderT (mapWriter f) . getFreeVarsT
{-# INLINABLE mapFreeVars #-}

bind :: (Monad m, Ord i) => i -> FreeVarsT i m a -> FreeVarsT i m a
bind x = FreeVarsT . local (S.insert x) . getFreeVarsT

bindAll :: (Monad m, Ord i) => Set i -> FreeVarsT i m a -> FreeVarsT i m a
bindAll xs = FreeVarsT . local (S.union xs) . getFreeVarsT

bound :: (Monad m, Ord i) => i -> FreeVarsT i m Bool
bound = FreeVarsT . asks . S.member

allBound :: (Monad m, Ord i) => Set i -> FreeVarsT i m Bool
allBound = FreeVarsT . asks . S.isSubsetOf

frees :: (Monad m, Ord i) => Set i -> FreeVarsT i m ()
frees = FreeVarsT . tell

free :: (Monad m, Ord i) => i -> FreeVarsT i m ()
free = frees . S.singleton

occurrence :: (Monad m, Ord i) => i -> FreeVarsT i m ()
occurrence = unlessM <$> bound <*> free

occurrences :: (Monad m, Ord i) => Set i -> FreeVarsT i m ()
occurrences = unlessM <$> allBound <*> frees
