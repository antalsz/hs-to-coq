{-# LANGUAGE MultiParamTypeClasses, FunctionalDependencies,
             FlexibleInstances, UndecidableInstances,
             GeneralizedNewtypeDeriving #-}

module Control.Monad.Trans.Variables.Internal (
  -- * The 'Variables' monad
  Variables, runVariables, execVariables,
  mapVariables,
  -- * The 'VariablesT' monad transformer
  VariablesT(..), runVariablesT, execVariablesT,
  mapVariablesT,
  -- * 'Variables' operations
  bind, bindAll,
  bound, allBound,
  occurrence, occurrences,
  isBound, areBound,
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
import Exception            (ExceptionMonad(..))

import Data.Map.Strict (Map)
import qualified Data.Map.Strict as M

import Data.Set (Set)
import qualified Data.Set as S

newtype VariablesT i d m a =
  VariablesT { getVariablesT :: ReaderT (Map i d) (WriterT (Set i) m) a }
  deriving ( Functor
           , Applicative, Alternative
           , Monad, MonadPlus, MonadFix
           , MonadState s, MonadError e, MonadCont, MonadIO )

instance Ord i => MonadTrans (VariablesT i d) where
  lift = VariablesT . lift . lift
  {-# INLINABLE lift #-}

instance (MonadReader r m, Ord i) => MonadReader r (VariablesT i d m) where
  ask    = VariablesT $ lift ask
  local  = mapVariablesT . local
  reader = VariablesT . lift . reader
  {-# INLINABLE ask    #-}
  {-# INLINABLE local  #-}
  {-# INLINABLE reader #-}

instance (MonadWriter w m, Ord i) => MonadWriter w (VariablesT i d m) where
  writer = VariablesT . lift . lift . writer
  tell   = VariablesT . lift . lift . tell
  listen = mapVariablesT $ fmap (\((a,fs),w)  -> ((a,w),fs)) . listen
  pass   = mapVariablesT $ pass . fmap (\((a,wf),fs) -> ((a,fs),wf))
  {-# INLINABLE writer #-}
  {-# INLINABLE tell   #-}
  {-# INLINABLE listen #-}
  {-# INLINABLE pass   #-}

instance (ExceptionMonad m, Ord i) => ExceptionMonad (VariablesT i d m) where
  m `gcatch` h = VariablesT . ReaderT $ \env -> WriterT $
    let unwrap m = runWriterT $ runReaderT (getVariablesT m) env
    in unwrap m `gcatch` (unwrap . h)

  gmask f = VariablesT . ReaderT $ \env -> WriterT $
    let unwrap m = runWriterT $ runReaderT (getVariablesT m) env
    in gmask $ unwrap . f . mapVariablesT

runVariablesT :: VariablesT i d m a -> m (a, Set i)
runVariablesT = runWriterT . flip runReaderT M.empty . getVariablesT
{-# INLINABLE runVariablesT #-}

execVariablesT :: Monad m => VariablesT i d m () -> m (Set i)
execVariablesT = execWriterT . flip runReaderT M.empty . getVariablesT
{-# INLINABLE execVariablesT #-}

mapVariablesT :: (m (a, Set i) -> n (b, Set i)) -> VariablesT i d m a -> VariablesT i d n b
mapVariablesT f = VariablesT . mapReaderT (mapWriterT f) . getVariablesT
{-# INLINABLE mapVariablesT #-}

type Variables i d = VariablesT i d Identity

runVariables :: Variables i d a -> (a, Set i)
runVariables = runIdentity . runVariablesT
{-# INLINABLE runVariables #-}

execVariables :: Variables i d () -> Set i
execVariables = runIdentity . execVariablesT
{-# INLINABLE execVariables #-}

mapVariables :: ((a, Set i) -> (b, Set i)) -> Variables i d a -> Variables i d b
mapVariables f = VariablesT . mapReaderT (mapWriter f) . getVariablesT
{-# INLINABLE mapVariables #-}

bind :: (Monad m, Ord i) => i -> d -> VariablesT i d m a -> VariablesT i d m a
bind x d = VariablesT . local (M.insert x d) . getVariablesT

bindAll :: (Monad m, Ord i) => Map i d -> VariablesT i d m a -> VariablesT i d m a
bindAll xs = VariablesT . local (M.union xs) . getVariablesT

bound :: (Monad m, Ord i) => i -> VariablesT i d m (Maybe d)
bound = VariablesT . asks . M.lookup

allBound :: (Monad m, Ord i) => Set i -> VariablesT i d m (Map i (Maybe d))
allBound xs = VariablesT $ asks (\bs -> M.fromSet (`M.lookup` bs) xs)

frees :: (Monad m, Ord i) => Set i -> VariablesT i d m ()
frees = VariablesT . tell

free :: (Monad m, Ord i) => i -> VariablesT i d m ()
free = frees . S.singleton

occurrence :: (Monad m, Ord i) => i -> VariablesT i d m ()
occurrence = unlessM <$> isBound <*> free

occurrences :: (Monad m, Ord i) => Set i -> VariablesT i d m ()
occurrences = unlessM <$> areBound <*> frees

isBound :: (Monad m, Ord i) => i -> VariablesT i d m Bool
isBound = VariablesT . asks . M.member

areBound :: (Monad m, Ord i) => Set i -> VariablesT i d m Bool
areBound xs = VariablesT $ asks (\bs -> all (`M.member` bs) xs)
