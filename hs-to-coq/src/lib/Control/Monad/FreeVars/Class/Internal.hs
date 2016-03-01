{-# LANGUAGE MultiParamTypeClasses, FunctionalDependencies,
             FlexibleInstances, UndecidableInstances #-}

module Control.Monad.FreeVars.Class.Internal (
  MonadFreeVars(..),
  occurrence, occurrences
  ) where
  
import Data.Foldable
import Control.Monad.Trans
import HsToCoq.Util.Monad

import Data.Set (Set)
import qualified Data.Set as S

import qualified Control.Monad.Trans.FreeVars.Internal as FV
import qualified Control.Monad.Trans.Identity          as I
import qualified Control.Monad.Trans.Reader            as R
import qualified Control.Monad.Trans.Writer.Strict     as WS
import qualified Control.Monad.Trans.Writer.Lazy       as WL
import qualified Control.Monad.Trans.State.Strict      as SS
import qualified Control.Monad.Trans.State.Lazy        as SL
import qualified Control.Monad.Trans.RWS.Strict        as RWSS
import qualified Control.Monad.Trans.RWS.Lazy          as RWSL
import qualified Control.Monad.Trans.Maybe             as M
import qualified Control.Monad.Trans.Except            as E
import qualified Control.Monad.Trans.List              as L
import qualified Control.Monad.Trans.Cont              as C

class (Monad m, Ord i) => MonadFreeVars i m | m -> i where
  bind     :: i     -> m a -> m a
  bindAll  :: Set i -> m a -> m a
  bound    :: i     -> m Bool
  allBound :: Set i -> m Bool
  free     :: i     -> m ()
  frees    :: Set i -> m ()
  
  bind  = bindAll  . S.singleton
  bound = allBound . S.singleton
  free  = frees    . S.singleton
  
  bindAll  = flip $ foldr bind
  allBound = foldr (andM . bound) (pure True)
  frees    = traverse_ free

  {-# MINIMAL bind, bound, free | bindAll, allBound, frees #-}

occurrence :: MonadFreeVars i m => i -> m ()
occurrence = unlessM <$> bound <*> free

occurrences :: MonadFreeVars i m => Set i -> m ()
occurrences = unlessM <$> allBound <*> frees

instance (Monad m, Ord i) => MonadFreeVars i (FV.FreeVarsT i m) where
  bind     = FV.bind
  bindAll  = FV.bindAll
  bound    = FV.bound
  allBound = FV.allBound
  free     = FV.free 
  frees    = FV.frees

instance MonadFreeVars i m => MonadFreeVars i (I.IdentityT m) where
  bind     = I.mapIdentityT . bind
  bindAll  = I.mapIdentityT . bindAll
  bound    = lift           . bound
  allBound = lift           . allBound
  free     = lift           . free 
  frees    = lift           . frees

instance MonadFreeVars i m => MonadFreeVars i (R.ReaderT r m) where
  bind     = R.mapReaderT . bind
  bindAll  = R.mapReaderT . bindAll
  bound    = lift         . bound
  allBound = lift         . allBound
  free     = lift         . free 
  frees    = lift         . frees

instance (MonadFreeVars i m, Monoid w) => MonadFreeVars i (WS.WriterT w m) where
  bind     = WS.mapWriterT . bind
  bindAll  = WS.mapWriterT . bindAll
  bound    = lift          . bound
  allBound = lift          . allBound
  free     = lift          . free 
  frees    = lift          . frees

instance (MonadFreeVars i m, Monoid w) => MonadFreeVars i (WL.WriterT w m) where
  bind     = WL.mapWriterT . bind
  bindAll  = WL.mapWriterT . bindAll
  bound    = lift          . bound
  allBound = lift          . allBound
  free     = lift          . free 
  frees    = lift          . frees

instance MonadFreeVars i m => MonadFreeVars i (SS.StateT s m) where
  bind     = SS.mapStateT . bind
  bindAll  = SS.mapStateT . bindAll
  bound    = lift         . bound
  allBound = lift         . allBound
  free     = lift         . free 
  frees    = lift         . frees

instance MonadFreeVars i m => MonadFreeVars i (SL.StateT s m) where
  bind     = SL.mapStateT . bind
  bindAll  = SL.mapStateT . bindAll
  bound    = lift         . bound
  allBound = lift         . allBound
  free     = lift         . free 
  frees    = lift         . frees

instance (MonadFreeVars i m, Monoid w) => MonadFreeVars i (RWSS.RWST r w s m) where
  bind     = RWSS.mapRWST . bind
  bindAll  = RWSS.mapRWST . bindAll
  bound    = lift         . bound
  allBound = lift         . allBound
  free     = lift         . free 
  frees    = lift         . frees

instance (MonadFreeVars i m, Monoid w) => MonadFreeVars i (RWSL.RWST r w s m) where
  bind     = RWSL.mapRWST . bind
  bindAll  = RWSL.mapRWST . bindAll
  bound    = lift         . bound
  allBound = lift         . allBound
  free     = lift         . free 
  frees    = lift         . frees

instance MonadFreeVars i m => MonadFreeVars i (M.MaybeT m) where
  bind     = M.mapMaybeT . bind
  bindAll  = M.mapMaybeT . bindAll
  bound    = lift        . bound
  allBound = lift        . allBound
  free     = lift        . free 
  frees    = lift        . frees

instance MonadFreeVars i m => MonadFreeVars i (E.ExceptT e m) where
  bind     = E.mapExceptT . bind
  bindAll  = E.mapExceptT . bindAll
  bound    = lift        . bound
  allBound = lift        . allBound
  free     = lift        . free 
  frees    = lift        . frees

instance MonadFreeVars i m => MonadFreeVars i (L.ListT m) where
  bind     = L.mapListT . bind
  bindAll  = L.mapListT . bindAll
  bound    = lift       . bound
  allBound = lift       . allBound
  free     = lift       . free 
  frees    = lift       . frees

instance MonadFreeVars i m => MonadFreeVars i (C.ContT r m) where
  bind     = C.mapContT . bind
  bindAll  = C.mapContT . bindAll
  bound    = lift       . bound
  allBound = lift       . allBound
  free     = lift       . free 
  frees    = lift       . frees
