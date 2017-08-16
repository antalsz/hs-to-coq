{-# LANGUAGE MultiParamTypeClasses, FunctionalDependencies,
             FlexibleInstances, UndecidableInstances #-}

module Control.Monad.Variables.Class.Internal (
  MonadVariables(..),
  occurrence, occurrences,
  isBound, areBound
  ) where
  
import Data.Foldable
import Control.Monad.Trans
import HsToCoq.Util.Monad
import HsToCoq.Util.Function
import Data.Maybe

import Data.Set (Set)
import qualified Data.Set as S

import Data.Map.Strict (Map)
import qualified Data.Map.Strict as M

import qualified Control.Monad.Trans.Variables.Internal as V
import qualified Control.Monad.Trans.Identity           as I
import qualified Control.Monad.Trans.Reader             as R
import qualified Control.Monad.Trans.Writer.Strict      as WS
import qualified Control.Monad.Trans.Writer.Lazy        as WL
import qualified Control.Monad.Trans.State.Strict       as SS
import qualified Control.Monad.Trans.State.Lazy         as SL
import qualified Control.Monad.Trans.RWS.Strict         as RWSS
import qualified Control.Monad.Trans.RWS.Lazy           as RWSL
import qualified Control.Monad.Trans.Maybe              as M
import qualified Control.Monad.Trans.Except             as E
import qualified Control.Monad.Trans.Cont               as C
import qualified HsToCoq.Util.GHC.Monad                 as GHC

class (Monad m, Ord i) => MonadVariables i d m | m -> i d where
  bind     :: i -> d  -> m a -> m a
  bindAll  :: Map i d -> m a -> m a
  bound    :: i       -> m (Maybe d)
  allBound :: Set i   -> m (Map i (Maybe d))
  free     :: i       -> m ()
  frees    :: Set i   -> m ()
  
  bind  i d = bindAll $ M.singleton i d
  bound     = fmap (maybe (error "MonadVariables.bound: error in default implementation") fst . M.minView) . allBound . S.singleton
  free      = frees . S.singleton
  
  bindAll  = flip $ M.foldrWithKey bind
  allBound = sequence . M.fromSet bound
  frees    = traverse_ free

  {-# MINIMAL (bind | bindAll), (bound | allBound), (free | frees) #-}

occurrence :: MonadVariables i d m => i -> m ()
occurrence = unlessM <$> isBound <*> free

occurrences :: MonadVariables i d m => Set i -> m ()
occurrences = unlessM <$> areBound <*> frees

isBound :: MonadVariables i d m => i -> m Bool
isBound = fmap isJust . bound

areBound :: MonadVariables i d m => Set i -> m Bool
areBound = fmap (all isJust) . allBound

instance (Monad m, Ord i) => MonadVariables i d (V.VariablesT i d m) where
  bind     = V.bind
  bindAll  = V.bindAll
  bound    = V.bound
  allBound = V.allBound
  free     = V.free
  frees    = V.frees

instance MonadVariables i d m => MonadVariables i d (I.IdentityT m) where
  bind     = I.mapIdentityT .: bind
  bindAll  = I.mapIdentityT .  bindAll
  bound    = lift           .  bound
  free     = lift           .  free
  frees    = lift           .  frees

instance MonadVariables i d m => MonadVariables i d (R.ReaderT r m) where
  bind     = R.mapReaderT  .: bind
  bindAll  = R.mapReaderT  .  bindAll
  bound    = lift          .  bound
  free     = lift          .  free
  frees    = lift          .  frees

instance (MonadVariables i d m, Monoid w) => MonadVariables i d (WS.WriterT w m) where
  bind     = WS.mapWriterT  .: bind
  bindAll  = WS.mapWriterT  .  bindAll
  bound    = lift           .  bound
  free     = lift           .  free
  frees    = lift           .  frees

instance (MonadVariables i d m, Monoid w) => MonadVariables i d (WL.WriterT w m) where
  bind     = WL.mapWriterT  .: bind
  bindAll  = WL.mapWriterT  .  bindAll
  bound    = lift           .  bound
  free     = lift           .  free
  frees    = lift           .  frees

instance MonadVariables i d m => MonadVariables i d (SS.StateT s m) where
  bind     = SS.mapStateT  .: bind
  bindAll  = SS.mapStateT  .  bindAll
  bound    = lift          .  bound
  free     = lift          .  free
  frees    = lift          .  frees

instance MonadVariables i d m => MonadVariables i d (SL.StateT s m) where
  bind     = SL.mapStateT  .: bind
  bindAll  = SL.mapStateT  .  bindAll
  bound    = lift          .  bound
  free     = lift          .  free
  frees    = lift          .  frees

instance (MonadVariables i d m, Monoid w) => MonadVariables i d (RWSS.RWST r w s m) where
  bind     = RWSS.mapRWST  .: bind
  bindAll  = RWSS.mapRWST  .  bindAll
  bound    = lift          .  bound
  free     = lift          .  free
  frees    = lift          .  frees

instance (MonadVariables i d m, Monoid w) => MonadVariables i d (RWSL.RWST r w s m) where
  bind     = RWSL.mapRWST  .: bind
  bindAll  = RWSL.mapRWST  .  bindAll
  bound    = lift          .  bound
  free     = lift          .  free
  frees    = lift          .  frees

instance MonadVariables i d m => MonadVariables i d (M.MaybeT m) where
  bind     = M.mapMaybeT  .: bind
  bindAll  = M.mapMaybeT  .  bindAll
  bound    = lift         .  bound
  free     = lift         .  free
  frees    = lift         .  frees

instance MonadVariables i d m => MonadVariables i d (E.ExceptT e m) where
  bind     = E.mapExceptT  .: bind
  bindAll  = E.mapExceptT  .  bindAll
  bound    = lift          .  bound
  free     = lift          .  free
  frees    = lift          .  frees

instance MonadVariables i d m => MonadVariables i d (C.ContT r m) where
  bind     = C.mapContT  .: bind
  bindAll  = C.mapContT  .  bindAll
  bound    = lift        .  bound
  free     = lift        .  free
  frees    = lift        .  frees

instance MonadVariables i d m => MonadVariables i d (GHC.GhcT m) where
  bind     = GHC.mapGhcT  .: bind
  bindAll  = GHC.mapGhcT  .  bindAll
  bound    = lift         .  bound
  free     = lift         .  free
  frees    = lift         .  frees
