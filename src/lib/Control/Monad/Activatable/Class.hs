{-# LANGUAGE MultiParamTypeClasses, FunctionalDependencies,
             FlexibleInstances, UndecidableInstances,
             FlexibleContexts,
             LambdaCase #-}

module Control.Monad.Activatable.Class (
  -- * The 'MonadActivatable' class
  MonadActivatable(..),
  switching', activateWith, activate,
  -- * Activation-related types
  ActivationError(..), Switched(..)
) where
  
import HsToCoq.Util.Functor
import Control.Monad.Error.Class
import Control.Monad.Trans

import Data.Foldable

import qualified Control.Monad.Trans.Activatable   as A
import qualified Control.Monad.Trans.Identity      as I
import qualified Control.Monad.Trans.Reader        as R
import qualified Control.Monad.Trans.Writer.Strict as WS
import qualified Control.Monad.Trans.Writer.Lazy   as WL
import qualified Control.Monad.Trans.State.Strict  as SS
import qualified Control.Monad.Trans.State.Lazy    as SL
import qualified Control.Monad.Trans.RWS.Strict    as RWSS
import qualified Control.Monad.Trans.RWS.Lazy      as RWSL

import Control.Monad.Trans.Activatable hiding (tryActivate, switching, switching')

-- |The idea is thus:
--
-- @
--                        /\
--                       /  \
--                      /    \  /\
-- ____________________/      \/  \__________________
--        |               |      |           |
--      basic       activated  residual    basic
-- @
--
-- Or, in code:
-- 
-- @
--     >>> basic         = pure 'b'
--     >>> activated     = pure ('A','X')
--     >>> cmd           = switching' basic activated
--     >>> activatedList = finalizeActivatableT @(Either _) (const Nothing) . sequence
--     >>> activatedList [cmd, cmd, cmd, cmd, cmd]
--     Right "bbbbb"
--     >>> activatedList [cmd, activateWith Just *> cmd, cmd, cmd, cmd]
--     Right "bAXbb"
--     >>> activatedList [cmd, cmd, cmd, activateWith Just *> cmd, cmd]
--     Right "bbbAX"
--     >>> activatedList [cmd, cmd, cmd, activateWith Just *> cmd, cmd]
--     Right "bbbAX"
--     >>> activatedList [cmd, activateWith Just *> cmd, cmd, activateWith Just *> cmd, cmd]
--     Right "bAXAX"
--     >>> activatedList [cmd, activateWith Just *> activateWith Just *> cmd, cmd, cmd, cmd]
--     Left (Just DoubleActivation)
--     >>> activatedList [cmd, activateWith Just *> cmd, activateWith Just *> cmd, cmd, cmd]
--     Left (Just EarlyActivation)
--     >>> activatedList [cmd, cmd, cmd, cmd, activateWith Just *> cmd]
--     Left Nothing
-- @
class Monad m => MonadActivatable x m | m -> x where
  tryActivate :: m (Maybe ActivationError)
  switching   :: m b -> m (a, x) -> m (Switched b a x)

switching' :: MonadActivatable a m => m a -> m (a, a) -> m a
switching' basic activated = switching basic activated <&> \case
                               Basic     b -> b
                               Activated a -> a
                               Residual  x -> x

activateWith :: (MonadError e m, MonadActivatable x m) => (ActivationError -> e) -> m ()
activateWith toError = traverse_ (throwError . toError) =<< tryActivate

activate :: (MonadError ActivationError m, MonadActivatable x m) => m ()
activate = activateWith id

--------------------------------------------------------------------------------
-- Instances

-- See "Instance helpers" below

instance Monad m => MonadActivatable x (ActivatableT x m) where
  tryActivate = A.tryActivate
  switching   = A.switching

instance MonadActivatable x m => MonadActivatable x (I.IdentityT m) where
  tryActivate                                           = lift tryActivate
  switching (I.IdentityT basic) (I.IdentityT activated) =
    I.IdentityT $ switching basic activated

instance MonadActivatable x m => MonadActivatable x (R.ReaderT r m) where
  tryActivate                                       = lift tryActivate
  switching (R.ReaderT basic) (R.ReaderT activated) =
    R.ReaderT $ switching <$> basic <*> activated

instance (MonadActivatable x m, Monoid w) => MonadActivatable x (WS.WriterT w m) where
  tryActivate                                         = lift tryActivate
  switching (WS.WriterT basic) (WS.WriterT activated) =
    WS.WriterT $ lift_switching (switch_pair_strict mempty) push_pair_strict basic activated

instance (MonadActivatable x m, Monoid w) => MonadActivatable x (WL.WriterT w m) where
  tryActivate                                         = lift tryActivate
  switching (WL.WriterT basic) (WL.WriterT activated) =
    WL.WriterT $ lift_switching (switch_pair_lazy mempty) push_pair_lazy basic activated

instance MonadActivatable x m => MonadActivatable x (SS.StateT s m) where
  tryActivate                                       = lift tryActivate
  switching (SS.StateT basic) (SS.StateT activated) =
    SS.StateT $ \s -> lift_switching (switch_pair_strict s) push_pair_strict (basic s) (activated s)

instance MonadActivatable x m => MonadActivatable x (SL.StateT s m) where
  tryActivate                                       = lift tryActivate
  switching (SL.StateT basic) (SL.StateT activated) =
    SL.StateT $ \s -> lift_switching (switch_pair_lazy s) push_pair_lazy (basic s) (activated s)

instance (MonadActivatable x m, Monoid w) => MonadActivatable x (RWSS.RWST r w s m) where
  tryActivate                                       = lift tryActivate
  switching (RWSS.RWST basic) (RWSS.RWST activated) =
    RWSS.RWST $ \r s -> lift_switching (switch_triple_strict s mempty) push_triple_strict (basic r s) (activated r s)

instance (MonadActivatable x m, Monoid w) => MonadActivatable x (RWSL.RWST r w s m) where
  tryActivate                                       = lift tryActivate
  switching (RWSL.RWST basic) (RWSL.RWST activated) =
    RWSL.RWST $ \r s -> lift_switching (switch_triple_lazy s mempty) push_triple_lazy (basic r s) (activated r s)

--------------------------------------------------------------------------------
-- Instance helpers (module-local)

push_pair_lazy :: ((a,x),o) -> ((a,o),x)
push_pair_lazy ~((a,x),o) = ((a,o),x)
{-# INLINE push_pair_lazy #-}

switch_pair_lazy :: o -> Switched (b,o) (a,o) x -> (Switched b a x, o)
switch_pair_lazy o' = \case
  Basic     ~(b,o) -> (Basic     b, o)
  Activated ~(a,o) -> (Activated a, o)
  Residual  x      -> (Residual  x, o')
{-# INLINE switch_pair_lazy #-}

push_pair_strict :: ((a,x),o) -> ((a,o),x)
push_pair_strict ((a,x),o) = ((a,o),x)
{-# INLINE push_pair_strict #-}

switch_pair_strict :: o -> Switched (b,o) (a,o) x -> (Switched b a x, o)
switch_pair_strict o_strict = \case
  Basic     (b,o) -> (Basic     b, o)
  Activated (a,o) -> (Activated a, o)
  Residual  x     -> (Residual  x, o_strict)
{-# INLINE switch_pair_strict #-}

push_triple_lazy :: ((a,x),s,w) -> ((a,s,w),x)
push_triple_lazy ~((a,x),s,w) = ((a,s,w),x)
{-# INLINE push_triple_lazy #-}

switch_triple_lazy :: s -> w -> Switched (b,s,w) (a,s,w) x -> (Switched b a x, s, w)
switch_triple_lazy s wempty = \case
  Basic     ~(b,s',w) -> (Basic     b, s', w)
  Activated ~(a,s',w) -> (Activated a, s', w)
  Residual  x         -> (Residual  x, s,  wempty) 
{-# INLINE switch_triple_lazy #-}

push_triple_strict :: ((a,x),s,w) -> ((a,s,w),x)
push_triple_strict ((a,x),s,w) = ((a,s,w),x)
{-# INLINE push_triple_strict #-}

switch_triple_strict :: s -> w -> Switched (b,s,w) (a,s,w) x -> (Switched b a x, s, w)
switch_triple_strict s wempty = \case
  Basic     (b,s',w) -> (Basic     b, s', w)
  Activated (a,s',w) -> (Activated a, s', w)
  Residual  x        -> (Residual  x, s,  wempty) 
{-# INLINE switch_triple_strict #-}

lift_switching :: MonadActivatable x m
               => (Switched b a x -> r) -> (a' -> (a, x))
               -> m b -> m a' -> m r
lift_switching switch push basic activated = switch <$> switching basic (push <$> activated)
{-# INLINE lift_switching #-}
