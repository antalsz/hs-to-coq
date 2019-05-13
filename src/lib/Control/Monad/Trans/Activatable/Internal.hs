{-# LANGUAGE GeneralizedNewtypeDeriving,
             UndecidableInstances, FlexibleInstances, MultiParamTypeClasses,
             ExplicitForAll, LambdaCase #-}
{-# OPTIONS_HADDOCK not-home #-}

module Control.Monad.Trans.Activatable.Internal (
  -- * The 'Activatable' monad
  Activatable, runActivatable, finalizeActivatable,
  -- * The 'ActivatableT' monad transformer (including implementation)
  ActivatableT(..), runActivatableT, finalizeActivatableT,
  -- * Activation-related types
  ActivationError(..), Switched(..),
  -- * Activation operations
  tryActivate, switching, switching',
  -- * The activation modes (internal)
  Mode(..)
) where

-- If you update this list with something else external, don't forget to update
-- "Control.Monad.Trans.Activatable"!
  
import HsToCoq.Util.Functor
import Data.Functor.Identity
import Control.Applicative
import Control.Monad
import Control.Monad.Fail
import Control.Monad.Fix
import Control.Monad.State
import Control.Monad.Except
import Control.Monad.Parse

import qualified Control.Monad.Reader.Class as R
import qualified Control.Monad.Writer.Class as W
import qualified Control.Monad.Cont.Class   as C

data Mode x = Base
            | Active
            | Residuating x
            deriving (Eq, Ord, Show, Read)

newtype ActivatableT x m a =
  ActivatableT { getActivatableT :: StateT (Mode x) m a }
  deriving ( Functor, Applicative, Monad
           , Alternative, MonadPlus
           , MonadFail, MonadFix, MonadIO
           , R.MonadReader r, W.MonadWriter w, MonadError e, C.MonadCont
           , MonadParse
           , MonadTrans )

instance MonadState s m => MonadState s (ActivatableT x m) where
  get   = ActivatableT $ lift get
  put   = ActivatableT . lift . put
  state = ActivatableT . lift . state
  {-# INLINEABLE get   #-}
  {-# INLINEABLE put   #-}
  {-# INLINEABLE state #-}

type Activatable x = ActivatableT x Identity

runActivatableT :: forall m x a. Functor m => ActivatableT x m a -> m (Either (x,a) a)
runActivatableT (ActivatableT act) =
  flip runStateT Base act <&> \case
    (res, Residuating x) -> Left  (x,res)
    (res, _)             -> Right res

finalizeActivatableT :: forall m e x a. MonadError e m => (x -> e) -> ActivatableT x m a -> m a
finalizeActivatableT toError (ActivatableT act) =
  flip runStateT Base act >>= \case
    (_,   Residuating x) -> throwError $ toError x
    (res, _)             -> pure res

runActivatable :: forall x a. Activatable x a -> Either (x,a) a
runActivatable = runIdentity . runActivatableT

finalizeActivatable :: forall x a. Activatable x a -> Maybe a
finalizeActivatable = either (const Nothing) Just . runIdentity . runActivatableT

data ActivationError = DoubleActivation
                     | EarlyActivation
                     deriving (Eq, Ord, Enum, Bounded, Show, Read)

tryActivate :: Monad m => ActivatableT x m (Maybe ActivationError)
tryActivate = ActivatableT get >>= \case
  Base          -> Nothing <$ ActivatableT (put Active)
  Active        -> pure . Just $ DoubleActivation
  Residuating _ -> pure . Just $ EarlyActivation

data Switched b a x = Basic     b
                    | Activated a
                    | Residual  x
                    deriving (Eq, Ord, Show, Read)

switching :: Monad m => ActivatableT x m b -> ActivatableT x m (a, x) -> ActivatableT x m (Switched b a x)
switching basic activated = ActivatableT get >>= \case
  Base          -> Basic <$> basic
  Active        -> do (a,x) <- activated
                      Activated a <$ ActivatableT (put $ Residuating x)
  Residuating x -> Residual x <$ ActivatableT (put Base)

switching' :: Monad m => ActivatableT a m a -> ActivatableT a m (a, a) -> ActivatableT a m a
switching' basic activated = switching basic activated <&> \case
                               Basic     b -> b
                               Activated a -> a
                               Residual  x -> x
