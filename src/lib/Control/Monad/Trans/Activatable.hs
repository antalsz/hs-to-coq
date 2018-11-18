module Control.Monad.Trans.Activatable (
  -- * The 'Activatable' monad
  Activatable, runActivatable, finalizeActivatable,
  -- * The 'ActivatableT' monad transformer
  ActivatableT(), runActivatableT, finalizeActivatableT,
  -- * Activation-related types
  ActivationError(..), Switched(..),
  -- * Activation operations
  tryActivate, switching, switching'
) where

import Control.Monad.Trans.Activatable.Internal
