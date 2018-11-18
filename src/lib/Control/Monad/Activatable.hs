module Control.Monad.Activatable (
  -- * The 'MonadActivatable' class
  MonadActivatable(..),
  switching', activateWith, activate,
  -- * The 'Activatable' monad
  Activatable, runActivatable, finalizeActivatable,
  -- * The 'ActivatableT' monad transformer
  ActivatableT(), runActivatableT, finalizeActivatableT,
  -- * Activation-related types
  ActivationError(..), Switched(..)
) where

import Control.Monad.Trans.Activatable hiding (switching')
import Control.Monad.Activatable.Class
