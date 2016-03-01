module Control.Monad.FreeVars.Internal (
  -- * The 'MonadFreeVars' class
  MonadFreeVars(..),
  occurrence, occurrences,
  -- * The 'FreeVars' monad
  FreeVars, runFreeVars, execFreeVars,
  mapFreeVars,
  -- * The 'FreeVarsT' monad transformer
  FreeVarsT(..), runFreeVarsT, execFreeVarsT,
  mapFreeVarsT
  ) where
  
import Control.Monad.FreeVars.Class.Internal
import Control.Monad.Trans.FreeVars.Internal
  hiding (bind, bindAll, bound, allBound, free, frees, occurrence, occurrences)
