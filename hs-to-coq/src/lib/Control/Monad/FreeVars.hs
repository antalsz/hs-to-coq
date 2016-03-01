module Control.Monad.FreeVars (
  -- * The 'MonadFreeVars' class
  MonadFreeVars(bind, bindAll, bound, allBound),
  occurrence, occurrences,
  -- * The 'FreeVars' monad
  FreeVars, runFreeVars, execFreeVars,
  mapFreeVars,
  -- * The 'FreeVarsT' monad transformer
  FreeVarsT(), runFreeVarsT, execFreeVarsT,
  mapFreeVarsT
  ) where
  
import Control.Monad.FreeVars.Class
import Control.Monad.Trans.FreeVars
  hiding (bind, bindAll, bound, allBound, occurrence, occurrences)
