module Control.Monad.Trans.FreeVars (
  -- * The 'FreeVars' monad
  FreeVars, runFreeVars, execFreeVars,
  mapFreeVars,
  -- * The 'FreeVarsT' monad transformer
  FreeVarsT(), runFreeVarsT, execFreeVarsT,
  mapFreeVarsT,
  -- * 'FreeVars' operations
  bind, bindAll,
  bound, allBound,
  occurrence, occurrences,
  ) where

import Control.Monad.Trans.FreeVars.Internal
