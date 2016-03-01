module Control.Monad.FreeVars.Class (
  MonadFreeVars(bind, bindAll, bound, allBound),
  occurrence, occurrences
  ) where

import Control.Monad.FreeVars.Class.Internal
