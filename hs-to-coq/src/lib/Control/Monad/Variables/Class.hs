module Control.Monad.Variables.Class (
  MonadVariables(bind, bindAll, bound, allBound),
  occurrence, occurrences,
  isBound, areBound
  ) where

import Control.Monad.Variables.Class.Internal
