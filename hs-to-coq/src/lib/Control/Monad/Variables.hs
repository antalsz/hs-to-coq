module Control.Monad.Variables (
  -- * The 'MonadVariables' class
  MonadVariables(bind, bindAll, bound, allBound),
  occurrence, occurrences,
  isBound, areBound,
  -- * The 'Variables' monad
  Variables, runVariables, execVariables, evalVariables,
  mapVariables,
  -- * The 'VariablesT' monad transformer
  VariablesT(), runVariablesT, execVariablesT, evalVariablesT,
  mapVariablesT
  ) where
  
import Control.Monad.Variables.Class
import Control.Monad.Trans.Variables
  hiding (bind, bindAll, bound, allBound, occurrence, occurrences, isBound, areBound)
