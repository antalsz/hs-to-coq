module Control.Monad.Variables.Internal (
  -- * The 'MonadVariables' class
  MonadVariables(..),
  occurrence, occurrences,
  isBound, areBound,
  -- * The 'Variables' monad
  Variables, runVariables, execVariables,
  mapVariables,
  -- * The 'VariablesT' monad transformer
  VariablesT(..), runVariablesT, execVariablesT,
  mapVariablesT
  ) where
  
import Control.Monad.Variables.Class.Internal
import Control.Monad.Trans.Variables.Internal
  hiding (bind, bindAll, bound, allBound, free, frees, occurrence, occurrences, isBound, areBound)
