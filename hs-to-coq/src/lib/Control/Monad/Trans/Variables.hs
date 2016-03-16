module Control.Monad.Trans.Variables (
  -- * The 'Variables' monad
  Variables, runVariables, execVariables,
  mapVariables,
  -- * The 'VariablesT' monad transformer
  VariablesT(), runVariablesT, execVariablesT,
  mapVariablesT,
  -- * 'Variables' operations
  bind, bindAll,
  bound, allBound,
  occurrence, occurrences,
  isBound, areBound
  ) where

import Control.Monad.Trans.Variables.Internal
