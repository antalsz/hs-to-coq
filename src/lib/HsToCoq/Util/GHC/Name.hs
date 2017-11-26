module HsToCoq.Util.GHC.Name (module Name, isOperator, freshInternalName) where

import Control.Monad.IO.Class
import Data.IORef
import System.IO.Unsafe

import OccName
import Name
import Unique
import UniqSupply
import SrcLoc

isOperator :: Name -> Bool
isOperator = isSymOcc . nameOccName
{-# INLINABLE isOperator #-}

-- Module-local
freshInternalName_uniqSupply :: IORef UniqSupply
freshInternalName_uniqSupply = unsafePerformIO $ newIORef =<< mkSplitUniqSupply '殊'
{-# NOINLINE freshInternalName_uniqSupply #-}

-- Module-local
freshInternalName_newUnique :: MonadIO m => m Unique
freshInternalName_newUnique = liftIO $ do
  supply <- readIORef freshInternalName_uniqSupply
  let (u, supply') = takeUniqFromSupply supply
  u <$ writeIORef freshInternalName_uniqSupply supply'

freshInternalName :: MonadIO m => String -> m Name
freshInternalName var = do
  u <- freshInternalName_newUnique
  pure $ mkInternalName u (mkVarOcc var) noSrcSpan
