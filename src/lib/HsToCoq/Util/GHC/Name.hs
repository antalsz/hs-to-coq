{-# LANGUAGE ViewPatterns #-}
module HsToCoq.Util.GHC.Name (module Name, isOperator, freshInternalName) where

import Control.Monad.IO.Class
import Data.IORef
import System.IO.Unsafe

import HsToCoq.ConvertHaskell.InfixNames
import qualified Data.Text as T
import Module

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
freshInternalName var
    | Just (T.unpack -> mn, T.unpack -> base) <- splitModule (T.pack var) = do
      let mod = mkModule (stringToUnitId "hs-to-coq") (mkModuleName mn)
      u <- freshInternalName_newUnique
      pure $ mkExternalName u (mod) (mkVarOcc base) noSrcSpan
    | otherwise = do
      u <- freshInternalName_newUnique
      pure $ mkInternalName u (mkVarOcc var) noSrcSpan
