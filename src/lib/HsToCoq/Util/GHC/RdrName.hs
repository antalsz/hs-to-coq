module HsToCoq.Util.GHC.RdrName (module RdrName, isRdrOperator) where

import OccName
import RdrName

isRdrOperator :: RdrName -> Bool
isRdrOperator = isSymOcc . rdrNameOcc
{-# INLINABLE isRdrOperator #-}
