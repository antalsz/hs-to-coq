module HsToCoq.Util.GHC.RdrName (module RdrName, isOperator) where

import OccName
import RdrName

isOperator :: RdrName -> Bool
isOperator = isSymOcc . rdrNameOcc
{-# INLINABLE isOperator #-}
