module HsToCoq.Util.GHC.HsTypes (
  module HsTypes,
  viewHsTyVar, viewLHsTyVar
) where

import HsTypes
import SrcLoc

viewHsTyVar :: HsType name -> Maybe name
viewHsTyVar (HsTyVar (L _ name))                      = Just name
viewHsTyVar (HsAppsTy [L _ (HsAppInfix  (L _ name))]) = Just name
viewHsTyVar (HsAppsTy [L _ (HsAppPrefix lty)])        = viewLHsTyVar lty
viewHsTyVar _                                         = Nothing

viewLHsTyVar :: LHsType name -> Maybe name
viewLHsTyVar = viewHsTyVar . unLoc
