module HsToCoq.Util.GHC.HsTypes (
  module HsTypes,
  viewHsTyVar, viewLHsTyVar
) where

import HsTypes
import SrcLoc
import HsExtension

viewHsTyVar :: HsType pass -> Maybe (IdP pass)
viewHsTyVar (HsTyVar _  (L _ name))                   = Just name
viewHsTyVar (HsAppsTy [L _ (HsAppInfix  (L _ name))]) = Just name
viewHsTyVar (HsAppsTy [L _ (HsAppPrefix lty)])        = viewLHsTyVar lty
viewHsTyVar _                                         = Nothing

viewLHsTyVar :: LHsType pass -> Maybe (IdP pass)
viewLHsTyVar = viewHsTyVar . unLoc
