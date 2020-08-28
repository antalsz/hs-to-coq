{-# LANGUAGE CPP #-}

module HsToCoq.Util.GHC.HsTypes (
  module HsTypes,
  viewHsTyVar, viewLHsTyVar,
  selectorFieldOcc_, fieldOcc,
  noExtCon
) where

#if __GLASGOW_HASKELL__ >= 806 && __GLASGOW_HASKELL__ < 810
import GHC.Stack (HasCallStack)
#endif
#if __GLASGOW_HASKELL__ >= 810
import GHC.Hs.Extension
import GHC.Hs.Types as HsTypes
#else
import HsExtension
import HsTypes
#endif
import RdrName (RdrName)
import Name (Name)
import SrcLoc

viewHsTyVar :: HsType pass -> Maybe (IdP pass)
#if __GLASGOW_HASKELL__ >= 806
viewHsTyVar (HsTyVar _ _ (L _ name))                  = Just name
#else
viewHsTyVar (HsTyVar _ (L _ name))                    = Just name
viewHsTyVar (HsAppsTy [L _ (HsAppInfix  (L _ name))]) = Just name
viewHsTyVar (HsAppsTy [L _ (HsAppPrefix lty)])        = viewLHsTyVar lty
#endif
viewHsTyVar _                                         = Nothing

viewLHsTyVar :: LHsType pass -> Maybe (IdP pass)
viewLHsTyVar = viewHsTyVar . unLoc

-- Compatibility shim for FieldOcc (the fields were flipped since GHC 8.6)
#if __GLASGOW_HASKELL__ >= 806
selectorFieldOcc_ :: FieldOcc GhcRn -> Name
selectorFieldOcc_ (FieldOcc n _) = n
selectorFieldOcc_ (XFieldOcc v) = noExtCon v

fieldOcc :: Located RdrName -> Name -> FieldOcc GhcRn
fieldOcc r n = FieldOcc n r

#if __GLASGOW_HASKELL__ < 810
noExtCon :: HasCallStack => NoExt -> a
noExtCon _ = error "cannot happen"
#endif
#else
selectorFieldOcc_ :: FieldOcc GhcRn -> Name
selectorFieldOcc_ (FieldOcc _ n) = n

fieldOcc :: Located RdrName -> Name -> FieldOcc GhcRn
fieldOcc = FieldOcc

noExtCon :: ()  -- dummy to not have to put a CPP conditional in the export list
noExtCon = ()
#endif
