{-# LANGUAGE MultiWayIf, OverloadedStrings, FlexibleContexts #-}

module HsToCoq.ConvertHaskell.Variables (
  -- * Generate variable names
  var', var, var_,
  freeVar', freeVar,
  -- * Avoiding reserved words/names
  tryEscapeReservedWord, escapeReservedNames
  ) where

import Control.Lens
import Data.Semigroup (Semigroup(..))
import Data.Monoid hiding ((<>))
import Data.Maybe
import qualified Data.Text as T

import Control.Monad

import GHC hiding (Name)
import qualified GHC
import Outputable (OutputableBndr)
import Name hiding (Name)

import HsToCoq.Util.GHC

import HsToCoq.Coq.Gallina
import HsToCoq.ConvertHaskell.Parameters.Renamings
import HsToCoq.ConvertHaskell.Monad

--------------------------------------------------------------------------------

tryEscapeReservedWord :: Ident -> Ident -> Maybe Ident
tryEscapeReservedWord reserved name = do
  suffix <- T.stripPrefix reserved name
  guard $ T.all (== '_') suffix
  pure $ name <> "_"

-- convert a haskell identifier to a Gallina identifier.
--   (a) avoiding certain Gallina reserved words and library definitions
--   (b) converting some operators into Gallina ops (such as composition)
escapeReservedNames :: Ident -> Ident
escapeReservedNames x =
  fromMaybe x . getFirst $
    foldMap (First . flip tryEscapeReservedWord x)
            (T.words "Set Type Prop fun fix forall return mod as cons pair nil")
    <> if | T.all (== '.') x  -> pure $ T.map (const '∘') x
          | T.all (== '∘') x  -> pure $ "⟨" <> x <> "⟩"
-- these type operators aren't parsed by the renaming file
          | x == "(->)"       -> pure $ ("[->]")
          | x == "(,)"        -> pure $ ("[,]")
-- Maybe add this as part of an Int# solution? But don't want to
-- always replace these, if we make "Int#" a notation for "Int_h"
--          | T.isInfixOf "#" x -> pure $ T.replace "#" "_h" x
          | otherwise         -> mempty

--------------------------------------------------------------------------------

freeVar' :: Ident -> Ident
freeVar' = escapeReservedNames

freeVar :: (GhcMonad m, OutputableBndr name) => name -> m Ident
freeVar = fmap freeVar' . ghcPpr

var' :: ConversionMonad m => HsNamespace -> Ident -> m Ident
var' ns x = use $ renamed ns x . non (escapeReservedNames x)

-- This is dishonest: it should return a Qualid for qualified names
var :: ConversionMonad m => HsNamespace -> GHC.Name -> m Ident
var _ns name = do
  thisModM <- use currentModule
  let nameModM = moduleName <$> nameModule_maybe name
      mod | thisModM /= nameModM, Just nameMod <- nameModM
            = T.snoc (T.pack $ moduleNameString nameMod) '.'
          | otherwise
            = ""
  
  let nameBase = T.pack . occNameString $ nameOccName name
      base     = escapeReservedNames nameBase
  
  pure $ mod <> base
  
var_ :: (ConversionMonad m, HasOccName name, OutputableBndr name) => HsNamespace -> name -> m Ident
var_ ns name =
  let ns' | ns == TypeNS && occNameSpace (occName name) `nameSpacesRelated` dataName = ExprNS
          | otherwise                                                                = ns
  in var' ns' =<< ghcPpr name -- TODO Check module part?
