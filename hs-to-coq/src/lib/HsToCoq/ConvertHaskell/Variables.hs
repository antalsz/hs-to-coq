{-# LANGUAGE MultiWayIf, OverloadedStrings, FlexibleContexts, LambdaCase #-}

module HsToCoq.ConvertHaskell.Variables (
  -- * Generate variable names
  var', var, recordField,
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
import HsToCoq.Util.GHC.Module

import HsToCoq.Coq.Gallina
import HsToCoq.Coq.Gallina.Util
import HsToCoq.ConvertHaskell.Parameters.Edits
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
            (T.words "Set Type Prop fun fix forall return mod as cons pair nil for is")
    <> if | T.all (== '.') x  -> pure $ T.map (const '∘') x
          | T.all (== '∘') x  -> pure $ "⟨" <> x <> "⟩"
-- these type operators aren't parsed by the renaming file
          | x == "(->)"       -> pure $ ("arrow")
          | x == "(,)"        -> pure $ ("pair_type")
          | x == "#."         -> pure $ ("hash_compose")  -- Data.Foldable
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


-- Removes the module prefix if this is in the current module
localize :: ConversionMonad m => Ident -> m Ident
localize q = do
  thisModM <- fmap moduleNameText <$> use currentModule
  pure $ case (identToQualid q, thisModM) of
    (Just (Qualified m b), Just thisMod) | qualidToIdent m == thisMod -> b
    _                                                                 -> q

-- This is dishonest: it should return a Qualid for qualified names
var :: ConversionMonad m => HsNamespace -> GHC.Name -> m Ident
var ns name = do
  let nameModM = moduleNameText . moduleName <$> nameModule_maybe name
  let base = T.pack . occNameString $ nameOccName name
  let escaped_base = escapeReservedNames base

  case nameModM of
    Just mod -> do
        -- The name has a module, so it (or at least may be) a global name
        let escapedQualName = mod <> "." <> escaped_base
            qualName        = mod <> "." <> base
        -- So look the _unescaped_ qualified name up in the renaming
        use (renamed ns qualName) >>= \case
            Just r ->  localize r
            Nothing -> localize escapedQualName
        -- A local name, no module. Not much to do here.
    Nothing -> pure escaped_base

recordField :: (ConversionMonad m, HasOccName name, OutputableBndr name) => name -> m Ident
recordField = var' ExprNS <=< ghcPpr -- TODO Check module part?
