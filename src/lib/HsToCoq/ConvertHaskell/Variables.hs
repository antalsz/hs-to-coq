{-# LANGUAGE MultiWayIf, LambdaCase, OverloadedStrings, FlexibleContexts #-}

module HsToCoq.ConvertHaskell.Variables (
  -- * Generate variable names
  var', var,
  unQualifyLocal,
  recordField, bareName,
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
import HsToCoq.ConvertHaskell.Parameters.Edits
import HsToCoq.ConvertHaskell.Monad
import HsToCoq.ConvertHaskell.InfixNames

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
          | x == "#."       -> pure $ ("hash_compose")  -- Data.Foldable
-- Maybe add this as part of an Int# solution? But don't want to
-- always replace these, if we make "Int#" a notation for "Int_h"
--          | T.isInfixOf "#" x -> pure $ T.replace "#" "_h" x
          | otherwise         -> mempty

--------------------------------------------------------------------------------

freeVar' :: Ident -> Ident
freeVar' = escapeReservedNames

freeVar :: (GhcMonad m, OutputableBndr name) => name -> m Ident
freeVar = fmap freeVar' . ghcPpr

-- Does not qualify with the module, does not look it up in renamings
-- (useful for locally bound names)
bareName :: GHC.Name -> Ident
bareName = toPrefix . escapeReservedNames . T.pack . occNameString . nameOccName

localName :: GHC.Name -> Ident
localName = toLocalPrefix . escapeReservedNames . T.pack . occNameString . nameOccName

var' :: ConversionMonad m => HsNamespace -> Ident -> m Qualid
var' ns x = use $ renamed ns (Bare x) . non (Bare (escapeReservedNames x))

unQualifyLocal :: ConversionMonad m => Qualid -> m Qualid
unQualifyLocal qi = do
  thisModM <- fmap moduleNameText <$> use currentModule
  case qi of
    -- Something in this module
    (Qualified m b) | Just m == thisModM -> pure (Bare b)
    -- Something bare (built-in or local) or external
    _                                    -> pure qi


var :: ConversionMonad m => HsNamespace -> GHC.Name -> m Qualid
var ns name = do
    renamed_qid <- use (renamed ns qid . non qid)
    pure renamed_qid
  where
    nameModM = moduleNameText . moduleName <$> nameModule_maybe name

    qid | Just m <- nameModM = Qualified m (bareName name)
        | otherwise          = Bare        (localName name)
recordField :: (ConversionMonad m, HasOccName name, OutputableBndr name) => name -> m Qualid
recordField = var' ExprNS <=< ghcPpr -- TODO Check module part?
