{-# LANGUAGE MultiWayIf, OverloadedStrings, FlexibleContexts #-}

module HsToCoq.ConvertHaskell.Variables (
  -- * Generate variable names
  var', var, recordField,
  freeVar', freeVar,
  -- * Avoiding reserved words/names
  tryEscapeReservedWord, escapeReservedNames,
  qualifyWithCurrentModule
  ) where

import Control.Lens
import Data.Semigroup (Semigroup(..))
import Data.Monoid hiding ((<>))
import Data.Maybe
import qualified Data.Text as T

import Control.Applicative
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

var' :: ConversionMonad m => HsNamespace -> Ident -> m Ident
var' ns x = use $ renamed ns x . non (escapeReservedNames x)

-- This is dishonest: it should return a Qualid for qualified names
var :: ConversionMonad m => HsNamespace -> GHC.Name -> m Ident
var ns name = do
  thisModM <- fmap moduleNameText <$> use currentModule
  let nameModM = moduleNameText . moduleName <$> nameModule_maybe name

  let mod = nameModM

      qual | thisModM == nameModM = ""
           | otherwise            = fromMaybe "" mod

      base = T.pack . occNameString $ nameOccName name

  let localize q = case (identToQualid q, thisModM) of
        (Just (Qualified m b), Just thisMod) | qualidToIdent m == thisMod -> b
        _                                                                 -> q

      "" <.> b = b
      q  <.> b = q <> "." <> b
      tryRenamed = fmap (fmap localize) . use . renamed ns
      (<<|>>) = liftA2 (<|>)

  fmap (fromMaybe $ qual <.> escapeReservedNames base)
    $     maybe (pure Nothing) (tryRenamed . (<.> base)) mod
    <<|>> tryRenamed (qual <.> base)

recordField :: (ConversionMonad m, HasOccName name, OutputableBndr name) => name -> m Ident
recordField = var' ExprNS <=< ghcPpr -- TODO Check module part?

-- This un-does what var does. It is all a big mess at this point...
qualifyWithCurrentModule :: ConversionMonad m => Ident -> m Ident
qualifyWithCurrentModule n = do
  thisMod <- moduleNameText . fromMaybe (error "no current module") <$> use currentModule
  case identToQualid n of
    Just (Qualified _ _) -> return n
    Just (Bare b)        -> return $ thisMod <> "." <> b
    _ -> error $ "qualifyWithCurrentModule: Not an indent: " ++ T.unpack n

