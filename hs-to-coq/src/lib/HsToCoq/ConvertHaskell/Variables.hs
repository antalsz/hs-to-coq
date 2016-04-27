{-# LANGUAGE MultiWayIf, OverloadedStrings, FlexibleContexts #-}

module HsToCoq.ConvertHaskell.Variables (
  -- * Generate variable names
  var,
  freeVar', freeVar,
  -- * Avoiding reserved words/names
  tryEscapeReservedWord, escapeReservedNames,
  -- * Anonymous variables
  anonymousArg, anonymousArg'
  ) where

import Control.Lens
import Data.Semigroup (Semigroup(..))
import Data.Monoid hiding ((<>))
import Data.Maybe
import Data.String
import Data.Text (Text)
import qualified Data.Text as T
import Numeric.Natural

import Control.Monad

import GHC hiding (Name)
import Outputable (OutputableBndr)

import HsToCoq.Util.GHC

import HsToCoq.Coq.Gallina
import HsToCoq.ConvertHaskell.Monad

--------------------------------------------------------------------------------

tryEscapeReservedWord :: Ident -> Ident -> Maybe Ident
tryEscapeReservedWord reserved name = do
  suffix <- T.stripPrefix reserved name
  guard $ T.all (== '_') suffix
  pure $ name <> "_"

escapeReservedNames :: Ident -> Ident
escapeReservedNames x =
  fromMaybe x . getFirst $
    foldMap (First . flip tryEscapeReservedWord x) (T.words "Set Type Prop fun fix forall") <>
    if | T.all (== '.') x -> pure $ T.map (const '∘') x
       | T.all (== '∘') x -> pure $ "⟨" <> x <> "⟩"
       | otherwise        -> mempty

--------------------------------------------------------------------------------

freeVar' :: Ident -> Ident
freeVar' = escapeReservedNames

freeVar :: (GhcMonad m, OutputableBndr name) => name -> m Ident
freeVar = fmap freeVar' . ghcPpr
                                        
var :: (ConversionMonad m, OutputableBndr name) => HsNamespace -> name -> m Ident
var ns x = do
  x' <- ghcPpr x -- TODO Check module part?
  use $ renaming ns x' . non (escapeReservedNames x')

--------------------------------------------------------------------------------

anonymousArg' :: (IsString s, Semigroup s) => Maybe Natural -> s
anonymousArg' mn = "__arg" <> maybe "" (("_" <>) . fromString . show) mn <> "__"
{-# SPECIALIZE anonymousArg' :: Maybe Natural -> String #-}
{-# SPECIALIZE anonymousArg' :: Maybe Natural -> Text #-}

anonymousArg :: (IsString s, Semigroup s) => Natural -> s
anonymousArg = anonymousArg' . Just
{-# INLINABLE anonymousArg #-}
{-# SPECIALIZE anonymousArg :: Natural -> String #-}
{-# SPECIALIZE anonymousArg :: Natural -> Text #-}
