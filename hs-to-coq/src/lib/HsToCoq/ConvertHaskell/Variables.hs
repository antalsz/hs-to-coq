{-# LANGUAGE LambdaCase, MultiWayIf,
             OverloadedStrings,
             FlexibleContexts #-}

module HsToCoq.ConvertHaskell.Variables (
  -- * Generate variable names
  var,
  freeVar', freeVar,
  -- * Avoiding reserved words/names
  tryEscapeReservedWord, escapeReservedNames,
  -- * Operators vs. variable names
  identIsVariable, identIsOperator,
  infixToPrefix, toPrefix,
  infixToCoq, toCoqName,
  -- * Anonymous variables
  anonymousArg, anonymousArg'
  ) where

import Data.Semigroup (Semigroup(..))
import Data.Monoid hiding ((<>))
import Data.Maybe
import Data.Char
import Data.String
import Data.Text (Text)
import qualified Data.Text as T
import Numeric.Natural

import Control.Monad
import Control.Monad.State

import qualified Data.Map.Strict as M

import GHC hiding (Name)
import Encoding (zEncodeString)
import Outputable (OutputableBndr)

import HsToCoq.Util.Functor
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
  gets $ fromMaybe (escapeReservedNames x') . (M.lookup ns <=< M.lookup x')

--------------------------------------------------------------------------------

identIsVariable :: Text -> Bool
identIsVariable = T.uncons <&> \case
  Just (h,t) -> (isAlpha h || h == '_') && T.all (\c -> isAlphaNum c || c == '_' || c == '\'') t
  Nothing    -> False

identIsOperator :: Text -> Bool
identIsOperator = not . identIsVariable

-- An operator's user-facing name in Coq (a notation)
infixToPrefix :: Op -> Ident
infixToPrefix = ("_" <>) . (<> "_")

toPrefix :: Ident -> Ident
toPrefix x | identIsVariable x = x
           | otherwise         = infixToPrefix x

-- An operator's defined name in Coq (hidden by a notation)
infixToCoq :: Op -> Ident
infixToCoq name = "__op_" <> T.pack (zEncodeString $ T.unpack name) <> "__"

toCoqName :: Op -> Ident
toCoqName x | identIsVariable x = x
            | otherwise         = infixToCoq x

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
