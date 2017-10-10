{-# LANGUAGE LambdaCase, OverloadedStrings #-}

module HsToCoq.ConvertHaskell.InfixNames (
  identIsVariable, identIsOperator,
  infixToPrefix, toPrefix,
  infixToCoq, toCoqName,
  canonicalName
  ) where

import Control.Lens

import Data.Semigroup (Semigroup(..))
import Data.Maybe
import Data.Char
import Data.Text (Text)
import qualified Data.Text as T

import Encoding (zEncodeString)

import HsToCoq.Coq.Gallina
import HsToCoq.Coq.Gallina.Util

--------------------------------------------------------------------------------

identIsVariable_ :: Text -> Bool
identIsVariable_ = T.uncons <&> \case
  Just (h,t) -> (isAlpha h || h == '_') && T.all (\c -> isAlphaNum c || c == '_' || c == '\'') t
  Nothing    -> False

identIsVariable :: Text -> Bool
identIsVariable = all identIsVariable_ . T.splitOn "."

identIsOperator :: Text -> Bool
identIsOperator = not . identIsVariable

-- An operator's user-facing name in Coq (a notation)
infixToPrefix :: Op -> Ident
infixToPrefix = ("_" <>) . (<> "_")

toPrefix :: Ident -> Ident
toPrefix x | identIsVariable x = x
           | otherwise         = infixToCoq x

-- An operator's defined name in Coq (hidden by a notation)
infixToCoq_ :: Op -> Ident
infixToCoq_ name = "op_" <> T.pack (zEncodeString $ T.unpack name) <> "__"

infixToCoq :: Op -> Ident
infixToCoq op =
  maybe (infixToCoq_ op) (qualidToIdent . qualidMapBase infixToCoq_) $ identToQualid op

toCoqName :: Op -> Ident
toCoqName x | identIsVariable x = x
            | otherwise         = infixToCoq x

canonicalName :: Op -> Ident
canonicalName x
  | identIsVariable x = x
  | otherwise         = infixToCoq . fromMaybe x $ T.stripPrefix "_" =<< T.stripSuffix "_" x
