{-# LANGUAGE LambdaCase, OverloadedStrings #-}

module HsToCoq.ConvertHaskell.InfixNames (
  identIsVariable, identIsOperator,
  infixToPrefix, toPrefix,
  infixToCoq, toCoqName,
  canonicalName,
  splitModule -- a bit out of place here. oh well.
  ) where

import Control.Lens

import Control.Applicative
import Data.Semigroup (Semigroup(..))
import Data.Maybe
import Data.Char
import Data.Text (Text)
import qualified Data.Text as T
import Text.Parsec hiding ((<|>), many)

import Encoding (zEncodeString)

import GHC.Stack

--------------------------------------------------------------------------------

-- Lets keep this module self-contained (but use the same type synonyms)
type Op = T.Text
type Ident = T.Text
type ModuleIdent = T.Text
type AccessIdent = T.Text

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

-- This is code smell: Why do we return an unstructured Ident, and not a QualId?
infixToCoq :: HasCallStack => Op -> Ident
infixToCoq op = case splitModule op of
    Just (m,op) -> m <> "." <> infixToCoq_ op
    Nothing     -> infixToCoq_ op

splitModule :: Ident -> Maybe (ModuleIdent, AccessIdent)
splitModule = either (const Nothing) Just . parse qualid "" where
  qualid = do
    let modFrag = T.cons <$> upper <*> (T.pack <$> many (alphaNum <|> char '\''))
    mod <- T.intercalate "." <$> many1 (try (modFrag <* char '.'))
    base <- T.pack <$> some anyChar -- since we're assuming we get a valid name
    pure $ (mod, base)

toCoqName :: Op -> Ident
toCoqName x | identIsVariable x = x
            | otherwise         = infixToCoq x

canonicalName :: Op -> Ident
canonicalName x
  | identIsVariable x = x
  | otherwise         = infixToCoq . fromMaybe x $ T.stripPrefix "_" =<< T.stripSuffix "_" x
