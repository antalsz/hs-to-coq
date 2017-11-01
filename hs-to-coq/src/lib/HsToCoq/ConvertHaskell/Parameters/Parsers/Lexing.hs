{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE TupleSections, LambdaCase, FlexibleContexts #-}
{-# LANGUAGE OverloadedStrings #-}

module HsToCoq.ConvertHaskell.Parameters.Parsers.Lexing (
  -- * Lexing and tokens
  Token(..), tokenDescription,
  token, token', tokens,
  -- * Character categories
  isHSpace, isVSpace, isDigit, isWordInit, isWord, isOperator, isOpen, isClose,
  -- * Component parsers
  -- ** Types
  NameCategory(..),
  -- ** Identifiers
  qualid, qualified, unqualified,
  -- ** Whitespace and comments
  comment, space, newline,
  -- ** Atomic components
  nat, uword, word, op, unit, nil
) where

import Prelude hiding (Num())

import Data.Foldable
import Data.Bifunctor (second)
import Data.Monoid
import HsToCoq.Util.Foldable
import HsToCoq.Util.Functor
import Control.Applicative
import Control.Monad
import HsToCoq.Util.Monad
import Control.Monad.State
import Control.Monad.Parse

import Data.Char
import HsToCoq.Util.Char

import Data.Text (Text)
import qualified Data.Text as T

import HsToCoq.Coq.Gallina

--------------------------------------------------------------------------------
-- Lexing-specific character categories
--------------------------------------------------------------------------------

isWordInit :: Char -> Bool
isWordInit c = isAlpha c || c == '_'

isWord :: Char -> Bool
isWord c = isAlphaNum c || c == '_' || c == '\'' || c == '#'

isOperator :: Char -> Bool
isOperator c =
  c /= '_' && c /= '\'' &&
  generalCategory c `elem` [ ConnectorPunctuation, DashPunctuation, OtherPunctuation
                           , MathSymbol, CurrencySymbol, ModifierSymbol, OtherSymbol ]

--------------------------------------------------------------------------------
-- Tokens
--------------------------------------------------------------------------------

data Token = TokWord    Ident
           | TokNat     Num
           | TokOp      Ident
           | TokOpen    Char
           | TokClose   Char
           | TokNewline
           | TokEOF
           deriving (Eq, Ord, Show, Read)

tokenDescription :: Token -> String
tokenDescription (TokWord    w) = "word `"              ++ T.unpack w ++ "'"
tokenDescription (TokNat     n) = "number `"            ++ show     n ++ "'"
tokenDescription (TokOp      o) = "operator `"          ++ T.unpack o ++ "'"
tokenDescription (TokOpen    o) = "opening delimeter `" ++ pure     o ++ "'"
tokenDescription (TokClose   c) = "closing delimeter `" ++ pure     c ++ "'"
tokenDescription TokNewline     = "newline"
tokenDescription TokEOF         = "end of file"

--------------------------------------------------------------------------------
-- Lexing
--------------------------------------------------------------------------------

-- Module-local
empty_brackets :: MonadParse m => Char -> Char -> m Text
empty_brackets open close = T.pack [open,close] <$ parseChar (== open)
                                                <* many (parseChar isSpace)
                                                <* parseChar (== close)

-- Module-local
none :: Char -> Bool
none = const False

-- Module-local
is :: Eq a => a -> a -> Bool
is = (==)

data NameCategory = CatWord | CatSym
                  deriving (Eq, Ord, Enum, Bounded, Show, Read)

uword, word, op, unit, nil :: MonadParse m => m Ident
uword = parseToken id isUpper    isWord
word  = parseToken id isWordInit isWord
op    = parseToken id isOperator isOperator
unit  = empty_brackets '(' ')'
nil   = empty_brackets '[' ']'

unqualified :: MonadParse m => m (NameCategory, Ident)
unqualified = asumFmap (CatWord,) [word, unit, nil] <|> (CatSym,) <$> op

qualified :: MonadParse m => m (NameCategory, Ident)
qualified = do
  root  <- uword
  _ <- parseChar (is '.')
  second ((root <> ".") <>) <$> qualid

qualid :: MonadParse m => m (NameCategory, Ident)
qualid = qualified <|> unqualified

comment, space, newline :: MonadParse m => m ()
comment = parseToken (const ()) (is '#') (not . isVSpace)
space   = parseToken (const ()) isHSpace isHSpace
newline = parseToken (const ()) isVSpace none

nat :: MonadParse m => m Num
nat = parseToken (read . T.unpack) isDigit isDigit

-- arguments from parseToken (from Control.Monad.Trans.Parse)
-- parseToken :: MonadParse m => (Text -> a)  -> (Char -> Bool) -> (Char -> Bool) -> m a
-- parseToken build isFirst isRest = ...

token' :: MonadNewlinesParse m => m (Maybe Token)
token' = asum $
  [ Nothing          <$  comment
  , Nothing          <$  space
  , newlineToken     <*  newline
  , Just . TokNat    <$> nat
  , Just . TokOpen   <$> parseChar isOpen
  , Just . TokClose  <$> parseChar isClose
  , Just . nameToken <$> qualid
  , Just TokEOF      <$  (guard =<< atEOF) ]
  where
    newlineToken = get <&> \case
                     NewlineSeparators -> Just TokNewline
                     NewlineWhitespace -> Nothing
    nameToken    = uncurry $ \case
                     CatWord -> TokWord
                     CatSym  -> TokOp

token :: MonadNewlinesParse m => m Token
token = untilJustM token'

tokens :: MonadNewlinesParse m => m [Token]
tokens = do
  tok <- token
  (tok :) <$> if tok == TokEOF then pure [] else tokens
