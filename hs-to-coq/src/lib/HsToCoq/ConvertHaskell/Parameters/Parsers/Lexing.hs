{-# LANGUAGE TupleSections, LambdaCase #-}

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
import HsToCoq.Util.Foldable
import Control.Applicative
import Control.Monad
import HsToCoq.Util.Monad
import Control.Monad.Trans.Parse
import Data.Char
import HsToCoq.Util.Char

import Data.Text (Text)
import qualified Data.Text as T

import HsToCoq.Coq.Gallina
import HsToCoq.Coq.Gallina.Util

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
empty_brackets :: Monad m => Char -> Char -> ParseT m Text
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

uword, word, op, unit, nil :: Monad m => ParseT m Ident
uword = parseToken id isUpper    isWord
word  = parseToken id isWordInit isWord
op    = parseToken id isOperator isOperator
unit  = empty_brackets '(' ')'
nil   = empty_brackets '[' ']'

unqualified :: Monad m => ParseT m (NameCategory, Ident)
unqualified = asumFmap (CatWord,) [word, unit, nil] <|> (CatSym,) <$> op

qualified :: Monad m => ParseT m (NameCategory, Qualid)
qualified = do
  root  <- uword
  guard =<< is (Just '.') <$> peekChar
  mods  <- many     $ parseChar (is '.') *> uword
  mbase <- optional $ parseChar (is '.') *> unqualified
  
  let (cat, base) = maybe (CatWord, []) (fmap pure) mbase
    
  pure . (cat,) . foldl' Qualified (Bare root) $ mods ++ base

qualid :: Monad m => ParseT m (NameCategory, Qualid)
qualid = qualified <|> fmap Bare <$> unqualified

comment, space, newline :: Monad m => ParseT m ()
comment = parseToken (const ()) (is '#') (not . isVSpace)
space   = parseToken (const ()) isHSpace isHSpace
newline = parseToken (const ()) isVSpace none

nat :: Monad m => ParseT m Num
nat = parseToken (read . T.unpack) isDigit isDigit

-- We differentiate between two kinds of @.@: word-dot (as in @Lists.list@) and
-- symbol-dot (as in @x .+. y@ or @Inductive unit : Type := tt.@).  This is a
-- horrible hack.

-- arguments from parseToken (from Control.Monad.Trans.Parse)
-- parseToken :: Monad m => (Text -> a)  -> (Char -> Bool) -> (Char -> Bool) -> ParseT m a
-- parseToken build isFirst isRest = ...

token' :: Monad m => ParseT m (Maybe Token)
token' = asum $
  [ Nothing          <$  comment
  , Nothing          <$  space
  , Just TokNewline  <$  newline
  , Just . TokNat    <$> nat
  , Just . TokOpen   <$> parseChar isOpen
  , Just . TokClose  <$> parseChar isClose
  , Just . nameToken <$> qualid'
  , Just TokEOF      <$  (guard =<< atEOF) ]
  where
    nameToken = uncurry $ \case
                  CatWord -> TokWord
                  CatSym  -> TokOp
    qualid'  = fmap qualidToIdent <$> qualid
      -- TODO: Fix when we have real qualid support

token :: Monad m => ParseT m Token
token = untilJustM token'

tokens :: Monad m => ParseT m [Token]
tokens = do
  tok <- token
  (tok :) <$> if tok == TokEOF then pure [] else tokens
