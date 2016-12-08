module HsToCoq.ConvertHaskell.Parameters.Parsers.Lexing (
  -- * Lexing and tokens
  Token(..), tokenDescription,
  token, token', tokens,
  -- * Character categories
  isHSpace, isVSpace, isDigit, isWordInit, isWord, isOperator, isOpen, isClose,
) where

import Prelude hiding (Num())

import Data.Foldable
import Control.Monad
import HsToCoq.Util.Monad
import Control.Monad.Trans.Parse
import Data.Char
import HsToCoq.Util.Char

import qualified Data.Text as T

import HsToCoq.Coq.Gallina

--------------------------------------------------------------------------------
-- Lexing-specific character categories
--------------------------------------------------------------------------------

isWordInit :: Char -> Bool
isWordInit c = isAlpha c || c == '_'

isWord :: Char -> Bool
isWord c = isAlphaNum c || c == '_' || c == '\''

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

-- We differentiate between two kinds of @.@: word-dot (as in @Lists.list@) and
-- symbol-dot (as in @x .+. y@ or @Inductive unit : Type := tt.@).  This is a
-- horrible hack.

token' :: Monad m => ParseT m (Maybe Token)
token' = asum $
  [ parseToken              (const Nothing)            (is '#')   (not . isVSpace)
  , parseToken              (const Nothing)            isHSpace   isHSpace
  , parseToken              (Just . const TokNewline)  isVSpace   none
  , parseToken              (Just . TokNat   . readT)  isDigit    isDigit
  , parseToken              (Just . TokOpen  . T.head) isOpen     none
  , parseToken              (Just . TokClose . T.head) isClose    none
  , parseToken              (Just . TokWord)           isWordInit isWord
  , parseCharTokenLookahead (Just . TokWord)           (is '.')   (exists isWordInit)
  , parseToken              (Just . TokOp)             isOperator isOperator
  , Just TokEOF <$ (guard =<< atEOF) ]
  where
    none   = const False
    is     = (==)
    exists = maybe False
    readT  = read . T.unpack

token :: Monad m => ParseT m Token
token = untilJustM token'

tokens :: Monad m => ParseT m [Token]
tokens = do
  tok <- token
  (tok :) <$> if tok == TokEOF then pure [] else tokens
