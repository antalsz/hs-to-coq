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

import qualified Data.Text as T

import HsToCoq.Coq.Gallina

--------------------------------------------------------------------------------
-- Character categories
--------------------------------------------------------------------------------

isHSpace :: Char -> Bool
isHSpace '\t' = True
isHSpace c    = generalCategory c == Space

isVSpace :: Char -> Bool
isVSpace '\n'   = True
isVSpace '\v'   = True
isVSpace '\f'   = True
isVSpace '\r'   = True
isVSpace '\x85' = True -- NEL
isVSpace c      = case generalCategory c of
                    LineSeparator      -> True
                    ParagraphSeparator -> True
                    _                  -> False

isWordInit :: Char -> Bool
isWordInit c = isAlpha c || c == '_'

isWord :: Char -> Bool
isWord c = isAlphaNum c || c == '_' || c == '\''

isOperator :: Char -> Bool
isOperator c =
  c /= '_' && c /= '\'' &&
  generalCategory c `elem` [ ConnectorPunctuation, DashPunctuation, OtherPunctuation
                           , MathSymbol, CurrencySymbol, ModifierSymbol, OtherSymbol ]

isOpen :: Char -> Bool
isOpen c = generalCategory c == OpenPunctuation

isClose :: Char -> Bool
isClose c = generalCategory c == ClosePunctuation

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

token' :: Monad m => ParseT m (Maybe Token)
token' = asum $
  [ parseToken (const Nothing)            (is '#')   (not . isVSpace)
  , parseToken (const Nothing)            isHSpace   isHSpace
  , parseToken (Just . const TokNewline)  isVSpace   none
  , parseToken (Just . TokNat   . readT)  isDigit    isDigit
  , parseToken (Just . TokOpen  . T.head) isOpen     none
  , parseToken (Just . TokClose . T.head) isClose    none
  , parseToken (Just . TokWord)           isWordInit isWord
  , parseToken (Just . TokOp)             isOperator isOperator
  , Just TokEOF <$ (guard =<< atEOF) ]
  where
    none  = const False
    is    = (==)
    readT = read . T.unpack

token :: Monad m => ParseT m Token
token = untilJustM token'

tokens :: Monad m => ParseT m [Token]
tokens = do
  tok <- token
  (tok :) <$> if tok == TokEOF then pure [] else tokens
