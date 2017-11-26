{-# LANGUAGE ConstraintKinds, FlexibleContexts #-}

module HsToCoq.Util.Parsec (
  -- * Parsers
  eol,
  hspace, hspaces, hspaces1,
  vspace, vspaces, vspaces1,
  -- * Working with indent parsers
  IndentStream, IndentStreamT, parseIndentParser
) where

import Data.Functor
import Data.Functor.Identity

import Text.Parsec hiding (State())
import Text.Parsec.Indent

import HsToCoq.Util.Char

eol :: Stream s m Char => ParsecT s u m ()
eol = (void endOfLine <|> eof) <?> "end of line"

hspace :: Stream s m Char => ParsecT s u m Char
hspace = satisfy isHSpace <?> "horizontal whitespace"

hspaces :: Stream s m Char => ParsecT s u m ()
hspaces = skipMany hspace

hspaces1 :: Stream s m Char => ParsecT s u m ()
hspaces1 = skipMany1 hspace

vspace :: Stream s m Char => ParsecT s u m Char
vspace = satisfy isVSpace <?> "vertical whitespace"

vspaces :: Stream s m Char => ParsecT s u m ()
vspaces = skipMany vspace

vspaces1 :: Stream s m Char => ParsecT s u m ()
vspaces1 = skipMany1 vspace

type IndentStreamT m s t = Stream s (IndentT m) t
type IndentStream    s t = IndentStreamT Identity s t

parseIndentParser :: IndentStream s t
                => IndentParser s () a -> SourceName -> s -> Either ParseError a
parseIndentParser p = runIndentParser p ()
