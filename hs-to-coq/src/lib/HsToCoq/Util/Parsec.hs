{-# LANGUAGE ConstraintKinds, FlexibleContexts #-}

module HsToCoq.Util.Parsec (
  -- * Parsers
  eol,
  hspace, hspaces, hspaces1,
  vspace, vspaces, vspaces1,
  -- * Working with indent parsers
  IndentStream, runIndentParser
) where

import Data.Functor
import HsToCoq.Util.Char
import Text.Parsec hiding (State())
import Text.Parsec.Indent
import Control.Monad.Trans.State.Lazy (State())

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

type IndentStream s t = Stream s (State SourcePos) t

runIndentParser :: IndentStream s t
                => IndentParser s () a -> SourceName -> s -> Either ParseError a
runIndentParser p src = runIndent src . runParserT p () src
