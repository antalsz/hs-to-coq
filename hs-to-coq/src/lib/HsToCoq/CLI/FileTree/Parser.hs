{-# LANGUAGE FlexibleContexts #-}

module HsToCoq.CLI.FileTree.Parser (
  -- * Parsers
  fileTree, fileTrees,
  -- * File name/path components
  isFilenameChar, filenameChar, filename, simpleRelativePath,
  -- * Whitespace and comments
  comment, skipToBOL,
  -- * Convenience function for non-Parsec users
  parseFileTrees
) where

import Data.Functor
import HsToCoq.Util.Functor
import Control.Applicative
import Data.Bifunctor

import Data.Maybe
import HsToCoq.Util.List
import Data.List.NonEmpty (NonEmpty(..))

import HsToCoq.Util.Char

import Text.Parsec hiding ((<|>), many, optional)
import Text.Parsec.Indent
import HsToCoq.Util.Parsec

import HsToCoq.CLI.FileTree

--------------------------------------------------------------------------------

isFilenameChar :: Char -> Bool
isFilenameChar c = not $ isVSpace c || c == '\0' || c == '/'

filenameChar :: Stream s m Char => ParsecT s u m Char
filenameChar = satisfy isFilenameChar <?> "filename character"

filename :: Stream s m Char => ParsecT s u m FilePath
filename = some filenameChar

simpleRelativePath :: Stream s m Char => ParsecT s u m (NonEmpty FilePath)
simpleRelativePath = (:|) <$> filename <*> many (try $ char '/' *> filename)

comment :: Stream s m Char => ParsecT s u m ()
comment = char '#' *> skipMany (satisfy $ not . isVSpace) *> eol
            <?> "comment"

skipToBOL :: Stream s m Char => ParsecT s u m ()
skipToBOL = eof <|> do
  hspaces
  void . optional $ do
    comment <|> eol
    skipToBOL

fileTree :: IndentStream s Char => IndentParser s u FileTree
fileTree = do
  (path, final) <- unsnocNEL <$> simpleRelativePath
  isDirectory   <- option False (True <$ char '/')
  eol *> skipToBOL
  
  let nest = foldr (\dir child -> Directory dir [child]) ?? path
  nest <$> if isDirectory
    then Directory final <$> option [] (indented *> block fileTree)
    else pure $ File final

fileTrees :: IndentStream s Char => IndentParser s u [FileTree]
fileTrees = skipToBOL *> option [] (same *> block fileTree)

parseFileTrees :: Maybe String -> String -> Either String [FileTree]
parseFileTrees src =
  first show . parseIndentParser (fileTrees <* eof) (fromMaybe "<input>" src)
