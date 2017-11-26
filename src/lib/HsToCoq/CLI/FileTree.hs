{-# LANGUAGE FlexibleContexts #-}

module HsToCoq.CLI.FileTree (
  -- * Type
  FileTree(..),
  -- * Get out a list of files
  resolveFileTree, resolveFileTrees,
  -- * Pretty-printing
  displayFileTree, displayFileTrees
) where

import System.FilePath

data FileTree = File      FilePath
              | Directory FilePath [FileTree]
              deriving (Eq, Ord, Show, Read)

resolveFileTree :: FileTree -> [FilePath]
resolveFileTree (File file) =
  [file]
resolveFileTree (Directory dir children) =
  map (dir </>) $ resolveFileTrees children

resolveFileTrees :: [FileTree] -> [FilePath]
resolveFileTrees = concatMap resolveFileTree

displayFileTrees :: [FileTree] -> String
displayFileTrees = unlines . goForest 0 where
  indent n = (replicate n ' ' ++)

  go i (File      file)          = [indent i file]
  go i (Directory dir  children) = indent i (dir ++ "/") : goForest (i+2) children
  
  goForest = concatMap . go

displayFileTree :: FileTree -> String
displayFileTree = displayFileTrees . pure
