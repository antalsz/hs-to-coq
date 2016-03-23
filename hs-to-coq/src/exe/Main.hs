module Main (main) where

import HsToCoq.Util.GHC
import HsToCoq.ConvertHaskell
import HsToCoq.CLI

main :: IO ()
main = defaultRunGhc . evalConversion $ processFilesMain convertDecls
