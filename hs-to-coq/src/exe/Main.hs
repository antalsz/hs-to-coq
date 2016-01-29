module Main (main) where

import HsToCoq.Util.GHC
import HsToCoq.CLI

main :: IO ()
main = defaultRunGhc $ processFilesMain convertDataDecls
