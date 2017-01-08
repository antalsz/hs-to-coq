#!/bin/zsh
stack exec hs-to-coq -- -I ~/prog/ghc/compiler -I ~/prog/ghc/compiler/stage2 -I ~/prog/ghc/compiler/stage2/build -o simple.v -p preamble.v -r renamings.txt Simple.hs
