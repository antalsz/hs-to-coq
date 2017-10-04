#!/bin/zsh

./hs-to-coq-ghc.sh \
  $1 \
  -p preamble.v -e renamings.txt -e edits.txt $1/compiler/simplCore/CallArity.hs \
  ${@:2}
