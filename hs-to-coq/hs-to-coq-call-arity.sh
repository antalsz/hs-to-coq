#!/bin/zsh

./hs-to-coq-ghc.sh \
  $1 \
  -p preamble.v -r renamings.txt -e edits.txt -m call-arity-modules.txt \
  ${@:2}
