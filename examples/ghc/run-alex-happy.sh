#!/bin/sh

# You probably don't need to run this -- this is how we generate some of the
# `gen-files` we need for GHC

alex ghc/compiler/parser/Lexer.x
alex ghc/compiler/cmm/CmmLex.x

happy -agc --strict ghc/compiler/parser/Parser.y
happy -agc --strict ghc/compiler/cmm/CmmParse.y
