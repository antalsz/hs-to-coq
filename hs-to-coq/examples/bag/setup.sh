#!/bin/bash
set -e
make -C ../ghc
cp -f ../ghc/MonadUtils.v ../ghc/Bag.v .
