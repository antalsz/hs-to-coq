#!/bin/bash

set -e

if which stack >/dev/null
then
  echo "Rebuilding the tool"
  stack build
fi

echo "Cleaning everything"
make -C examples/tests clean
make -C examples/base-thy clean
make -C examples/successors clean
make -C examples/compiler clean
make -C examples/rle clean
make -C examples/bag clean
make -C examples/ghc clean

if -e examples/ghc-base/ghc
then
	echo "Regenerating examples/ghc-base/lib"
	rm -rf examples/ghc-base/lib/
	make -C examples/ghc-base
else
	echo "Rebuiding examples/ghc-base/lib"
	make -C examples/ghc-base/lib/ -f Makefile.coq clean
	make -C examples/ghc-base/lib/ -f Makefile.coq
fi

echo "Building base-thy"
make -C examples/base-thy
