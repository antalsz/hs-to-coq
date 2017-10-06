#!/bin/bash

set -e

if which stack >/dev/null
then
  echo "Rebuilding the tool"
  stack build
fi

echo "Cleaning everything"
make -C tests clean
make -C base-thy clean
make -C successors clean
make -C compiler clean
make -C rle clean
make -C bag clean
make -C ghc clean

if -e ghc-base/base
then
	echo "Regenerating ghc-base/lib"
	rm -rf ghc-base/lib/
	make -C ghc-base
else
	echo "Rebuiding ghc-base/lib"
	make -C ghc-base/lib/ -f Makefile.coq clean
	make -C ghc-base/lib/ -f Makefile.coq
fi

echo "Building base-thy"
make -C base-thy
