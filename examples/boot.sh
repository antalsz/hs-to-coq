#!/bin/bash

set -e

if which stack >/dev/null
then
  echo "Rebuilding the tool"
  stack build
fi

echo "Cleaning everything"
make -C tests clean
make -C successors clean
make -C compiler clean
make -C rle clean
make -C bag clean
make -C ghc clean
make -C ../base-thy clean

if [[ -e base-src/base ]]
then
	echo "Regenerating ../base"
	rm -rf ../base
	make -C base-src
else
	echo "Rebuiding ../base"
	make -C ../base clean
	make -C ../base
fi

echo "Building ../base-thy"
make -C ../base-thy
