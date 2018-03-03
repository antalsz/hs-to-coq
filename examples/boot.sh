#!/bin/bash

set -e

if which stack >/dev/null
then
  echo "Rebuilding the tool"
  stack build
fi

cd $(dirname $0)

echo "Cleaning everything"
make -C tests clean
make -C base-tests clean
make -C successors clean
make -C intervals clean
make -C compiler clean
make -C rle clean
make -C bag clean
make -C ../base-thy clean
make -C containers/theories clean

if [[ -e base-src/base ]]
then
	echo "Regenerating ../base"
	make -C base-src clean
	make -C base-src
else
	echo "Rebuiding ../base"
	make -C ../base clean
	make -C ../base
fi

echo "Building ../base-thy"
make -C ../base-thy

echo "Building examples"
make -C base-tests
make -C successors
make -C intervals
make -C compiler
make -C rle
make -C bag
make -C quicksort

if [[ -e containers/containers ]]
then
	echo "Regenerating containers"
	make -C containers clean
	make -C containers
else
	echo "Rebuiding containers/lib"
	make -C containers/lib clean
	make -C containers/lib
fi
make -C containers/theories


if [[ -e ghc/ghc ]]
then
	echo "Regenerating ghc"
	make -C ghc clean
	make -C ghc
else
	echo "Rebuiding ghc/lib"
	make -C ghc/lib clean
	make -C ghc/lib
fi
