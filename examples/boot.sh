#!/bin/bash

set -e

if which stack >/dev/null
then
  echo "Rebuilding the tool"
  stack build
fi

cd $(dirname $0)


if [ "$1" = "noclean" ]
then
  echo "Skipping cleaning"
  shift
  function clean () { true ; }
else
  function clean () { "$@" ; }
fi

clean echo "Cleaning everything"
clean make -C tests clean
clean make -C base-tests clean
clean make -C successors clean
clean make -C intervals clean
clean make -C compiler clean
clean make -C rle clean
clean make -C bag clean
clean make -C ../base-thy clean
clean make -C containers/theories clean

if [[ -e base-src/base ]]
then
	echo "Regenerating ../base"
	clean make -C base-src clean
	make -C base-src
else
	echo "Rebuiding ../base"
	clean make -C ../base clean
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
	clean make -C containers clean
	make -C containers
else
	echo "Rebuiding containers/lib"
	clean make -C containers/lib clean
	make -C containers/lib
fi
make -C containers/theories


if [[ -e ghc/ghc ]]
then
	echo "Regenerating ghc"
	clean make -C ghc clean
	make -C ghc
else
	echo "Rebuiding ghc/lib"
	clean make -C ghc/lib clean
	make -C ghc/lib
fi
