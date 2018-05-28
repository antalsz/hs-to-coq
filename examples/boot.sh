#!/bin/bash

set -e

if [ -z "USE_SYSTEM_HS_TO_COQ" ] && which stack >/dev/null
then
  echo "Rebuilding the tool"
  stack build
fi

cd $(dirname $0)


CLEAN=YES
COQ=YES

function clean () { if [ "$CLEAN" = "YES" ]; then "$@"; fi }
function coq ()   { if [ "$COQ"   = "YES" ]; then "$@"; fi }

while [ -n "$1" ]
do
 if [ "$1" = "noclean" ]
 then
   echo "Skipping cleaning"
   CLEAN=NO
 elif [ "$1" = "nocoq" ]
 then
   echo "Skipping running Coq"
   COQ=NO
 else
   echo "Unknown option $1"
   exit 1
 fi
 shift
done

function check_coq_version() {
  if ! which coqc >/dev/null
  then
    echo "No coqc in the path. Did you forget to run . <(opam config env)?"
    exit 1
  fi
  if ! coqc --version | grep -q -F '8.7.2'
  then
    echo "coqc does not seem to be version 8.7.2. Did you forget to run . <(opam config env)?"
    exit 1
  fi
}

coq check_coq_version

clean echo "Cleaning everything"
clean make -C tests clean
clean make -C base-tests clean
clean make -C successors clean
clean make -C intervals clean
clean make -C compiler clean
clean make -C dlist clean
clean make -C rle clean
clean make -C bag clean
clean make -C quicksort clean
clean make -C coinduction clean
clean make -C ../base-thy clean
clean make -C containers clean
clean make -C containers/theories clean
clean make -C ghc/theories clean

if [[ -e base-src/base ]]
then
	echo "Regenerating ../base"
	clean make -C base-src clean
	make -C base-src vfiles
else
	echo "Rebuiding ../base"
	clean make -C ../base clean
fi
coq make -C ../base

coq echo "Building ../base-thy"
coq make -C ../base-thy

coq echo "Building examples"
coq make -C base-tests
coq make -C successors
coq make -C intervals
coq make -C compiler
coq make -C rle
coq make -C bag
coq make -C quicksort
coq make -C dlist
coq make -C coinduction
make -C containers vfiles
coq make -C containers coq
coq make -C containers/theories

if [[ -e transformers/transformers ]]
then
	echo "Regenerating transformers"
	clean make -C transformers clean
	make -C transformers vfiles
else
	echo "Rebuiding transformers/lib"
	clean make -C transformers/lib clean
fi
coq make -C transformers coq

if [[ -e ghc/ghc ]]
then
	echo "Regenerating ghc"
	clean make -C ghc clean
	make -C ghc vfiles
else
	echo "Rebuiding ghc/lib"
	clean make -C ghc/lib clean
fi
coq make -C ghc/lib
coq make -C ghc/theories
