#!/bin/bash

set -e

if [ -z "$NO_BUILD_HS_TO_COQ" ] && which stack >/dev/null
then
  echo "Rebuilding the tool"
  stack build
fi

cd $(dirname $0)


CLEAN=YES
COQ=YES
COQ_TEST=YES
COQ_VERSION=8.8

function clean ()    { if [ "$CLEAN"    = "YES" ]; then "$@"; fi }
function coq ()      { if [ "$COQ"      = "YES" ]; then "$@"; fi }
function coq-test () { if [ "$COQ_TEST" = "YES" ]; then "$@"; fi }

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
   COQ_TEST=NO
 elif [ "$1" = "quick" ]
 then
   echo "Skipping cleaning and tests"
   CLEAN=NO
   COQ_TEST=NO
 elif [ "$1" = "help" ]
 then
   echo "Possible options:"
   echo "  - noclean: Don't clean"
   echo "  - nocoq:   Don't run Coq"
   echo "  - quick:   Don't clean or run tests"
   echo "  - help:    Print this help message"
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
  if ! coqc --version | grep -q -F "$COQ_VERSION"
  then
    echo "coqc does not seem to be version $COQ_VERSION. Did you forget to run . <(opam config env)?"
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
clean make -C core-semantics clean
clean make -C base-src clean
clean make -C transformers clean
clean make -C ghc clean

make -C base-src vfiles
coq make -C ../base
coq make -C ../base-thy
coq-test make -C base-tests

make -C containers vfiles
coq make -C containers coq
coq make -C containers/theories
make -C transformers vfiles
coq make -C transformers coq
#coq make -C transformers/theories no theories yet
make -C ghc vfiles
coq make -C ghc/lib
coq make -C ghc/theories
make -C core-semantics vfiles
coq make -C core-semantics/lib
#coq make -C core-semantics/theories theories yet

coq make -C successors
coq make -C intervals
coq make -C compiler
coq make -C rle
coq make -C bag
coq make -C quicksort
coq make -C dlist
coq make -C coinduction
