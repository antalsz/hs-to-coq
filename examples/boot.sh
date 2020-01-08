#!/bin/bash

set -e

################################################################################
## Arguments and configuring what does/doesn't get done

CLEAN=YES
COQ=YES
COQ_TEST=YES
COQ_VERSION=8.10

function clean ()    { if [ "$CLEAN"    = "YES" ]; then "$@"; fi }
function coq ()      { if [ "$COQ"      = "YES" ]; then "$@"; fi }
function coq-test () { if [ "$COQ_TEST" = "YES" ]; then "$@"; fi }

function usage () {
    echo "Usage: $0 [OPTION]"
    echo
    echo "Possible options:"
    echo "  - full:    Clean, run Coq, and run tests [default]"
    echo "  - noclean: Don't clean"
    echo "  - nocoq:   Don't run Coq"
    echo "  - quick:   Don't clean or run tests"
    echo "  - help:    Print this help message"
}

case $# in
  0)
    OPTION='full'
    ;;
  1)
    OPTION=$1
    ;;
  *)
    echo "Too many arguments"
    echo
    usage
    exit 1
esac

case $OPTION in
  full)
    echo "Doing everything"
    ;;
  noclean)
    echo "Skipping cleaning"
    CLEAN=NO
    ;;
  nocoq)
    echo "Skipping running Coq"
    COQ=NO
    COQ_TEST=NO
    ;;
  quick)
    echo "Skipping cleaning and tests"
    CLEAN=NO
    COQ_TEST=NO
    ;;
  help|--help|-h)
    usage
    exit 0
    ;;
  *)
    echo "Unknown option $1"
    echo
    usage
    exit 1
esac

################################################################################
## Rebuild what's requested

cd $(dirname $0)

if [ -z "$NO_BUILD_HS_TO_COQ" ] && which stack >/dev/null
then
  echo "Rebuilding the tool if necessary"
  stack build
fi

function have () { command -v "$1" >/dev/null 2>&1 ; }

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
have ruby         && clean make -C ../emacs clean
have sphinx-build && clean make -C ../doc   clean

have ruby         && make -C ../emacs
have sphinx-build && make -C ../doc html

coq-test make -C tests

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
