# hs-to-coq

This repository contains a converter from Haskell code to equivalent Coq code,
as part of the [CoreSpec] component of the [DeepSpec] project.

It it described in the CPP'18 paper “Total Haskell is Reasonable Coq” by
Antal Spector-Zabusky, Joachim Breitner, Christine Rizkallah, and Stephanie Weirich.

# Requirements

`hs-to-coq` uses GHC-8.0 (which 

# Compilation

The recommended way of building `hs-to-coq` is to use `stack`. If you have not
setup stack before, run:

   stack setup

To build `hs-to-coq`, then run

   stack build

# Building the `base` library

This repository comes with a version of (parts of the) Haskell base library
converted to Coq, which you will likely need if you want to verify Haskell
code. You can build it with

   make -C base

Th directory `base-thy/` contains auxillary definitions and lemmas, such as
lawful type-class instances. You can build these with

   make -C base-thy

# Using the tool

To use the tool, run it (using `stack`), passing the Haskell file to be
translated and an output directory to write to:

  stack exec hs-to-coq -- -o output-directory/ Input/File.hs

Very likely you want to make use of the `base/` library. In that case, make
sure you pass `-e base/edits`.

Have a look at the example directories, e.g. `examples/successors`, for a
convenient `Makefile` based setup.

# Other directories

* The `examples/` directories contains a number of example translation and
  verification projects, including

  * [successors](examples/successors) Successors Monad
  * [compiler](examples/compiler) Hutton's razor
  * [bag](examples/bag) Multiset implementation
  * [quicksort](examples/quicksort) Quicksort
  * [rle](examples/rle) Run-length encoding
  * [tests](examples/tests) Simple unit-tests
  * [base-src](examples/base-src) The sources of the `base/` directory

* `structural-isomorphism-plugin`: (In progress.)  A GHC plugin that connects
   the re-extracted converted code back into GHC, allowing us to run Haskell
   programs against verified/verifiable code.  Currently does not work.


[CoreSpec]: https://deepspec.org/entry/Project/Haskell+CoreSpec
[DeepSpec]: http://www.deepspec.org/

