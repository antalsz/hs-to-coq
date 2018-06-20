Coqified ghc core
=================

This directory contains the beginnings of a coqified version of GHC's core
language.

Compilation
-----------

This directory depends on ghc's `base` and `containers` libraries. Before
compiling here make sure those libraries have already been compiled.

  * make -C ../../base
  * make -C ../containers

What's here
-----------

 * `ghc`: A pristine check-out of GHC
 * `gen-files`: Additionaly artifacts that are produced when building GHC,
    included here for convenience.
 * `lib`: Output of compilation
 * `Makefile`: Lists the files injected from GHC and also
   the hand-written Coq (e.g. proofs) files you include
 * `edits`: Top level edit file
 * `module-edits/*`: Per-module edits, `preamble.v` and `midamble.v`
 * `manual`:  Hand generated versions of some modules
