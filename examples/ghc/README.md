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

Also need to have a the compiled source to ghc-8.0.2 available.  This working
copy needs to be configured for certain header files to be present.

 * `ghc`: Create a symlink to a checkout of `ghc`, e.g.
   `your/path/ghc-8.0.2`.

Use `make` to build. As with other parts of this repo, requires Coq-8.6 and
ssreflect.

What's here
-----------

 * `lib`: Output of compilation
 * `Makefile`: Lists the files injected from GHC and also
   the hand-written Coq (e.g. proofs) files you include
 * `edits`: Top level edit file
 * `module-edits/*`: Per-module edits, `preamble.v` and `midamble.v`
 * `manual`:  Hand generated versions of some modules
