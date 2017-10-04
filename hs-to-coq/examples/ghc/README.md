Coq’ified ghc
===============

This directory contains beginnings a coqified version of GHC.

 * `ghc`: Create a symlink to a checkout of `ghc`, e.g.
   `your/path/ghc-8.0`.
   This working copy needs to be configured for certain header files to be
   present.
 * `Makefile`: List the files you want to inject from GHC and also
   the hand-written Coq (e.g. proofs) files you include
 * `edits`: Edit file
