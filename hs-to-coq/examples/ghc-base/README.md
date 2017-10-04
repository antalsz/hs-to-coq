Coq’ified base library
======================

This directory contains beginnings a coqified version of the `Prelude` and
assorted bits of `base`.

We have the following directories:

 * `base`: Create a symlink to a checkout of `base`, e.g.
   `your/path/ghc-8.0/libraries/base`. This needs to be configured for certain
   header files to be present.
 * `edits`: Global edit file
 * `module-edits/Foo/Bar/`: Edit files (`edit` and `preamble.v`) for `Foo.Bar`.
 * `drop-in/Foo/Bar.hs`: Manually edited Haskell file, to replace
    `base/Foo/Bar.hs`.
 * `manual/Foo/Bar.v`: Manually created `.v` files.
 * `lib/`: Output, including `_CoqProject`

The generated files in `lib/` are added to the repository for two reasons:
 * So that `hs-to-coq` is usable without a source checkout of `base`.
 * So tht we can how its output changes.
