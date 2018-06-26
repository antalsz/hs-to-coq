Coq’ified base library
======================

This directory contains beginnings a coqified version of the `Prelude` and
assorted bits of `base`.

We have the following directories:

 * `base`: A pristine check-out of base
 * `gen-files`: Additionaly artifacts that are produced when building base,
    included here for convenience.
 * `edits`: Global edit file
 * `module-edits/Foo/Bar/`: Edit files (`edit` and `preamble.v`) for `Foo.Bar`.
 * `drop-in/Foo/Bar.hs`: Manually edited Haskell file, to replace
    `base/Foo/Bar.hs`.
 * `manual/Foo/Bar.v`: Manually created `.v` files.
 * `../../base`: Output, including `_CoqProject`

The generated files in `../../base/` are added to the repository for two reasons:
 * So that `hs-to-coq` is usable translating `base`.
 * So that we can how its output changes.
