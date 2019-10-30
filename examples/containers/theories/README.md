This directory contains the specifications and proofs of [the translated Gallina
code](../lib) of Haskell's `containers` library.

We have formalized and proved a representative subset of three modules. They can
be found in:
* <SetProofs.v> for `Data.Set`,
* <IntSetProofs.v> for `Data.IntSet`, and
* <MapProofs> for `Data.Map` (formalizations for `Data.Map` is too big so we
  divided it into several files under one directory).

There is also a small subset of specifications and proofs for `Data.IntMap` in
`IntMapProofs.v`.

All the files follow the same naming convention for theorems. Most top-level
theorems will start with the operations they specify, with `_Desc` as their
suffixes. For example, the top-level theorem of `insert` operation is named
`insert_Desc`. A few operations do not have theorems in the form of `Desc`: they
are specified in terms of equality or iff relations with other terms. These
theorems also start with the names of the operations, with `_spec` as their
suffixes (for example, `member_spec`).

Each file contains some comments explaining what has been formalized and
contains some instructions on how to navigate there. Formalizations for
`Data.Map` has its own README file [here](MapProofs/README.md).
