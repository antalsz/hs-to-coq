This directory contains the specifications and proofs of [the
translated Gallina code](../lib) of Haskell's `containers` library.

We have formalized and proved a representative subset of three
modules, namely: [`Data.Set`](SetProofs.v),
[`Data.IntSet`](IntSetProofs.v), and [`Data.Map`](MapProofs/); as well
as small subset of [`Data.IntMap`](IntMapProofs.v).

All the files follow the same naming convention for theorems.  Most
top-level theorems will start with the operations they specify, with
the suffix `_Desc`. For example, the top-level theorem of `insert`
operation is named `insert_Desc`. A few operations do not have
theorems in the form of `Desc`: they are specified in terms of
equality or iff relations with other terms. These theorems also start
with the names of the operations, with `_spec` as their suffixes (for
example, `member_spec`).
