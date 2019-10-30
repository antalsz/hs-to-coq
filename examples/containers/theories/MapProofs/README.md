This directory contains our specifications and proofs for `Data.Map`. We divide
them into multiple files because they would otherwise be too big to be fit into
a single file.

This README will give you a brief summary of what each file contains:
* `Bounds.v` contains:
  - definitions, lemmas, and tactics related to the bounds of the map,
  - definitions, lemmas, and tactics related to `Desc` and `WF`, and
  - theorems and proofs of operations `null`, `singleton`, `balanceL`,
    `balanceR`, `balance`, `link`, `insertMax`, `insertMin`, and `link`.
* `LookupProofs.v` contains theorems and proofs of operations `lookup`,
  `member`, `notMember`, `findWithDefault`, `lookupLT`, and `lookupLE`.
* `InsertProofs.v` contains top-level theorems and proofs of operations
  `insert`, `insertWith`, `insertWithKey`, `insertLookupWithKey`, and `insertR`.
* `MaxMinProofs.v` contains theorems and proofs of operations `maxViewSure`,
  `maxViewWithKey`, `maxView`, `minViewSure`, `minViewWithKey`, `minView`,
  `lookupMaxSure`, `lookupMax`, `lookupMin`, and `lookupMinSure`.
* `DeleteUpdateProofs.v` contains theorems and proofs of operations `glue`,
  `delete`, `deleteMin`, `deleteMax`, `adjustWithKey`, `adjust`,
  `updateWithKey`, `update`, `updateLookupWithKey`, and `alter`.
* `UnionIntersectDifferenceProofs.v` contains theorems and proofs of operations
  `split`, `splitLookup`, `splitMember`, `union`, `unions`, `unionWith`,
  `unionWithKey`, `unionsWith`, `insertWithR`, `insertWithKeyR`, `link2`,
  `intersection`, `intersectionWith`, `intersectionWithKey`, and `difference`.
* `ToListProofs.v` contains theorems and proofs of operations `foldrWithKey`,
   `foldr`, `foldr'`, `foldlWithKey`, `foldl`, `foldl'`, `elems`, `keys`,
   `assoc`, `toDescList`, `size`, `toList`, and `(==)`.
* `FromListProofs.v` contains theorems and proofs of operations
  `fromDistinctAscList`, `fromDistinctDescList`, `fromAscList`, `fromDescList`,
  and `fromList`.
* `FilterPartitionProofs.v` contains theorems and proofs of operations
  `isSubmapOfBy`, `isProperSubmapOfBy`, `isProperSubmapOf`, `filterWithKey`,
  `filter`, `partitionWithKey`, `partition`, `take`, `drop`.
* `MapFunctionProofs.v` contains theorems and proofs of operations `mapWithKey`,
    `map`, `mapAccumL`, `mapAccumWithKey`, `mapAccum`, `mapAccumRWithKey`,
    `mapKeys`, `mapKeysMonotonic`, `foldMapWithKey`, `mapMaybeWithKey`,
    `mapEitherWithKey`, `mapEither`, `splitRoot`, and `findIndex`.

Additionally,
* `TypeclassProofs.v` contains proofs that `Data.Map` satisfies certain type
  class laws, namely, `Eq` (`EqLaws_Map`), `Ord` (`OrdLaws_Map`), `Semigroup`
  (`SemigroupLaws_Map`), and `Functor` (`FunctorLaws_MapWF`).
* `InterfaceProofs.v` contains proofs that `Data.Map` satisfies Coq's
  `FMapInterface` (`MapFMap`).
* `ContainerFacts.v` contains a few theorems about `Data.Map` that we rely on in
  other verifications (esp. [on verifications of GHC](../../../ghc)).
