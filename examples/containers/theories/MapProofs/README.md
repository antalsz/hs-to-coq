This directory contains our specifications and proofs for `Data.Map`. We divide
them into multiple files because they would otherwise be too big to be fit into
a single file.

This README will give you a brief summary of what each file contains:
* `Bounds.v` contains:
  - definitions, lemmas, and tactics related to the bounds of the map,
  - definitions, lemmas, and tactics related to `Desc` and `WF`, and
  - top-level theorems and proofs of operations `null`, `singleton`, `balanceL`,
    `balanceR`, `balance`, `link`, `insertMax`, `insertMin`, and `link`.
* `LookupProofs.v` contains top-level theorems and proofs of operations
  `lookup`, `member`, `notMember`, `findWithDefault`, `lookupLT`, and
  `lookupLE`.
* `InsertProofs.v` contains top-level theorems and proofs of operations
  `insert`, `insertWith`, `insertWithKey`, `insertLookupWithKey`, and `insertR`.
* `MaxMinProofs.v` contains top-level theorems and proofs of operations
  `maxViewSure`, `maxViewWithKey`, `maxView`, `minViewSure`, `minViewWithKey`,
  `minView`, `lookupMaxSure`, `lookupMax`, `lookupMin`, and `lookupMinSure`.
* `DeleteUpdateProofs.v` contains top-level theorems and proofs of operations
  `glue`, `delete`, `deleteMin`, `deleteMax`, `adjustWithKey`, `adjust`,
  `updateWithKey`, `update`, `updateLookupWithKey`, and `alter`.
* `UnionIntersectDifferenceProofs.v` contains top-level theorems and proofs of
  operations `split`, `splitLookup`, `splitMember`, `union`, `unions`,
  `unionWith`, `unionWithKey`, `unionsWith`, `insertWithR`, `insertWithKeyR`,
  `link2`, `intersection`, `intersectionWith`, `intersectionWithKey`, and
  `difference`.
* `ToListProofs.v` contains
   - theorems and proofs of operations `foldrWithKey`, `foldr`, `foldr'`,
     `foldlWithKey`, `foldl`, `foldl'`, `elems`, `keys`, `assoc`, `toDescList`,
     `size`, and `(==)` and
   - many theorems related to `toList`.
