Here we support extraction for the Coq-ified version of the containers
library. 

# install and run

- make sure that `base/` and `containers/lib/` is up to date 

- type `make` in the `containers/extraction/src/` directory 

- `cabal install --enable-tests --enable-benchmarks --dependencies-only`

- `cabal bench`

- `cabal test`

# The shim

The file `ExtractedSet.hs` is a "shim" file that restores the original
interface of the library. 

- provides explicit type class dictionaries when
  necessary (Coq's extraction process compiles these away).
- create instances Eq, Ord, Semigroup, Monoid, Foldable from 
  Coq definitions
- add instances that were not translated (`NFData` and `Show`) that are
  needed for benchmarking and testing.
- convert between `Int` and `BinNums.Z`

# The tests/benchmarks

The benchmarks and test suite come directly from containers, with slight
modification (i.e. using ExtractedSet, `Bin` to `bin`, removing tests &
benchmarks for the untranslated functions).

   SetProperties.hs  is ../containers/tests/set-properties.hs
   Bench.hs is ../containers/benchmarks/Set.hs 

