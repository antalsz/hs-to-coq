Here we support extraction for the Coq-ified version of the containers
library. 

The extraction process is specified in the file `extracted-src/Extract.v`

NOTE: you must use stack to make sure that you use the right version of 
GHC (8.4.3), the base libraries (4.11.1.0) and containers (0.5.11.0).

# install and run

- make sure that `base/` and `containers/lib/` is up to date 

- type `make` in the `containers/extraction/extracted-src/` directory 
  This will extract Haskell modules from the containers/lib .v files.
  
  Use fixcode.pl script to add missing imports to a few extracted files.
	  Ascii.hs
	  QArith_base.hs
	  Real.hs

- `stack build` 

- `stack test`

- `stack bench`

# The shim

The file `src/ExtractedSet.hs` is a "shim" file that restores the original
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

   SetProperties.hs  is derived from `../containers/tests/set-properties.hs`
   Bench.hs is derived from `../containers/benchmarks/Set.hs` 

