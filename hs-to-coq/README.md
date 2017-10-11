# hs-to-coq

## Setup (run once)

```
stack setup
```

## Build and run

```
stack build
stack exec hs-to-coq -- -I $GHC_PATH/compiler -I $GHC_PATH/compiler/stage2 -I $GHC_PATH/compiler/stage2/build -o $OUTPUT_FILE -p $PREAMBLE -e $EDITS -m $MODULES -d $GHC_PATH --ghc-tree $GHC_PATH $INPUT_FILES
```

## Example command line

```
stack exec hs-to-coq -- -I ~/prog/ghc/compiler -I ~/prog/ghc/compiler/stage2 -I ~/prog/ghc/compiler/stage2/build -o test.v -p preamble.v -e edits.txt -m modules.txt -d ~/prog/ghc --ghc-tree ~/prog/ghc --ghc -DSTAGE=2
```

## GHC API

```
https://downloads.haskell.org/~ghc/8.0.2/docs/html/libraries/ghc-8.0.2/
```

## GHC version

* Use [GHC 8.0.2](https://www.haskell.org/ghc/download_ghc_8_0_2.html) for
  compilation (handled by Stack) and translation

## Examples:

* [ghc-base](examples/ghc-base) GHC base library `base-4.9.1.0`.

* [successors](examples/successors) Successors Monad

* [compiler](examples/compiler) Hutton's razor

* [bag](examples/bag) Multiset implementation
