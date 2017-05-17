# hs-to-coq

## Setup (run once)

```
stack setup
```

## Build and run

```
stack build
stack exec hs-to-coq -- -I $GHC_PATH/compiler -I $GHC_PATH/compiler/stage2 -I $GHC_PATH/compiler/stage2/build -o $OUTPUT_FILE -p $PREAMBLE -r $RENAMINGS -e $EDITS -m $MODULES -d $GHC_PATH $INPUT_FILES
```

## Example command line

```
stack exec hs-to-coq -- -I ~/prog/ghc/compiler -I ~/prog/ghc/compiler/stage2 -I ~/prog/ghc/compiler/stage2/build -o test.v -p preamble.v -r renamings.txt -e edits.txt -m modules.txt -d ~/prog/ghc
```

-----

## GHC version

* Use [GHC 8.0.2](https://www.haskell.org/ghc/download_ghc_8_0_2.html) for
  compilation (handled by Stack) and translation

## Files:

* `preamble.v`: Coq code inserted at the start of the injected output

* `renamings.txt`: Simple renamings from Haskell to Coq (e.g., Haskell `Bool` is
  Coq `bool`)

* `edits.txt`: Various ways the injected Coq code should be different than the
  input Haskell code.  Documentation on the different kinds of edits is
  forthcoming.

* `modules.txt`/`call-arity-modules.txt`: Module file trees to be used when
  translating GHC source code; `modules.txt` is in some sense the transitive
  closure from `CoreSyn`, and `call-arity-modules.txt` is the transitive closure
  from `CallArity`.
