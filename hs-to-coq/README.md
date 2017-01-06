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
