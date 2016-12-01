```
cabal install --only-dependencies
cabal build
./hs-to-coq -I$GHC_PATH/compiler -I$GHC_PATH/compiler/stage2 -o $OUTPUT_FILE -p $PREAMBLE -r $RENAMINGS -e $EDITS -m $MODULES -d $GHC_PATH $INPUT_FILES
```

Example:

```
./hs-to-coq -I$HOME/prog/ghc/compiler -I$HOME/prog/ghc/compiler/stage2 -o test.v -p preamble.v -r renamings.txt -e edits.txt -m modules.txt -d ~/prog/ghc
```
