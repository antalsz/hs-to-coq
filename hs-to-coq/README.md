```
cabal install --only-dependencies
cabal build
./hs-to-coq -I$GHC_PATH/compiler -I$GHC_PATH/stage2 -o $OUTPUT_FILE $INPUT_FILES
```

Example:

```
cabal build && echo && ./hs-to-coq -I$HOME/prog/ghc/compiler -I$HOME/prog/ghc/compiler/stage2 -o test.v ~/prog/ghc/compiler/{basicTypes/{BasicTypes,Var,DataCon,ConLike,VarSet,VarEnv,SrcLoc},types/{TyCon,Class,Coercion,TyCoRep,CoAxiom},coreSyn/CoreSyn,profiling/CostCentre}.hs && echo && ./count-failures.pl test.v
```
