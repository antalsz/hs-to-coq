#!/bin/zsh

ghc_dir=$1
args=(${@:2})

include_dirs=( compiler compiler/stage2 compiler/stage2/build \
               includes/dist-derivedconstants/header )

import_dirs=( backpack basicTypes cmm codeGen coreSyn deSugar ghci hsSyn iface \
              llvmGen main nativeGen parser prelude profiling rename simplCore \
              simplStg specialise stgSyn stranal typecheck types utils \
              vectorise stage2/build )

stack exec hs-to-coq -- \
  -I$ghc_dir/$^include_dirs \
  -i$ghc_dir/compiler/$^import_dirs \
  --ghc -DSTAGE=2 \
  --ghc -package=ghc-boot-th \
  -d $ghc_dir \
  $args
