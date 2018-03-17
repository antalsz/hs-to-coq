Require Import Coq.ZArith.BinInt.
Require GHC.Err.

Definition bitSlice {a} `{Data.Bits.Bits a} `{GHC.Num.Num a}
   : a -> GHC.Num.Int -> GHC.Num.Int -> a.
Admitted.
