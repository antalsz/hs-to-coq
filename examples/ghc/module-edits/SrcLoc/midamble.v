(* Default values *)
Require Import GHC.Err.
Instance Default_SrcSpan : Default SrcSpan := Build_Default _ (UnhelpfulSpan default).
