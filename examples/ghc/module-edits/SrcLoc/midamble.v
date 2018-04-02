(* Default values *)
Require Import GHC.Err.
Instance Default__SrcSpan : Default SrcSpan := Build_Default _ (UnhelpfulSpan default).
