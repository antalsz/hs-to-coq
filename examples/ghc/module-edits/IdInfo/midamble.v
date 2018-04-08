Require GHC.Err.


Instance Default_TickBoxOp : GHC.Err.Default TickBoxOp :=
  GHC.Err.Build_Default _ (TickBox GHC.Err.default GHC.Err.default).

Instance Default_CafInfo : GHC.Err.Default CafInfo :=
  GHC.Err.Build_Default _ MayHaveCafRefs.

(*
Instance Default_IdInfo : GHC.Err.Default IdInfo :=
  GHC.Err.Build_Default _ (Mk_IdInfo GHC.Err.default GHC.Err.default GHC.Err.default
                         GHC.Err.default GHC.Err.default GHC.Err.default GHC.Err.default
                         GHC.Err.default GHC.Err.default GHC.Err.default).
*)