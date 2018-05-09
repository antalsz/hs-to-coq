(*Axiom uniqAway' : InScopeSet -> Core.Var -> Core.Var.
  fun arg_55__ arg_56__ =>
    match arg_55__ , arg_56__ with
      | InScope set n , var =>
        let orig_unique := Unique.getUnique var in
        let try :=
            fix try k
              := let uniq := Unique.deriveUnique orig_unique (n GHC.Num.* k) in
                 if VarSet.elemVarSetByKey uniq set : bool
                 then try (k GHC.Num.+ GHC.Num.fromInteger 1)
                 else Var.setVarUnique var uniq in
        try (GHC.Num.fromInteger 1)
    end.
*)

Require GHC.Err.

Instance Default__InScopeSet : GHC.Err.Default InScopeSet :=
  GHC.Err.Build_Default _ (InScope GHC.Err.default GHC.Err.default).
Instance Default__RnEnv2 : GHC.Err.Default RnEnv2 :=
  GHC.Err.Build_Default _ (RV2 GHC.Err.default GHC.Err.default GHC.Err.default).
Instance Default__TidyEnv : GHC.Err.Default TidyEnv.
Admitted.


(* needs UniqFM.plusUFM_CD *)
(*
Parameter plusVarEnv_CD : forall {a}, (a -> a -> a) -> VarEnv a -> a -> VarEnv
                               a -> a -> VarEnv a. *)
