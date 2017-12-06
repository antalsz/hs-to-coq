Axiom uniqAway' : InScopeSet -> Var.Var -> Var.Var.

(*
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

Require Panic.

Instance Default_InScopeSet : Panic.Default InScopeSet :=
  Panic.Build_Default _ (InScope Panic.default Panic.default).
Instance Default_RnEnv2 : Panic.Default RnEnv2 :=
  Panic.Build_Default _ (RV2 Panic.default Panic.default Panic.default).

(* needs UniqFM.plusUFM_CD *)
Parameter plusVarEnv_CD : forall {a}, (a -> a -> a) -> VarEnv a -> a -> VarEnv
                               a -> a -> VarEnv a.
