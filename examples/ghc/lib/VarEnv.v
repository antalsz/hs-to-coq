(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Coq.Program.Tactics.
Require Coq.Program.Wf.

(* Preamble *)



(* Converted imports: *)

Require Data.Foldable.
Require Data.Tuple.
Require GHC.Base.
Require GHC.DeferredFix.
Require GHC.Err.
Require GHC.Num.
Require Maybes.
Require OccName.
Require Panic.
Require UniqDFM.
Require UniqFM.
Require UniqSet.
Require Unique.
Require Util.
Require Var.
Require VarSet.
Import GHC.Base.Notations.
Import GHC.Num.Notations.

(* Converted type declarations: *)

Definition VarEnv :=
  UniqFM.UniqFM%type.

Definition TyVarEnv :=
  VarEnv%type.

Definition TyCoVarEnv :=
  VarEnv%type.

Definition TidyEnv :=
  (OccName.TidyOccEnv * VarEnv Var.Var)%type%type.

Inductive InScopeSet : Type
  := InScope : VarSet.VarSet -> GHC.Num.Int -> InScopeSet.

Inductive RnEnv2 : Type
  := RV2 : VarEnv Var.Var -> VarEnv Var.Var -> InScopeSet -> RnEnv2.

Definition IdEnv :=
  VarEnv%type.

Definition DVarEnv :=
  UniqDFM.UniqDFM%type.

Definition DTyVarEnv :=
  DVarEnv%type.

Definition DIdEnv :=
  DVarEnv%type.

Definition CoVarEnv :=
  VarEnv%type.

Definition envL (arg_0__ : RnEnv2) :=
  let 'RV2 envL _ _ := arg_0__ in
  envL.

Definition envR (arg_0__ : RnEnv2) :=
  let 'RV2 _ envR _ := arg_0__ in
  envR.

Definition in_scope (arg_0__ : RnEnv2) :=
  let 'RV2 _ _ in_scope := arg_0__ in
  in_scope.
(* Midamble *)

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
Parameter plusVarEnv_CD : forall {a}, (a -> a -> a) -> VarEnv a -> a -> VarEnv
                               a -> a -> VarEnv a.

(* Converted value declarations: *)

(* Skipping instance Outputable__InScopeSet of class Outputable *)

Definition alterDVarEnv {a}
   : (option a -> option a) -> DVarEnv a -> Var.Var -> DVarEnv a :=
  UniqDFM.alterUDFM.

Definition alterVarEnv {a}
   : (option a -> option a) -> VarEnv a -> Var.Var -> VarEnv a :=
  UniqFM.alterUFM.

Definition anyDVarEnv {a} : (a -> bool) -> DVarEnv a -> bool :=
  UniqDFM.anyUDFM.

Definition dVarEnvElts {a} : DVarEnv a -> list a :=
  UniqDFM.eltsUDFM.

Definition delDVarEnv {a} : DVarEnv a -> Var.Var -> DVarEnv a :=
  UniqDFM.delFromUDFM.

Definition delDVarEnvList {a} : DVarEnv a -> list Var.Var -> DVarEnv a :=
  UniqDFM.delListFromUDFM.

Definition delInScopeSet : InScopeSet -> Var.Var -> InScopeSet :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | InScope in_scope n, v => InScope (VarSet.delVarSet in_scope v) n
    end.

Definition delVarEnv {a} : VarEnv a -> Var.Var -> VarEnv a :=
  UniqFM.delFromUFM.

Definition delVarEnvList {a} : VarEnv a -> list Var.Var -> VarEnv a :=
  UniqFM.delListFromUFM.

Definition delVarEnv_Directly {a} : VarEnv a -> Unique.Unique -> VarEnv a :=
  UniqFM.delFromUFM_Directly.

Definition disjointVarEnv {a} : VarEnv a -> VarEnv a -> bool :=
  UniqFM.disjointUFM.

Definition elemDVarEnv {a} : Var.Var -> DVarEnv a -> bool :=
  UniqDFM.elemUDFM.

Definition elemInScopeSet : Var.Var -> InScopeSet -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | v, InScope in_scope _ => VarSet.elemVarSet v in_scope
    end.

Definition rnInScope : Var.Var -> RnEnv2 -> bool :=
  fun x env => elemInScopeSet x (in_scope env).

Definition elemVarEnv {a} : Var.Var -> VarEnv a -> bool :=
  UniqFM.elemUFM.

Definition inRnEnvL : RnEnv2 -> Var.Var -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | RV2 env _ _, v => elemVarEnv v env
    end.

Definition inRnEnvR : RnEnv2 -> Var.Var -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | RV2 _ env _, v => elemVarEnv v env
    end.

Definition elemVarEnvByKey {a} : Unique.Unique -> VarEnv a -> bool :=
  UniqFM.elemUFM_Directly.

Definition emptyDVarEnv {a} : DVarEnv a :=
  UniqDFM.emptyUDFM.

Definition emptyInScopeSet : InScopeSet :=
  InScope VarSet.emptyVarSet #1.

Definition emptyVarEnv {a} : VarEnv a :=
  UniqFM.emptyUFM.

Definition mkRnEnv2 : InScopeSet -> RnEnv2 :=
  fun vars => RV2 emptyVarEnv emptyVarEnv vars.

Definition nukeRnEnvL : RnEnv2 -> RnEnv2 :=
  fun env =>
    let 'RV2 envL_0__ envR_1__ in_scope_2__ := env in
    RV2 emptyVarEnv envR_1__ in_scope_2__.

Definition nukeRnEnvR : RnEnv2 -> RnEnv2 :=
  fun env =>
    let 'RV2 envL_0__ envR_1__ in_scope_2__ := env in
    RV2 envL_0__ emptyVarEnv in_scope_2__.

Definition emptyTidyEnv : TidyEnv :=
  pair OccName.emptyTidyOccEnv emptyVarEnv.

Definition extendDVarEnv {a} : DVarEnv a -> Var.Var -> a -> DVarEnv a :=
  UniqDFM.addToUDFM.

Definition extendDVarEnvList {a}
   : DVarEnv a -> list (Var.Var * a)%type -> DVarEnv a :=
  UniqDFM.addListToUDFM.

Definition extendDVarEnv_C {a}
   : (a -> a -> a) -> DVarEnv a -> Var.Var -> a -> DVarEnv a :=
  UniqDFM.addToUDFM_C.

Definition extendInScopeSet : InScopeSet -> Var.Var -> InScopeSet :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | InScope in_scope n, v =>
        InScope (VarSet.extendVarSet in_scope v) (n GHC.Num.+ #1)
    end.

Definition delBndrR : RnEnv2 -> Var.Var -> RnEnv2 :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | (RV2 _ env in_scope as rn), v =>
        let 'RV2 envL_2__ envR_3__ in_scope_4__ := rn in
        RV2 envL_2__ (delVarEnv env v) (extendInScopeSet in_scope v)
    end.

Definition delBndrL : RnEnv2 -> Var.Var -> RnEnv2 :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | (RV2 env _ in_scope as rn), v =>
        let 'RV2 envL_2__ envR_3__ in_scope_4__ := rn in
        RV2 (delVarEnv env v) envR_3__ (extendInScopeSet in_scope v)
    end.

Definition extendInScopeSetList : InScopeSet -> list Var.Var -> InScopeSet :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | InScope in_scope n, vs =>
        InScope (Data.Foldable.foldl (fun s v => VarSet.extendVarSet s v) in_scope vs)
        (n GHC.Num.+ Data.Foldable.length vs)
    end.

Definition delBndrsR : RnEnv2 -> list Var.Var -> RnEnv2 :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | (RV2 _ env in_scope as rn), v =>
        let 'RV2 envL_2__ envR_3__ in_scope_4__ := rn in
        RV2 envL_2__ (delVarEnvList env v) (extendInScopeSetList in_scope v)
    end.

Definition delBndrsL : RnEnv2 -> list Var.Var -> RnEnv2 :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | (RV2 env _ in_scope as rn), v =>
        let 'RV2 envL_2__ envR_3__ in_scope_4__ := rn in
        RV2 (delVarEnvList env v) envR_3__ (extendInScopeSetList in_scope v)
    end.

Definition extendInScopeSetSet : InScopeSet -> VarSet.VarSet -> InScopeSet :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | InScope in_scope n, vs =>
        InScope (VarSet.unionVarSet in_scope vs) (n GHC.Num.+ UniqSet.sizeUniqSet vs)
    end.

Definition addRnInScopeSet : RnEnv2 -> VarSet.VarSet -> RnEnv2 :=
  fun env vs =>
    if VarSet.isEmptyVarSet vs : bool then env else
    let 'RV2 envL_0__ envR_1__ in_scope_2__ := env in
    RV2 envL_0__ envR_1__ (extendInScopeSetSet (in_scope env) vs).

Definition extendVarEnv {a} : VarEnv a -> Var.Var -> a -> VarEnv a :=
  UniqFM.addToUFM.

Definition extendVarEnvList {a}
   : VarEnv a -> list (Var.Var * a)%type -> VarEnv a :=
  UniqFM.addListToUFM.

Definition extendVarEnv_Acc {a} {b}
   : (a -> b -> b) -> (a -> b) -> VarEnv b -> Var.Var -> a -> VarEnv b :=
  UniqFM.addToUFM_Acc.

Definition extendVarEnv_C {a}
   : (a -> a -> a) -> VarEnv a -> Var.Var -> a -> VarEnv a :=
  UniqFM.addToUFM_C.

Definition extendVarEnv_Directly {a}
   : VarEnv a -> Unique.Unique -> a -> VarEnv a :=
  UniqFM.addToUFM_Directly.

Definition filterDVarEnv {a} : (a -> bool) -> DVarEnv a -> DVarEnv a :=
  UniqDFM.filterUDFM.

Definition filterVarEnv {a} : (a -> bool) -> VarEnv a -> VarEnv a :=
  UniqFM.filterUFM.

Definition filterVarEnv_Directly {a}
   : (Unique.Unique -> a -> bool) -> VarEnv a -> VarEnv a :=
  UniqFM.filterUFM_Directly.

Definition restrictVarEnv {a} : VarEnv a -> VarSet.VarSet -> VarEnv a :=
  fun env vs =>
    let keep :=
      fun arg_0__ arg_1__ =>
        match arg_0__, arg_1__ with
        | u, _ => VarSet.elemVarSetByKey u vs
        end in
    filterVarEnv_Directly keep env.

Definition foldDVarEnv {a} {b} : (a -> b -> b) -> b -> DVarEnv a -> b :=
  UniqDFM.foldUDFM.

Definition getInScopeVars : InScopeSet -> VarSet.VarSet :=
  fun arg_0__ => let 'InScope vs _ := arg_0__ in vs.

Definition isEmptyDVarEnv {a} : DVarEnv a -> bool :=
  UniqDFM.isNullUDFM.

Definition isEmptyVarEnv {a} : VarEnv a -> bool :=
  UniqFM.isNullUFM.

Definition intersectsVarEnv {a} : VarEnv a -> VarEnv a -> bool :=
  fun e1 e2 => negb (isEmptyVarEnv (UniqFM.intersectUFM e1 e2)).

Definition lookupDVarEnv {a} : DVarEnv a -> Var.Var -> option a :=
  UniqDFM.lookupUDFM.

Definition modifyDVarEnv {a} : (a -> a) -> DVarEnv a -> Var.Var -> DVarEnv a :=
  fun mangle_fn env key =>
    match (lookupDVarEnv env key) with
    | None => env
    | Some xx => extendDVarEnv env key (mangle_fn xx)
    end.

Definition lookupInScope : InScopeSet -> Var.Var -> option Var.Var :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | InScope in_scope _, v => VarSet.lookupVarSet in_scope v
    end.

Definition lookupRnInScope : RnEnv2 -> Var.Var -> Var.Var :=
  fun env v => Maybes.orElse (lookupInScope (in_scope env) v) v.

Definition lookupInScope_Directly
   : InScopeSet -> Unique.Unique -> option Var.Var :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | InScope in_scope _, uniq => VarSet.lookupVarSet_Directly in_scope uniq
    end.

Definition lookupVarEnv {a} : VarEnv a -> Var.Var -> option a :=
  UniqFM.lookupUFM.

Definition rnOccL : RnEnv2 -> Var.Var -> Var.Var :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | RV2 env _ _, v => Maybes.orElse (lookupVarEnv env v) v
    end.

Definition rnOccL_maybe : RnEnv2 -> Var.Var -> option Var.Var :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | RV2 env _ _, v => lookupVarEnv env v
    end.

Definition rnOccR : RnEnv2 -> Var.Var -> Var.Var :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | RV2 _ env _, v => Maybes.orElse (lookupVarEnv env v) v
    end.

Definition rnOccR_maybe : RnEnv2 -> Var.Var -> option Var.Var :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | RV2 _ env _, v => lookupVarEnv env v
    end.

Definition modifyVarEnv {a} : (a -> a) -> VarEnv a -> Var.Var -> VarEnv a :=
  fun mangle_fn env key =>
    match (lookupVarEnv env key) with
    | None => env
    | Some xx => extendVarEnv env key (mangle_fn xx)
    end.

Definition lookupVarEnv_Directly {a} : VarEnv a -> Unique.Unique -> option a :=
  UniqFM.lookupUFM_Directly.

Definition lookupVarEnv_NF {a} `{_ : GHC.Err.Default a} (env : VarEnv a) id
   : a :=
  match lookupVarEnv env id with
  | Some xx => xx
  | None => GHC.Err.default
  end.

Definition lookupWithDefaultVarEnv {a} : VarEnv a -> a -> Var.Var -> a :=
  UniqFM.lookupWithDefaultUFM.

Definition mapDVarEnv {a} {b} : (a -> b) -> DVarEnv a -> DVarEnv b :=
  UniqDFM.mapUDFM.

Definition mapVarEnv {a} {b} : (a -> b) -> VarEnv a -> VarEnv b :=
  UniqFM.mapUFM.

Definition minusDVarEnv {a} {a'} : DVarEnv a -> DVarEnv a' -> DVarEnv a :=
  UniqDFM.minusUDFM.

Definition minusVarEnv {a} {b} : VarEnv a -> VarEnv b -> VarEnv a :=
  UniqFM.minusUFM.

Definition mkDVarEnv {a} : list (Var.Var * a)%type -> DVarEnv a :=
  UniqDFM.listToUDFM.

Definition mkInScopeSet : VarSet.VarSet -> InScopeSet :=
  fun in_scope => InScope in_scope #1.

Definition mkVarEnv {a} : list (Var.Var * a)%type -> VarEnv a :=
  UniqFM.listToUFM.

Definition zipVarEnv {a} : list Var.Var -> list a -> VarEnv a :=
  fun tyvars tys =>
    mkVarEnv (Util.zipEqual (GHC.Base.hs_string__ "zipVarEnv") tyvars tys).

Definition mkVarEnv_Directly {a} : list (Unique.Unique * a)%type -> VarEnv a :=
  UniqFM.listToUFM_Directly.

Definition modifyVarEnv_Directly {a}
   : (a -> a) -> UniqFM.UniqFM a -> Unique.Unique -> UniqFM.UniqFM a :=
  fun mangle_fn env key =>
    match (UniqFM.lookupUFM_Directly env key) with
    | None => env
    | Some xx => UniqFM.addToUFM_Directly env key (mangle_fn xx)
    end.

Definition partitionDVarEnv {a}
   : (a -> bool) -> DVarEnv a -> (DVarEnv a * DVarEnv a)%type :=
  UniqDFM.partitionUDFM.

Definition partitionVarEnv {a}
   : (a -> bool) -> VarEnv a -> (VarEnv a * VarEnv a)%type :=
  UniqFM.partitionUFM.

Definition plusDVarEnv {a} : DVarEnv a -> DVarEnv a -> DVarEnv a :=
  UniqDFM.plusUDFM.

Definition plusDVarEnv_C {a}
   : (a -> a -> a) -> DVarEnv a -> DVarEnv a -> DVarEnv a :=
  UniqDFM.plusUDFM_C.

Definition plusMaybeVarEnv_C {a}
   : (a -> a -> option a) -> VarEnv a -> VarEnv a -> VarEnv a :=
  UniqFM.plusMaybeUFM_C.

Definition plusVarEnv {a} : VarEnv a -> VarEnv a -> VarEnv a :=
  UniqFM.plusUFM.

Definition plusVarEnvList {a} : list (VarEnv a) -> VarEnv a :=
  UniqFM.plusUFMList.

Definition plusVarEnv_C {a}
   : (a -> a -> a) -> VarEnv a -> VarEnv a -> VarEnv a :=
  UniqFM.plusUFM_C.

Definition rnEnvL : RnEnv2 -> VarEnv Var.Var :=
  envL.

Definition rnEnvR : RnEnv2 -> VarEnv Var.Var :=
  envR.

Definition rnInScopeSet : RnEnv2 -> InScopeSet :=
  in_scope.

Definition rnSwap : RnEnv2 -> RnEnv2 :=
  fun arg_0__ => let 'RV2 envL envR in_scope := arg_0__ in RV2 envR envL in_scope.

Definition unionInScope : InScopeSet -> InScopeSet -> InScopeSet :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | InScope s1 _, InScope s2 n2 => InScope (VarSet.unionVarSet s1 s2) n2
    end.

Definition uniqAway' : InScopeSet -> Var.Var -> Var.Var :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | InScope set n, var =>
        let orig_unique := Unique.getUnique var in
        let try :=
          GHC.DeferredFix.deferredFix1 (fun try k =>
                                          let uniq := Unique.deriveUnique orig_unique (n GHC.Num.* k) in
                                          let msg :=
                                            GHC.Base.mappend (GHC.Base.mappend (GHC.Base.mappend (Panic.noString k) (id
                                                                                                  (GHC.Base.hs_string__
                                                                                                   "tries")))
                                                                               (Panic.noString var)) (Panic.noString
                                                              n) in
                                          if andb Util.debugIsOn (k GHC.Base.> #1000) : bool
                                          then Panic.panicStr (GHC.Base.hs_string__ "uniqAway loop:") msg else
                                          if VarSet.elemVarSetByKey uniq set : bool then try (k GHC.Num.+ #1) else
                                          if k GHC.Base.> #3 : bool then Var.setVarUnique var uniq else
                                          Var.setVarUnique var uniq) in
        try #1
    end.

Definition rnBndr2_var
   : RnEnv2 -> Var.Var -> Var.Var -> (RnEnv2 * Var.Var)%type :=
  fun arg_0__ arg_1__ arg_2__ =>
    match arg_0__, arg_1__, arg_2__ with
    | RV2 envL envR in_scope, bL, bR =>
        let new_b :=
          if negb (elemInScopeSet bL in_scope) : bool then bL else
          if negb (elemInScopeSet bR in_scope) : bool then bR else
          uniqAway' in_scope bL in
        pair (RV2 (extendVarEnv envL bL new_b) (extendVarEnv envR bR new_b)
                  (extendInScopeSet in_scope new_b)) new_b
    end.

Definition rnBndr2 : RnEnv2 -> Var.Var -> Var.Var -> RnEnv2 :=
  fun env bL bR => Data.Tuple.fst (rnBndr2_var env bL bR).

Definition uniqAway : InScopeSet -> Var.Var -> Var.Var :=
  fun in_scope var =>
    if elemInScopeSet var in_scope : bool then uniqAway' in_scope var else
    var.

Definition rnBndrL : RnEnv2 -> Var.Var -> (RnEnv2 * Var.Var)%type :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | RV2 envL envR in_scope, bL =>
        let new_b := uniqAway in_scope bL in
        pair (RV2 (extendVarEnv envL bL new_b) envR (extendInScopeSet in_scope new_b))
             new_b
    end.

Definition rnBndrR : RnEnv2 -> Var.Var -> (RnEnv2 * Var.Var)%type :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | RV2 envL envR in_scope, bR =>
        let new_b := uniqAway in_scope bR in
        pair (RV2 envL (extendVarEnv envR bR new_b) (extendInScopeSet in_scope new_b))
             new_b
    end.

Definition rnEtaL : RnEnv2 -> Var.Var -> (RnEnv2 * Var.Var)%type :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | RV2 envL envR in_scope, bL =>
        let new_b := uniqAway in_scope bL in
        pair (RV2 (extendVarEnv envL bL new_b) (extendVarEnv envR new_b new_b)
                  (extendInScopeSet in_scope new_b)) new_b
    end.

Definition rnEtaR : RnEnv2 -> Var.Var -> (RnEnv2 * Var.Var)%type :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | RV2 envL envR in_scope, bR =>
        let new_b := uniqAway in_scope bR in
        pair (RV2 (extendVarEnv envL new_b new_b) (extendVarEnv envR bR new_b)
                  (extendInScopeSet in_scope new_b)) new_b
    end.

Definition unitDVarEnv {a} : Var.Var -> a -> DVarEnv a :=
  UniqDFM.unitUDFM.

Definition unitVarEnv {a} : Var.Var -> a -> VarEnv a :=
  UniqFM.unitUFM.

Definition varSetInScope : VarSet.VarSet -> InScopeSet -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | vars, InScope s1 _ => VarSet.subVarSet vars s1
    end.

(* External variables:
     None Some andb bool id list negb op_zt__ option pair Data.Foldable.foldl
     Data.Foldable.length Data.Tuple.fst GHC.Base.mappend GHC.Base.op_zg__
     GHC.DeferredFix.deferredFix1 GHC.Err.Default GHC.Err.default GHC.Num.Int
     GHC.Num.fromInteger GHC.Num.op_zp__ GHC.Num.op_zt__ Maybes.orElse
     OccName.TidyOccEnv OccName.emptyTidyOccEnv Panic.noString Panic.panicStr
     UniqDFM.UniqDFM UniqDFM.addListToUDFM UniqDFM.addToUDFM UniqDFM.addToUDFM_C
     UniqDFM.alterUDFM UniqDFM.anyUDFM UniqDFM.delFromUDFM UniqDFM.delListFromUDFM
     UniqDFM.elemUDFM UniqDFM.eltsUDFM UniqDFM.emptyUDFM UniqDFM.filterUDFM
     UniqDFM.foldUDFM UniqDFM.isNullUDFM UniqDFM.listToUDFM UniqDFM.lookupUDFM
     UniqDFM.mapUDFM UniqDFM.minusUDFM UniqDFM.partitionUDFM UniqDFM.plusUDFM
     UniqDFM.plusUDFM_C UniqDFM.unitUDFM UniqFM.UniqFM UniqFM.addListToUFM
     UniqFM.addToUFM UniqFM.addToUFM_Acc UniqFM.addToUFM_C UniqFM.addToUFM_Directly
     UniqFM.alterUFM UniqFM.delFromUFM UniqFM.delFromUFM_Directly
     UniqFM.delListFromUFM UniqFM.disjointUFM UniqFM.elemUFM UniqFM.elemUFM_Directly
     UniqFM.emptyUFM UniqFM.filterUFM UniqFM.filterUFM_Directly UniqFM.intersectUFM
     UniqFM.isNullUFM UniqFM.listToUFM UniqFM.listToUFM_Directly UniqFM.lookupUFM
     UniqFM.lookupUFM_Directly UniqFM.lookupWithDefaultUFM UniqFM.mapUFM
     UniqFM.minusUFM UniqFM.partitionUFM UniqFM.plusMaybeUFM_C UniqFM.plusUFM
     UniqFM.plusUFMList UniqFM.plusUFM_C UniqFM.unitUFM UniqSet.sizeUniqSet
     Unique.Unique Unique.deriveUnique Unique.getUnique Util.debugIsOn Util.zipEqual
     Var.Var Var.setVarUnique VarSet.VarSet VarSet.delVarSet VarSet.elemVarSet
     VarSet.elemVarSetByKey VarSet.emptyVarSet VarSet.extendVarSet
     VarSet.isEmptyVarSet VarSet.lookupVarSet VarSet.lookupVarSet_Directly
     VarSet.subVarSet VarSet.unionVarSet
*)
