(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Coq.Program.Tactics.
Require Coq.Program.Wf.

(* Preamble *)

Require Import Core.

(* Converted imports: *)

Require Core.
Require Data.Foldable.
Require Data.Tuple.
Require GHC.Base.
Require GHC.Err.
Require GHC.Num.
Require Maybes.
Require OccName.
Require UniqDFM.
Require UniqFM.
Require Unique.
Require Util.
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
  (OccName.TidyOccEnv * VarEnv Core.Var)%type%type.

Inductive InScopeSet : Type
  := InScope : (VarEnv Core.Var) -> GHC.Num.Int -> InScopeSet.

Inductive RnEnv2 : Type
  := RV2 : VarEnv Core.Var -> VarEnv Core.Var -> InScopeSet -> RnEnv2.

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

Definition envR (arg_1__ : RnEnv2) :=
  let 'RV2 _ envR _ := arg_1__ in
  envR.

Definition in_scope (arg_2__ : RnEnv2) :=
  let 'RV2 _ _ in_scope := arg_2__ in
  in_scope.

(* The Haskell code containes partial or untranslateable code, which needs the
   following *)

Axiom missingValue : forall {a}, a.
(* Midamble *)

Axiom uniqAway' : InScopeSet -> Core.Var -> Core.Var.
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

Require GHC.Err.

Instance Default_InScopeSet : GHC.Err.Default InScopeSet :=
  GHC.Err.Build_Default _ (InScope GHC.Err.default GHC.Err.default).
Instance Default_RnEnv2 : GHC.Err.Default RnEnv2 :=
  GHC.Err.Build_Default _ (RV2 GHC.Err.default GHC.Err.default GHC.Err.default).
Instance Default_TidyEnv : GHC.Err.Default TidyEnv.
Admitted.


(* needs UniqFM.plusUFM_CD *)
Parameter plusVarEnv_CD : forall {a}, (a -> a -> a) -> VarEnv a -> a -> VarEnv
                               a -> a -> VarEnv a.

(* Converted value declarations: *)

(* Translating `instance Outputable.Outputable VarEnv.InScopeSet' failed: OOPS!
   Cannot find information for class Qualified "Outputable" "Outputable"
   unsupported *)

Definition alterDVarEnv {a}
   : (option a -> option a) -> DVarEnv a -> Core.Var -> DVarEnv a :=
  UniqDFM.alterUDFM.

Definition alterVarEnv {a}
   : (option a -> option a) -> VarEnv a -> Core.Var -> VarEnv a :=
  UniqFM.alterUFM.

Definition anyDVarEnv {a} : (a -> bool) -> DVarEnv a -> bool :=
  UniqDFM.anyUDFM.

Definition dVarEnvElts {a} : DVarEnv a -> list a :=
  UniqDFM.eltsUDFM.

Definition delDVarEnv {a} : DVarEnv a -> Core.Var -> DVarEnv a :=
  UniqDFM.delFromUDFM.

Definition delDVarEnvList {a} : DVarEnv a -> list Core.Var -> DVarEnv a :=
  UniqDFM.delListFromUDFM.

Definition delVarEnv {a} : VarEnv a -> Core.Var -> VarEnv a :=
  UniqFM.delFromUFM.

Definition delInScopeSet : InScopeSet -> Core.Var -> InScopeSet :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | InScope in_scope n, v => InScope (delVarEnv in_scope v) n
    end.

Definition delVarEnvList {a} : VarEnv a -> list Core.Var -> VarEnv a :=
  UniqFM.delListFromUFM.

Definition delVarEnv_Directly {a} : VarEnv a -> Unique.Unique -> VarEnv a :=
  UniqFM.delFromUFM_Directly.

Definition elemVarEnv {a} : Core.Var -> VarEnv a -> bool :=
  UniqFM.elemUFM.

Definition inRnEnvL : RnEnv2 -> Core.Var -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | RV2 env _ _, v => elemVarEnv v env
    end.

Definition inRnEnvR : RnEnv2 -> Core.Var -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | RV2 _ env _, v => elemVarEnv v env
    end.

Definition elemInScopeSet : Core.Var -> InScopeSet -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | v, InScope in_scope _ => elemVarEnv v in_scope
    end.

Definition rnBndr2_var
   : RnEnv2 -> Core.Var -> Core.Var -> (RnEnv2 * Core.Var)%type :=
  fun arg_0__ arg_1__ arg_2__ =>
    match arg_0__, arg_1__, arg_2__ with
    | RV2 envL envR in_scope, bL, bR =>
        let new_b :=
          if negb (elemInScopeSet bL in_scope) : bool
          then bL
          else if negb (elemInScopeSet bR in_scope) : bool
               then bR
               else uniqAway' in_scope bL in
        pair (RV2 missingValue missingValue missingValue) new_b
    end.

Definition rnBndr2 : RnEnv2 -> Core.Var -> Core.Var -> RnEnv2 :=
  fun env bL bR => Data.Tuple.fst GHC.Base.$ rnBndr2_var env bL bR.

Definition rnBndrs2 : RnEnv2 -> list Core.Var -> list Core.Var -> RnEnv2 :=
  fun env bsL bsR => Util.foldl2 rnBndr2 env bsL bsR.

Definition rnInScope : Core.Var -> RnEnv2 -> bool :=
  fun x env => elemInScopeSet x (in_scope env).

Definition uniqAway : InScopeSet -> Core.Var -> Core.Var :=
  fun in_scope var =>
    if elemInScopeSet var in_scope : bool
    then uniqAway' in_scope var
    else var.

Definition rnBndrL : RnEnv2 -> Core.Var -> (RnEnv2 * Core.Var)%type :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | RV2 envL envR in_scope, bL =>
        let new_b := uniqAway in_scope bL in
        pair (RV2 missingValue missingValue missingValue) new_b
    end.

Definition rnBndrR : RnEnv2 -> Core.Var -> (RnEnv2 * Core.Var)%type :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | RV2 envL envR in_scope, bR =>
        let new_b := uniqAway in_scope bR in
        pair (RV2 missingValue missingValue missingValue) new_b
    end.

Definition rnEtaL : RnEnv2 -> Core.Var -> (RnEnv2 * Core.Var)%type :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | RV2 envL envR in_scope, bL =>
        let new_b := uniqAway in_scope bL in
        pair (RV2 missingValue missingValue missingValue) new_b
    end.

Definition rnEtaR : RnEnv2 -> Core.Var -> (RnEnv2 * Core.Var)%type :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | RV2 envL envR in_scope, bR =>
        let new_b := uniqAway in_scope bR in
        pair (RV2 missingValue missingValue missingValue) new_b
    end.

Definition elemVarEnvByKey {a} : Unique.Unique -> VarEnv a -> bool :=
  UniqFM.elemUFM_Directly.

Definition emptyDVarEnv {a} : DVarEnv a :=
  UniqDFM.emptyUDFM.

Definition emptyInScopeSet : InScopeSet :=
  InScope VarSet.emptyVarSet #1.

Definition emptyVarEnv {a} : VarEnv a :=
  UniqFM.emptyUFM.

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

Definition extendDVarEnv {a} : DVarEnv a -> Core.Var -> a -> DVarEnv a :=
  UniqDFM.addToUDFM.

Definition extendDVarEnv_C {a}
   : (a -> a -> a) -> DVarEnv a -> Core.Var -> a -> DVarEnv a :=
  UniqDFM.addToUDFM_C.

Definition extendVarEnv {a} : VarEnv a -> Core.Var -> a -> VarEnv a :=
  UniqFM.addToUFM.

Definition extendInScopeSetList : InScopeSet -> list Core.Var -> InScopeSet :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | InScope in_scope n, vs =>
        InScope (Data.Foldable.foldl (fun s v => extendVarEnv s v v) in_scope vs) (n
                                                                                   GHC.Num.+
                                                                                   Data.Foldable.length vs)
    end.

Definition delBndrsR : RnEnv2 -> list Core.Var -> RnEnv2 :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | (RV2 _ env in_scope as rn), v =>
        let 'RV2 envL_2__ envR_3__ in_scope_4__ := rn in
        RV2 envL_2__ (delVarEnvList env v) (extendInScopeSetList in_scope v)
    end.

Definition delBndrsL : RnEnv2 -> list Core.Var -> RnEnv2 :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | (RV2 env _ in_scope as rn), v =>
        let 'RV2 envL_2__ envR_3__ in_scope_4__ := rn in
        RV2 (delVarEnvList env v) envR_3__ (extendInScopeSetList in_scope v)
    end.

Definition extendInScopeSet : InScopeSet -> Core.Var -> InScopeSet :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | InScope in_scope n, v => InScope (extendVarEnv in_scope v v) (n GHC.Num.+ #1)
    end.

Definition delBndrR : RnEnv2 -> Core.Var -> RnEnv2 :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | (RV2 _ env in_scope as rn), v =>
        let 'RV2 envL_2__ envR_3__ in_scope_4__ := rn in
        RV2 envL_2__ (delVarEnv env v) (extendInScopeSet in_scope v)
    end.

Definition delBndrL : RnEnv2 -> Core.Var -> RnEnv2 :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | (RV2 env _ in_scope as rn), v =>
        let 'RV2 envL_2__ envR_3__ in_scope_4__ := rn in
        RV2 (delVarEnv env v) envR_3__ (extendInScopeSet in_scope v)
    end.

Definition extendVarEnvList {a}
   : VarEnv a -> list (Core.Var * a)%type -> VarEnv a :=
  UniqFM.addListToUFM.

Definition extendVarEnv_Acc {a} {b}
   : (a -> b -> b) -> (a -> b) -> VarEnv b -> Core.Var -> a -> VarEnv b :=
  UniqFM.addToUFM_Acc.

Definition extendVarEnv_C {a}
   : (a -> a -> a) -> VarEnv a -> Core.Var -> a -> VarEnv a :=
  UniqFM.addToUFM_C.

Definition extendVarEnv_Directly {a}
   : VarEnv a -> Unique.Unique -> a -> VarEnv a :=
  UniqFM.addToUFM_Directly.

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

Definition foldVarEnv {a} {b} : (a -> b -> b) -> b -> VarEnv a -> b :=
  UniqFM.foldUFM.

Definition foldVarEnv_Directly {a} {b}
   : (Unique.Unique -> a -> b -> b) -> b -> VarEnv a -> b :=
  UniqFM.foldUFM_Directly.

Definition getInScopeVars : InScopeSet -> VarEnv Core.Var :=
  fun arg_0__ => let 'InScope vs _ := arg_0__ in vs.

Definition isEmptyDVarEnv {a} : DVarEnv a -> bool :=
  UniqDFM.isNullUDFM.

Definition isEmptyVarEnv {a} : VarEnv a -> bool :=
  UniqFM.isNullUFM.

Definition intersectsVarEnv {a} : VarEnv a -> VarEnv a -> bool :=
  fun e1 e2 => negb (isEmptyVarEnv (UniqFM.intersectUFM e1 e2)).

Definition lookupDVarEnv {a} : DVarEnv a -> Core.Var -> option a :=
  UniqDFM.lookupUDFM.

Definition modifyDVarEnv {a} : (a -> a) -> DVarEnv a -> Core.Var -> DVarEnv a :=
  fun mangle_fn env key =>
    match (lookupDVarEnv env key) with
    | None => env
    | Some xx => extendDVarEnv env key (mangle_fn xx)
    end.

Definition lookupVarEnv {a} : VarEnv a -> Core.Var -> option a :=
  UniqFM.lookupUFM.

Definition rnOccL : RnEnv2 -> Core.Var -> Core.Var :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | RV2 env _ _, v => Maybes.orElse (lookupVarEnv env v) v
    end.

Definition rnOccL_maybe : RnEnv2 -> Core.Var -> option Core.Var :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | RV2 env _ _, v => lookupVarEnv env v
    end.

Definition rnOccR : RnEnv2 -> Core.Var -> Core.Var :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | RV2 _ env _, v => Maybes.orElse (lookupVarEnv env v) v
    end.

Definition rnOccR_maybe : RnEnv2 -> Core.Var -> option Core.Var :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | RV2 _ env _, v => lookupVarEnv env v
    end.

Definition lookupInScope : InScopeSet -> Core.Var -> option Core.Var :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | InScope in_scope _, v => lookupVarEnv in_scope v
    end.

Definition lookupRnInScope : RnEnv2 -> Core.Var -> Core.Var :=
  fun env v => Maybes.orElse (lookupInScope (in_scope env) v) v.

Definition modifyVarEnv {a} : (a -> a) -> VarEnv a -> Core.Var -> VarEnv a :=
  fun mangle_fn env key =>
    match (lookupVarEnv env key) with
    | None => env
    | Some xx => extendVarEnv env key (mangle_fn xx)
    end.

Definition lookupVarEnv_Directly {a} : VarEnv a -> Unique.Unique -> option a :=
  UniqFM.lookupUFM_Directly.

Definition lookupInScope_Directly
   : InScopeSet -> Unique.Unique -> option Core.Var :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | InScope in_scope _, uniq => lookupVarEnv_Directly in_scope uniq
    end.

Definition lookupVarEnv_NF {a} `{_ : GHC.Err.Default a} (env : VarEnv a) (id
    : Core.Var)
   : a :=
  match lookupVarEnv env id with
  | Some xx => xx
  | None => GHC.Err.default
  end.

Definition lookupWithDefaultVarEnv {a} : VarEnv a -> a -> Core.Var -> a :=
  UniqFM.lookupWithDefaultUFM.

Definition mapDVarEnv {a} {b} : (a -> b) -> DVarEnv a -> DVarEnv b :=
  UniqDFM.mapUDFM.

Definition mapVarEnv {a} {b} : (a -> b) -> VarEnv a -> VarEnv b :=
  UniqFM.mapUFM.

Definition minusVarEnv {a} {b} : VarEnv a -> VarEnv b -> VarEnv a :=
  UniqFM.minusUFM.

Definition mkInScopeSet : VarEnv Core.Var -> InScopeSet :=
  fun in_scope => InScope in_scope #1.

Definition mkRnEnv2 : InScopeSet -> RnEnv2 :=
  fun vars => RV2 missingValue missingValue missingValue.

Definition mkVarEnv {a} : list (Core.Var * a)%type -> VarEnv a :=
  UniqFM.listToUFM.

Definition zipVarEnv {a} : list Core.Var -> list a -> VarEnv a :=
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

Definition plusDVarEnv_C {a}
   : (a -> a -> a) -> DVarEnv a -> DVarEnv a -> DVarEnv a :=
  UniqDFM.plusUDFM_C.

Definition plusVarEnv {a} : VarEnv a -> VarEnv a -> VarEnv a :=
  UniqFM.plusUFM.

Definition unionInScope : InScopeSet -> InScopeSet -> InScopeSet :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | InScope s1 _, InScope s2 n2 => InScope (plusVarEnv s1 s2) n2
    end.

Definition extendInScopeSetSet : InScopeSet -> VarEnv Core.Var -> InScopeSet :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | InScope in_scope n, vs =>
        InScope (plusVarEnv in_scope vs) (n GHC.Num.+ UniqFM.sizeUFM vs)
    end.

Definition addRnInScopeSet : RnEnv2 -> VarEnv Core.Var -> RnEnv2 :=
  fun env vs =>
    if isEmptyVarEnv vs : bool
    then env
    else let 'RV2 envL_0__ envR_1__ in_scope_2__ := env in
         RV2 envL_0__ envR_1__ (extendInScopeSetSet (in_scope env) vs).

Definition plusVarEnv_C {a}
   : (a -> a -> a) -> VarEnv a -> VarEnv a -> VarEnv a :=
  UniqFM.plusUFM_C.

Definition rnEnvL : RnEnv2 -> VarEnv Core.Var :=
  envL.

Definition rnEnvR : RnEnv2 -> VarEnv Core.Var :=
  envR.

Definition rnInScopeSet : RnEnv2 -> InScopeSet :=
  in_scope.

Definition rnSwap : RnEnv2 -> RnEnv2 :=
  fun arg_0__ =>
    let 'RV2 envL envR in_scope := arg_0__ in
    RV2 missingValue missingValue missingValue.

Definition unitDVarEnv {a} : Core.Var -> a -> DVarEnv a :=
  UniqDFM.unitUDFM.

Definition unitVarEnv {a} : Core.Var -> a -> VarEnv a :=
  UniqFM.unitUFM.

Definition varEnvElts {a} : VarEnv a -> list a :=
  UniqFM.eltsUFM.

Definition varEnvKeys {a} : VarEnv a -> list Unique.Unique :=
  UniqFM.keysUFM.

Definition varEnvToList {a} : VarEnv a -> list (Unique.Unique * a)%type :=
  UniqFM.ufmToList.

Definition varSetInScope : VarSet.VarSet -> InScopeSet -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | vars, InScope s1 _ => VarSet.subVarSet vars s1
    end.

(* Unbound variables:
     None Some bool list negb op_zt__ option pair uniqAway' Core.Var
     Data.Foldable.foldl Data.Foldable.length Data.Tuple.fst GHC.Base.op_zd__
     GHC.Err.Default GHC.Err.default GHC.Num.Int GHC.Num.fromInteger GHC.Num.op_zp__
     Maybes.orElse OccName.TidyOccEnv OccName.emptyTidyOccEnv UniqDFM.UniqDFM
     UniqDFM.addToUDFM UniqDFM.addToUDFM_C UniqDFM.alterUDFM UniqDFM.anyUDFM
     UniqDFM.delFromUDFM UniqDFM.delListFromUDFM UniqDFM.eltsUDFM UniqDFM.emptyUDFM
     UniqDFM.foldUDFM UniqDFM.isNullUDFM UniqDFM.lookupUDFM UniqDFM.mapUDFM
     UniqDFM.partitionUDFM UniqDFM.plusUDFM_C UniqDFM.unitUDFM UniqFM.UniqFM
     UniqFM.addListToUFM UniqFM.addToUFM UniqFM.addToUFM_Acc UniqFM.addToUFM_C
     UniqFM.addToUFM_Directly UniqFM.alterUFM UniqFM.delFromUFM
     UniqFM.delFromUFM_Directly UniqFM.delListFromUFM UniqFM.elemUFM
     UniqFM.elemUFM_Directly UniqFM.eltsUFM UniqFM.emptyUFM UniqFM.filterUFM
     UniqFM.filterUFM_Directly UniqFM.foldUFM UniqFM.foldUFM_Directly
     UniqFM.intersectUFM UniqFM.isNullUFM UniqFM.keysUFM UniqFM.listToUFM
     UniqFM.listToUFM_Directly UniqFM.lookupUFM UniqFM.lookupUFM_Directly
     UniqFM.lookupWithDefaultUFM UniqFM.mapUFM UniqFM.minusUFM UniqFM.partitionUFM
     UniqFM.plusUFM UniqFM.plusUFM_C UniqFM.sizeUFM UniqFM.ufmToList UniqFM.unitUFM
     Unique.Unique Util.foldl2 Util.zipEqual VarSet.VarSet VarSet.elemVarSetByKey
     VarSet.emptyVarSet VarSet.subVarSet
*)
