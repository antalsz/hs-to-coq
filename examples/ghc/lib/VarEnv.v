(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Coq.Program.Tactics.
Require Coq.Program.Wf.

(* Converted imports: *)

Require Data.Foldable.
Require Data.Tuple.
Require GHC.Base.
Require GHC.Num.
Require Maybes.
Require OccName.
Require Panic.
Require UniqDFM.
Require UniqFM.
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

Inductive InScopeSet : Type := InScope : (VarEnv
                                         Var.Var) -> GHC.Num.Int -> InScopeSet.

Inductive RnEnv2 : Type := RV2 : VarEnv Var.Var -> VarEnv
                                 Var.Var -> InScopeSet -> RnEnv2.

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
  match arg_0__ with
    | RV2 envL _ _ => envL
  end.

Definition envR (arg_1__ : RnEnv2) :=
  match arg_1__ with
    | RV2 _ envR _ => envR
  end.

Definition in_scope (arg_2__ : RnEnv2) :=
  match arg_2__ with
    | RV2 _ _ in_scope => in_scope
  end.
(* Midamble *)

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

(* Converted value declarations: *)

(* The Haskell code containes partial or untranslateable code, which needs the
   following *)

Axiom missingValue : forall {a}, a.

(* Translating `instance Outputable.Outputable VarEnv.InScopeSet' failed: OOPS!
   Cannot find information for class Qualified "Outputable" "Outputable"
   unsupported *)

Definition alterDVarEnv {a} : (option a -> option a) -> DVarEnv
                              a -> Var.Var -> DVarEnv a :=
  UniqDFM.alterUDFM.

Definition alterVarEnv {a} : (option a -> option a) -> VarEnv
                             a -> Var.Var -> VarEnv a :=
  UniqFM.alterUFM.

Definition anyDVarEnv {a} : (a -> bool) -> DVarEnv a -> bool :=
  UniqDFM.anyUDFM.

Definition dVarEnvElts {a} : DVarEnv a -> list a :=
  UniqDFM.eltsUDFM.

Definition delDVarEnv {a} : DVarEnv a -> Var.Var -> DVarEnv a :=
  UniqDFM.delFromUDFM.

Definition delDVarEnvList {a} : DVarEnv a -> list Var.Var -> DVarEnv a :=
  UniqDFM.delListFromUDFM.

Definition delVarEnv {a} : VarEnv a -> Var.Var -> VarEnv a :=
  UniqFM.delFromUFM.

Definition delInScopeSet : InScopeSet -> Var.Var -> InScopeSet :=
  fun arg_0__ arg_1__ =>
    match arg_0__ , arg_1__ with
      | InScope in_scope n , v => InScope (delVarEnv in_scope v) n
    end.

Definition delVarEnvList {a} : VarEnv a -> list Var.Var -> VarEnv a :=
  UniqFM.delListFromUFM.

Definition delVarEnv_Directly {a} : VarEnv a -> Unique.Unique -> VarEnv a :=
  UniqFM.delFromUFM_Directly.

Definition elemVarEnv {a} : Var.Var -> VarEnv a -> bool :=
  UniqFM.elemUFM.

Definition inRnEnvL : RnEnv2 -> Var.Var -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__ , arg_1__ with
      | RV2 env _ _ , v => elemVarEnv v env
    end.

Definition inRnEnvR : RnEnv2 -> Var.Var -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__ , arg_1__ with
      | RV2 _ env _ , v => elemVarEnv v env
    end.

Definition elemInScopeSet : Var.Var -> InScopeSet -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__ , arg_1__ with
      | v , InScope in_scope _ => elemVarEnv v in_scope
    end.

Definition rnBndr2_var : RnEnv2 -> Var.Var -> Var.Var -> (RnEnv2 *
                         Var.Var)%type :=
  fun arg_0__ arg_1__ arg_2__ =>
    match arg_0__ , arg_1__ , arg_2__ with
      | RV2 envL envR in_scope , bL , bR => let new_b :=
                                              let j_3__ := uniqAway' in_scope bL in
                                              let j_4__ :=
                                                if negb (elemInScopeSet bR in_scope) : bool
                                                then bR
                                                else j_3__ in
                                              if negb (elemInScopeSet bL in_scope) : bool
                                              then bL
                                              else j_4__ in
                                            pair (RV2 missingValue missingValue missingValue) new_b
    end.

Definition rnBndr2 : RnEnv2 -> Var.Var -> Var.Var -> RnEnv2 :=
  fun env bL bR => Data.Tuple.fst GHC.Base.$ rnBndr2_var env bL bR.

Definition rnBndrs2 : RnEnv2 -> list Var.Var -> list Var.Var -> RnEnv2 :=
  fun env bsL bsR => Util.foldl2 rnBndr2 env bsL bsR.

Definition rnInScope : Var.Var -> RnEnv2 -> bool :=
  fun x env => elemInScopeSet x (in_scope env).

Definition uniqAway : InScopeSet -> Var.Var -> Var.Var :=
  fun in_scope var =>
    if elemInScopeSet var in_scope : bool
    then uniqAway' in_scope var
    else var.

Definition rnBndrL : RnEnv2 -> Var.Var -> (RnEnv2 * Var.Var)%type :=
  fun arg_0__ arg_1__ =>
    match arg_0__ , arg_1__ with
      | RV2 envL envR in_scope , bL => let new_b := uniqAway in_scope bL in
                                       pair (RV2 missingValue missingValue missingValue) new_b
    end.

Definition rnBndrR : RnEnv2 -> Var.Var -> (RnEnv2 * Var.Var)%type :=
  fun arg_0__ arg_1__ =>
    match arg_0__ , arg_1__ with
      | RV2 envL envR in_scope , bR => let new_b := uniqAway in_scope bR in
                                       pair (RV2 missingValue missingValue missingValue) new_b
    end.

Definition rnEtaL : RnEnv2 -> Var.Var -> (RnEnv2 * Var.Var)%type :=
  fun arg_0__ arg_1__ =>
    match arg_0__ , arg_1__ with
      | RV2 envL envR in_scope , bL => let new_b := uniqAway in_scope bL in
                                       pair (RV2 missingValue missingValue missingValue) new_b
    end.

Definition rnEtaR : RnEnv2 -> Var.Var -> (RnEnv2 * Var.Var)%type :=
  fun arg_0__ arg_1__ =>
    match arg_0__ , arg_1__ with
      | RV2 envL envR in_scope , bR => let new_b := uniqAway in_scope bR in
                                       pair (RV2 missingValue missingValue missingValue) new_b
    end.

Definition elemVarEnvByKey {a} : Unique.Unique -> VarEnv a -> bool :=
  UniqFM.elemUFM_Directly.

Definition emptyDVarEnv {a} : DVarEnv a :=
  UniqDFM.emptyUDFM.

Definition emptyInScopeSet : InScopeSet :=
  InScope VarSet.emptyVarSet (GHC.Num.fromInteger 1).

Definition emptyVarEnv {a} : VarEnv a :=
  UniqFM.emptyUFM.

Definition nukeRnEnvL : RnEnv2 -> RnEnv2 :=
  fun env =>
    match env with
      | RV2 envL_0__ envR_1__ in_scope_2__ => RV2 emptyVarEnv envR_1__ in_scope_2__
    end.

Definition nukeRnEnvR : RnEnv2 -> RnEnv2 :=
  fun env =>
    match env with
      | RV2 envL_0__ envR_1__ in_scope_2__ => RV2 envL_0__ emptyVarEnv in_scope_2__
    end.

Definition emptyTidyEnv : TidyEnv :=
  pair OccName.emptyTidyOccEnv emptyVarEnv.

Definition extendDVarEnv {a} : DVarEnv a -> Var.Var -> a -> DVarEnv a :=
  UniqDFM.addToUDFM.

Definition extendDVarEnv_C {a} : (a -> a -> a) -> DVarEnv
                                 a -> Var.Var -> a -> DVarEnv a :=
  UniqDFM.addToUDFM_C.

Definition extendVarEnv {a} : VarEnv a -> Var.Var -> a -> VarEnv a :=
  UniqFM.addToUFM.

Definition extendInScopeSetList : InScopeSet -> list Var.Var -> InScopeSet :=
  fun arg_0__ arg_1__ =>
    match arg_0__ , arg_1__ with
      | InScope in_scope n , vs => InScope (Data.Foldable.foldl (fun s v =>
                                                                  extendVarEnv s v v) in_scope vs) (n GHC.Num.+
                                                                                                   Data.Foldable.length
                                                                                                   vs)
    end.

Definition delBndrsR : RnEnv2 -> list Var.Var -> RnEnv2 :=
  fun arg_0__ arg_1__ =>
    match arg_0__ , arg_1__ with
      | (RV2 _ env in_scope as rn) , v => match rn with
                                            | RV2 envL_2__ envR_3__ in_scope_4__ => RV2 envL_2__ (delVarEnvList env v)
                                                                                        (extendInScopeSetList in_scope
                                                                                                              v)
                                          end
    end.

Definition delBndrsL : RnEnv2 -> list Var.Var -> RnEnv2 :=
  fun arg_0__ arg_1__ =>
    match arg_0__ , arg_1__ with
      | (RV2 env _ in_scope as rn) , v => match rn with
                                            | RV2 envL_2__ envR_3__ in_scope_4__ => RV2 (delVarEnvList env v) envR_3__
                                                                                        (extendInScopeSetList in_scope
                                                                                                              v)
                                          end
    end.

Definition extendInScopeSet : InScopeSet -> Var.Var -> InScopeSet :=
  fun arg_0__ arg_1__ =>
    match arg_0__ , arg_1__ with
      | InScope in_scope n , v => InScope (extendVarEnv in_scope v v) (n GHC.Num.+
                                                                      GHC.Num.fromInteger 1)
    end.

Definition delBndrR : RnEnv2 -> Var.Var -> RnEnv2 :=
  fun arg_0__ arg_1__ =>
    match arg_0__ , arg_1__ with
      | (RV2 _ env in_scope as rn) , v => match rn with
                                            | RV2 envL_2__ envR_3__ in_scope_4__ => RV2 envL_2__ (delVarEnv env v)
                                                                                        (extendInScopeSet in_scope v)
                                          end
    end.

Definition delBndrL : RnEnv2 -> Var.Var -> RnEnv2 :=
  fun arg_0__ arg_1__ =>
    match arg_0__ , arg_1__ with
      | (RV2 env _ in_scope as rn) , v => match rn with
                                            | RV2 envL_2__ envR_3__ in_scope_4__ => RV2 (delVarEnv env v) envR_3__
                                                                                        (extendInScopeSet in_scope v)
                                          end
    end.

Definition extendVarEnvList {a} : VarEnv a -> list (Var.Var * a)%type -> VarEnv
                                  a :=
  UniqFM.addListToUFM.

Definition extendVarEnv_Acc {a} {b} : (a -> b -> b) -> (a -> b) -> VarEnv
                                      b -> Var.Var -> a -> VarEnv b :=
  UniqFM.addToUFM_Acc.

Definition extendVarEnv_C {a} : (a -> a -> a) -> VarEnv
                                a -> Var.Var -> a -> VarEnv a :=
  UniqFM.addToUFM_C.

Definition extendVarEnv_Directly {a} : VarEnv a -> Unique.Unique -> a -> VarEnv
                                       a :=
  UniqFM.addToUFM_Directly.

Definition filterVarEnv {a} : (a -> bool) -> VarEnv a -> VarEnv a :=
  UniqFM.filterUFM.

Definition filterVarEnv_Directly {a} : (Unique.Unique -> a -> bool) -> VarEnv
                                       a -> VarEnv a :=
  UniqFM.filterUFM_Directly.

Definition restrictVarEnv {a} : VarEnv a -> VarSet.VarSet -> VarEnv a :=
  fun env vs =>
    let keep :=
      fun arg_0__ arg_1__ =>
        match arg_0__ , arg_1__ with
          | u , _ => VarSet.elemVarSetByKey u vs
        end in
    filterVarEnv_Directly keep env.

Definition foldDVarEnv {a} {b} : (a -> b -> b) -> b -> DVarEnv a -> b :=
  UniqDFM.foldUDFM.

Definition foldVarEnv {a} {b} : (a -> b -> b) -> b -> VarEnv a -> b :=
  UniqFM.foldUFM.

Definition foldVarEnv_Directly {a} {b}
    : (Unique.Unique -> a -> b -> b) -> b -> VarEnv a -> b :=
  UniqFM.foldUFM_Directly.

Definition getInScopeVars : InScopeSet -> VarEnv Var.Var :=
  fun arg_0__ => match arg_0__ with | InScope vs _ => vs end.

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
    let scrut_0__ := (lookupDVarEnv env key) in
    match scrut_0__ with
      | None => env
      | Some xx => extendDVarEnv env key (mangle_fn xx)
    end.

Definition lookupVarEnv {a} : VarEnv a -> Var.Var -> option a :=
  UniqFM.lookupUFM.

Definition rnOccL : RnEnv2 -> Var.Var -> Var.Var :=
  fun arg_0__ arg_1__ =>
    match arg_0__ , arg_1__ with
      | RV2 env _ _ , v => Maybes.orElse (lookupVarEnv env v) v
    end.

Definition rnOccL_maybe : RnEnv2 -> Var.Var -> option Var.Var :=
  fun arg_0__ arg_1__ =>
    match arg_0__ , arg_1__ with
      | RV2 env _ _ , v => lookupVarEnv env v
    end.

Definition rnOccR : RnEnv2 -> Var.Var -> Var.Var :=
  fun arg_0__ arg_1__ =>
    match arg_0__ , arg_1__ with
      | RV2 _ env _ , v => Maybes.orElse (lookupVarEnv env v) v
    end.

Definition rnOccR_maybe : RnEnv2 -> Var.Var -> option Var.Var :=
  fun arg_0__ arg_1__ =>
    match arg_0__ , arg_1__ with
      | RV2 _ env _ , v => lookupVarEnv env v
    end.

Definition lookupInScope : InScopeSet -> Var.Var -> option Var.Var :=
  fun arg_0__ arg_1__ =>
    match arg_0__ , arg_1__ with
      | InScope in_scope _ , v => lookupVarEnv in_scope v
    end.

Definition lookupRnInScope : RnEnv2 -> Var.Var -> Var.Var :=
  fun env v => Maybes.orElse (lookupInScope (in_scope env) v) v.

Definition modifyVarEnv {a} : (a -> a) -> VarEnv a -> Var.Var -> VarEnv a :=
  fun mangle_fn env key =>
    let scrut_0__ := (lookupVarEnv env key) in
    match scrut_0__ with
      | None => env
      | Some xx => extendVarEnv env key (mangle_fn xx)
    end.

Definition lookupVarEnv_Directly {a} : VarEnv a -> Unique.Unique -> option a :=
  UniqFM.lookupUFM_Directly.

Definition lookupInScope_Directly : InScopeSet -> Unique.Unique -> option
                                    Var.Var :=
  fun arg_0__ arg_1__ =>
    match arg_0__ , arg_1__ with
      | InScope in_scope _ , uniq => lookupVarEnv_Directly in_scope uniq
    end.

Definition lookupVarEnv_NF {a} `{_ : Panic.Default a} (env : VarEnv a) (id
                             : Var.Var) : a :=
  match lookupVarEnv env id with
    | Some xx => xx
    | None => Panic.default
  end.

Definition lookupWithDefaultVarEnv {a} : VarEnv a -> a -> Var.Var -> a :=
  UniqFM.lookupWithDefaultUFM.

Definition mapDVarEnv {a} {b} : (a -> b) -> DVarEnv a -> DVarEnv b :=
  UniqDFM.mapUDFM.

Definition mapVarEnv {a} {b} : (a -> b) -> VarEnv a -> VarEnv b :=
  UniqFM.mapUFM.

Definition minusVarEnv {a} {b} : VarEnv a -> VarEnv b -> VarEnv a :=
  UniqFM.minusUFM.

Definition mkInScopeSet : VarEnv Var.Var -> InScopeSet :=
  fun in_scope => InScope in_scope (GHC.Num.fromInteger 1).

Definition mkRnEnv2 : InScopeSet -> RnEnv2 :=
  fun vars => RV2 missingValue missingValue missingValue.

Definition mkVarEnv {a} : list (Var.Var * a)%type -> VarEnv a :=
  UniqFM.listToUFM.

Definition zipVarEnv {a} : list Var.Var -> list a -> VarEnv a :=
  fun tyvars tys =>
    mkVarEnv (Util.zipEqual (GHC.Base.hs_string__ "zipVarEnv") tyvars tys).

Definition mkVarEnv_Directly {a} : list (Unique.Unique * a)%type -> VarEnv a :=
  UniqFM.listToUFM_Directly.

Definition modifyVarEnv_Directly {a} : (a -> a) -> UniqFM.UniqFM
                                       a -> Unique.Unique -> UniqFM.UniqFM a :=
  fun mangle_fn env key =>
    let scrut_0__ := (UniqFM.lookupUFM_Directly env key) in
    match scrut_0__ with
      | None => env
      | Some xx => UniqFM.addToUFM_Directly env key (mangle_fn xx)
    end.

Definition partitionDVarEnv {a} : (a -> bool) -> DVarEnv a -> (DVarEnv a *
                                  DVarEnv a)%type :=
  UniqDFM.partitionUDFM.

Definition partitionVarEnv {a} : (a -> bool) -> VarEnv a -> (VarEnv a * VarEnv
                                 a)%type :=
  UniqFM.partitionUFM.

Definition plusDVarEnv_C {a} : (a -> a -> a) -> DVarEnv a -> DVarEnv
                               a -> DVarEnv a :=
  UniqDFM.plusUDFM_C.

Definition plusVarEnv {a} : VarEnv a -> VarEnv a -> VarEnv a :=
  UniqFM.plusUFM.

Definition unionInScope : InScopeSet -> InScopeSet -> InScopeSet :=
  fun arg_0__ arg_1__ =>
    match arg_0__ , arg_1__ with
      | InScope s1 _ , InScope s2 n2 => InScope (plusVarEnv s1 s2) n2
    end.

Definition extendInScopeSetSet : InScopeSet -> VarEnv Var.Var -> InScopeSet :=
  fun arg_0__ arg_1__ =>
    match arg_0__ , arg_1__ with
      | InScope in_scope n , vs => InScope (plusVarEnv in_scope vs) (n GHC.Num.+
                                                                    UniqFM.sizeUFM vs)
    end.

Definition addRnInScopeSet : RnEnv2 -> VarEnv Var.Var -> RnEnv2 :=
  fun env vs =>
    let j_5__ :=
      match env with
        | RV2 envL_0__ envR_1__ in_scope_2__ => RV2 envL_0__ envR_1__
                                                    (extendInScopeSetSet (in_scope env) vs)
      end in
    if isEmptyVarEnv vs : bool
    then env
    else j_5__.

Definition plusVarEnv_C {a} : (a -> a -> a) -> VarEnv a -> VarEnv a -> VarEnv
                              a :=
  UniqFM.plusUFM_C.

Definition rnEnvL : RnEnv2 -> VarEnv Var.Var :=
  envL.

Definition rnEnvR : RnEnv2 -> VarEnv Var.Var :=
  envR.

Definition rnInScopeSet : RnEnv2 -> InScopeSet :=
  in_scope.

Definition rnSwap : RnEnv2 -> RnEnv2 :=
  fun arg_0__ =>
    match arg_0__ with
      | RV2 envL envR in_scope => RV2 missingValue missingValue missingValue
    end.

Definition unitDVarEnv {a} : Var.Var -> a -> DVarEnv a :=
  UniqDFM.unitUDFM.

Definition unitVarEnv {a} : Var.Var -> a -> VarEnv a :=
  UniqFM.unitUFM.

Definition varEnvElts {a} : VarEnv a -> list a :=
  UniqFM.eltsUFM.

Definition varEnvKeys {a} : VarEnv a -> list Unique.Unique :=
  UniqFM.keysUFM.

Definition varEnvToList {a} : VarEnv a -> list (Unique.Unique * a)%type :=
  UniqFM.ufmToList.

Definition varSetInScope : VarSet.VarSet -> InScopeSet -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__ , arg_1__ with
      | vars , InScope s1 _ => VarSet.subVarSet vars s1
    end.

(* Unbound variables:
     None Some bool list negb op_zt__ option pair uniqAway' Data.Foldable.foldl
     Data.Foldable.length Data.Tuple.fst GHC.Base.op_zd__ GHC.Num.Int GHC.Num.op_zp__
     Maybes.orElse OccName.TidyOccEnv OccName.emptyTidyOccEnv Panic.Default
     Panic.default UniqDFM.UniqDFM UniqDFM.addToUDFM UniqDFM.addToUDFM_C
     UniqDFM.alterUDFM UniqDFM.anyUDFM UniqDFM.delFromUDFM UniqDFM.delListFromUDFM
     UniqDFM.eltsUDFM UniqDFM.emptyUDFM UniqDFM.foldUDFM UniqDFM.isNullUDFM
     UniqDFM.lookupUDFM UniqDFM.mapUDFM UniqDFM.partitionUDFM UniqDFM.plusUDFM_C
     UniqDFM.unitUDFM UniqFM.UniqFM UniqFM.addListToUFM UniqFM.addToUFM
     UniqFM.addToUFM_Acc UniqFM.addToUFM_C UniqFM.addToUFM_Directly UniqFM.alterUFM
     UniqFM.delFromUFM UniqFM.delFromUFM_Directly UniqFM.delListFromUFM
     UniqFM.elemUFM UniqFM.elemUFM_Directly UniqFM.eltsUFM UniqFM.emptyUFM
     UniqFM.filterUFM UniqFM.filterUFM_Directly UniqFM.foldUFM
     UniqFM.foldUFM_Directly UniqFM.intersectUFM UniqFM.isNullUFM UniqFM.keysUFM
     UniqFM.listToUFM UniqFM.listToUFM_Directly UniqFM.lookupUFM
     UniqFM.lookupUFM_Directly UniqFM.lookupWithDefaultUFM UniqFM.mapUFM
     UniqFM.minusUFM UniqFM.partitionUFM UniqFM.plusUFM UniqFM.plusUFM_C
     UniqFM.sizeUFM UniqFM.ufmToList UniqFM.unitUFM Unique.Unique Util.foldl2
     Util.zipEqual Var.Var VarSet.VarSet VarSet.elemVarSetByKey VarSet.emptyVarSet
     VarSet.subVarSet
*)
