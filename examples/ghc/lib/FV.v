(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Coq.Program.Tactics.
Require Coq.Program.Wf.

(* Converted imports: *)

Require Core.
Require Data.Tuple.
Require GHC.Base.
Import GHC.Base.Notations.

(* Converted type declarations: *)

Definition InterestingVarFun :=
  (Core.Var -> bool)%type.

Definition FV :=
  (InterestingVarFun ->
   Core.VarSet ->
   (list Core.Var * Core.VarSet)%type -> (list Core.Var * Core.VarSet)%type)%type.

(* Converted value declarations: *)

Definition unitFV : Core.Id -> FV :=
  fun arg_0__ arg_1__ arg_2__ arg_3__ =>
    match arg_0__, arg_1__, arg_2__, arg_3__ with
    | var, fv_cand, in_scope, (pair have haveSet as acc) =>
        if Core.elemVarSet var in_scope : bool then acc else
        if Core.elemVarSet var haveSet : bool then acc else
        if fv_cand var : bool
        then pair (cons var have) (Core.extendVarSet haveSet var) else
        acc
    end.

Definition unionFV : FV -> FV -> FV :=
  fun fv1 fv2 fv_cand in_scope acc =>
    fv1 fv_cand in_scope (fv2 fv_cand in_scope acc).

Definition mapUnionFV {a} : (a -> FV) -> list a -> FV :=
  fix mapUnionFV arg_0__ arg_1__ arg_2__ arg_3__ arg_4__
        := match arg_0__, arg_1__, arg_2__, arg_3__, arg_4__ with
           | _f, nil, _fv_cand, _in_scope, acc => acc
           | f, cons a as_, fv_cand, in_scope, acc =>
               mapUnionFV f as_ fv_cand in_scope (f a fv_cand in_scope acc)
           end.

Definition mkFVs : list Core.Var -> FV :=
  fun vars fv_cand in_scope acc => mapUnionFV unitFV vars fv_cand in_scope acc.

Definition unionsFV : list FV -> FV :=
  fun fvs fv_cand in_scope acc => mapUnionFV GHC.Base.id fvs fv_cand in_scope acc.

Definition fvVarListVarSet : FV -> (list Core.Var * Core.VarSet)%type :=
  fun fv => fv (GHC.Base.const true) Core.emptyVarSet (pair nil Core.emptyVarSet).

Definition fvVarSet : FV -> Core.VarSet :=
  Data.Tuple.snd GHC.Base.∘ fvVarListVarSet.

Definition fvVarList : FV -> list Core.Var :=
  Data.Tuple.fst GHC.Base.∘ fvVarListVarSet.

Definition fvDVarSet : FV -> Core.DVarSet :=
  fvVarSet.

Definition filterFV : InterestingVarFun -> FV -> FV :=
  fun fv_cand2 fv fv_cand1 in_scope acc =>
    fv (fun v => andb (fv_cand1 v) (fv_cand2 v)) in_scope acc.

Definition emptyFV : FV :=
  fun arg_0__ arg_1__ arg_2__ =>
    match arg_0__, arg_1__, arg_2__ with
    | _, _, acc => acc
    end.

Definition delFVs : Core.VarSet -> FV -> FV :=
  fun vars fv fv_cand in_scope acc =>
    fv fv_cand (Core.unionVarSet in_scope vars) acc.

Definition delFV : Core.Var -> FV -> FV :=
  fun var fv fv_cand in_scope acc =>
    fv fv_cand (Core.extendVarSet in_scope var) acc.

(* External variables:
     andb bool cons list nil op_zt__ pair true Core.DVarSet Core.Id Core.Var
     Core.VarSet Core.elemVarSet Core.emptyVarSet Core.extendVarSet Core.unionVarSet
     Data.Tuple.fst Data.Tuple.snd GHC.Base.const GHC.Base.id GHC.Base.op_z2218U__
*)
