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

Require Combined.
Require Data.Tuple.
Require GHC.Base.
Import GHC.Base.Notations.

(* Converted type declarations: *)

Definition InterestingVarFun :=
  (Combined.Var -> bool)%type.

Definition FV :=
  (InterestingVarFun ->
   Combined.VarSet ->
   (list Combined.Var * Combined.VarSet)%type ->
   (list Combined.Var * Combined.VarSet)%type)%type.
(* Converted value declarations: *)

Definition delFV : Combined.Var -> FV -> FV :=
  fun var fv fv_cand in_scope acc =>
    fv fv_cand (Combined.extendVarSet in_scope var) acc.

Definition delFVs : Combined.VarSet -> FV -> FV :=
  fun vars fv fv_cand in_scope acc =>
    fv fv_cand (Combined.unionVarSet in_scope vars) acc.

Definition emptyFV : FV :=
  fun arg_0__ arg_1__ arg_2__ =>
    match arg_0__, arg_1__, arg_2__ with
    | _, _, acc => acc
    end.

Definition filterFV : InterestingVarFun -> FV -> FV :=
  fun fv_cand2 fv fv_cand1 in_scope acc =>
    fv (fun v => andb (fv_cand1 v) (fv_cand2 v)) in_scope acc.

Definition fvVarListVarSet : FV -> (list Combined.Var * Combined.VarSet)%type :=
  fun fv =>
    fv (GHC.Base.const true) Combined.emptyVarSet (pair nil Combined.emptyVarSet).

Definition fvVarSet : FV -> Combined.VarSet :=
  Data.Tuple.snd GHC.Base.∘ fvVarListVarSet.

Definition fvVarList : FV -> list Combined.Var :=
  Data.Tuple.fst GHC.Base.∘ fvVarListVarSet.

Definition fvDVarSet : FV -> Combined.DVarSet :=
  Combined.mkDVarSet GHC.Base.∘ (Data.Tuple.fst GHC.Base.∘ fvVarListVarSet).

Definition mapUnionFV {a} : (a -> FV) -> list a -> FV :=
  fix mapUnionFV arg_0__ arg_1__ arg_2__ arg_3__ arg_4__
        := match arg_0__, arg_1__, arg_2__, arg_3__, arg_4__ with
           | _f, nil, _fv_cand, _in_scope, acc => acc
           | f, cons a as_, fv_cand, in_scope, acc =>
               mapUnionFV f as_ fv_cand in_scope (f a fv_cand in_scope acc)
           end.

Definition unionsFV : list FV -> FV :=
  fun fvs fv_cand in_scope acc => mapUnionFV GHC.Base.id fvs fv_cand in_scope acc.

Definition unionFV : FV -> FV -> FV :=
  fun fv1 fv2 fv_cand in_scope acc =>
    fv1 fv_cand in_scope (fv2 fv_cand in_scope acc).

Definition unitFV : Combined.Var -> FV :=
  fun arg_0__ arg_1__ arg_2__ arg_3__ =>
    match arg_0__, arg_1__, arg_2__, arg_3__ with
    | var, fv_cand, in_scope, (pair have haveSet as acc) =>
        if Combined.elemVarSet var in_scope : bool then acc else
        if Combined.elemVarSet var haveSet : bool then acc else
        if fv_cand var : bool
        then pair (cons var have) (Combined.extendVarSet haveSet var) else
        acc
    end.

Definition mkFVs : list Combined.Var -> FV :=
  fun vars fv_cand in_scope acc => mapUnionFV unitFV vars fv_cand in_scope acc.

(* External variables:
     andb bool cons list nil op_zt__ pair true Combined.DVarSet Combined.Var
     Combined.VarSet Combined.elemVarSet Combined.emptyVarSet Combined.extendVarSet
     Combined.mkDVarSet Combined.unionVarSet Data.Tuple.fst Data.Tuple.snd
     GHC.Base.const GHC.Base.id GHC.Base.op_z2218U__
*)
