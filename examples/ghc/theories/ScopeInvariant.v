Require Import Core.
Require Import CoreFVs.
Require Import CoreUtils.

Require Import Coq.Lists.List.
Import ListNotations.

Require Import Proofs.Base.
Require Import Proofs.GhcTactics.
Require Import Proofs.Forall.
Require Import Proofs.CoreFVs.
Require Import Proofs.VarSet.

Set Bullet Behavior "Strict Subproofs".

(*
This file describes an invariant of Core files that
 * all variables must be in scope
 * and be structurally equal to their binder
*)

(* This returns a [Prop] rather than a bool because
   we do not have a function that determines structural
   equality.
*)

(* SCW: why not use the GHC.Base.== instance for Var here? 
   This instance just compares realUnique a and realUnique b. 
*)

Inductive almostEqual : Var -> Var -> Prop :=
 | AE_TyVar   : forall n u ty,
   almostEqual (Mk_TyVar n u ty)
               (Mk_TyVar n u ty)
 | AE_TcTyVar : forall n u ty1 ty2,
   almostEqual (Mk_TcTyVar n u ty1 ty2)
               (Mk_TcTyVar n u ty1 ty2)
 | AE_Id : forall n u ty ids idd id1 id2,
   almostEqual (Mk_Id n u ty ids idd id1)
               (Mk_Id n u ty ids idd id2).

Definition WellScopedVar (v : Var) (in_scope : VarSet) : Prop :=
   match lookupVarSet in_scope v with
    | None => False
    | Some v' => almostEqual v v'
    end.

Fixpoint WellScoped (e : CoreExpr) (in_scope : VarSet) {struct e} : Prop :=
  match e with
  | Mk_Var v => WellScopedVar v in_scope
  | Lit l => True
  | App e1 e2 => WellScoped e1 in_scope /\  WellScoped e2 in_scope
  | Lam v e => WellScoped e (extendVarSet in_scope v)
  | Let bind body =>
      WellScopedBind bind in_scope /\
      WellScoped body (extendVarSetList in_scope (bindersOf bind))
  | Case scrut bndr ty alts  => 
    WellScoped scrut in_scope /\
    Forall' (fun alt =>
      let in_scope' := extendVarSetList in_scope (bndr :: snd (fst alt)) in
      WellScoped (snd alt) in_scope') alts
  | Cast e _ =>   WellScoped e in_scope
  | Tick _ e =>   WellScoped e in_scope
  | Type_ _  =>   True
  | Coercion _ => True
  end
with WellScopedBind (bind : CoreBind) (in_scope : VarSet) : Prop :=
  match bind with
  | NonRec v rhs => WellScoped rhs in_scope
  | Rec pairs => 
     NoDup (map varUnique (map fst pairs)) /\
      Forall' (fun p => WellScoped (snd p) (extendVarSetList in_scope (map fst pairs))) pairs
  end.

Definition WellScopedAlt bndr (alt : CoreAlt) in_scope  :=
    let in_scope' := extendVarSetList in_scope (bndr :: snd (fst alt)) in
    WellScoped (snd alt) in_scope'.

Fixpoint WellScopedProgram (pgm : CoreProgram) (in_scope : VarSet) : Prop :=
  match pgm with
  | [] => True
  | bind :: pgm' =>
    WellScopedBind bind in_scope /\
    WellScopedProgram pgm' (extendVarSetList in_scope (bindersOf bind))
  end.

(** ** Lots of lemmas *)

(** *** [almostEqual] *)

Lemma almostEqual_refl:
  forall v, almostEqual v v.
Proof. intros. destruct v; constructor. Qed.

Lemma delVarSet_ae:
  forall vs v1 v2,
  almostEqual v1 v2 ->
  delVarSet vs v1 = delVarSet vs v2.
Proof.
  induction 1; simpl;
  unfold UniqFM.delFromUFM; simpl; auto.
Qed.

Lemma elemVarSet_ae:
  forall vs v1 v2,
  almostEqual v1 v2 ->
  elemVarSet v1 vs = elemVarSet v2 vs.
Proof.
  induction 1; simpl;
  unfold UniqFM.delFromUFM; simpl; auto.
Qed.

Axiom WellScoped_extendVarSet_ae:
  forall e vs v1 v2,
  almostEqual v1 v2 ->
  WellScoped e (extendVarSet vs v1) <-> WellScoped e (extendVarSet vs v2).


(** *** Structural lemmas *)

Lemma WellScoped_Lam:
  forall v e isvs,
  WellScoped (Lam v e) isvs <-> WellScoped e (extendVarSet isvs v).
Proof. intros. reflexivity. Qed.


Lemma WellScoped_mkLams:
  forall vs e isvs,
  WellScoped (mkLams vs e) isvs <-> WellScoped e (extendVarSetList  isvs vs).
Proof.
  induction vs; intros.
  * reflexivity.
  * simpl.
    rewrite extendVarSetList_cons.
    refine (IHvs _ _).
Qed.

Lemma WellScoped_varToCoreExpr:
  forall v isvs,
  WellScopedVar v isvs -> WellScoped (varToCoreExpr v) isvs.
Proof.
  intros.
  destruct v; simpl; try trivial.
  unfold varToCoreExpr; simpl.
  destruct_match; simpl; try trivial.
Qed.

Lemma WellScoped_mkVarApps:
  forall e vs isvs,
  WellScoped e isvs -> 
  Forall (fun v => WellScopedVar v isvs) vs ->
  WellScoped (mkVarApps e vs) isvs.
Proof.
  intros.
  unfold mkVarApps.
  rewrite Foldable.hs_coq_foldl_list.
  revert e H.
  induction H0; intros.
  * simpl. intuition.
  * simpl.
    apply IHForall; clear IHForall.
    simpl.
    split; try assumption.
    apply WellScoped_varToCoreExpr; assumption.
Qed.

Lemma WellScopedVar_extendVarSet:
  forall v vs,
  WellScopedVar v (extendVarSet vs v).
Proof.
  intros.
  unfold WellScopedVar.
  rewrite lookupVarSet_extendVarSet_self.
  apply almostEqual_refl.
Qed.

Lemma WellScoped_MkLetRec: forall pairs body isvs,
  WellScoped (mkLetRec pairs body) isvs <-> WellScoped (Let (Rec pairs) body) isvs .
Proof.
  intros.
  unfold mkLetRec.
  destruct pairs; try reflexivity.
  simpl.
  rewrite extendVarSetList_nil.
  split; intro; repeat split; try constructor; intuition.
Qed.

Lemma WellScoped_MkLet: forall bind body isvs,
  WellScoped (mkLet bind body) isvs <-> WellScoped (Let bind body) isvs .
Proof.
  intros.
  unfold mkLet.
  destruct bind; try reflexivity.
  destruct l; try reflexivity.
  simpl.
  rewrite extendVarSetList_nil.
  split; intro; repeat split; try constructor; intuition.
Qed.

(** *** Relation to [exprFreeVars] *)

Axiom WellScoped_subset:
  forall e vs,
  WellScoped e vs -> subVarSet (exprFreeVars e) vs = true.


(** *** Freshness *)

Axiom WellScopedVar_extendVarSetList_l:
  forall v vs1 vs2,
  WellScopedVar v vs1 ->
  elemVarSet v (mkVarSet vs2) = false ->
  WellScopedVar v (extendVarSetList vs1 vs2).

Axiom WellScopedVar_extendVarSetList_r:
  forall v vs1 vs2,
  In v vs2 ->
  NoDup (map varUnique vs2) ->
  WellScopedVar v (extendVarSetList vs1 vs2).


Lemma WellScoped_extendVarSet_fresh:
  forall v e vs,
  elemVarSet v (exprFreeVars e) = false ->
  WellScoped e (extendVarSet vs v) <-> WellScoped e vs.
Proof.
  intros.
  split.
  intro h.
  pose (K := WellScoped_subset e _ h). clearbody K.
  set (fve := exprFreeVars e) in *.
  
  unfold_VarSet.

  set (key := Unique.getWordKey (Unique.getUnique v)) in *.
Admitted.  

Axiom WellScoped_extendVarSetList_fresh:
  forall vs e vs1,
  disjointVarSet (exprFreeVars e) (mkVarSet vs) = true ->
  WellScoped e (extendVarSetList vs1 vs) <-> WellScoped e vs1.


Axiom WellScoped_extendVarSetList:
  forall vs e vs1,
  disjointVarSet vs1 (mkVarSet vs) = true ->
  WellScoped e vs1 -> WellScoped e (extendVarSetList vs1 vs).


Lemma WellScoped_extendVarSetList_fresh_under:
  forall vs1 vs2 e vs,
  disjointVarSet (exprFreeVars e) (mkVarSet vs1)  = true ->
  WellScoped e (extendVarSetList (extendVarSetList vs vs1) vs2) <-> WellScoped e (extendVarSetList vs vs2).
Proof.
  intros.
  rewrite <- WellScoped_mkLams.
  rewrite WellScoped_extendVarSetList_fresh.
  rewrite -> WellScoped_mkLams.
  reflexivity.
  rewrite exprFreeVars_mkLams.
  eapply disjointVarSet_subVarSet_l; only 1: eassumption.
  apply subVarSet_delVarSetList.
Qed.

