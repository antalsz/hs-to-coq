Require Import Name.
Require Import Id.
Require Import Core.
Require Import CoreFVs.
Require Import CoreUtils.

Require Import Coq.Lists.List.
Import ListNotations.

Require Import Proofs.Base.
Require Import Proofs.GhcTactics.
Require Import Proofs.Forall.
Require Import Proofs.Unique.
Require Import Proofs.CoreFVs.
Require Import Proofs.VarSet.
Require Import Proofs.CoreInduct.
Require Import Proofs.Var.

Import GHC.Base.ManualNotations.



Set Bullet Behavior "Strict Subproofs".

(*
This file describes an invariant of Core files that
 * all variables must be in scope
 * and be structurally almost equal to their binder
 * all local variables are indeed local variables
   (both according to [IdDetail] and [isLocalUnique])
*)

Definition WellScopedVar (v : Var) (in_scope : VarSet) : Prop :=
  if isLocalVar v then
   match lookupVarSet in_scope v with
    | None => False
    | Some v' => almostEqual v v'
    end
  else True (* we do not track local variables yet *).

(**
This captures all invariants that we can state about a
[Var] in isolation:
- It is a localVar when the unique is local.
- Its unique agrees with the unique of the name
*)
Definition GoodVar (v : Var) : Prop :=
  isLocalVar v = isLocalUnique (varUnique v) /\
  varUnique v = nameUnique (varName v).

Definition GoodLocalVar (v : Var) : Prop :=
  GoodVar v /\ isLocalVar v = true.

Fixpoint WellScoped (e : CoreExpr) (in_scope : VarSet) {struct e} : Prop :=
  match e with
  | Mk_Var v => WellScopedVar v in_scope
  | Lit l => True
  | App e1 e2 => WellScoped e1 in_scope /\  WellScoped e2 in_scope
  | Lam v e => GoodLocalVar v /\ WellScoped e (extendVarSet in_scope v)
  | Let bind body =>
      WellScopedBind bind in_scope /\
      WellScoped body (extendVarSetList in_scope (bindersOf bind))
  | Case scrut bndr ty alts  => 
    WellScoped scrut in_scope /\
    GoodLocalVar bndr /\
    Forall' (fun alt =>
      Forall GoodLocalVar (snd (fst alt)) /\
      let in_scope' := extendVarSetList in_scope (bndr :: snd (fst alt)) in
      WellScoped (snd alt) in_scope') alts
  | Cast e _ =>   WellScoped e in_scope
  | Tick _ e =>   WellScoped e in_scope
  | Type_ _  =>   True
  | Coercion _ => True
  end
with WellScopedBind (bind : CoreBind) (in_scope : VarSet) : Prop :=
  match bind with
  | NonRec v rhs =>
    GoodLocalVar v /\
    WellScoped rhs in_scope
  | Rec pairs => 
    Forall (fun p => GoodLocalVar (fst p)) pairs /\
    NoDup (map varUnique (map fst pairs)) /\
    Forall' (fun p => WellScoped (snd p) (extendVarSetList in_scope (map fst pairs))) pairs
  end.

Definition WellScopedAlt bndr (alt : CoreAlt) in_scope  :=
    Forall GoodLocalVar (snd (fst alt)) /\
    let in_scope' := extendVarSetList in_scope (bndr :: snd (fst alt)) in
    WellScoped (snd alt) in_scope'.

(** We can treat a [CoreProgram] as one big recursive group, it seems. *)
Definition WellScopedProgram (pgm : CoreProgram) : Prop :=
   NoDup (map varUnique (bindersOfBinds pgm)) /\
   Forall' (fun p => WellScoped (snd p) (mkVarSet (bindersOfBinds pgm))) (flattenBinds pgm).


(** ** Lots of lemmas *)

(** *** [almostEqual] *)

Axiom WellScoped_extendVarSet_ae:
  forall e vs v1 v2,
  almostEqual v1 v2 ->
  WellScoped e (extendVarSet vs v1) <-> WellScoped e (extendVarSet vs v2).

Axiom WellScoped_extendVarSetList_ae:
  forall e vs vs1 vs2,
  Forall2 almostEqual vs1 vs2 ->
  WellScoped e (extendVarSetList vs vs1) <-> WellScoped e (extendVarSetList vs vs2).


(** *** Structural lemmas *)

Lemma WellScoped_Lam:
  forall v e isvs,
  WellScoped (Lam v e) isvs <-> GoodLocalVar v /\ WellScoped e (extendVarSet isvs v).
Proof. intros. reflexivity. Qed.


Lemma WellScoped_mkLams:
  forall vs e isvs,
  WellScoped (mkLams vs e) isvs <-> Forall GoodLocalVar vs /\ WellScoped e (extendVarSetList isvs vs).
Proof.
  induction vs; intros.
  * intuition.
  * simpl.
    rewrite extendVarSetList_cons.
    rewrite Forall_cons_iff.
    rewrite and_assoc.
    rewrite <- (IHvs _ _).
    reflexivity.
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
  destruct_match.
  * apply almostEqual_refl.
  * trivial.
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

(** *** StrongSubset *)

Lemma WellScopedVar_StrongSubset : forall e vs1 vs2, 
    WellScopedVar e vs1 -> StrongSubset vs1 vs2 -> WellScopedVar e vs2.
Proof.
  intros v vs1 vs2 WS SS.
  unfold WellScopedVar, StrongSubset in *.
  destruct_match; only 2: trivial.
  specialize (SS v).
  destruct (lookupVarSet vs1 v); try contradiction.
  destruct (lookupVarSet vs2 v) eqn:LV2; try contradiction.
  eapply almostEqual_trans with (v2 := v0); auto.
Qed.

Lemma WellScoped_StrongSubset : forall e vs1 vs2, 
    WellScoped e vs1 -> StrongSubset vs1 vs2 -> WellScoped e vs2.
Proof.
  intro e.
  apply (core_induct e); intros; try (destruct binds);
    unfold WellScoped in *; fold WellScoped in *; eauto.
  - eapply WellScopedVar_StrongSubset; eauto.
  - destruct H1. split; eauto.
  - split; only 1: apply H0.
    destruct H0 as [_ H0].
    eapply H; eauto.
    unfold StrongSubset in *.
    intro var.
    specialize (H1 var).
    unfold CoreBndr in v. (* make sure that the type class looks right.*)
    destruct (v GHC.Base.== var) eqn:Eq.
    + rewrite lookupVarSet_extendVarSet_eq; auto.
      rewrite lookupVarSet_extendVarSet_eq; auto.
      eapply almostEqual_refl.
    + rewrite lookupVarSet_extendVarSet_neq.
      destruct (lookupVarSet vs1 var) eqn:IN; auto.
      rewrite lookupVarSet_extendVarSet_neq.
      auto.
      intro h;
      rewrite h in Eq; discriminate.
      intro h;
      rewrite h in Eq; discriminate.
  - destruct H1 as [[GLV WE] Wb].
     split; only 1: split; eauto.
     eapply H0; eauto.
     eapply StrongSubset_extendVarSetList.
     auto.
  - destruct H1 as [[WE1 [WE2 WE3]] Wb].
     repeat split; auto.
     rewrite Forall'_Forall in *.
     rewrite Forall_forall in *.
     intros h IN. destruct h as [v rhs].
     specialize (WE3 (v,rhs)).
     simpl in *.
     eauto using StrongSubset_extendVarSetList.
     eauto using StrongSubset_extendVarSetList.
  - destruct H1 as [W1 [W2 W3]].
    split; only 2: split; eauto.
     rewrite Forall'_Forall in *.
     rewrite Forall_forall in *.
     intros h IN. destruct h as [[dc pats] rhs].
     specialize (H0 dc pats rhs IN).
     specialize (W3 (dc,pats,rhs) IN).
     simpl in *.
     destruct W3 as [GLV WS].
     eauto using StrongSubset_extendVarSetList.
Qed.

(** *** Relation to [exprFreeVars] *)

(* This proof will be nicer if we have a naive calculation
   of exprFreeVars, and first rewrite to that one.*)
Lemma WellScoped_subset:
  forall e vs,
    WellScoped e vs -> subVarSet (exprFreeVars e) vs = true.
Proof.
  intro e.
  unfold exprFreeVars, exprFVs, Base.op_z2218U__.
  unfold FV.fvVarSet, Base.op_z2218U__,
         FV.fvVarListVarSet, FV.filterFV, Base.const, andb.

  apply (core_induct e); intros.
  - unfold WellScoped, WellScopedVar in *.
    destruct (isLocalVar v) eqn:HisLocal.
    + destruct (lookupVarSet vs v) eqn:Hl; try contradiction.
      unfold expr_fvs, FV.unitFV.
      rewrite elemVarSet_emptyVarSet.
      rewrite HisLocal.
      unfold Tuple.snd.
      eapply subVarSet_extendVarSet_l.
      * apply subVarSet_emptyVarSet.
      * eassumption.
    + simpl. rewrite HisLocal.
      unfold Tuple.snd.
      apply subVarSet_emptyVarSet.
  - apply subVarSet_emptyVarSet.
  - simpl.
    admit.
Admitted.


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

Instance Respects_StrongSubset_WellScopedVar v : Respects_StrongSubset (WellScopedVar v).
Proof.
  admit.
Admitted.

Instance Respects_StrongSubset_WellScoped e : Respects_StrongSubset (WellScoped e).
Proof.
  admit.
Admitted.

Lemma WellScoped_extendVarSetList_fresh_under:
  forall vs1 vs2 e vs,
  disjointVarSet (exprFreeVars e) (mkVarSet vs1)  = true ->
  WellScoped e (extendVarSetList (extendVarSetList vs vs1) vs2) <-> WellScoped e (extendVarSetList vs vs2).
Admitted.
(* Proof.
  intros.
  rewrite <- WellScoped_mkLams.
  rewrite WellScoped_extendVarSetList_fresh.
  rewrite -> WellScoped_mkLams.
  reflexivity.
  rewrite exprFreeVars_mkLams.
  eapply disjointVarSet_subVarSet_l; only 1: eassumption.
  apply subVarSet_delVarSetList.
Qed.
 *)

Lemma WellScoped_extendVarSetList_fresh_between:
  forall (vs1 vs2 vs3 : list Var) (e : CoreExpr) (vs : VarSet),
  disjointVarSet (delVarSetList (exprFreeVars e) vs3) (mkVarSet vs2) = true ->
  WellScoped e (extendVarSetList vs ((vs1 ++ vs2) ++ vs3)) <->
  WellScoped e (extendVarSetList vs (vs1 ++ vs3)).
Admitted.

(** ** Lemmas about [GoodLocalVar] *)

Lemma GoodLocalVar_asJoinid :
  forall v n, GoodLocalVar v -> GoodLocalVar (asJoinId v n).
Admitted.

Lemma GoodLocalVar_uniqAway:
  forall vss v, GoodLocalVar v -> GoodLocalVar (uniqAway vss v).
Admitted.

Lemma GoodLocalVar_mkSysLocal:
  forall s u ty, isLocalUnique u = true -> GoodLocalVar (mkSysLocal s u ty).
Admitted.

Lemma GoodLocalVar_almostEqual:
  forall v1 v2,
  GoodLocalVar v1 ->
  almostEqual v1 v2 ->
  GoodLocalVar v2.
Admitted.

