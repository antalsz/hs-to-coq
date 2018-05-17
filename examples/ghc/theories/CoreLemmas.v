Require Import Id.
Require Import Core.
Require Import CoreFVs.

Require Import Proofs.GHC.Base.
Require Import Proofs.GHC.List.
Require Import GhcProofs.Tactics.
Require Import GhcProofs.BaseLemmas.

Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Lists.List.
Import ListNotations.


Opaque Base.hs_string__.

Set Bullet Behavior "Strict Subproofs".

Open Scope list_scope.
Close Scope Z_scope.

(** ** AST functions *)

Lemma mkLets_append:
  forall b binds1 binds2 (e : Expr b),
  mkLets (binds1 ++ binds2) e = mkLets binds1 (mkLets binds2 e).
Proof.
  intros.
  unfold mkLets.
  rewrite Foldable_foldr_app.
  auto.
Qed.
  
Lemma mkLets_cons:
  forall b bind binds (e : Expr b),
  mkLets (bind :: binds) e = mkLet bind (mkLets binds e).
Proof.
  intros.
  unfold mkLets.
  unfold_Foldable.
  reflexivity.
Qed.

Lemma mkLets_nil:
  forall b (e : Expr b),
  mkLets [] e = e.
Proof.
  intros.
  unfold mkLets. unfold_Foldable.
  reflexivity.
Qed.


Lemma bindersOf_Rec:
  forall {v} (pairs : list (v * Expr v)),
  bindersOf (Rec pairs) = map fst pairs.
Proof.
  induction pairs; simpl; intros; auto.
  destruct a.
  now rewrite <- IHpairs.
Qed.



(** ** [AnnExpr] related lemmas *)

Lemma deAnnBinds_AnnRec:
 forall {a v} (pairs : list (v * AnnExpr v a)),
 deAnnBind (AnnRec pairs) = Rec (map (fun p => (fst p, deAnnotate (snd p))) pairs).
Proof.
  unfold deAnnBind.
  symmetry.
  rewrite <- flat_map_cons_f.
  f_equal; f_equal.
  extensionality x.
  now destruct x.
Qed.

Lemma deAnnotate_AnnLet_AnnRec:
 forall {a v} fvs pairs (e : AnnExpr a v),
 deAnnotate (fvs, AnnLet (AnnRec pairs) e)
  = Let (Rec (map (fun p => (fst p, deAnnotate (snd p))) pairs)) (deAnnotate e).
Proof.
  induction pairs; simpl; intros; auto.
  f_equal; f_equal.
  destruct a0; simpl; f_equal.
  symmetry.
  rewrite <- flat_map_cons_f.
  f_equal.
  extensionality x.
  now destruct x.
Qed.

(** ** [HasNLams] related lemmas (currently unused) *)


Fixpoint HasNLams {v : Type} (n : nat) (e : Expr v) : Prop :=
  match n, e with
  | 0, _ => True
  | S n, Lam _ e => HasNLams n e
  | _, _ => False
  end.

Fixpoint AnnHasNLams {a v : Type} (n : nat) (e : AnnExpr a v) : Prop :=
  match n, e with
  | 0, _ => True
  | S n, (_, AnnLam _ e) => AnnHasNLams n e
  | _, _ => False
  end.


Lemma AnnHasNLams_weaken : forall n a v (s : AnnExpr a v) v0 a0, 
    AnnHasNLams n s ->
    AnnHasNLams n (v0, AnnLam a0 s).
Proof.
  induction n.
  intros. 
  simpl in *; auto.
  intros. simpl in *. destruct s. destruct a1; try contradiction.
  eapply IHn in H.
  eauto.
Qed.

Require Import Omega.

Ltac name_collect collect := 
  match goal with [ |- context[collectNAnnBndrs ?n ?m] ] => 
                  unfold collectNAnnBndrs;
                  (match goal with [ |- context[?tm n ?ll m] ] => 
                                  set (collect := tm);
                                  simpl in collect
                   end)
  end.

Ltac name_go go := 
  match goal with [ |- context[collectNBinders ?n ?m] ] => 
                  unfold collectNBinders;
                  (match goal with [ |- context[?tm n ?ll m] ] => 
                                  set (go := tm)
                   end)
  end.



Lemma HasNLams_deAnnotate:
  forall { a v : Type} n (e : AnnExpr a v) `{GHC.Err.Default v},
  HasNLams n (deAnnotate e) <-> AnnHasNLams n e.
Proof.
  induction n; intros.
  * reflexivity.
  * destruct e as [fvs e']; destruct e'; simpl; try reflexivity.
    + apply IHn; assumption.
    + expand_pairs.
      reflexivity.
Qed.



Lemma deAnnotate_snd_collectNAnnBndrs:
  forall { a v : Type} n (e : AnnExpr a v) `{GHC.Err.Default v},
  AnnHasNLams n e ->
  deAnnotate (snd (collectNAnnBndrs n e)) = 
  snd (collectNBinders n (deAnnotate e)).
Proof.
  intros a v n.
  intros.

  name_collect collect.
  name_go go. 
  match goal with [ |- context[collect n ?ll e]] => generalize ll end.
  generalize n e H0. clear n e H0.
  induction n; intros.
  + destruct e.
    simpl.
    destruct (deAnnotate' a0);
      simplify_zeze;
      simpl;
      auto.
  + destruct e.
    destruct a0; try contradiction.
    destruct s.
    simpl in *.
    replace (n - 0) with n; auto.
    apply IHn; auto.
    omega.
Qed.