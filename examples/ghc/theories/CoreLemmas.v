Require Import Core.
Require Import Tactics.
Require Import CoreFVs.

Require Import Coq.NArith.BinNat.

Opaque Base.hs_string__.

Set Bullet Behavior "Strict Subproofs".

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

Ltac simplify_zeze :=
  unfold Base.op_zeze__;
  unfold Nat.Eq_nat;
  unfold Base.op_zeze____;
  unfold Nat.eqb.


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

Ltac unfold_Foldable :=
  unfold Foldable.foldr,
  Foldable.foldr__,
  Foldable.Foldable__list,
  Foldable.Foldable__list_foldr,
  Base.foldr.

Open Scope list_scope.

(* Haskell library reverse is equivalent to Coq library rev *)
Lemma reverse_rev : forall A (xs : list A), 
    List.rev xs = List.reverse xs.
Proof.
  intros A.
  unfold List.reverse.
  set (rev := fix rev (arg_0__ arg_1__ : list A) {struct arg_0__} : 
   list A :=
     match arg_0__ with
     | nil => arg_1__
     | x :: xs => rev xs (x :: arg_1__)
     end).
  induction xs.
  simpl.
  auto.
  simpl.
  rewrite <- List.rev_append_rev.
  replace (List.rev_append xs (a :: nil)) with 
      (List.rev_append (a :: xs) nil); auto.
Qed.

Lemma reverse_append : forall A (vs1:list A) (vs0:list A)  a ,
  (List.reverse (a :: vs0) ++ vs1 = List.reverse vs0 ++ (a :: vs1)).
Proof.
  intros A.
  intros.
  rewrite <- reverse_rev.
  rewrite <- reverse_rev.
  rewrite <- List.rev_append_rev.
  rewrite <- List.rev_append_rev.
  simpl.
  auto.
Qed.

Lemma collectNAnnBndrs_freeVars_mkLams:
  forall vs rhs,
  collectNAnnBndrs (length vs) (freeVars (mkLams vs rhs)) = (vs, freeVars rhs).
Proof.
  intros vs rhs.
  name_collect collect.
  assert (forall vs1 vs0 n, 
             n = length vs1 ->
             collect n vs0 (freeVars (mkLams vs1 rhs)) = (List.app (List.reverse vs0)  vs1, freeVars rhs)).
  { induction vs1; intros.
    + simpl in *.  subst. 
      unfold mkLams.
      unfold_Foldable.
      simpl. 
      rewrite List.app_nil_r.
      auto.
    + simpl in *. 
      destruct n; inversion H.
      pose (IH := IHvs1 (cons a vs0) n H1). clearbody IH. clear IHvs1.
      unfold mkLams in IH.
      unfold Foldable.foldr in IH.
      unfold Foldable.Foldable__list in IH.
      unfold Foldable.foldr__ in IH.
      simpl. 
      remember (freeVars (Foldable.Foldable__list_foldr Lam rhs vs1)) as fv.
      destruct fv.
      rewrite <-  H1.
      rewrite reverse_append in IH.
      auto.
  }       
  pose (K := H vs nil (length vs) eq_refl).
  simpl in K.
  auto.
Qed.


