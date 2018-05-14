Require Import Core.
Require Import Tactics.
Require Import CoreFVs.

Require Import Coq.NArith.BinNat.


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


(*
Fixpoint HasNLams {v : Type} (n : BinNums.N) : Expr v -> Prop :=
  BinNat.N.recursion (fun e => True)
                     (fun m k (e:Expr v) => 
                        match e with Lam _ e' => k e' | _ => False end )
                     n.

Fixpoint AnnHasNLams {a v : Type} (n : BinNums.N) : AnnExpr a v -> Prop :=
  BinNat.N.recursion (fun e => True)
                     (fun m k e => 
                        match e with (_,AnnLam _ e') => k e' | _ => False end )
                     n.
*)

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

Lemma deAnnotate_snd_collectNAnnBndrs:
  forall { a v : Type} n (e : AnnExpr a v) `{GHC.Err.Default v},
  AnnHasNLams n e ->
  deAnnotate (snd (collectNAnnBndrs n e)) = 
  snd (collectNBinders n (deAnnotate e)).
Proof.
  intros.
  induction n; simpl in *.
  + destruct e.
    simpl.
    unfold collectNBinders.
    destruct (deAnnotate' a0);
      unfold Base.op_zeze__;
      unfold Nat.Eq_nat;
      unfold Base.op_zeze____;
      unfold Nat.eqb;
      simpl;
      auto.
  + destruct e.
    destruct a0; try contradiction.
    eapply AnnHasNLams_weaken in H0.
    apply IHn in H0. clear IHn.
Admitted.

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


Lemma collectNAnnBndrs_freeVars_mkLams:
  forall vs rhs,
  collectNAnnBndrs (length vs) (freeVars (mkLams vs rhs)) = (vs, freeVars rhs).
Admitted.

