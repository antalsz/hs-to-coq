Require Import Core.
Require Import Tactics.


Set Bullet Behavior "Strict Subproofs".

Open Scope nat_scope.

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


Lemma deAnnotate_snd_collectNAnnBndrs:
  forall { a v : Type} n (e : AnnExpr a v) `{GHC.Err.Default v},
  AnnHasNLams n e ->
  deAnnotate (snd (collectNAnnBndrs n e)) = snd (collectNBinders n (deAnnotate e)).
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
  