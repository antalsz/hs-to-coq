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


Lemma deAnnotate_snd_collectNAnnBndrs:
  forall { a v : Type} n (e : AnnExpr a v) `{GHC.Err.Default v},
  AnnHasNLams n e ->
  deAnnotate (snd (collectNAnnBndrs (N.of_nat n) e)) = 
  snd (collectNBinders (N.of_nat n) (deAnnotate e)).
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
  collectNAnnBndrs (N.of_nat (length vs)) (freeVars (mkLams vs rhs)) = (vs, freeVars rhs).
Admitted.