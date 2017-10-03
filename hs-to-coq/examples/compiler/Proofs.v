Require Import Prelude.
Require Import Compiler.

Import ListNotations.

Definition apply {aT} {rT} (f : aT -> rT) x u :=
  if u is Some y then f y else x.

Definition bind {aT} {rT} (f : aT -> option rT) :=
  apply f None.


Lemma exec_app_distributivity: forall c d s,
    exec (c ++ d) s = bind (exec d) (exec c s).
Proof.
  induction c; intros; [auto|].
  destruct a; [simpl; auto|].
  destruct s; [auto|].
  destruct s; [auto|].
  simpl. auto.
Qed.

Lemma comp_correct_helper: forall e s,
    exec (comp e) s =  Some (eval e :: s).
Proof.
  induction e; intros; auto.
  simpl.
  rewrite exec_app_distributivity.
  rewrite IHe1.
  simpl.
  rewrite exec_app_distributivity.
  rewrite IHe2.
  auto.
Qed.

Theorem comp_correct: forall e,
    exec (comp e) [] = Some [eval e].
Proof.
  intros; apply comp_correct_helper; auto.
Qed.