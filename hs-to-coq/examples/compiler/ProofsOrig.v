Require Import Prelude.
Require Import CompilerOrig.

Import ListNotations.

Lemma comp_correct_helper: forall e s d,
    exec (comp e ++ d) s =  exec d (eval e :: s).
Proof.
  induction e; intros; auto.
  simpl.
  rewrite <- app_assoc.
  rewrite IHe1.
  rewrite <- app_assoc.
  rewrite IHe2.
  reflexivity.
Qed.

Theorem comp_correct: forall e,
    exec (comp e) [] = [eval e].
Proof.
  intros.
  replace (comp e) with (comp e ++ []) by apply app_nil_r.
  apply comp_correct_helper.
Qed.

(* Nice, but actually useless: The precondition cannot be
   shown for concrete [c] and [s]. *)
Lemma comp_correct_book: forall c s d,
    exec c s <> patternFailure ->
    exec (c ++ d) s =  exec d (exec c s).
Proof.
  induction c; intros.
  * reflexivity.
  * destruct a.
    - simpl.
      rewrite IHc.
      reflexivity.
      simpl in H. assumption.
    - simpl.
      destruct s.
      + simpl in H. contradict H. reflexivity.
      + destruct s.
        ** simpl in H. contradict H. reflexivity.
        ** rewrite IHc. reflexivity.
           simpl in H. assumption.
Qed.
