Require Import Prelude.
Require Import CompilerOrig.

Import ListNotations.


(* Alternative proof that goes through, even
   with patternFailures in the code.
*)

Lemma comp_correct_helper: forall e s d,
    exec (comp e ++ d) s =  exec d (eval e :: s).
Proof.
  induction e; intros; auto.
  simpl.
  rewrite <- app_assoc.
  rewrite <- app_assoc.
  rewrite IHe1.
  rewrite IHe2.
  simpl.
  reflexivity.
Qed.

Theorem comp_correct: forall e,
    exec (comp e) [] = [eval e].
Proof.
  intros.
  replace (comp e) with (comp e ++ []) by apply app_nil_r.
  apply comp_correct_helper.
Qed.

(* Anther approach that tries to follow the original code
   in the presence of pattenFailure *)

(* Nice, but actually useless: The precondition cannot be
   shown for concrete [c] and [s]. *)
(* AKA comp_correct_book *)
Lemma distributivity: forall c s d,
    exec c s <> patternFailure ->
    exec (c ++ d) s =  exec d (exec c s).
Proof.
  induction c; intros; auto.
  destruct a.
  - simpl. rewrite IHc. auto.
    simpl in H. auto.
  - simpl. destruct s. simpl in H. contradiction.
    destruct s. simpl in H. contradiction.
    simpl in H.
    rewrite IHc.
    auto. auto.
Qed.

(* We need a precondition to this lemma too. Can't put my finger on it though. *)
Lemma comp_correct_book : forall e s,
    exec (comp e) s = eval e :: s.
Proof.
  induction e; intros s.
  auto.
  simpl.
  rewrite <- app_assoc.
  rewrite distributivity.
  rewrite IHe1.
  rewrite distributivity.
  rewrite IHe2.
  simpl.
  auto.
  admit. (* exec (comp e2) (eval e1 :: s) <> patternFailure *)
  admit. (* Cannot prove exec (comp e1) s <> patternFailure *)
Abort.
