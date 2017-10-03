Require Import Prelude.
Require Import CompilerOrig.

Import ListNotations.

(* AKA comp_correct_book *)
Lemma distributivity : forall c s d,
    exec c s <> patternFailure ->
    exec (app c d) s =  exec d (exec c s).
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



Lemma app_assoc : forall A (a b c : list A), app a (app b c) = app (app a b) c.
Admitted.

Lemma classical : forall e s, exec e s = patternFailure \/ exec e s <> patternFailure.
Admitted.


Lemma comp_correct_book : forall e s,
    (forall s1, exec (comp e) s1 <> patternFailure) ->
    exec (comp e) s = eval e :: s.
Proof.
  induction e; intros s DEF.
  auto.
  simpl.
  rewrite <- app_assoc.
  rewrite distributivity.
  rewrite IHe1.
  rewrite distributivity.
  rewrite IHe2.
  simpl.
  auto.
  admit.
  admit.
Admitted.


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
