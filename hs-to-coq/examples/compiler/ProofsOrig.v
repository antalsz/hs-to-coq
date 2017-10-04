Require Import Prelude.
Require Import CompilerOrig.

Import ListNotations.



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

(* Alternative proof that goes through with patternFailures *)

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

Axiom bottom_ne_cons : forall A (x : A) xs, (x :: xs) <> patternFailure.

Lemma stack_replace : forall e s s' i j, exec e (s' ++ i :: s) <> patternFailure ->
                                    exec e (s' ++ j :: s) <> patternFailure.
Proof.
  induction e; intros; simpl in *; auto.
  - destruct s'; simpl; apply bottom_ne_cons.
  - destruct a.
    replace  (i0 :: s' ++ j :: s) with
    ((i0 :: s') ++ j :: s); auto.
    apply IHe with (i:=i); auto.
  - destruct s'. simpl in *. destruct s. contradiction.
    match goal with
      | [ H:_  |- exec ?e ?s <> patternFailure] => rewrite <- (app_nil_l s)
    end.
    eapply IHe.
    simpl. eauto.
    simpl in *.
    destruct s'. simpl in *.
    match goal with
      | [ H:_  |- exec ?e ?s <> patternFailure] => rewrite <- (app_nil_l s)
    end.
    eapply IHe.
    simpl. eauto.
    simpl in *.
Admitted.

Lemma stack_extend : forall e s i, exec e s <> patternFailure ->
                               exec e (i :: s) <> patternFailure.
Proof.
  induction e; intros.
  simpl.
  simpl in H.
  apply bottom_ne_cons.
  - destruct a. simpl in *.
    apply IHe.
    eapply stack_replace with (s' := nil). simpl. eauto.
  - simpl. destruct s. contradiction.
    apply IHe.
    simpl in H. destruct s. contradiction.
    eapply stack_replace with (s' := nil). simpl. eauto.
Qed.

Lemma stack_extend_app : forall e s s', exec e s <> patternFailure ->
                               exec e (s' ++ s) <> patternFailure.
Proof.
  induction s'. simpl. auto.
  intros. simpl.
  apply stack_extend. auto.
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
