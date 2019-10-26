Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Lists.ListDec.
(*Helper Lemmas and tactics*)

Definition null {a} (l: list a) :=
  match l with
  | nil => true
  | _ => false
  end.

Ltac simplify' := try(rewrite andb_diag in *); try(rewrite andb_true_iff in *); try(rewrite negb_true_iff in *);
  try(rewrite andb_false_iff in *); try(rewrite negb_false_iff in *); intuition.

Ltac destruct_all :=
repeat(match goal with
            |[H: (exists _, _) |- _] => destruct H
            |[H: _ /\ _ |- _] => destruct H 
            end; try(rewrite andb_true_iff in *)).

(*Ltac for solving statements of the form: In x l, where l may be many lists appended together*) 
Ltac solve_in :=
  match goal with
  | [ H : _ |- In ?x (?l ++ ?r)] => apply in_or_app; solve_in
  | [ H : _ |- In ?x ?s \/ In ?x ?s'] => (right; solve_in) + (left; solve_in) 
  | [ H : _ |- In ?x (?x :: ?l)] => simpl; left; reflexivity
  | [H : _ |- In ?x (?a :: ?l)] => simpl; right; solve_in
  | [ H : _ |- _ ] => try(reflexivity); assumption
end. 

Lemma in_split_app_fst: forall (A: Type) (l: list A) (x: A),
  (forall x y : A, {x = y} + {x <> y}) ->
  In x l ->
  exists l1 l2, l = l1 ++ (x :: l2) /\ forall y, In y l1 -> y <> x.
Proof.
  intros. induction l.
  - inversion H.
  - destruct (X x a). subst. exists nil. exists l. split. reflexivity. intros. inversion H0.
    simpl in H. destruct H. subst. contradiction.  apply IHl in H. destruct_all.
    exists (a :: x0). exists x1. split. rewrite H. reflexivity. intros. intro. subst.
    simpl in H1. destruct H1. subst. contradiction. apply H0 in H. contradiction.
Qed.

Lemma no_no_dup: forall (A: Type) (l: list A),
  (forall x y : A, {x = y} + {x <> y}) ->
  ~(NoDup l) <-> (exists w l1 l2 l3, l = l1 ++ w :: l2 ++ w :: l3).
Proof.
  intros. split; intros.
  - induction l.
    + assert (@NoDup A nil). constructor. contradiction.
    + destruct (NoDup_dec X l).
      * assert (In a l). destruct (In_dec X a l). apply i.
        assert (NoDup (a :: l)). constructor. apply n0. apply n. contradiction.
        apply in_split_app_fst in H0. destruct_all. exists a. exists nil. exists x. exists x0.
        rewrite H0. reflexivity. apply X.
      * apply IHl in n. destruct_all. exists x. exists (a :: x0). exists x1. exists x2. rewrite H0.
        reflexivity.
  -  intro. destruct_all.  subst. induction x0; simpl in *.
    + rewrite NoDup_cons_iff in H0. destruct_all. apply H.
    solve_in.
    + simpl in H0. rewrite NoDup_cons_iff in H0. destruct_all. apply IHx0. apply H0.
Qed.