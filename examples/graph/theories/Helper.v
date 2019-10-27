Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Lists.ListDec.
Require Import Coq.Lists.SetoidList.
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

Lemma In_InA_equiv: forall A (x : A) l,
    In x l <-> InA eq x l.
  Proof.
    intros. induction l.
    - simpl. split; intros. 
      + destruct H.
      + apply InA_nil in H. destruct H.
    - simpl. split; intros.
      + apply InA_cons. destruct H. left. subst. reflexivity. right. apply IHl. assumption.
      + apply InA_cons in H. destruct H. left. subst. reflexivity. right. apply IHl. assumption.
  Qed.

Lemma NoDup_NoDupA: forall {a} (l: list a),
  NoDup l <-> NoDupA eq l.
Proof.
  intros; split; intros; induction H; try(constructor).
  - rewrite <- In_InA_equiv. assumption.
  - assumption.
  - rewrite In_InA_equiv. assumption.
  - assumption.
Qed.

Lemma contrapositive: forall (P Q : Prop), (P -> Q) -> (~Q -> ~P).
Proof.
  tauto.
Qed. 

(*If (x,y) is the only occurrence of x in l, we can find the first occurrence of (x,y)*)
Lemma in_split_app_fst_map: forall {A B: Type} {Eq1: (forall x y : A, {x = y} + {x <> y})}
   {Eq2: forall x y : B, {x = y} + {x <> y}}  (l: list (A * B)) x y,
  In (x, y) l ->
  (forall y', In (x, y') l -> y = y') ->
  exists l1 l2, l = l1 ++ ((x, y) :: l2) /\ forall y, In y (map fst l1) -> y <> x.
Proof.
  intros. induction l.
  - inversion H.
  - destruct a. simpl. destruct (Eq2 y b). subst. destruct (Eq1 x a). subst. exists nil.
    exists l. split. reflexivity. intros. inversion H1. 
    subst. simpl in H. destruct H. inversion H; subst. contradiction.
     apply IHl in H. destruct_all.
    exists ((a, b) :: x0). exists x1. split. rewrite H. reflexivity. intros. intro. subst.
    simpl in H2. destruct H2. subst. contradiction. apply H1 in H. contradiction.
    intros. apply H0. solve_in. destruct (Eq1 x a). subst. assert (y = b). apply H0.
    simpl. left. reflexivity. subst. contradiction. simpl in H. destruct H.
    inversion H; subst; contradiction. apply IHl in H.
    destruct_all. exists ((a, b) :: x0). exists x1. split. rewrite H. simpl. reflexivity.
    intros. simpl in H2. destruct H2. subst. intro. subst. contradiction. apply H1. assumption.
    intros. apply H0. solve_in.
Qed.

(*A more general form, if (x,y) is in l for some y, then there is a y' so that (x,y') is the first
  occurence of x*)
Lemma in_split_app_special:  forall {A B: Type} {Eq1: (forall x y : A, {x = y} + {x <> y})}
    (l: list (A * B)) x,
  In x (map fst l) ->
  exists y l1 l2, l = l1 ++ ((x, y) :: l2) /\ forall y, In y (map fst l1) -> y <> x.
Proof.
  intros. induction l.
  - destruct H.
  - simpl in *. destruct a. destruct (Eq1 x a). subst. destruct H. simpl in H. inversion H; subst. exists b.
    exists nil. exists l. split. reflexivity. intros. destruct H1.
    exists b. exists nil. exists l. split. reflexivity. intros. inversion H0.
    destruct H. simpl in H. inversion H. subst. contradiction. 
    apply IHl in H. destruct_all. exists x0. exists ((a, b) :: x1). exists x2. split. rewrite H. reflexivity.
    intros. simpl in H1. destruct H1. subst. auto. apply H0. assumption.
Qed.

(*If l1 ++ l2 is sorted, anything in l1 is less than anything in l2*)
Lemma sort_app: forall {A : Type} (l1 l2 : list A) R,
  Sorted R (l1 ++ l2) ->
  Relations_1.Transitive R ->
  (forall x y, In x l1 -> In y l2 -> R x y).
Proof.
  intros. generalize dependent l2. induction l1; intros.
  - simpl in H. destruct H1.
  - simpl in H. apply Sorted_StronglySorted in H. inversion H. subst.
    rewrite Forall_forall in H6. simpl in H1.
    destruct H1. subst. apply H6. solve_in. eapply IHl1.
    assumption. apply StronglySorted_Sorted . apply H5.
    assumption. assumption.
Qed. 

Lemma NoDup_pairs: forall {a b} (l1 : list (a * b)) x y y',
  NoDup (map fst l1) ->
  In (x,y) l1 ->
  In (x, y') l1 ->
  y = y'.
Proof.
  intros. induction l1.
  - destruct H0.
  - simpl in *. destruct a0. simpl in H. inversion H. subst.
    destruct H0. inversion H0; subst. destruct H1. inversion H1; subst.
    reflexivity. assert (In x (map fst l1)). rewrite in_map_iff. exists (x, y').
    simpl. split. reflexivity. assumption. contradiction.
    destruct H1. inversion H1; subst. assert (In x (map fst l1)). rewrite in_map_iff.
    exists (x, y). simpl. split. reflexivity. assumption. contradiction.
    apply IHl1; assumption.
Qed.
