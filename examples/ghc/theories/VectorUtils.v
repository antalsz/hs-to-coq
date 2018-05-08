(** ** Vector utilities *)

Require Import Coq.Lists.List.
Require Vector.
Require Import  Coq.Program.Equality.

(** *** [to_list] *)

Lemma length_to_list:
  forall {A} {n : nat} {v : Vector.t A n},
  length (Vector.to_list v) = n.
Proof.
  intros.
  induction v.
  * simpl. auto.
  * simpl. f_equal. assumption.
Qed.

Lemma to_list_map:
  forall {n} {A B} (f : A -> B) (v : Vector.t A n),
  Vector.to_list (Vector.map f v) = map f (Vector.to_list v).
Proof.
  intros. induction v.
  - reflexivity.
  - simpl.
    unfold Vector.to_list in *.
    f_equal.
    apply IHv.
Qed.

Lemma to_list_cons:
  forall {n A} x (v : Vector.t A n),
  Vector.to_list (Vector.cons _ x _ v) = cons x (Vector.to_list v).
Proof. reflexivity. Qed.

Lemma to_list_append:
  forall {n n' A} (v1 : Vector.t A n) (v2 : Vector.t A n'),
  Vector.to_list (Vector.append v1 v2) = app (Vector.to_list v1) (Vector.to_list v2).
Proof.
  intros. induction v1.
  - reflexivity.
  - simpl.
    unfold Vector.to_list in *.
    f_equal.
    apply IHv1.
Qed.

Lemma to_list_eq_rect_r:
  forall {n m A} (xs : Vector.t A n) (H : m = n),
  @Vector.to_list _ m (eq_rect_r _ xs H) = Vector.to_list xs.
Proof. intros. rewrite H. auto. Qed.

Lemma to_list_nil:
  forall A,
  Vector.to_list (Vector.nil A) = nil.
Proof. reflexivity. Qed.

Lemma Forall2_to_list:
  forall A B n (P : A -> B -> Prop)  (v1: Vector.t A n) (v2: Vector.t B n),
  Forall2 P (Vector.to_list v1) (Vector.to_list v2) <->
  Vector.Forall2 P v1 v2.
Proof.
  induction n; intros; dependent destruction v1; dependent destruction v2.
  * intuition.
    - apply Vector.Forall2_nil.
    - apply Forall2_nil.
  * progress repeat rewrite to_list_cons.
    intuition.
    - dependent destruction H.
      apply IHn in H0.
      apply Vector.Forall2_cons; auto.
    - dependent destruction H.
      apply IHn in H0.
      apply Forall2_cons; try auto.
Qed.

(** *** [zip_with] *)

Section zip_with.
Set Implicit Arguments.
Variables (A : Type) (B : Type) (C : Type).
Variable f : A -> B -> C.
Fixpoint zip_with
  {n : nat} (xs : Vector.t A n) : Vector.t B n -> Vector.t C n
  := match xs in (Vector.t _ n) return Vector.t B n -> Vector.t C n with
  | Vector.nil _ => fun _ =>
    Vector.nil _
  | Vector.cons _ x _ xs => fun ys =>
    Vector.cons _ (f x (Vector.hd ys)) _ (zip_with xs (Vector.tl ys))
  end.
End zip_with.

Lemma map_zip_with:
  forall A B C D (f : C -> D) (g : A -> B -> C) n (xs : Vector.t A n) ys,
  Vector.map f (zip_with g xs ys) = zip_with (fun x y => f (g x y)) xs ys.
Proof.
  induction n; intros; dependent destruction xs; dependent destruction ys.
  * reflexivity.
  * simpl. rewrite IHn. reflexivity.
Qed.

Lemma zip_with_map_l:
  forall A B C D (f : A -> B) (g : B -> C -> D) n (xs : Vector.t A n) ys,
  zip_with g (Vector.map f xs) ys = zip_with (fun x y => g (f x) y) xs ys.
Proof.
  induction n; intros; dependent destruction xs; dependent destruction ys.
  * reflexivity.
  * simpl. rewrite IHn. reflexivity.
Qed.

Lemma nth_zip_with:
  forall A B C n (f : A -> B -> C) (xs : Vector.t A n) ys v,
  Vector.nth (zip_with f xs ys) v = f (Vector.nth xs v)  (Vector.nth ys v).
Proof.
  induction n; intros; dependent destruction v; dependent destruction xs; dependent destruction ys.
  * reflexivity.
  * simpl. apply IHn.
Qed.

Lemma In_zip_with:
  forall A B C n (f : A -> B -> C) (xs : Vector.t A n) ys x,
  In x (Vector.to_list (zip_with f xs ys)) <->
  (exists a b, In (a,b) (combine (Vector.to_list xs) (Vector.to_list ys)) /\ x = f a b).
Proof.
  induction n; intros; dependent destruction xs; dependent destruction ys.
  * split; intro.
    - simpl in H. inversion H.
    - simpl in H. destruct H as [?[?[??]]]. intuition.
  * split; intro.
    - inversion_clear H.
      + simpl in H0.
        exists h, h0. do 2 rewrite to_list_cons. intuition. left. reflexivity.
      + apply IHn in H0.
        destruct H0 as [? [? [??]]].
        exists x0, x1. intuition. right. assumption.
    - destruct H as [? [? [??]]]; subst.
      destruct H.
      + dependent destruction H. left. reflexivity.
      + right. apply IHn. exists x0, x1. intuition.
Qed.


Lemma Forall2_zip_with:
  forall A B C n (P : C -> C -> Prop) f1 f2 (v1 : Vector.t A n) (v2 : Vector.t B n),
  Vector.Forall2 P (zip_with f1 v1 v2) (zip_with f2 v1 v2) <->
  Vector.Forall2 (fun x y => P (f1 x y) (f2 x y)) v1 v2.
Proof.
  induction n; intros; dependent destruction v1; dependent destruction v2.
  * intuition (auto; apply Vector.Forall2_nil).
  * simpl.
    intuition.
    - dependent destruction H.
      apply IHn in H0.
      apply Vector.Forall2_cons; try auto.
    - dependent destruction H.
      apply IHn in H0.
      apply Vector.Forall2_cons; try auto.
Qed.

Lemma Forall2_combine:
  forall A B n (P : A -> B -> Prop) (v1 : Vector.t A n) (v2 : Vector.t B n),
  Vector.Forall2 P v1 v2 <->
  (forall x y,
  (In (x,y) (combine (Vector.to_list v1) (Vector.to_list v2))) -> P x y).
Proof.
  induction n; intros; dependent destruction v1; dependent destruction v2.
  * intuition. apply Vector.Forall2_nil.
  * repeat rewrite to_list_cons.
    simpl.
    intuition.
    - dependent destruction H.
      congruence.
    - dependent destruction H.
      rewrite IHn in H0.
      auto.
    - apply Vector.Forall2_cons; try auto.
      rewrite IHn; auto.
Qed.

Lemma combine_zip_with:
  forall A B n (xs : Vector.t A n) (ys : Vector.t B n),
  combine (Vector.to_list xs) (Vector.to_list ys) = Vector.to_list (zip_with (fun x y => (x, y)) xs ys).
Proof.
  dependent induction n; intros.
  * induction xs using Vector.case0.
    induction ys using Vector.case0.
    reflexivity.
  * induction n, xs using Vector.caseS.
    induction n, ys using Vector.caseS.
    repeat rewrite to_list_cons.
    simpl combine. simpl zip_with.
    repeat rewrite to_list_cons.
    f_equal. apply IHn.
Qed.

(** *** [nth] *)

Lemma In_exist_nths:
  forall n A (xs : Vector.t A n) x,
  In x (Vector.to_list xs) <-> (exists v, x = Vector.nth xs v).
Proof.
  dependent induction n; intros; dependent destruction xs; split; intro.
  * inversion H.
  * destruct H. dependent destruction x0.
  * rewrite to_list_cons in H.
    destruct H; subst.
    - exists Fin.F1. reflexivity.
    - apply IHn in H.
      destruct H as [v?].
      exists (Fin.FS v).
      apply H.
  * destruct H as [v?].
    rewrite to_list_cons.
    dependent destruction v.
    - left. simpl in H. congruence.
    - right. apply IHn. exists v. apply H.
Qed.

(** *** [all_fins] *)

Fixpoint all_fins n : Vector.t (Fin.t n) n :=
  match n with | 0 => Vector.nil _
               | S n => Vector.cons _ Fin.F1 _ (Vector.map Fin.FS (all_fins n)) end.


Lemma all_fins_complete:
  forall n x,
  In x (Vector.to_list (all_fins n)).
Proof.
  intros.
  dependent induction n.
  * dependent destruction x.
  * simpl all_fins.
    rewrite to_list_cons.
    dependent destruction x.
    - left. reflexivity.
    - right. rewrite to_list_map. apply in_map. apply IHn.
Qed.


Lemma nth_all_fins:
  forall n v,
  Vector.nth (all_fins n) v = v.
Proof.
  intros.
  dependent induction n; dependent destruction v; simpl.
  * reflexivity.
  * erewrite Vector.nth_map by reflexivity.
    rewrite IHn.
    reflexivity.
Qed.
Lemma In_nths_combine_all_fins:
  forall n A (xs : Vector.t A n) v,
  In (Vector.nth xs v, v) (combine (Vector.to_list xs) (Vector.to_list (all_fins n))).
Proof.
  intros.
  rewrite combine_zip_with.
  rewrite In_exist_nths.
  exists v.
  rewrite nth_zip_with.
  rewrite nth_all_fins.
  reflexivity.
Qed.

Lemma to_list_as_map_nth:
  forall A n (xs : Vector.t A n),
  Vector.to_list xs = map (fun i => Vector.nth xs i) (Vector.to_list (all_fins n)).
Proof.
  dependent induction n; intros.
  * dependent destruction xs. reflexivity.
  * dependent destruction xs.
    simpl all_fins.
    repeat rewrite to_list_cons.
    simpl map.
    rewrite IHn.
    rewrite to_list_map.
    rewrite map_map.
    simpl.
    reflexivity.
Qed.


