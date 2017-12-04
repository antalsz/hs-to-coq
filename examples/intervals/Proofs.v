(**
This file verifies some of the logic of Interval.hs from
bisect-binary. <https://github.com/nomeata/bisect-binary/>
*)


Require Import Intervals.

Require Import GHC.Base.

Require Import Coq.Sets.Ensembles.
Require Import Coq.Sets.Powerset_facts.
Import ListNotations.
Require Import Omega.

Definition goodI (i : Interval) : Prop :=
  match i with I f t => (f < t)%Z end.

Fixpoint goodLIs (is : list Interval) (lb : Z) : Prop :=
  match is with
    | [] => True
    | (I f t :: is) => (lb <= f)%Z /\ (f < t)%Z /\ goodLIs is t
  end.

Definition good is := match is with
  ival is => exists n, goodLIs is n end.

Definition range (f t : Z) : Ensemble Z :=
  (fun z => (f <= z)%Z /\ (z < t)%Z).

Definition semI (i : Interval) : Ensemble Z :=
  match i with I f t => range f t end.

Fixpoint semLIs (is : list Interval) : Ensemble Z :=
  match is with
    | [] => Empty_set Z
    | (i :: is) => Union Z (semI i) (semLIs is)
  end.

Definition sem is := match is with
  ival is => semLIs is end.
  
(* utils *)

Lemma range_empty (z : Z) :
  (z <= 0)%Z -> range 0 z = Empty_set Z.
Proof.
  intro H. apply Extensionality_Ensembles. split.
  * intros z' H2.
    unfold range, In in *.
    contradict H2.
    intuition.
  * apply Included_Empty.
Qed.

Lemma union_reorder:
  forall A s1 s2 s3 s4,
  Union A (Union A s1 s2) (Union A s3 s4) = 
  Union A (Union A s1 s3) (Union A s2 s4).
Proof.
  intros.
  repeat rewrite Union_associative.
  f_equal.
  repeat rewrite <- Union_associative.
  f_equal.
  apply Union_commutative.
Qed.

(** proofs *)

(** [nullIntervals] *)

Theorem nullIntervals_good : good nullInterval.
Proof.
  exists 0%Z. constructor.
Qed.

Theorem nullIntervals_spec : sem nullInterval = Empty_set Z.
Proof. reflexivity. Qed.

(** [fullIntervals] *)

Theorem fullIntervals_good : forall z, good (fullIntervals z).
Proof.
  intros.
  unfold fullIntervals, mkInterval.
  unfold GHC.Base.op_zl__, Ord_Integer___, op_zl____ in *.
  simpl in *.
  destruct (Z.ltb_spec 0 z).
  * exists 0%Z. unfold goodLIs. intuition.
  * exists 0%Z. unfold goodLIs. intuition.
Qed.

Theorem fullIntervals_spec (z : Z) : sem (fullIntervals z) = range 0 z.
Proof.
  intros.
  unfold fullIntervals, mkInterval.
  unfold GHC.Base.op_zl__, Ord_Integer___, op_zl____ in *.
  simpl in *.
  destruct (Z.ltb_spec 0 z).
  * simpl. rewrite Union_commutative. rewrite Empty_set_zero. reflexivity.
  * simpl. rewrite range_empty by assumption. reflexivity.
Qed.

(** [isEmpty] *)

Lemma isEmpty_specL (is : list Interval) (lb : Z) (Hgood : goodLIs is lb) :
  is = [] <-> (semLIs is = Empty_set Z).
Proof.
  split; intros.
  * subst. reflexivity.
  * destruct is; try congruence.
    destruct i.
    simpl in *.
    assert (In Z (range o o0) o).
    - unfold range. intuition.
    - eapply Union_introl in H0.
      rewrite H in H0.
      apply Noone_in_empty in H0.
      contradict H0.
Qed.

Theorem isEmpty_spec (i : Intervals) (Hgood : good i) :
  isEmpty i = true <-> (sem i = Empty_set Z).
Proof.
  destruct i.
  simpl.
  simpl in Hgood; destruct Hgood.
  unfold Foldable.null, Foldable.Foldable__list, Foldable.null__, Foldable.Foldable__list_null.
  rewrite <- isEmpty_specL by eassumption.
  destruct l; simpl; intuition; try congruence.
Qed.

(** unsafe fix *)

Axiom unsafeFix_eq: forall {a} (f : a -> a), unsafeFix f = f (unsafeFix f).

(** induction principle *)

Definition needs_reorder (is1 is2 : list Interval) : bool :=
  match is1, is2 with
    | (I f1 t1 :: _), (I f2 t2 :: _) => (t1 <? t2)%Z
    | _, _ => false
  end.

Definition size2 (is1 is2 : list Interval) : nat :=
  (if needs_reorder is1 is2 then 1 else 0) + 2 * length is1 + 2 * length is2.

Definition my_ind {A}
  (sz : A -> A -> nat)
  (P : A -> A -> Prop) :
  (forall a b, (forall x y, (sz x y < sz a b)%nat -> P x y) -> P a b ) ->
  forall x y, P x y.
Proof.
  intros.
  remember (sz x y) as n.
  revert x y Heqn.
  apply (lt_wf_ind n).
  intros. apply H. intros. apply H0 with (m := sz x0 y0); intuition.
Qed.

(** [union] *)

Lemma goodLIs_mono : forall is lb lb', (lb' <= lb)%Z -> goodLIs is lb -> goodLIs is lb'.
Proof.
  intros.
  induction is.
  * auto.
  * destruct a. simpl in *. intuition.
Qed.

Lemma union_good : forall (is1 is2 : Intervals),
    good is1 -> good is2 -> good (union is1 is2).
Proof.
  intros.
  destruct is1 as [is1], is2 as [is2].
  destruct H as [lb1 H1] , H0 as [lb2 H2].
  exists (Z.min lb1 lb2).
  match goal with [ |- goodLIs (unsafeFix ?f _ _) _ ] => set (u := f) end.
  apply (goodLIs_mono _ _ _ (Z.le_min_l lb1 lb2)) in H1.
  apply (goodLIs_mono _ _ _ (Z.le_min_r lb1 lb2)) in H2.
  revert H1 H2.
  generalize (Z.min lb1 lb2).
  revert is1 is2.
  refine (my_ind size2 _ _).
  intros is1 is2 IH lb H1 H2.
  rewrite unsafeFix_eq.
  destruct is1 as [|i1 is1], is2 as [|i2 is2].
  * simpl. trivial.
  * destruct i2. simpl in *. intuition.
  * destruct i1. simpl in *. intuition.
  * simpl.
    unfold GHC.Base.op_zl__, Ord_Integer___, op_zl____ in *.
    unfold GHC.Base.op_zg__, Ord_Integer___, op_zg____ in *.
    destruct (Z.ltb_spec (to i1) (to i2)); [|destruct (Z.ltb_spec (to i2) (from i1))];
    destruct i1 as [f1 t1], i2 as [f2 t2].
    - apply IH; try assumption.
      + unfold size2. simpl in *. repeat rewrite Z.ltb_irrefl.
        destruct (Z.ltb_spec t2 t1), (Z.ltb_spec t1 t2); simpl; omega.
    - simpl in *. repeat rewrite Z.min_le_iff.
      intuition.
      apply IH.
      + destruct is2 as [|[f2' t2'] is].
        -- unfold size2. simpl in *. repeat rewrite Z.ltb_irrefl.
           destruct (Z.ltb_spec t1 t2); simpl; omega.
        -- unfold size2. simpl in *. repeat rewrite Z.ltb_irrefl.
           destruct (Z.ltb_spec t1 t2'), (Z.ltb_spec t1 t2); simpl; omega.
      + simpl. intuition.
      + simpl. intuition.
    - simpl in *.
      apply IH.
      + destruct is2 as [|[f2' t2'] is].
        -- unfold size2. simpl in *. repeat rewrite Z.ltb_irrefl.
           destruct (Z.ltb_spec t1 t2); simpl; omega.
        -- unfold size2. simpl in *. repeat rewrite Z.ltb_irrefl.
           destruct (Z.ltb_spec t1 t2'), (Z.ltb_spec t1 t2); simpl; omega.
      + simpl. intuition.
        rewrite Z.min_glb_iff in *. intuition.
        rewrite  Z.min_lt_iff in *. intuition.
      + simpl. intuition.
        refine (goodLIs_mono _ _ _ _ H7). intuition.
Qed.

Lemma union_spec : forall (is1 is2 : Intervals),
    good is1 -> good is2 -> sem (union is1 is2) = Union Z (sem is1) (sem is2).
Proof.
  intros.
  destruct is1 as [is1], is2 as [is2].
  destruct H as [lb1 H1] , H0 as [lb2 H2].
  unfold union.
  match goal with [ |- context [unsafeFix ?f _ _]  ] => set (u := f) end.
  apply (goodLIs_mono _ _ _ (Z.le_min_l lb1 lb2)) in H1.
  apply (goodLIs_mono _ _ _ (Z.le_min_r lb1 lb2)) in H2.
  simpl.
  revert H1 H2.
  generalize (Z.min lb1 lb2).
  revert is1 is2.
  refine (my_ind size2 _ _).
  intros is1 is2 IH lb H1 H2.
  rewrite unsafeFix_eq.
  destruct is1 as [|i1 is1], is2 as [|i2 is2].
  * simpl. rewrite Empty_set_zero. reflexivity.
  * destruct i2. simpl in *. intuition.
  * destruct i1. simpl in *. 
    generalize (Union Z (range o o0) (semLIs is1)). intro. (* ugh *)
    rewrite Union_commutative at 1. rewrite  Empty_set_zero. intuition.
  * simpl.
    unfold GHC.Base.op_zl__, Ord_Integer___, op_zl____ in *.
    unfold GHC.Base.op_zg__, Ord_Integer___, op_zg____ in *.
    destruct (Z.ltb_spec (to i1) (to i2)); [|destruct (Z.ltb_spec (to i2) (from i1))];
    destruct i1 as [f1 t1], i2 as [f2 t2].
    - rewrite IH with (z:=lb).
      + intuition.
      + unfold size2. simpl in *. repeat rewrite Z.ltb_irrefl.
        destruct (Z.ltb_spec t2 t1), (Z.ltb_spec t1 t2); simpl; omega.
      + assumption.
      + assumption.
    - simpl in *. repeat rewrite Z.min_le_iff.
      intuition.
      rewrite IH with (z:=t2).
      + simpl. intuition. clear dependent u.
        (* reorder Union *)
        repeat rewrite Union_associative.
        rewrite Union_commutative.
        repeat rewrite Union_associative.
        do 2 f_equal.
        rewrite Union_commutative.
        reflexivity.
      + destruct is2 as [|[f2' t2'] is].
        -- unfold size2. simpl in *. repeat rewrite Z.ltb_irrefl.
           destruct (Z.ltb_spec t1 t2); simpl; omega.
        -- unfold size2. simpl in *. repeat rewrite Z.ltb_irrefl.
           destruct (Z.ltb_spec t1 t2'), (Z.ltb_spec t1 t2); simpl; omega.
      + simpl in *. intuition.
      + simpl. intuition.
    - simpl in *.
      rewrite IH with (z:=lb).
      + simpl. clear dependent u.
        rewrite union_reorder.
        rewrite Union_associative.
        f_equal.
        (* range and min *)
        apply Extensionality_Ensembles. split.
        ** intros z' H3.
           unfold range, In in *.
           rewrite Z.min_le_iff in *.
           intuition.
           left. unfold In. intuition.
           destruct (Z.ltb_spec z' t2).
           right. unfold In. intuition.
           left. unfold In. intuition.
        ** intros z' H3.
           apply Union_inv in H3.
           unfold range, In in *.
           rewrite Z.min_le_iff in *.
           intuition.
      + destruct is2 as [|[f2' t2'] is].
        -- unfold size2. simpl in *. repeat rewrite Z.ltb_irrefl.
           destruct (Z.ltb_spec t1 t2); simpl; omega.
        -- unfold size2. simpl in *. repeat rewrite Z.ltb_irrefl.
           destruct (Z.ltb_spec t1 t2'), (Z.ltb_spec t1 t2); simpl; omega.
      + simpl. intuition.
        rewrite Z.min_glb_iff in *. intuition.
        rewrite  Z.min_lt_iff in *. intuition.
      + simpl. intuition.
        refine (goodLIs_mono _ _ _ _ H7). intuition.
Qed.


Lemma intersect_good : forall (is1 is2 : Intervals),
    good is1 -> good is2 -> good (intersect is1 is2).
Proof.
  intros.
  destruct is1 as [is1], is2 as [is2].
  destruct H as [lb1 H1] , H0 as [lb2 H2].
  exists (Z.min lb1 lb2).
  match goal with [ |- goodLIs (unsafeFix ?f _ _) _ ] => set (u := f) end.
  apply (goodLIs_mono _ _ _ (Z.le_min_l lb1 lb2)) in H1.
  apply (goodLIs_mono _ _ _ (Z.le_min_r lb1 lb2)) in H2.
  revert H1 H2.
  generalize (Z.min lb1 lb2).
  revert is1 is2.
  refine (my_ind size2 _ _).
  intros is1 is2 IH lb H1 H2.
  rewrite unsafeFix_eq.
  destruct is1 as [|i1 is1], is2 as [|i2 is2].
  * simpl. trivial.
  * destruct i2. simpl in *. intuition.
  * destruct i1. simpl in *. intuition.
  * simpl.
    unfold GHC.Base.op_zl__, Ord_Integer___, op_zl____ in *.
    unfold GHC.Base.op_zgze__, Ord_Integer___, op_zgze____ in *.
    unfold GHC.Base.op_zeze__, Eq_Integer___, op_zeze____ in *.
    destruct i1 as [f1 t1], i2 as [f2 t2]; simpl in *.
    destruct (Z.ltb_spec t1 t2);
      [|destruct (Z.leb_spec t2 f1)];
      [| |destruct (Z.eqb_spec t1 t2)].
    - apply IH; clear dependent u.
      + unfold size2. simpl in *. repeat rewrite Z.ltb_irrefl.
        destruct (Z.ltb_spec t2 t1), (Z.ltb_spec t1 t2); simpl; omega.
      + assumption.
      + assumption.
    - simpl in *. repeat rewrite Z.min_le_iff.
      intuition.
      apply IH;  clear dependent u.
      + destruct is2 as [|[f2' t2'] is].
        -- unfold size2. simpl in *. repeat rewrite Z.ltb_irrefl.
           destruct (Z.ltb_spec t1 t2); simpl; omega.
        -- unfold size2. simpl in *. repeat rewrite Z.ltb_irrefl.
           destruct (Z.ltb_spec t1 t2'), (Z.ltb_spec t1 t2); simpl; omega.
      + simpl. intuition.
      + simpl. refine (goodLIs_mono _ _ _ _ H7). intuition.
    - simpl in *. repeat rewrite Z.max_le_iff. repeat rewrite Z.max_lub_lt_iff.
      intuition.
      apply IH; clear dependent u.
      + unfold size2. simpl in *.
        destruct is1 as [|[f1' t1'] is1];
        destruct is2 as [|[f2' t2'] is2].
        -- unfold size2. simpl in *. repeat rewrite Z.ltb_irrefl.
           destruct (Z.ltb_spec t1 t2); simpl; omega.
        -- unfold size2. simpl in *. repeat rewrite Z.ltb_irrefl.
           destruct (Z.ltb_spec t1 t2); simpl; omega.
        -- unfold size2. simpl in *. repeat rewrite Z.ltb_irrefl.
           destruct (Z.ltb_spec t1 t2); simpl; omega.
        -- unfold size2. simpl in *. repeat rewrite Z.ltb_irrefl.
           destruct (Z.ltb_spec t1 t2), (Z.ltb_spec t1' t2'); simpl; omega.
      + simpl. refine (goodLIs_mono _ _ _ _ H6). intuition.
      + simpl. refine (goodLIs_mono _ _ _ _ H7). intuition.
    - simpl in *. repeat rewrite Z.max_le_iff. repeat rewrite Z.max_lub_lt_iff.
      intuition.
      apply IH; clear dependent u.
      + destruct is2 as [|[f2' t2'] is].
        -- unfold size2. simpl in *. repeat rewrite Z.ltb_irrefl.
           destruct (Z.ltb_spec t1 t2); simpl; omega.
        -- unfold size2. simpl in *. repeat rewrite Z.ltb_irrefl.
           destruct (Z.ltb_spec t1 t2'), (Z.ltb_spec t1 t2); simpl; omega.
      + simpl. intuition.
      + simpl. intuition.
Qed.
