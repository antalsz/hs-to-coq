(**
This file verifies some of the logic of Interval.hs from
bisect-binary. <https://github.com/nomeata/bisect-binary/>
*)


Require Import Intervals.

Require Import GHC.Base.
Require Import GHC.Err.

Require Import Coq.Sets.Ensembles.
Require Import Coq.Sets.Powerset_facts.
Require Import Ensemble_facts.
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

Lemma goodLIs_mono : forall is lb lb', (lb' <= lb)%Z -> goodLIs is lb -> goodLIs is lb'.
Proof.
  intros.
  induction is.
  * auto.
  * destruct a. simpl in *. intuition.
Qed.

Lemma good_sem_lb:
  forall is lb x,
  goodLIs is lb -> In Z (semLIs is) x -> (lb <= x)%Z.
Proof.
  intros.
  unfold In in *.
  induction is.
  * simpl in *. exfalso. intuition.
  * destruct a as [f t]; simpl in *; intuition.
    destruct H0; unfold In, range in *; intuition.
    apply IHis.
    refine (goodLIs_mono _ _ _ _ H3). intuition.
    auto.
Qed.

Lemma Intersection_range_range:
  forall f1 t1 f2 t2,
  Intersection Z (range f1 t1) (range f2 t2)
  = range (Z.max f1 f2) (Z.min t1 t2).
Proof.
  intros. apply Extensionality_Ensembles. split.
  * intros x H1. destruct H1. unfold In, range in *.
    rewrite Z.max_lub_iff.
    rewrite Z.min_glb_lt_iff.
    intuition.
  * intros x H. constructor;
    unfold In, range in *;
    rewrite Z.max_lub_iff in *;
    rewrite Z.min_glb_lt_iff in *;
    intuition.
Qed.

Lemma Intersection_range_range_empty:
  forall f1 t1 f2 t2,
  (t1 <= f2)%Z \/ (t2 <= f1)%Z ->
  Intersection Z (range f1 t1) (range f2 t2) = Empty_set Z.
Proof.
  intros. apply Extensionality_Ensembles. split.
  * intros x H1. destruct H1. unfold In, range in *.
    exfalso. intuition.
  * intuition.
Qed.

Lemma Included_range_range:
  forall f1 t1 f2 t2,
  (f2 <= f1)%Z /\ (t1 <= t2)%Z ->
  Included Z (range f1 t1) (range f2 t2).
Proof.
  intros.
  intros x H1.
  unfold In, range in *. intuition.
Qed.

Lemma Intersection_range_semLIs_empty:
  forall f t is lb,
  goodLIs is lb -> (t <= lb)%Z ->
  Intersection Z (range f t) (semLIs is) = Empty_set Z.
Proof.
  induction is; intros.
  * apply Disjoint_Empty_set_r.
  * destruct a as [f' t']. simpl in *.
    rewrite Distributivity.
    rewrite Intersection_range_range_empty.
    rewrite Empty_set_zero.
    apply IHis with (lb := t').
    intuition.
    intuition.
    intuition.
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

(** deferred fix *)

Axiom deferredFix_eq: forall {a} `{Default a} (f : a -> a), deferredFix f = f (deferredFix f).

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

Lemma union_good : forall (is1 is2 : Intervals),
    good is1 -> good is2 -> good (union is1 is2).
Proof.
  intros.
  destruct is1 as [is1], is2 as [is2].
  destruct H as [lb1 H1] , H0 as [lb2 H2].
  exists (Z.min lb1 lb2).
  match goal with [ |- goodLIs (deferredFix ?f _ _) _ ] => set (u := f) end.
  apply (goodLIs_mono _ _ _ (Z.le_min_l lb1 lb2)) in H1.
  apply (goodLIs_mono _ _ _ (Z.le_min_r lb1 lb2)) in H2.
  revert H1 H2.
  generalize (Z.min lb1 lb2).
  revert is1 is2.
  refine (my_ind size2 _ _).
  intros is1 is2 IH lb H1 H2.
  rewrite deferredFix_eq.
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
  match goal with [ |- context [deferredFix ?f _ _]  ] => set (u := f) end.
  apply (goodLIs_mono _ _ _ (Z.le_min_l lb1 lb2)) in H1.
  apply (goodLIs_mono _ _ _ (Z.le_min_r lb1 lb2)) in H2.
  simpl.
  revert H1 H2.
  generalize (Z.min lb1 lb2).
  revert is1 is2.
  refine (my_ind size2 _ _).
  intros is1 is2 IH lb H1 H2.
  rewrite deferredFix_eq.
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

(** [intersect] *)


Lemma intersect_good : forall (is1 is2 : Intervals),
    good is1 -> good is2 -> good (intersect is1 is2).
Proof.
  intros.
  destruct is1 as [is1], is2 as [is2].
  destruct H as [lb1 H1] , H0 as [lb2 H2].
  exists (Z.min lb1 lb2).
  match goal with [ |- goodLIs (deferredFix ?f _ _) _ ] => set (u := f) end.
  apply (goodLIs_mono _ _ _ (Z.le_min_l lb1 lb2)) in H1.
  apply (goodLIs_mono _ _ _ (Z.le_min_r lb1 lb2)) in H2.
  revert H1 H2.
  generalize (Z.min lb1 lb2).
  revert is1 is2.
  refine (my_ind size2 _ _).
  intros is1 is2 IH lb H1 H2.
  rewrite deferredFix_eq.
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

Lemma intersection_spec : forall (is1 is2 : Intervals),
    good is1 -> good is2 -> sem (intersect is1 is2) = Intersection Z (sem is1) (sem is2).
Proof.
  intros.
  destruct is1 as [is1], is2 as [is2].
  destruct H as [lb1 H1] , H0 as [lb2 H2].
  unfold intersect.
  match goal with [ |- context [deferredFix ?f _ _]  ] => set (u := f) end.
  apply (goodLIs_mono _ _ _ (Z.le_min_l lb1 lb2)) in H1.
  apply (goodLIs_mono _ _ _ (Z.le_min_r lb1 lb2)) in H2.
  simpl.
  revert H1 H2.
  generalize (Z.min lb1 lb2).
  revert is1 is2.
  refine (my_ind size2 _ _).
  intros is1 is2 IH lb H1 H2.
  rewrite deferredFix_eq.
  destruct is1 as [|i1 is1], is2 as [|i2 is2].
  * simpl. clear dependent u. 
    apply Extensionality_Ensembles. split.
    - intuition.
    - intros x H. destruct H. intuition.
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
    - rewrite IH with (z := lb). clear dependent u.
      + simpl.
        apply Intersection_commutative.
      + unfold size2. simpl in *. repeat rewrite Z.ltb_irrefl.
        destruct (Z.ltb_spec t2 t1), (Z.ltb_spec t1 t2); simpl; omega.
      + assumption.
      + assumption.
    - simpl in *. repeat rewrite Z.min_le_iff.
      intuition.
      rewrite IH with (z := lb). clear dependent u.
      + simpl.
        rewrite Distributivity.
        repeat rewrite Distributivity_l.
        rewrite Intersection_range_range_empty.
        rewrite Empty_set_zero.
        rewrite (Intersection_commutative _ (semLIs is1) (range f2 t2)).
        rewrite (Intersection_range_semLIs_empty _ _ _ _ H6).
        rewrite Empty_set_zero.
        reflexivity.
        intuition.
        intuition.
      + destruct is2 as [|[f2' t2'] is].
        -- unfold size2. simpl in *. repeat rewrite Z.ltb_irrefl.
           destruct (Z.ltb_spec t1 t2); simpl; omega.
        -- unfold size2. simpl in *. repeat rewrite Z.ltb_irrefl.
           destruct (Z.ltb_spec t1 t2'), (Z.ltb_spec t1 t2); simpl; omega.
      + simpl. intuition.
      + simpl. refine (goodLIs_mono _ _ _ _ H7). intuition.
    - simpl in *. repeat rewrite Z.max_le_iff. repeat rewrite Z.max_lub_lt_iff.
      intuition.
      rewrite IH with (z := t2). clear dependent u.
      + simpl. subst.
        rewrite Distributivity.
        repeat rewrite Distributivity_l.
        rewrite Intersection_range_range.
        rewrite (Intersection_commutative _ (semLIs is1) (range f2 t2)).
        rewrite (Intersection_range_semLIs_empty _ _ _ _ H6).
        rewrite Empty_set_zero_l.
        rewrite (Intersection_range_semLIs_empty _ _ _ _ H7).
        rewrite Empty_set_zero.
        f_equal. f_equal.
        rewrite Z.min_r.
        intuition. intuition. intuition. intuition.
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
      rewrite IH with (z := t2). clear dependent u.
      + simpl in *.
        rewrite Distributivity.
        repeat rewrite Distributivity_l.
        rewrite Intersection_range_range.
        rewrite (Intersection_commutative _ (semLIs is1) (range f2 t2)).
        rewrite (Intersection_range_semLIs_empty _ _ is1 _ H6) by intuition.
        rewrite Empty_set_zero_l.
        do 2 f_equal.
        rewrite Z.min_r. reflexivity.
        intuition.
        (* lets do it by hand *)
        apply Extensionality_Ensembles. split.
        ++ intros x H8.
           destruct H8. constructor.
           -- apply (good_sem_lb _ _ _ H7) in H8.
              unfold In, range in *. intuition.
           -- assumption.
        ++ intros x H8.
           destruct H8. constructor.
           -- apply (good_sem_lb _ _ _ H7) in H8.
              unfold In, range in *. intuition.
           -- assumption.
      + destruct is2 as [|[f2' t2'] is].
        -- unfold size2. simpl in *. repeat rewrite Z.ltb_irrefl.
           destruct (Z.ltb_spec t1 t2); simpl; omega.
        -- unfold size2. simpl in *. repeat rewrite Z.ltb_irrefl.
           destruct (Z.ltb_spec t1 t2'), (Z.ltb_spec t1 t2); simpl; omega.
      + simpl. intuition.
      + simpl. intuition.
Qed.

(** [subtract] *)

Lemma subtract_good : forall (is1 is2 : Intervals),
    good is1 -> good is2 -> good (subtract is1 is2).
Proof.
  intros.
  destruct is1 as [is1], is2 as [is2].
  destruct H as [lb1 H1] , H0 as [lb2 H2].
  exists (Z.min lb1 lb2).
  match goal with [ |- goodLIs (deferredFix ?f _ _) _ ] => set (u := f) end.
  apply (goodLIs_mono _ _ _ (Z.le_min_l lb1 lb2)) in H1.
  apply (goodLIs_mono _ _ _ (Z.le_min_r lb1 lb2)) in H2.
  revert H1 H2.
  generalize (Z.min lb1 lb2).
  revert is1 is2.
  refine (my_ind size2 _ _).
  intros is1 is2 IH lb H1 H2.
  rewrite deferredFix_eq.
  destruct is1 as [|i1 is1], is2 as [|i2 is2].
  * simpl. auto. 
  * destruct i2. simpl in *. intuition.
  * destruct i1. simpl in *. intuition.
  * simpl.
    unfold GHC.Base.op_zl__, Ord_Integer___, op_zl____ in *.
    unfold GHC.Base.op_zgze__, Ord_Integer___, op_zgze____ in *.
    unfold GHC.Base.op_zlze__, Ord_Integer___, op_zlze____ in *.
    destruct i1 as [f1 t1], i2 as [f2 t2]; simpl in *.
    destruct (Z.leb_spec t1 f2);
      [| destruct (Z.leb_spec t2 f1)];
      [| | destruct (Z.leb_spec f2 f1)];
      [| | destruct (Z.leb_spec t1 t2) | destruct (Z.leb_spec t1 t2)].
    - simpl. intuition. apply IH with (z := t1); clear dependent u.
      + unfold size2. simpl.
        destruct is1 as [|[f1' t1'] is1].
        -- unfold size2. simpl in *. repeat rewrite Z.ltb_irrefl.
           destruct (Z.ltb_spec t1 t2); simpl; omega.
        -- unfold size2. simpl in *. repeat rewrite Z.ltb_irrefl.
           destruct (Z.ltb_spec t1 t2), (Z.ltb_spec t1' t2); simpl; omega.
      + assumption.
      + simpl. intuition.
    - intuition. apply IH with (z := lb); clear dependent u.
      + unfold size2. simpl.
        destruct is2 as [|[f2' t2'] is2].
        -- unfold size2. simpl in *. repeat rewrite Z.ltb_irrefl.
           destruct (Z.ltb_spec t1 t2); simpl; omega.
        -- unfold size2. simpl in *. repeat rewrite Z.ltb_irrefl.
           destruct (Z.ltb_spec t1 t2), (Z.ltb_spec t1 t2'); simpl; omega.
      + simpl. intuition.
      + simpl. refine (goodLIs_mono _ _ _ _ H7). intuition.
    - intuition. apply IH with (z := lb); clear dependent u.
      + unfold size2. simpl.
        destruct is1 as [|[f1' t1'] is1].
        -- unfold size2. simpl in *. repeat rewrite Z.ltb_irrefl.
           destruct (Z.ltb_spec t1 t2); simpl; omega.
        -- unfold size2. simpl in *. repeat rewrite Z.ltb_irrefl.
           destruct (Z.ltb_spec t1' t2), (Z.ltb_spec t1 t2); simpl; omega.
      + simpl. refine (goodLIs_mono _ _ _ _ H8). intuition.
      + simpl. intuition.
    - simpl. intuition. apply IH with (z := lb); clear dependent u.
      + unfold size2. simpl.
        destruct is2 as [|[f2' t2'] is2].
        -- unfold size2. simpl in *. repeat rewrite Z.ltb_irrefl.
           destruct (Z.ltb_spec t1 t2); simpl; omega.
        -- unfold size2. simpl in *. repeat rewrite Z.ltb_irrefl.
           destruct (Z.ltb_spec t1 t2), (Z.ltb_spec t1 t2'); simpl; omega.
      + simpl. intuition.
      + simpl. refine (goodLIs_mono _ _ _ _ H9). intuition.
    - simpl. intuition. apply IH with (z := f2); clear dependent u.
      + unfold size2. simpl.
        destruct is1 as [|[f1' t1'] is1].
        -- unfold size2. simpl in *. repeat rewrite Z.ltb_irrefl.
           destruct (Z.ltb_spec t1 t2); simpl; omega.
        -- unfold size2. simpl in *. repeat rewrite Z.ltb_irrefl.
           destruct (Z.ltb_spec t1' t2), (Z.ltb_spec t1 t2); simpl; omega.
      + simpl. refine (goodLIs_mono _ _ _ _ H8). intuition.
      + simpl. intuition.
    - simpl. intuition. apply IH with (z := f2); clear dependent u.
      + unfold size2. simpl.
        destruct is2 as [|[f2' t2'] is2].
        -- unfold size2. simpl in *. repeat rewrite Z.ltb_irrefl.
           destruct (Z.ltb_spec t1 t2); simpl; omega.
        -- unfold size2. simpl in *. repeat rewrite Z.ltb_irrefl.
           destruct (Z.ltb_spec t1 t2'), (Z.ltb_spec t1 t2) ; simpl; omega.
      + simpl. intuition.
      + simpl. refine (goodLIs_mono _ _ _ _ H9). intuition.
Qed.


Lemma subtract_spec : forall (is1 is2 : Intervals),
    good is1 -> good is2 -> sem (subtract is1 is2) = Setminus Z (sem is1) (sem is2).
Proof.
  intros.
  destruct is1 as [is1], is2 as [is2].
  destruct H as [lb1 H1] , H0 as [lb2 H2].
  unfold subtract.
  match goal with [ |- context [deferredFix ?f _ _] ] => set (u := f) end.
  apply (goodLIs_mono _ _ _ (Z.le_min_l lb1 lb2)) in H1.
  apply (goodLIs_mono _ _ _ (Z.le_min_r lb1 lb2)) in H2.
  revert H1 H2.
  generalize (Z.min lb1 lb2).
  clear lb1 lb2.
  revert is1 is2.
  refine (my_ind size2 _ _).
  intros is1 is2 IH lb H1 H2.
  rewrite deferredFix_eq.
  destruct is1 as [|i1 is1], is2 as [|i2 is2].
  * simpl. clear dependent u.
    rewrite Seminus_Empty_r.
    reflexivity.
  * destruct i2. simpl in *. clear dependent u.
    rewrite Seminus_Empty_l.
    reflexivity.
  * destruct i1. simpl in *. clear dependent u.
    rewrite Seminus_Empty_r.
    reflexivity.
  * simpl.
    unfold GHC.Base.op_zl__, Ord_Integer___, op_zl____ in *.
    unfold GHC.Base.op_zgze__, Ord_Integer___, op_zgze____ in *.
    unfold GHC.Base.op_zlze__, Ord_Integer___, op_zlze____ in *.
    destruct i1 as [f1 t1], i2 as [f2 t2]; simpl in *.
    destruct (Z.leb_spec t1 f2);
      [| destruct (Z.leb_spec t2 f1)];
      [| | destruct (Z.leb_spec f2 f1)];
      [| | destruct (Z.leb_spec t1 t2) | destruct (Z.leb_spec t1 t2)].
    - simpl. intuition. rewrite IH with (z := t1); clear dependent u.
      + simpl.
        rewrite Setminus_Union.
        f_equal.
        symmetry.
        apply Setminus_noop.
        rewrite Distributivity.
        rewrite Intersection_range_range_empty by intuition.
        rewrite (Intersection_range_semLIs_empty _ _ _ _ H6) by intuition.
        intuition.
      + unfold size2. simpl.
        destruct is1 as [|[f1' t1'] is1].
        -- unfold size2. simpl in *. repeat rewrite Z.ltb_irrefl.
           destruct (Z.ltb_spec t1 t2); simpl; omega.
        -- unfold size2. simpl in *. repeat rewrite Z.ltb_irrefl.
           destruct (Z.ltb_spec t1 t2), (Z.ltb_spec t1' t2); simpl; omega.
      + assumption.
      + simpl. intuition.
    - intuition. rewrite IH with (z := Z.min f1 f2); clear dependent u.
      + simpl.
        rewrite Setminus_Union_r.
        f_equal.
        symmetry.
        apply Setminus_noop.
        rewrite Distributivity_l.
        rewrite Intersection_range_range_empty by intuition.
        rewrite Intersection_commutative.
        rewrite (Intersection_range_semLIs_empty _ _ _ _ H6) by intuition.
        intuition.
      + unfold size2. simpl.
        destruct is2 as [|[f2' t2'] is2].
        -- unfold size2. simpl in *. repeat rewrite Z.ltb_irrefl.
           destruct (Z.ltb_spec t1 t2); simpl; omega.
        -- unfold size2. simpl in *. repeat rewrite Z.ltb_irrefl.
           destruct (Z.ltb_spec t1 t2), (Z.ltb_spec t1 t2'); simpl; omega.
      + simpl. intuition.
      + simpl. refine (goodLIs_mono _ _ _ _ H7). rewrite Z.min_le_iff. intuition.
    - intuition. simpl. rewrite IH with (z := Z.min f1 f2); clear dependent u.
      + simpl.
        rewrite Setminus_Union.
        rewrite (Setminus_empty _ (range f1 t1) (Union Z (range f2 t2) (semLIs is2))).
        rewrite Empty_set_zero. reflexivity.
        apply Included_Union_l.
        apply Included_range_range.
        intuition.
      + unfold size2. simpl.
        destruct is1 as [|[f1' t1'] is1].
        -- unfold size2. simpl in *. repeat rewrite Z.ltb_irrefl.
           destruct (Z.ltb_spec t1 t2); simpl; omega.
        -- unfold size2. simpl in *. repeat rewrite Z.ltb_irrefl.
           destruct (Z.ltb_spec t1' t2), (Z.ltb_spec t1 t2); simpl; omega.
      + simpl. refine (goodLIs_mono _ _ _ _ H8). rewrite Z.min_le_iff. intuition.
      + simpl. intuition.
    - simpl. intuition. rewrite IH with (z := Z.min f1 f2); clear dependent u.
      + simpl.
        repeat rewrite Setminus_Union.
        f_equal.
        -- rewrite Setminus_Union_r.
           f_equal.
            (* lets do it by hand *)
            apply Extensionality_Ensembles. split.
            ++ unfold Included, Setminus, In, range.
               intuition.
            ++ unfold Included, Setminus, In, range.
               intuition.
        -- rewrite Setminus_Union_r.
           f_equal.
           symmetry.
           apply Setminus_noop.          
           rewrite Intersection_commutative.
           apply (Intersection_range_semLIs_empty _ _ _ _ H8).
           intuition.
      + unfold size2. simpl.
        destruct is2 as [|[f2' t2'] is2].
        -- unfold size2. simpl in *. repeat rewrite Z.ltb_irrefl.
           destruct (Z.ltb_spec t1 t2); simpl; omega.
        -- unfold size2. simpl in *. repeat rewrite Z.ltb_irrefl.
           destruct (Z.ltb_spec t1 t2), (Z.ltb_spec t1 t2'); simpl; omega.
      + simpl. rewrite Z.min_le_iff.  intuition.
      + simpl. refine (goodLIs_mono _ _ _ _ H9). rewrite Z.min_le_iff.  intuition.
    - simpl. intuition. rewrite IH with (z := f2); clear dependent u.
      + simpl.
        rewrite Setminus_Union.
        f_equal.
        symmetry.
        rewrite Setminus_Union_r.
        rewrite (Setminus_noop _ (Setminus Z (range f1 t1) (range f2 t2)) (semLIs is2)).
        -- (* lets do it by hand *)
           apply Extensionality_Ensembles. split.
            ++ unfold Included, Setminus, In, range.
               intuition.
            ++ unfold Included, Setminus, In, range.
               intuition.
        -- assert (Included Z (Setminus Z (range f1 t1) (range f2 t2)) (range f1 t2))
             by (unfold Included, Setminus, In, range; intuition).
           apply Extensionality_Ensembles; split; try intuition.
           apply (Intersection_mono_trans_l _ _ _ _ _ H7).
           rewrite (Intersection_range_semLIs_empty _ _ _ _ H9) by intuition.
           intuition.           
      + unfold size2. simpl.
        destruct is1 as [|[f1' t1'] is1].
        -- unfold size2. simpl in *. repeat rewrite Z.ltb_irrefl.
           destruct (Z.ltb_spec t1 t2); simpl; omega.
        -- unfold size2. simpl in *. repeat rewrite Z.ltb_irrefl.
           destruct (Z.ltb_spec t1' t2), (Z.ltb_spec t1 t2); simpl; omega.
      + simpl. refine (goodLIs_mono _ _ _ _ H8). intuition.
      + simpl. intuition.
    - simpl. intuition. rewrite IH with (z := f2); clear dependent u.
      + simpl.
        symmetry.
        repeat rewrite Setminus_Union.
        rewrite <- Union_associative.
        f_equal.
        -- rewrite Setminus_Union_r.
           replace (range f1 f2) with (Setminus Z (range f1 f2) (semLIs is2)).
           rewrite <- Setminus_Union.
           f_equal.
           ++ (* lets do it by hand *)
               apply Extensionality_Ensembles. split.
                ** intros x H10. inversion H10.
                   destruct (Z.ltb_spec x f2).
                   --- left. unfold In, range in *; intuition.
                   --- right. unfold In, range in *; intuition.
                ** intros X H10. inversion H10; subst.
                   --- unfold Setminus, In, range in *; intuition.
                   --- unfold Setminus, In, range in *; intuition.
          ++ apply Setminus_noop.
             apply (Intersection_range_semLIs_empty _ _ _ _ H9).
             intuition.
        -- rewrite Setminus_Union_r.
           f_equal.
           apply Setminus_noop.
           rewrite Intersection_commutative.
           apply (Intersection_range_semLIs_empty _ _ _ _ H8).
           intuition.
      + unfold size2. simpl.
        destruct is2 as [|[f2' t2'] is2].
        -- unfold size2. simpl in *. repeat rewrite Z.ltb_irrefl.
           destruct (Z.ltb_spec t1 t2); simpl; omega.
        -- unfold size2. simpl in *. repeat rewrite Z.ltb_irrefl.
           destruct (Z.ltb_spec t1 t2'), (Z.ltb_spec t1 t2) ; simpl; omega.
      + simpl. intuition.
      + simpl. refine (goodLIs_mono _ _ _ _ H9). intuition.
Qed.

(** subsetof *)

Lemma subSetOf_spec:
  forall s1 s2, good s1 -> good s2 -> subSetOf s1 s2 = true <-> Included Z (sem s1) (sem s2).
Proof.
  intros.
  unfold subSetOf.
  rewrite isEmpty_spec by (apply subtract_good; assumption).
  rewrite subtract_spec by assumption.
  apply Setminus_empty_classical.
Qed.