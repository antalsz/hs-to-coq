(**
This file verifies some of the logic of Interval.hs from
bisect-binary. <https://github.com/nomeata/bisect-binary/>

It is a variant of Proofs.v that uses the Function command to use [deferredFix] in a safer ay and get a nice induction lemma. I stopped after the proof for [union].
*)


Require Import Intervals.

Require Import GHC.Base.
Require Import GHC.DeferredFix.

Require Import Coq.Sets.Ensembles.
Require Import Coq.Sets.Powerset_facts.
Require Import Ensemble_facts.
Import ListNotations.
Require Import Omega.

Require Import Coq.Logic.FunctionalExtensionality.

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
    assert (In Z (range from to) from).
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

(* Variant of the axiom that is safe to use. *)
Axiom deferredFix2_safe_eq: forall {a b r} `{Default r} (f : (a -> b -> r) -> (a -> b -> r)) x,
  f x = x -> deferredFix2 f = f (deferredFix2 f).
  

(** induction principle *)

Definition needs_reorder (is1 is2 : list Interval) : bool :=
  match is1, is2 with
    | (I f1 t1 :: _), (I f2 t2 :: _) => (t1 <? t2)%Z
    | _, _ => false
  end.

Definition size2 (is1_is2 : list Interval * list Interval) : nat := match is1_is2 with
  (is1, is2) => (if needs_reorder is1 is2 then 1 else 0) + 2 * length is1 + 2 * length is2 end.

(** Function definitions using Program Fixpoint. We use them only
  to show that the axiomatized fixpoints in the code exist, and to
  get a nice termination principle.
  
  The code was copied out of the argument to [deferredFix], and case splits pulled out of function arguments.
  *)

Ltac solve_size2 :=
  intros;
  try match goal with [ H :  _<_ ?x ?y = true |- _ ] =>
      unfold GHC.Base.op_zl__, Ord_Integer___, op_zl____ in H;
      destruct (Z.ltb_spec x y); try congruence
  end;
  repeat match goal with [ i : Interval |- _ ] => destruct i end;
  match goal with [ |- context [size2 (?is1, ?is2)]] =>
    try (lazymatch is1 with | _ :: _ => fail | _ => destruct is1 as [|[??]?] end);
    try (lazymatch is2 with | _ :: _ => fail | _ => destruct is2 as [|[??]?] end)
  end;
  unfold size2; simpl in *;
  repeat rewrite Z.ltb_irrefl;
  repeat (
    match goal with [ |- context [if (?x <? ?y)%Z then _ else _] ] => destruct (Z.ltb_spec x y) end
  );
  try omega.
  
Require Import Recdef.

Function union_go_witness' (is1_is2 : list Interval * list Interval)  {measure size2 is1_is2} :list Interval :=
  match is1_is2 with (arg_25__, arg_26__) =>
     match arg_25__ with
     | [] => match arg_26__ with
             | [] => arg_25__
             | _ :: _ => arg_26__
             end
     | i1 :: is1 =>
         match arg_26__ with
         | [] => arg_25__
         | i2 :: is2 =>
            if _<_ (to i1) (to i2)
            then union_go_witness' (i2 :: is2, i1 :: is1)
            else if _>_ (from i1) (to i2)
               then i2 :: union_go_witness' (i1 :: is1, is2)
               else match i1 with | I _ to_29__ =>
                 union_go_witness' ( I (min (from i1) (from i2)) to_29__ :: is1, is2) end
         end
     end
   end.
Proof. all: solve_size2. Qed.
Definition union_go_witness (is1 is2 : list Interval) : list Interval :=
  union_go_witness' (is1, is2).

Definition union_go_f :=
  fun (go : list Interval -> list Interval -> list Interval)
               (arg_25__ arg_26__ : list Interval) =>
             match arg_25__ with
             | [] =>
                 match arg_26__ with
                 | [] => arg_25__
                 | _ :: _ => arg_26__
                 end
             | i1 :: is3 =>
                 match arg_26__ with
                 | [] => arg_25__
                 | i2 :: is4 =>
                     let f' := min (from i1) (from i2) in
                     let j_32__ :=
                       go
                         (match i1 with
                          | I _ to_29__ => I f' to_29__
                          end :: is3) is4 in
                     let j_33__ :=
                       if _>_ (from i1) (to i2) : bool
                       then i2 :: go (i1 :: is3) is4
                       else j_32__ in
                     if _<_ (to i1) (to i2) : bool
                     then go (i2 :: is4) (i1 :: is3)
                     else j_33__
                 end
             end.

Lemma union_go_eq :
  deferredFix2 union_go_f = union_go_f (deferredFix2 union_go_f).
Proof.
  apply deferredFix2_safe_eq with (x := union_go_witness).
  extensionality is1. extensionality is2.
  unfold union_go_f.
  unfold union_go_witness at 4.
  rewrite union_go_witness'_equation.
  unfold union_go_witness.
  repeat (match goal with [ |- context [match ?scrut with | _ => _ end ] ] => destruct scrut end;simpl);
  reflexivity.
Qed.

Definition union_go_ind P : _ :=
  (union_go_witness'_ind (fun is1_is2 _ => match is1_is2 with (is1, is2) => P is1 is2 end)).


(** [union] *)

Lemma union_good : forall (is1 is2 : Intervals),
    good is1 -> good is2 -> good (union is1 is2).
Proof.
  intros.
  destruct is1 as [is1], is2 as [is2].
  destruct H as [lb1 H1] , H0 as [lb2 H2].
  exists (Z.min lb1 lb2).
  fold union_go_f.
  apply (goodLIs_mono _ _ _ (Z.le_min_l lb1 lb2)) in H1.
  apply (goodLIs_mono _ _ _ (Z.le_min_r lb1 lb2)) in H2.
  generalize dependent (Z.min lb1 lb2). clear lb1 lb2.
  (* ready for induction *)
  refine (union_go_ind (fun is1 is2 => forall lb : Z,
  goodLIs is1 lb -> goodLIs is2 lb -> goodLIs (deferredFix2 union_go_f is1 is2) lb) _ _ _ _ _ _ (is1, is2)); clear is1 is2;
  intros is1_is2_ is1 is2.
  * intros ???;subst.
    intros lb H1 H2.
    rewrite union_go_eq. unfold union_go_f at 1.
    simpl. trivial.
  * intros ?? i2 is2' ?; subst. intros lb H1 H2.
    rewrite union_go_eq. unfold union_go_f at 1.
    assumption.
  * intros ?? i1 is1' ?; subst. intros lb H1 H2.
    rewrite union_go_eq. unfold union_go_f at 1.
    assumption.
  * rename is1 into is1', is2 into is2'.
    intros ???????? IH lb H1 H2; subst.
    rewrite union_go_eq. unfold union_go_f at 1.
    simpl.
    rewrite e2.
    unfold GHC.Base.op_zl__, Ord_Integer___, op_zl____ in *.
    unfold GHC.Base.op_zg__, Ord_Integer___, op_zg____ in *.
    apply IH; try assumption.
  * rename is1 into is1', is2 into is2'.
    intros ????????? IH lb H1 H2; subst.
    rewrite union_go_eq. unfold union_go_f at 1.
    rewrite e2, e3.
    unfold GHC.Base.op_zl__, Ord_Integer___, op_zl____ in *.
    unfold GHC.Base.op_zg__, Ord_Integer___, op_zg____ in *.
    destruct i1 as [f1 t1], i2 as [f2 t2].
    simpl in *.
    repeat match goal with [ H :  (?x <? ?y)%Z = true |- _ ] =>
      unfold GHC.Base.op_zl__, Ord_Integer___, op_zl____ in H;
      destruct (Z.ltb_spec x y); try congruence
    end.
    intuition.
  * rename is1 into is1', is2 into is2'.
    intros ???????????? IH lb H1 H2; subst.
    rewrite union_go_eq. unfold union_go_f at 1.
    rewrite e2, e3.
    unfold GHC.Base.op_zl__, Ord_Integer___, op_zl____ in *.
    unfold GHC.Base.op_zg__, Ord_Integer___, op_zg____ in *.
    destruct i2 as [f2 t2].
    simpl in *.
    repeat match goal with [ H :  (?x <? ?y)%Z = _ |- _ ] =>
      unfold GHC.Base.op_zl__, Ord_Integer___, op_zl____ in H;
      destruct (Z.ltb_spec x y); try congruence
    end.
    intuition.
    apply IH.
    rewrite Z.min_glb_iff in *. intuition.
    rewrite  Z.min_lt_iff in *. intuition.
    refine (goodLIs_mono _ _ _ _ H7). intuition.
Qed.

Lemma union_spec : forall (is1 is2 : Intervals),
    good is1 -> good is2 -> sem (union is1 is2) = Union Z (sem is1) (sem is2).
Proof.
  intros.
  destruct is1 as [is1], is2 as [is2].
  destruct H as [lb1 H1] , H0 as [lb2 H2].
  unfold union.
  fold union_go_f.
  apply (goodLIs_mono _ _ _ (Z.le_min_l lb1 lb2)) in H1.
  apply (goodLIs_mono _ _ _ (Z.le_min_r lb1 lb2)) in H2.
  generalize dependent (Z.min lb1 lb2). clear lb1 lb2.
    
  (* ready for induction *)
  refine (union_go_ind (fun is1 is2 => forall lb : Z,
  goodLIs is1 lb -> goodLIs is2 lb -> semLIs (deferredFix2 union_go_f is1 is2) = Union Z (semLIs is1) (semLIs is2)) _ _ _ _ _ _ (is1, is2)); clear is1 is2;
  intros is1_is2_ is1' is2'.
  * intros ??? lb H1 H2;subst.
    rewrite union_go_eq. unfold union_go_f at 1.
    simpl.  rewrite Empty_set_zero. reflexivity.
  * intros ?? i2 is2 ? lb H1 H2; subst.
    rewrite union_go_eq. unfold union_go_f at 1.
    simpl in *. intuition.
  * intros ?? i1 is1 ?; subst. intros lb H1 H2.
    rewrite union_go_eq. unfold union_go_f at 1.
    simpl in *. rewrite  Empty_set_zero_l. intuition.
  * intros ???????? IH lb H1 H2; subst.
    rewrite union_go_eq. unfold union_go_f at 1.
    simpl.
    rewrite e2.
    unfold GHC.Base.op_zl__, Ord_Integer___, op_zl____ in *.
    unfold GHC.Base.op_zg__, Ord_Integer___, op_zg____ in *.
    rewrite IH with (lb:=lb).
      + intuition.
      + assumption.
      + assumption.
  * intros ????????? IH lb H1 H2; subst.
    rewrite union_go_eq. unfold union_go_f at 1.
    rewrite e2, e3.
    unfold GHC.Base.op_zl__, Ord_Integer___, op_zl____ in *.
    unfold GHC.Base.op_zg__, Ord_Integer___, op_zg____ in *.
    destruct i1 as [f1 t1], i2 as [f2 t2].
    simpl in *.
    repeat match goal with [ H :  (?x <? ?y)%Z = true |- _ ] =>
      unfold GHC.Base.op_zl__, Ord_Integer___, op_zl____ in H;
      destruct (Z.ltb_spec x y); try congruence
    end.
    rewrite IH with (lb:=t2).
    + simpl. intuition.
      (* reorder Union *)
      repeat rewrite Union_associative.
      rewrite Union_commutative.
      repeat rewrite Union_associative.
      do 2 f_equal.
      rewrite Union_commutative.
      reflexivity.
    + simpl in *. intuition.
    + simpl. intuition.
  * intros ???????????? IH lb H1 H2; subst.
    rewrite union_go_eq. unfold union_go_f at 1.
    rewrite e2, e3.
    unfold GHC.Base.op_zl__, Ord_Integer___, op_zl____ in *.
    unfold GHC.Base.op_zg__, Ord_Integer___, op_zg____ in *.
    destruct i2 as [f2 t2].
    simpl in *.
    repeat match goal with [ H :  (?x <? ?y)%Z = _ |- _ ] =>
      unfold GHC.Base.op_zl__, Ord_Integer___, op_zl____ in H;
      destruct (Z.ltb_spec x y); try congruence
    end.
    rewrite IH with (lb:=lb).
    + simpl.
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
    + simpl. intuition.
      rewrite Z.min_glb_iff in *. intuition.
      rewrite  Z.min_lt_iff in *. intuition.
    + simpl. intuition.
      refine (goodLIs_mono _ _ _ _ H7). intuition.
Qed.

