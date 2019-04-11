Require Import GHC.Base.
Import GHC.Base.Notations.
Require Import Proofs.GHC.Base.
Require Import Data.Map.Internal.
Import GHC.Num.Notations.
Require Import OrdTactic.
Require Import Psatz.
Require Import Tactics.
Set Bullet Behavior "Strict Subproofs".
Require Import MapProofs.Bounds.
Require Import MapProofs.Tactics.

Section WF.
Context {e : Type} {a : Type} {HEq : Eq_ e} {HOrd : Ord e} {HEqLaws : EqLaws e}  {HOrdLaws : OrdLaws e}.

(** ** Verification of [lookup] *)

Lemma lookup_spec:
 forall (s: Map e a) lb ub i, Bounded s lb ub -> lookup i s = sem s i.
Proof.
  intros ???? HB.
  induction HB.
  * simpl. reflexivity.
  * subst; simpl.
    destruct (compare i x) eqn:?.
    + replace (i == x) with true by order_Bounds e.
      rewrite (sem_outside_above HB1) by order_Bounds e.
      reflexivity.
    + replace (i == x) with false by order_Bounds e.
      rewrite IHHB1.
      rewrite (sem_outside_below HB2) by order_Bounds e.
      simpl_options.
      reflexivity.
    + replace (i == x) with false by order_Bounds e.
      rewrite IHHB2.
      rewrite (sem_outside_above HB1) by order_Bounds e.
      simpl_options.
      reflexivity.
Qed.

(** ** Verification of [member] *)

Lemma member_spec:
 forall (s: Map e a) lb ub i, Bounded s lb ub -> member i s = true <-> exists v, sem s i = Some v.
Proof.
  intros. induction H.
  - simpl. split. intros. discriminate H. intros. destruct H. discriminate H. 
  - subst. simpl. destruct (compare i x) eqn: ?; split; intros.
    + replace (i==x) with true by order_Bounds e.
      rewrite (sem_outside_above H) by order_Bounds e.
      simpl. exists v. reflexivity.
    + reflexivity.
    + replace (i==x) with false by order_Bounds e.
      rewrite (sem_outside_below H0) by order_Bounds e.
      simpl_options. apply IHBounded1 in H3. destruct H3. exists x0. assumption.
    + assert (sem s2 i = None). { eapply sem_outside_below. apply H0. unfold isLB.
      order_Bounds e. }
      rewrite H5 in H3. assert (i == x = false). { rewrite compare_Lt in Heqc.
      apply lt_not_eq. assumption. } rewrite H6 in H3. simpl in H3. simpl_options. 
      apply IHBounded1. destruct H3. exists x0. assumption. 
    + replace (i==x) with false by order_Bounds e.
      rewrite (sem_outside_above H) by order_Bounds e.
      simpl. apply IHBounded2 in H3. destruct H3. exists x0. assumption.
    + assert (sem s1 i = None). { eapply sem_outside_above. apply H. order_Bounds e. }
      rewrite H5 in H3. rewrite compare_Gt in Heqc. apply gt_not_eq in Heqc. rewrite Heqc in H3.
      simpl_options. destruct H3. apply IHBounded2. exists x0. assumption.
Qed.

(** ** Verification of [notMember] *)

Lemma contrapositive : forall (P : Prop) (Q: Prop),
  (P -> Q) -> (~Q -> ~P).
Proof.
  intros. intro. apply H in H1. contradiction.
Qed.

Lemma notMember_spec:
 forall (s: Map e a) lb ub i, Bounded s lb ub -> notMember i s = true <-> sem s i = None.
Proof.
  intros ???? HB.
  unfold notMember, op_zd__. split; intros.
  pose proof (@member_spec s lb ub i). apply H0 in HB. destruct HB. apply contrapositive in H2.
  unfold not in H2. destruct (sem s i). destruct H2. exists a0. reflexivity. reflexivity.
  rewrite negb_true_iff in H. intro. rewrite H3 in H. inversion H.
  pose proof (@member_spec s lb ub i). apply H0 in HB. destruct HB. apply contrapositive in H1.
  rewrite negb_true_iff. destruct (member i s). contradiction. reflexivity. intro.
  destruct H3. rewrite H3 in H. inversion H.
Qed.

(** ** Verification of [findWithDefault] *)
Lemma findWithDefault_spec:
  forall (m: Map e a) lb ub i v, Bounded m lb ub -> 
  Some (findWithDefault v i m) = sem m i ||| Some v.
Proof.
  intros. induction H.
  - simpl. reflexivity.
  - simpl. destruct (compare i x) eqn : ?.
    + assert (sem s1 i = None). { eapply sem_outside_above. eassumption. solve_Bounds e. }
      rewrite H5. assert (i == x = true) by (order e). rewrite H6. reflexivity.
    + assert (i == x = false) by (order e). assert (sem s2 i = None). { eapply sem_outside_below.
      eassumption. solve_Bounds e. } rewrite H5. rewrite H6. simpl. rewrite oro_None_r.
      rewrite oro_None_r. apply IHBounded1.
    + assert (i == x = false) by (order e). assert (sem s1 i = None). { eapply sem_outside_above.
      eassumption. solve_Bounds e. } rewrite H5. rewrite H6. simpl. apply IHBounded2.
Qed.
(** ** Verification of [lookupLT] *)
Fixpoint goJustLT k  (k1: e) v1 (m : Map e a) : option (e * a) :=
  match m with
  | Tip => Some (k1, v1)
  | Bin sz k2 v2 l r => if (_GHC.Base.<=_ k k2) then goJustLT k k1 v1 l else
    goJustLT k k2 v2 r 
  end.
Fixpoint lookupLT' k (m : Map e a) :=
  match m with
  | Tip => None
  | Bin sz k1 v1 l r => if (_GHC.Base.<=_ k k1) then lookupLT' k l else goJustLT k k1 v1 r
  end.

Lemma lookupLT_equiv:
  forall m k,
  lookupLT' k m = lookupLT k m.
Proof.
  intros. unfold lookupLT'. unfold lookupLT. unfold goJustLT. reflexivity.
Qed.

Lemma goJustLT_pres_smaller: forall k k1 v1 m k2 v2 lb ub,
  Bounded m lb ub ->
  _GHC.Base.<_ k1 k = true ->
  goJustLT k k1 v1 m = Some (k2, v2) ->
  _GHC.Base.<_ k2 k = true.
Proof.
  intros. generalize dependent k1. revert v1 v2 k2 k. induction H; intros.
  - simpl in H1. inversion H1; subst. assumption.
  - simpl in H6. destruct (_GHC.Base.<=_ k x) eqn : ?.
   + eapply IHBounded1. eassumption. eassumption.
   + assert (_GHC.Base.<_ x k = true) by (order e). eapply IHBounded2. apply H7.
      apply H6.
Qed.

Lemma goJustLT_bounded: forall k k1 v1 m k2 v2 lb ub l u,
  Bounded m lb ub ->
  _GHC.Base.<_ k1 k = true ->
  goJustLT k k1 v1 m = Some (k2, v2) ->
  (lb = Some l /\ _GHC.Base.<=_ l k1 = true -> _GHC.Base.<=_ l k2 = true ) 
  /\ (ub = Some u /\ _GHC.Base.<=_ k1 u = true -> _GHC.Base.<=_ k2 u = true).
Proof.
  intros. generalize dependent k1. revert k v1 k2 v2 u l. induction H; intros.
  - simpl in H1. inversion H1; subst. split; intros; subst; solve_Bounds e.
  - simpl in H6. destruct (_GHC.Base.<=_ k x) eqn : ?. 
    + split; intros; subst.  specialize (IHBounded1 _ _ _ _ u l _ H5 H6). destruct IHBounded1.
       apply H3. apply H7. specialize (IHBounded1 _ _ _ _ x l  _ H5 H6). destruct IHBounded1.
        destruct H7; subst. assert (Some x = Some x /\ _GHC.Base.<=_ k1 x = true).
        split. reflexivity. order e. apply H8 in H7.  assert (compare x u = Lt) by (solve_Bounds e). 
        order e.
    + assert (_GHC.Base.<_ x k = true) by (order e).  split; intros; subst. 
      specialize (IHBounded2  _ _ _ _ u x _ H7 H6). destruct IHBounded2. 
      destruct H8; subst. assert (_GHC.Base.<=_ x k2 = true). apply H3. split. reflexivity.
      order e. assert (_GHC.Base.<_ l x = true) by (solve_Bounds e). order e.
      specialize (IHBounded2 _ _ _ _ u l _ H7 H6). destruct IHBounded2. apply H9.
      split. apply H8. destruct H8. subst. solve_Bounds e.
Qed. 

Lemma goJustLT_nothing_between: forall k k1 v1 m lb ub k2 v2,
  Bounded m lb ub ->
  _GHC.Base.<_ k1 k = true ->
  goJustLT k k1 v1 m = Some (k2, v2) ->
  (forall i, compare k2 i = Lt /\ compare i k = Lt ->
  sem m i = None).
Proof.
  intros. generalize dependent i. generalize dependent k2. generalize dependent k1.
  revert k v1 v2.
  induction H; intros.
  - reflexivity.
  - simpl. simpl in H6. destruct ( _GHC.Base.<=_ k x) eqn : ?.
    + assert (i == x = false) by (order e). rewrite H8. assert (sem s2 i = None). {
      eapply sem_outside_below. eassumption. solve_Bounds e. } rewrite H9.
      simpl. repeat(rewrite oro_None_r). eapply IHBounded1. apply H5. apply H6.
      assumption.
    + assert (_GHC.Base.<_ x k = true) by (order e).
      pose proof goJustLT_bounded. specialize (H9 _ _ _ _ _ _ _ _ x k H0 H8 H6).
      destruct H9. assert (_GHC.Base.<=_ x k2 = true). apply H9. split. reflexivity.
      order e. assert (_GHC.Base.<_ x i = true). order e. assert (sem s1 i = None).
      eapply sem_outside_above. eassumption. solve_Bounds e. rewrite H13.
      assert (i == x = false) by (order e). rewrite H14. simpl. eapply IHBounded2.
      apply H8. apply H6. apply H7.
Qed.

Lemma goJustLT_finds_upper_bound: forall k k1 v1 m lb ub k2 v2,
  Bounded m lb ub ->
  _GHC.Base.<_ k1 k = true ->
  goJustLT k k1 v1 m = Some (k2, v2) ->
   (_GHC.Base.<_  k2 k = true) /\ 
  (forall k3, (_GHC.Base.<_  k3 k = true) /\ (k2 == k3 = false) /\
  sem m k3 <> None -> (_GHC.Base.<_  k3 k2 = true)).
Proof.
  intros. pose proof (goJustLT_nothing_between k k1 v1 m lb ub k2 v2 H H0 H1).
  split. eapply goJustLT_pres_smaller. apply H. apply H0. apply H1. intros.
  specialize (H2 k3). destruct H3. destruct H4.
  destruct (_GHC.Base.<_ k3 k2 ) eqn : ?.
  - reflexivity.
  - assert (sem m k3 = None). apply H2. split. order e. order e. contradiction.
Qed.

Lemma goJustLt_val_in_map: forall k k1 v1 m lb ub k2 v2,
  Bounded m lb ub ->
  goJustLT k k1 v1 m = Some (k2, v2) ->
  sem m k2 = Some v2 \/ ((k2 == k1 = true) /\ v2 = v1).
Proof.
  intros. generalize dependent k2. revert k k1 v1 v2. induction H; intros.
  - simpl in H0. inversion H0; subst. right. split. apply Eq_Reflexive. reflexivity.
  - simpl. simpl in H5. destruct (_GHC.Base.<=_ k x) eqn : ?.
    + specialize (IHBounded1 k k1 v1 v2 k2 H5). destruct IHBounded1.
      * rewrite H6. simpl. left. reflexivity.
      * right. apply H6.
    + assert (_GHC.Base.<_ x k = true) by (order e).
      pose proof goJustLT_bounded. specialize (H7 k x v s2 k2 v2 (Some x) ub x k H0 H6 H5).
      destruct H7. assert (_GHC.Base.<=_ x k2 = true). apply H7. split. reflexivity. order e.
      assert (sem s1 k2 = None). eapply sem_outside_above. eassumption. solve_Bounds e. rewrite H10.
      simpl. specialize (IHBounded2 k x v v2 k2 H5). destruct IHBounded2.
      * assert (k2 == x = false) by (solve_Bounds e). rewrite H12. simpl. left.
        assumption.
      * destruct H11.  left. rewrite H11. simpl. subst. reflexivity.
Qed. 

Lemma goJustLt_never_none: forall k k1 v1 m,
  goJustLT k k1 v1 m <> None.
Proof.
  intros. revert k k1 v1. induction m; intros.
  - simpl. destruct (_GHC.Base.<=_ k0 k ). apply IHm1. apply IHm2.
  - simpl. intro contra. discriminate contra.
Qed. 

(*Part 1 of the spec: If lookupLT returns a k1, v1 pair, then (k1, v1) is in the map
  and k1 is the largest key smaller than k*)
Lemma lookupLT_spec_Some:
  forall (m: Map e a) lb ub k (k1: e) v1, Bounded m lb ub ->
  lookupLT k m = Some (k1, v1) ->
  sem m k1 = Some v1 /\ (_GHC.Base.<_  k1 k = true) /\ 
  (forall k2, (_GHC.Base.<_  k2 k = true) /\ (k1 == k2 = false) /\
  sem m k2 <> None -> (_GHC.Base.<_  k2 k1 = true)).
Proof.
  intros. rewrite <- lookupLT_equiv in H0. generalize dependent k. revert k1 v1. induction H; intros; split; intros.
  - inversion H0.
  - inversion H0.
  - simpl in H5. simpl. destruct (_GHC.Base.<=_  k x) eqn : ?.
    + apply IHBounded1 in H5. destruct H5. rewrite H5. simpl. reflexivity. 
    + assert ( _GHC.Base.<_ x k = true) by (order e).
      pose proof (goJustLT_finds_upper_bound k x v s2 (Some x) ub k1 v1 H0 H6 H5).
      destruct H7. specialize (H8 x).  
      pose proof (goJustLt_val_in_map k x v s2 (Some x) ub k1 v1 H0 H5). 
      pose proof goJustLT_bounded. specialize (H10 k x v s2 k1 v1 (Some x) ub x k H0 H6 H5). 
      destruct H10. assert (_GHC.Base.<=_ x k1 = true). apply H10. split. reflexivity. order e.
      assert (sem s1 k1 = None). eapply sem_outside_above. eassumption. solve_Bounds e.
      rewrite H13. simpl. destruct H9.
      * assert (k1 == x = false) by (solve_Bounds e). rewrite H14. simpl. assumption.
      * destruct H9. subst. rewrite H9. reflexivity.
  - simpl in H5. destruct (_GHC.Base.<=_ k x) eqn : ?. 
    + simpl. specialize (IHBounded1 k1 v1 k H5). destruct IHBounded1. destruct H7. split.
      assumption. intros. apply H8. destruct H9. destruct H10.
      split. assumption. split. assumption. assert (k2 == x = false) by (order e). 
      assert (sem s2 k2 = None). eapply sem_outside_below. eassumption. solve_Bounds e.
      rewrite H13 in H11. rewrite H12 in H11. simpl in H11. repeat (rewrite oro_None_r in H11).
      assumption.
    + assert (_GHC.Base.<_ x k = true) by (order e). split. eapply goJustLT_pres_smaller. apply H0.
      apply H6. apply H5. intros. destruct H7. destruct H8. simpl in H9.
      pose proof goJustLT_bounded. specialize (H10 k x v s2 k1 v1 (Some x) ub x k H0 H6 H5). 
      destruct H10. assert (_GHC.Base.<=_ x k1 = true). apply H10. split. reflexivity.
      order e. destruct (compare k2 k1) eqn : ?.
      order e.
      order e.
      assert (k2 == x = false) by (order e). rewrite H13 in H9. simpl in H9.
      assert (sem s1 k2 = None). eapply sem_outside_above. eassumption. solve_Bounds e.
      rewrite H14 in H9. simpl in H9. eapply goJustLT_finds_upper_bound.
       apply H0. apply H6. apply H5. split; try(assumption); split; assumption.
Qed.

(*Part 2: If lookupLT returns None, then every key in the map is smaller than k*)
Lemma lookupLT_spec_None:
  forall (m: Map e a) lb ub k, Bounded m lb ub ->
  lookupLT k m = None ->
  (forall k2 v2, sem m k2 = Some v2 -> _GHC.Base.<=_ k k2 = true).
Proof.
  intros. generalize dependent k2. generalize dependent k. revert v2. induction H; intros.
  - inversion H1.
  - rewrite <- lookupLT_equiv in H5. simpl in H5. destruct (_GHC.Base.<=_ k x) eqn : ?.
    simpl in H6. destruct (sem s1 k2) eqn : ?.  
    * simpl in H6; inversion H6; subst. eapply IHBounded1. apply H5. apply Heqo.
    * simpl in H6. destruct (k2 == x) eqn : ?.
      -- order e.
      -- simpl in H6. solve_Bounds e.
    * assert (goJustLT k x v s2 <> None). apply goJustLt_never_none. rewrite H5 in H7.
      contradiction.
Qed.

(** ** Verification of [lookupLE] *)
Fixpoint goJustLE k (k1: e) v1 (m : Map e a) : option (e * a) :=
  match m with
  | Tip => Some (k1, v1)
  | Bin sz k2 v2 l r => match compare k k2 with
                        | Lt => goJustLE k k1 v1 l
                        | Eq => Some (k2, v2)
                        | Gt => goJustLE k k2 v2 r
                        end
  end.

Fixpoint lookupLE' k (m : Map e a) :=
  match m with
  | Tip => None
  | Bin sz k1 v1 l r => match compare k k1 with
                        | Lt => lookupLE' k l
                        | Eq => Some (k1, v1)
                        | Gt => goJustLE k k1 v1 r
                        end 
  end.

Lemma lookupLE_equiv:
  forall m k,
  lookupLE' k m = lookupLE k m.
Proof.
  intros. unfold lookupLE'. unfold lookupLE. unfold goJustLE. reflexivity.
Qed.

Lemma goJustLE_pres_smaller: forall k k1 v1 m k2 v2 lb ub,
  Bounded m lb ub ->
  _GHC.Base.<_ k1 k = true ->
  goJustLE k k1 v1 m = Some (k2, v2) ->
  _GHC.Base.<=_ k2 k = true.
Proof.
  intros. generalize dependent k1. revert v1 v2 k2 k. induction H; intros.
  - simpl in H1. inversion H1; subst. order e. 
  - simpl in H6. destruct (compare k x) eqn : ?.
    + inversion H6; subst. order e.
    + eapply IHBounded1. eassumption. eassumption.
    + assert (_GHC.Base.<_ x k = true) by (order e). eapply IHBounded2. apply H7.
      apply H6.
Qed.

Lemma goJustLE_bounded: forall k k1 v1 m k2 v2 lb ub l u,
  Bounded m lb ub ->
  _GHC.Base.<_ k1 k = true ->
  goJustLE k k1 v1 m = Some (k2, v2) ->
  (lb = Some l /\ _GHC.Base.<=_ l k1 = true -> _GHC.Base.<=_ l k2 = true ) 
  /\ (ub = Some u /\ _GHC.Base.<=_ k1 u = true -> _GHC.Base.<=_ k2 u = true).
Proof.
  intros. generalize dependent k1. revert k v1 k2 v2 u l. induction H; intros.
  - simpl in H1. inversion H1; subst. split; intros; subst; solve_Bounds e.
  - simpl in H6. destruct (compare k x) eqn : ?.
    + inversion H6; subst. split; intros. order e. destruct H3. subst. solve_Bounds e.
    + split; intros; subst.  specialize (IHBounded1 _ _ _ _ u l _ H5 H6). destruct IHBounded1.
       apply H3. apply H7. specialize (IHBounded1 _ _ _ _ x l  _ H5 H6). destruct IHBounded1.
        destruct H7; subst. assert (Some x = Some x /\ _GHC.Base.<=_ k1 x = true).
        split. reflexivity. order e. apply H8 in H7.  assert (compare x u = Lt) by (solve_Bounds e). 
        order e.
    + assert (_GHC.Base.<_ x k = true) by (order e).  split; intros; subst. 
      specialize (IHBounded2  _ _ _ _ u x _ H7 H6). destruct IHBounded2. 
      destruct H8; subst. assert (_GHC.Base.<=_ x k2 = true). apply H3. split. reflexivity.
      order e. assert (_GHC.Base.<_ l x = true) by (solve_Bounds e). order e.
      specialize (IHBounded2 _ _ _ _ u l _ H7 H6). destruct IHBounded2. apply H9.
      split. apply H8. destruct H8. subst. solve_Bounds e.
Qed. 

Lemma goJustLE_nothing_between: forall k k1 v1 m lb ub k2 v2,
  Bounded m lb ub ->
  _GHC.Base.<_ k1 k = true ->
  goJustLE k k1 v1 m = Some (k2, v2) ->
  (forall i, compare k2 i = Lt /\ compare i k = Lt ->
  sem m i = None).
Proof.
  intros. generalize dependent i. generalize dependent k2. generalize dependent k1.
  revert k v1 v2.
  induction H; intros.
  - reflexivity.
  - simpl. simpl in H6. destruct (compare k x) eqn : ?.
    + assert (i == x = false) by (order e). rewrite H8. assert (sem s2 i = None). {
      eapply sem_outside_below. eassumption. solve_Bounds e. } rewrite H9.
      simpl. repeat(rewrite oro_None_r). inversion H6; subst. eapply sem_outside_above.
      eassumption. solve_Bounds e. 
    + assert (i == x = false) by (order e). rewrite H8. assert (sem s2 i = None). {
      eapply sem_outside_below. eassumption. solve_Bounds e. } rewrite H9.
      simpl. repeat(rewrite oro_None_r).  eapply IHBounded1. apply H5. apply H6.
      assumption.
    + assert (_GHC.Base.<_ x k = true) by (order e).
      pose proof goJustLE_bounded. specialize (H9 _ _ _ _ _ _ _ _ x k H0 H8 H6).
      destruct H9. assert (_GHC.Base.<=_ x k2 = true). apply H9. split. reflexivity.
      order e. assert (_GHC.Base.<_ x i = true). order e. assert (sem s1 i = None).
      eapply sem_outside_above. eassumption. solve_Bounds e. rewrite H13.
      assert (i == x = false) by (order e). rewrite H14. simpl. eapply IHBounded2.
      apply H8. apply H6. apply H7.
Qed.

Lemma goJustLE_finds_upper_bound: forall k k1 v1 m lb ub k2 v2,
  Bounded m lb ub ->
  _GHC.Base.<_ k1 k = true ->
  goJustLE k k1 v1 m = Some (k2, v2) ->
   (_GHC.Base.<=_  k2 k = true) /\ 
  (forall k3, (_GHC.Base.<_  k3 k = true) /\ (k2 == k3 = false) /\
  sem m k3 <> None -> (_GHC.Base.<_  k3 k2 = true)).
Proof.
  intros. pose proof (goJustLE_nothing_between k k1 v1 m lb ub k2 v2 H H0 H1).
  split. eapply goJustLE_pres_smaller. apply H. apply H0. apply H1. intros.
  specialize (H2 k3). destruct H3. destruct H4.
  destruct (_GHC.Base.<_ k3 k2 ) eqn : ?.
  - reflexivity.
  - assert (sem m k3 = None). apply H2. split. order e. order e. contradiction.
Qed.

Lemma goJustLE_val_in_map: forall k k1 v1 m lb ub k2 v2,
  Bounded m lb ub ->
  goJustLE k k1 v1 m = Some (k2, v2) ->
  sem m k2 = Some v2 \/ ((k2 == k1 = true) /\ v2 = v1).
Proof.
  intros. generalize dependent k2. revert k k1 v1 v2. induction H; intros.
  - simpl in H0. inversion H0; subst. right. split. apply Eq_Reflexive. reflexivity.
  - simpl. simpl in H5. destruct (compare k x) eqn : ?.
    + inversion H5; subst. assert (sem s1 k2 = None). eapply sem_outside_above.
      eassumption. solve_Bounds e. rewrite H3. rewrite Eq_Reflexive. simpl.
      left. reflexivity. 
    + specialize (IHBounded1 k k1 v1 v2 k2 H5). destruct IHBounded1.
      * rewrite H6. simpl. left. reflexivity.
      * right. apply H6.
    + assert (_GHC.Base.<_ x k = true) by (order e).
      pose proof goJustLE_bounded. specialize (H7 k x v s2 k2 v2 (Some x) ub x k H0 H6 H5).
      destruct H7. assert (_GHC.Base.<=_ x k2 = true). apply H7. split. reflexivity. order e.
      assert (sem s1 k2 = None). eapply sem_outside_above. eassumption. solve_Bounds e. rewrite H10.
      simpl. specialize (IHBounded2 k x v v2 k2 H5). destruct IHBounded2.
      * assert (k2 == x = false) by (solve_Bounds e). rewrite H12. simpl. left.
        assumption.
      * destruct H11.  left. rewrite H11. simpl. subst. reflexivity.
Qed. 

Lemma goJustLE_never_none: forall k k1 v1 m,
  goJustLE k k1 v1 m <> None.
Proof.
  intros. revert k k1 v1. induction m; intros.
  - simpl. destruct (compare k0 k) eqn : ?.
    + intro contra. discriminate contra.
    + apply IHm1.
    + apply IHm2.
  - simpl. intro contra. discriminate contra.
Qed. 

(*Part 1 of the spec: If lookupLT returns a k1, v1 pair, then (k1, v1) is in the map
  and k1 is the largest key less than or equal to than k*)
Lemma lookupLE_spec_Some:
  forall (m: Map e a) lb ub k (k1: e) v1, Bounded m lb ub ->
  lookupLE k m = Some (k1, v1) ->
  sem m k1 = Some v1 /\ (_GHC.Base.<=_  k1 k = true) /\ 
  (forall k2, (_GHC.Base.<_  k2 k = true) /\ (k1 == k2 = false) /\
  sem m k2 <> None -> (_GHC.Base.<_  k2 k1 = true)).
Proof.
  intros. rewrite <- lookupLE_equiv in H0. generalize dependent k. revert k1 v1. induction H; intros; split; intros.
  - inversion H0.
  - inversion H0.
  - simpl in H5. simpl. destruct (compare k x) eqn : ?.
    + inversion H5; subst. assert (sem s1 k1 = None). eapply sem_outside_above. eassumption.
      solve_Bounds e. rewrite H3. rewrite Eq_Reflexive. reflexivity.
    + apply IHBounded1 in H5. destruct H5. rewrite H5. simpl. reflexivity. 
    + assert ( _GHC.Base.<_ x k = true) by (order e).
      pose proof (goJustLE_finds_upper_bound k x v s2 (Some x) ub k1 v1 H0 H6 H5).
      destruct H7. specialize (H8 x).  
      pose proof (goJustLE_val_in_map k x v s2 (Some x) ub k1 v1 H0 H5). 
      pose proof goJustLE_bounded. specialize (H10 k x v s2 k1 v1 (Some x) ub x k H0 H6 H5). 
      destruct H10. assert (_GHC.Base.<=_ x k1 = true). apply H10. split. reflexivity. order e.
      assert (sem s1 k1 = None). eapply sem_outside_above. eassumption. solve_Bounds e.
      rewrite H13. simpl. destruct H9.
      * assert (k1 == x = false) by (solve_Bounds e). rewrite H14. simpl. assumption.
      * destruct H9. subst. rewrite H9. reflexivity.
  - simpl in H5. destruct (compare k x ) eqn : ?.
    + inversion H5; subst. split. order e. intros. order e. 
    + simpl. specialize (IHBounded1 k1 v1 k H5). destruct IHBounded1. destruct H7. split.
      assumption. intros. apply H8. destruct H9. destruct H10.
      split. assumption. split. assumption. assert (k2 == x = false) by (order e). 
      assert (sem s2 k2 = None). eapply sem_outside_below. eassumption. solve_Bounds e.
      rewrite H13 in H11. rewrite H12 in H11. simpl in H11. repeat (rewrite oro_None_r in H11).
      assumption.
    + assert (_GHC.Base.<_ x k = true) by (order e). split. eapply goJustLE_pres_smaller. apply H0.
      apply H6. apply H5. intros. destruct H7. destruct H8. simpl in H9.
      pose proof goJustLE_bounded. specialize (H10 k x v s2 k1 v1 (Some x) ub x k H0 H6 H5). 
      destruct H10. assert (_GHC.Base.<=_ x k1 = true). apply H10. split. reflexivity.
      order e. destruct (compare k2 k1) eqn : ?.
      order e.
      order e.
      assert (k2 == x = false) by (order e). rewrite H13 in H9. simpl in H9.
      assert (sem s1 k2 = None). eapply sem_outside_above. eassumption. solve_Bounds e.
      rewrite H14 in H9. simpl in H9. eapply goJustLE_finds_upper_bound.
       apply H0. apply H6. apply H5. split; try(assumption); split; assumption.
Qed.

Lemma goJustLE_spec_eq: forall m lb ub k v k' v',
  Bounded m lb ub ->
  sem m k = Some v ->
  (exists k1, k1 == k = true /\ goJustLE k k' v' m = Some (k1, v)).
Proof.
  intros. generalize dependent k. revert v k' v'. induction H; intros.
  - inversion H0.
  - simpl in H5. simpl. destruct (sem s1 k) eqn : ?. 
    + assert (compare k x = Lt) by (solve_Bounds e).
      rewrite H6. apply IHBounded1. simpl in H5. inversion H5; subst. assumption.
    + simpl in H5. destruct (k == x) eqn : ?. assert (compare k x = Eq) by (order e).
      * rewrite H6. exists x. split. order e. inversion H5. reflexivity.
      * simpl in H5. assert (compare k x = Gt) by (solve_Bounds e). rewrite H6.
        apply IHBounded2. assumption.
Qed.

(*Part 2: If the value is in the map, lookupLE returns it*)
Lemma lookupLE_spec_eq: forall (m: Map e a) lb ub k v,
  Bounded m lb ub ->
  sem m k = Some v ->
  (exists k1, k1 == k = true /\ lookupLE k m = Some (k1, v)).
Proof.
  intros. generalize dependent k. revert v. induction H; intros.
  - inversion H0.
  - simpl in H5. rewrite <- lookupLE_equiv. simpl.
    destruct (sem s1 k) eqn : ?.
    + assert (compare k x = Lt) by (solve_Bounds e). rewrite H6. apply IHBounded1.
      simpl in H5. inversion H5; subst. assumption.
    + simpl in H5. destruct (k == x) eqn : ?.
      * simpl in H5. exists x. split. order e. assert (compare k x = Eq) by (order e).
        rewrite H6. inversion H5; subst. reflexivity.
      * simpl in H5. assert (compare k x = Gt) by (solve_Bounds e). rewrite H6.
        eapply goJustLE_spec_eq. eassumption. assumption.
Qed.
    
(*Part 3: If lookupLT returns None, then every key in the map is smaller than k*)
Lemma lookupLE_spec_None:
  forall (m: Map e a) lb ub k, Bounded m lb ub ->
  lookupLE k m = None ->
  (forall k2 v2, sem m k2 = Some v2 -> _GHC.Base.<_ k k2 = true).
Proof.
  intros. generalize dependent k2. generalize dependent k. revert v2. induction H; intros.
  - inversion H1.
  - rewrite <- lookupLE_equiv in H5. simpl in H5. destruct (compare k x) eqn : ?.
    + simpl in H6. order e. 
    + simpl in H6. destruct (sem s1 k2) eqn : ?.  
      * simpl in H6; inversion H6; subst. eapply IHBounded1. apply H5. apply Heqo.
      * simpl in H6. destruct (k2 == x) eqn : ?.
      -- order e.
      -- simpl in H6. solve_Bounds e.
    + assert (goJustLE k x v s2 <> None). apply goJustLE_never_none. rewrite H5 in H7.
      contradiction.
Qed.
End WF.