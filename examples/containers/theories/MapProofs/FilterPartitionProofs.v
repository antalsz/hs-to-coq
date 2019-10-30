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
Require Import MapProofs.UnionIntersectDifferenceProofs.
Require Import MapProofs.ToListProofs.
Require Import Coq.Classes.Morphisms.

Section WF.
Context {e : Type} {a : Type} {HEq : Eq_ e} {HOrd : Ord e} {HEqLaws : EqLaws e}  {HOrdLaws : OrdLaws e}.

(** ** Verification of [submap] *)
Lemma submap'_spec:
  forall (m1: Map e a) (m2: Map e a) lb ub f,
  Bounded m1 lb ub ->
  Bounded m2 lb ub ->
  submap' f m1 m2 = true <->
  (forall i value, sem m1 i = Some value -> exists v, (sem m2 i = Some v /\ f value v = true)).
Proof.
  intros ????? HB1 HB2.
  revert dependent m2.
  induction HB1; intros; simpl; subst.
  * intuition. discriminate H0.
  * destruct m2 eqn:Hs0.
    - rewrite <- Hs0 in *.
      clear s e0 a0 m1 m3 Hs0.
      eapply splitLookup_Desc; [solve_Bounded e|].
      intros sr1 b sr2 HBsr1 HBsr2 Hb Hsem.
      destruct HB2.
      + simpl. split; intros. simpl in Hb. subst. discriminate H1. specialize (H1 x v).
        assert (sem s1 x = None). { eapply sem_outside_above. apply HB1_1. unfold isUB. order e. }
        rewrite H3 in H1. simpl in H1. rewrite Eq_Reflexive in H1. simpl in H1.
        assert (exists v0 : a, None = Some v0 /\ f v v0 = true) by  (apply H1; reflexivity).
        destruct H4. destruct H4. discriminate H4.
      + destruct b. rewrite andb_true_iff. rewrite andb_true_iff. rewrite IHHB1_1 by eassumption.
        rewrite IHHB1_2 by eassumption. split; intro.
        -- destruct H6. destruct H7. intros i value Hi. rewrite Hsem. destruct (sem s1 i) eqn : ?.
            ** apply H7 in Heqo. destruct Heqo. destruct H9. exists x1.
               destruct (i == x) eqn : ?. solve_Bounds e. rewrite H9. simpl. simpl in Hi. split. reflexivity.
              inversion Hi. subst. apply H10.
            ** simpl in Hi. destruct (i == x) eqn : ?. simpl in Hi. exists a0. split.
              eapply sem_resp_eq in Heqb. rewrite <- Hb in Heqb. assumption. inversion Hi; subst.
              assumption. simpl in Hi. apply H8 in Hi. destruct Hi. exists x1.
              assert (sem sr1 i = None). { eapply sem_outside_above. apply HBsr1.
              destruct H9. apply (sem_inside HBsr2) in H9. destruct H9. solve_Bounds e. }
              rewrite H10. simpl. apply H9.
       -- split. specialize (H6 x v). assert (sem s1 x = None). { eapply sem_outside_above.
          apply HB1_1. unfold isUB. order e. } rewrite H7 in H6. simpl in H6. rewrite Eq_Reflexive in H6.
          simpl in H6.
          assert (exists v1 : a, sem s0 x ||| SomeIf (_GHC.Base.==_ x x0) v0 ||| sem s3 x = Some v1
          /\ f v v1 = true) by (apply H6; reflexivity). destruct H8. simpl in Hb. rewrite <- Hb in H8.
          destruct H8. inversion H8; subst. assumption.
          split.
          ** intros. specialize (H6 i value). rewrite H7 in H6. simpl in H6.
             assert (exists v : a, sem s0 i ||| SomeIf (_GHC.Base.==_ i x0) v0 ||| sem s3 i = Some v
             /\ f value v = true) by (apply H6; reflexivity). destruct H8. destruct H8.
            specialize (Hsem i). simpl in Hsem. rewrite H8 in Hsem. destruct (i==x) eqn : ?.
            ++ solve_Bounds e.
            ++ assert (sem sr2 i = None). { eapply (sem_inside HB1_1) in H7. destruct H7.
              unfold isUB in H10. eapply (sem_outside_below). apply HBsr2. solve_Bounds e. }
              rewrite H10 in Hsem. rewrite oro_None_r in Hsem. exists x1. split. symmetry.
              apply Hsem. apply H9.
          ** intros. specialize (H6 i value). rewrite H7 in H6.
              assert (sem s1 i = None). eapply sem_outside_above. apply HB1_1. eapply (sem_inside HB1_2) in H7.
              destruct H7. solve_Bounds e. rewrite H8 in H6. simpl in H6. destruct (i == x) eqn : ?.
              ++ solve_Bounds e.
              ++ simpl in H6. assert ( exists v : a, sem s0 i |||
              SomeIf (_GHC.Base.==_ i x0) v0 ||| sem s3 i = Some v /\ f value v = true) by (apply H6; reflexivity).
             destruct H9. specialize (Hsem i). simpl in Hsem. destruct H9. rewrite H9 in Hsem.
              rewrite Heqb in Hsem. assert (sem sr1 i = None). { eapply (sem_inside HB1_2) in H7.
              destruct H7. unfold isLB in H7. eapply sem_outside_above. apply HBsr1. solve_Bounds e. }
              rewrite H11 in Hsem. simpl in Hsem. exists x1. split. symmetry. apply Hsem. apply H10.
          -- split; intros. discriminate H6. specialize (H6 x). assert (sem s1 x = None). {
              eapply sem_outside_above. apply HB1_1. unfold isUB.  order e. } rewrite H7 in H6. simpl in H6.
              specialize (H6 v). rewrite Eq_Reflexive in H6. simpl in H6. destruct H6. reflexivity.
              simpl in Hb. rewrite <- Hb in H6. destruct H6. discriminate H6.
    - intuition.
      + discriminate H1.
      + subst. simpl in H1. specialize (H1 x v). assert (sem s1 x = None). { eapply sem_outside_above.
        apply HB1_1. unfold isUB. order e. } rewrite H3 in H1. simpl in H1. rewrite Eq_Reflexive in H1.
        simpl in H1. destruct H1. reflexivity. destruct H1. discriminate H1.
Qed.

Lemma submap_size :
  forall (m1: Map e a) (m2: Map e a) lb ub,
  Bounded m1 lb ub ->
  Bounded m2 lb ub ->
  (forall i value, sem m1 i = Some value ->  exists v, sem m2 i = Some v) ->
  (size m1 <= size m2)%Z.
Proof.
  intros ???? HB1 HB2 Hsubmap.
  revert dependent m2.
  induction HB1; intros; simpl; subst.
  * simpl. solve_size.
  * assert (exists v, sem m2 x = Some v). { specialize (Hsubmap x v). simpl in Hsubmap.
    assert (sem s1 x = None). { eapply sem_outside_above. apply HB1_1. unfold isUB. order e. }
    rewrite H1 in Hsubmap. simpl in Hsubmap. rewrite Eq_Reflexive in Hsubmap. simpl in Hsubmap.
    destruct Hsubmap. reflexivity. exists x0. assumption. }
    assert (size m2 = let '(sl,sr) := split x m2 in 1 + size sl + size sr)%Z.
    { eapply split_Desc; [eassumption|]. intros. destruct H1. rewrite H1 in H5. simpl in H5. lia. }
    rewrite H3.
    eapply split_Desc; [eassumption|]. intros.
    assert (size s1 <= size s0)%Z.
    { apply IHHB1_1; try assumption.
      intros i v1 Hi.
      specialize (Hsubmap i). simpl in Hsubmap.
      rewrite Hi in Hsubmap. simpl in Hsubmap.
      specialize (Hsubmap v1). destruct Hsubmap. reflexivity.
      specialize (H7 i). destruct (i == x) eqn : ?.
      { solve_Bounds e. }
      { assert (sem s3 i = None). { assert (i < x = true) by solve_Bounds e. eapply sem_outside_below.
        apply H5. unfold isLB. order e. }
        rewrite H9 in H7. rewrite oro_None_r  in H7. exists x0. rewrite <- H7. assumption. }
   }
    assert (size s2 <= size s3)%Z.
    { apply IHHB1_2; try assumption.
      intros i v1 Hi.
      specialize (Hsubmap i). simpl in Hsubmap.
      rewrite Hi in Hsubmap. simpl in Hsubmap.
      specialize (Hsubmap v1).
      assert (sem s1 i = None). { eapply sem_outside_above. apply HB1_1. solve_Bounds e. }
      rewrite H9 in Hsubmap. simpl in Hsubmap.
      assert (i == x = false) by solve_Bounds e. rewrite H10 in Hsubmap. simpl in Hsubmap.
      destruct Hsubmap. reflexivity. specialize (H7 i). rewrite H11 in H7. rewrite H10 in H7.
     assert (sem s0 i = None). { assert (x < i = true) by solve_Bounds e. eapply sem_outside_above.
      apply H4. solve_Bounds e. }
      rewrite H12 in H7. simpl in H7. exists x0. symmetry. apply H7. }
    lia.
Qed.

Lemma isSubmapOfBy_spec:
  forall (m1: Map e a) (m2: Map e a) f lb ub,
  Bounded m1 lb ub ->
  Bounded m2 lb ub ->
  isSubmapOfBy f m1 m2 = true <-> (forall i value, sem m1 i = Some value -> exists v, sem m2 i =
  Some v /\ f value v = true).
Proof.
  intros. unfold isSubmapOfBy. split; intros.
  - eapply submap'_spec. apply H. apply H0. rewrite andb_true_iff in H1. destruct H1. apply H3.
    apply H2.
  - apply andb_true_iff. split. unfold op_zlze__. unfold Ord_Integer___. unfold op_zlze____.
    rewrite size_size. rewrite Z.leb_le. eapply submap_size. apply H. apply H0. intros.
    specialize (H1 i value). apply H1 in H2. destruct H2. destruct H2. exists x. apply H2.
    eapply submap'_spec. apply H. apply H0. apply H1.
Qed.

Lemma isSubmapOf_spec:
  forall `{Eq_ a} m1 m2 lb ub,
  Bounded m1 lb ub ->
  Bounded m2 lb ub ->
  isSubmapOf m1 m2 = true <-> (forall i value, sem m1 i = Some value -> exists v, sem m2 i = Some v /\
  value == v = true).
Proof.
  intros. eapply isSubmapOfBy_spec. apply H0. apply H1.
Qed.

(** ** Verification of [isProperSubmapOfBy] *)
Lemma isProperSubmapOfBy_spec:
  forall (m1: Map e a) (m2: Map e a) lb ub f,
  Bounded m1 lb ub ->
  Bounded m2 lb ub ->
    isProperSubmapOfBy f m1 m2 = true <-> isSubmapOfBy f m1 m2 = true /\ size m1 < size m2 = true.
Proof.
  intros. unfold isProperSubmapOfBy. unfold isSubmapOfBy. repeat (rewrite andb_true_iff in *). split; intros.
   - destruct H1. split. split. order Int. assumption. order Int.
   - destruct H1. destruct H1. split. order Int. apply H3.
Qed.

(** ** Veriticcation of [isProperSubmpaOf] *)
Lemma isProperSubmapOf_spec:
  forall `{EqLaws a} (m1: Map e a) (m2: Map e a) lb ub,
  Bounded m1 lb ub ->
  Bounded m2 lb ub ->
  isProperSubmapOf m1 m2 = true <-> isSubmapOf m1 m2 = true /\ size m1 < size m2 = true.
Proof.
  intros. unfold isProperSubmapOf. unfold isSubmapOf. eapply isProperSubmapOfBy_spec; eassumption.
Qed.


(** ** Verification of [filter] *)

(**
For filter we need two lemmas: We need to know that [filter P s] is
well-formed even if P does not respect equality (this is
required by the [FSetInterface]). But to prove something about its
semantics, we need to assume that [P] respects equality.
*)

Lemma filterWithKey_Bounded:
  forall (P : e -> a -> bool) map lb ub,
  Bounded map lb ub ->
  Bounded (Internal.filterWithKey P map) lb ub.
Proof.
  intros.
  induction H.
  * simpl. solve_Bounded e.
  * simpl.
    destruct (P x v) eqn:HPx.
    - destruct_ptrEq.
      + solve_Bounded e.
      + applyDesc e (@link_Desc e a).
    - applyDesc e (@link2_Desc e a).
Qed.

Lemma filterWithKey_Desc:
  forall (P : e -> a -> bool) map lb ub,
  Bounded map lb ub ->
  Proper ((fun i j : e => _GHC.Base.==_ i j = true) ==> eq) P ->
  Desc' (Internal.filterWithKey P map) lb ub (fun x => match sem map x with
                                                      | Some y => if P x y then Some y else None
                                                      | None => None
                                                      end).
Proof.
  intros.
  induction H.
  * simpl. solve_Desc e. reflexivity.
  * simpl.
    applyDesc e IHBounded1.
    applyDesc e IHBounded2.
    destruct (P x v) eqn:HPx.
    - destruct_ptrEq.
      + solve_Desc e. f_solver e. assert (P i v = true). { erewrite H0. apply HPx. apply Heqb. }
        rewrite Heqb0 in H4. inversion H4.
      + applyDesc e (@link_Desc e a).
        solve_Desc e. f_solver e. assert (P i a0 = true). { erewrite H0. apply HPx. apply Heqb. }
        rewrite Heqb0 in H4. inversion H4.
    - applyDesc e (@link2_Desc e a).
      solve_Desc e. f_solver e. assert (P x v = true). { erewrite H0. apply Heqb0. apply Eq_Symmetric.
      apply Heqb. } rewrite HPx in H6. inversion H6.
Qed.

Lemma filterWithKey_WF :
  forall f (s : Map e a),
    Proper ((fun i j : e => _GHC.Base.==_ i j = true) ==> eq) f ->
    WF s -> WF (filterWithKey f s).
Proof.
  intros. eapply Desc'_WF.
  apply filterWithKey_Desc; assumption.
Qed.

(*This requires no conditions on the function P*)
Lemma filter_Desc:
  forall  (P : a -> bool) map lb ub,
  Bounded map lb ub ->
  Desc' (Internal.filter P map) lb ub (fun x => match sem map x with
                                                |Some y => if P y then Some y else None
                                                |None => None
                                                end).
Proof.
  intros. eapply filterWithKey_Desc. apply H. f_solver e.
Qed.

Lemma filter_WF :
  forall f (s : Map e a),
    WF s -> WF (filter f s).
Proof.
  intros. eapply Desc'_WF.
  apply filter_Desc; assumption.
Qed.

(** ** Verification of [partition] *)

Lemma partitionWithKey_Bounded:
  forall p map lb ub,
  Bounded map lb ub ->
  forall (P : (Map e a * Map e a) -> Prop),
  (forall m1 m2, Bounded m1 lb ub /\ Bounded m2 lb ub -> P (m1, m2)) ->
  P (partitionWithKey p map).
Proof.
  intros ???? HB.
  induction HB.
  * intros X HX; apply HX; clear X HX; split; solve_Bounded e.
  * simpl.
    apply IHHB1; intros sl1 sl2 [HDsl1 HDsl2]; clear IHHB1.
    apply IHHB2; intros sr1 sr2 [HDsr1 HDsr2]; clear IHHB2.
    destruct (p x) eqn:?.
    - intros X HX; apply HX; clear X HX; split.
      + destruct_ptrEq.
        -- solve_Bounded e.
        -- applyDesc e (@link_Desc e a).
      + applyDesc e (@link2_Desc e a).
    - intros X HX; apply HX; clear X HX; split.
      + applyDesc e (@link2_Desc e a).
      + destruct_ptrEq.
        -- solve_Bounded e.
        -- applyDesc e (@link_Desc e a).
Qed.


Lemma partitionWithKey_spec:
  forall (p : e -> a -> bool) map lb ub,
  Bounded map lb ub ->
  Proper ((fun i j : e => i == j = true) ==> eq) p ->
  forall (P : (Map e a * Map e a) -> Prop),
  (forall m1 m2,
    Desc' m1 lb ub (fun i => match sem map i with
                             | Some y => if p i y then Some y else None
                             | None => None
                              end)  /\
    Desc' m2 lb ub (fun i => match sem map i with
                             | Some y => if p i y then None else Some y
                             | None => None
                             end) ->
    P (m1, m2)) ->
  P (partitionWithKey p map).
Proof.
  intros ???? HB HProper.
  induction HB.
  * intros X HX; apply HX; clear X HX; split; solve_Desc e; f_solver e.
  * simpl.
    apply IHHB1; intros sl1 sl2 [HDsl1 HDsl2]; clear IHHB1.
    applyDesc e HDsl1; clear HDsl1.
    applyDesc e HDsl2; clear HDsl2.
    apply IHHB2; intros sr1 sr2 [HDsr1 HDsr2]; clear IHHB2.
    applyDesc e HDsr1; clear HDsr1.
    applyDesc e HDsr2; clear HDsr2.
    destruct (p x) eqn:?.
    - intros X HX; apply HX; clear X HX; split.
      + destruct_ptrEq.
        -- solve_Desc e. f_solver e. assert (p i v = p x v). apply equal_f. apply HProper. assumption.
            rewrite Heqb in H1. rewrite Heqb1 in H1. inversion H1.
        -- applyDesc e (@link_Desc e a). solve_Desc e. f_solver e. assert (p i a0 = p x a0). apply equal_f.
           apply HProper. assumption. rewrite Heqb1 in H1. rewrite Heqb in H1. inversion H1.
      + applyDesc e (@link2_Desc e a). solve_Desc e. f_solver e. assert (p i v = p x v). apply equal_f.
        apply HProper. assumption. rewrite Heqb in H3. rewrite Heqb1 in H3. inversion H3.
    - intros X HX; apply HX; clear X HX; split.
      + applyDesc e (@link2_Desc e a). solve_Desc e. f_solver e. assert (p i v = p x v). apply equal_f.
        apply HProper. assumption. rewrite Heqb in H3. rewrite Heqb1 in H3. inversion H3.
      + destruct_ptrEq.
        -- solve_Desc e. f_solver e. assert (p x v = p i v). apply equal_f. apply HProper. order e.
           rewrite Heqb in H1. rewrite Heqb1 in H1. inversion H1.
        -- applyDesc e (@link_Desc e a). solve_Desc e. f_solver e. assert (p x a0 = p i a0). apply equal_f.
           apply HProper. order e. rewrite Heqb in H1. rewrite Heqb1 in H1. inversion H1.
Qed.

Lemma partition_spec:
  forall (p : a -> bool) map lb ub,
  Bounded map lb ub ->
  forall (P : (Map e a * Map e a) -> Prop),
  (forall m1 m2,
    Desc' m1 lb ub (fun i => match sem map i with
                             | Some y => if p y then Some y else None
                             | None => None
                              end)  /\
    Desc' m2 lb ub (fun i => match sem map i with
                             | Some y => if p y then None else Some y
                             | None => None
                             end) ->
    P (m1, m2)) ->
  P (partition p map).
Proof.
  intros. unfold partition. eapply partitionWithKey_spec. apply H. f_solver e. apply H0.
Qed.


(** ** Verification of [take] *)
(*This is exactly the same as SetProofs, since the take function works the exact same way*)
Definition takeGo : Int -> Map e a -> Map e a.
Proof.
  let rhs := eval unfold take in (@take e a) in
  match rhs with fun n s => if _ then _ else ?go _ _  => exact go end.
Defined.

Lemma take_neg: forall a n (l : list a), (n <= 0)%Z -> List.take n l = nil.
Proof.
  intros. destruct l; simpl; destruct (Z.leb_spec n 0); try lia; try reflexivity.
Qed.

Lemma take_all:
  forall a n (xs : list a), (Z.of_nat (length xs) <= n)%Z -> List.take n xs = xs.
Proof.
  intros. revert n H.
  induction xs; intros n Hall.
  * simpl. destruct (Z.leb_spec n 0); reflexivity.
  * simpl.
    simpl length in Hall. rewrite Nat2Z.inj_succ, <- Z.add_1_l in Hall.
    rewrite IHxs by lia.
    destruct (Z.leb_spec n 0); [lia|reflexivity].
Qed.

Lemma take_app_cons:
  forall a n (l1 : list a) (x : a) (l2 : list a),
  List.take n (l1 ++ x :: l2) = match (n ?= Z.of_nat (length l1))%Z with
    | Lt => List.take n l1
    | Eq => l1
    | Gt => l1 ++ (x :: nil) ++ List.take (n - Z.of_nat (length l1) - 1)%Z l2
  end.
Proof.
  intros. revert n.
  induction l1; intros n.
  * simpl.
    rewrite Z.sub_0_r.
    destruct (Z.leb_spec n 0), (Z.compare_spec n 0)%Z; try reflexivity; lia.
  * cbn -[Z.add Z.of_nat].
    rewrite IHl1. clear IHl1.
    rewrite Nat2Z.inj_succ, <- Z.add_1_l.
    replace (n - (1 + Z.of_nat (length l1)) - 1)%Z with (n - 2 - Z.of_nat (length l1))%Z by lia.
    replace (n - 1 - (Z.of_nat (length l1)) - 1)%Z with (n - 2 - Z.of_nat (length l1))%Z by lia.
    destruct (Z.leb_spec n 0),
             (Z.compare_spec (n - 1) (Z.of_nat (length l1)))%Z,
             (Z.compare_spec n (1 + Z.of_nat (length l1)))%Z; try reflexivity; lia.
Qed.

Lemma takeGo_spec :
  forall n map lb ub,
  Bounded map lb ub ->
  forall (P : Map e a -> Prop),
  (forall m',
    Bounded m' lb ub /\
    toList m' = List.take n (toList map) ->
    P m') ->
  P (takeGo n map).
Proof.
  intros ???? HD. revert n.
  induction HD; intros n.
  * intros X HX; apply HX. split.
    + simpl. destruct_match; solve_Bounded e.
    + simpl. do 2 destruct_match; reflexivity.
  * simpl.
    intros X HX; apply HX.
    rewrite toList_Bin.
    unfold op_zlze__ , Ord_Integer___, op_zlze____.
    unfold compare , Ord_Integer___, compare__.
    rewrite size_size.
    apply IHHD1. intros s1' [HBs1' Hs1']. clear IHHD1.
    apply IHHD2. intros s2' [HBs2' Hs2']. clear IHHD2.
    destruct (Z.leb_spec n 0).
    + rewrite take_neg by assumption. split.
      - solve_Bounded e.
      - reflexivity.
    + simpl app.
      rewrite take_app_cons.
      erewrite <- size_spec by eassumption.
      destruct (Z.compare_spec n (size s1)).
      - split.
        ** eapply Bounded_relax_ub; eassumption.
        ** reflexivity.
      - split.
        ** eapply Bounded_relax_ub; eassumption.
        ** assumption.
      - split.
        ** applyDesc e (@link_Desc e a).
        ** erewrite toList_link by solve_Precondition e.
           rewrite Hs2'.
           reflexivity.
Qed.

Lemma toList_take:
  forall n map lb ub,
  Bounded map lb ub ->
  forall (P : Map e a -> Prop),
  (forall m',
    Bounded m' lb ub /\
    toList m' = List.take n (toList map) ->
    P m') ->
  P (take n map).
Proof.
  intros. apply H0.
  unfold take. fold takeGo.
  unfold op_zgze__ , Ord_Integer___, op_zgze____.
  rewrite size_size.
  destruct (Z.leb_spec (size map) n).
  * split; [assumption|].
    rewrite take_all. reflexivity.
    erewrite <- size_spec by eassumption.
    assumption.
  * eapply takeGo_spec; [solve_Precondition e..|].
    intros. assumption.
Qed.

(** ** Verification of [drop] *)

Definition dropGo : Int -> Map e a -> Map e a.
Proof.
  let rhs := eval unfold drop in (@drop e a) in
  match rhs with fun n s => if _ then _ else ?go _ _  => exact go end.
Defined.

Lemma drop_neg: forall a n (l : list a), (n <= 0)%Z -> List.drop n l = l.
Proof.
  intros. destruct l; simpl; destruct (Z.leb_spec n 0); try lia; try reflexivity.
Qed.

Lemma drop_all:
  forall a n (xs : list a), (Z.of_nat (length xs) <= n)%Z -> List.drop n xs = nil.
Proof.
  intros. revert n H.
  induction xs; intros n Hall.
  * simpl. destruct (Z.leb_spec n 0); reflexivity.
  * simpl.
    simpl length in Hall. rewrite Nat2Z.inj_succ, <- Z.add_1_l in Hall.
    rewrite IHxs by lia.
    destruct (Z.leb_spec n 0); [lia|reflexivity].
Qed.

Lemma drop_app_cons:
  forall a n (l1 : list a) (x : a) (l2 : list a),
  List.drop n (l1 ++ x :: l2) = match (n ?= Z.of_nat (length l1))%Z with
    | Lt => List.drop n l1 ++ (x :: nil) ++ l2
    | Eq => (x :: nil) ++ l2
    | Gt => List.drop (n - Z.of_nat (length l1) - 1)%Z l2
  end.
Proof.
  intros. revert n.
  induction l1; intros n.
  * simpl.
    rewrite Z.sub_0_r.
    destruct (Z.leb_spec n 0), (Z.compare_spec n 0)%Z; try reflexivity; lia.
  * cbn -[Z.add Z.of_nat].
    rewrite IHl1. clear IHl1.
    rewrite Nat2Z.inj_succ, <- Z.add_1_l.
    replace (n - (1 + Z.of_nat (length l1)) - 1)%Z with (n - 2 - Z.of_nat (length l1))%Z by lia.
    replace (n - 1 - (Z.of_nat (length l1)) - 1)%Z with (n - 2 - Z.of_nat (length l1))%Z by lia.
    destruct (Z.leb_spec n 0),
             (Z.compare_spec (n - 1) (Z.of_nat (length l1)))%Z,
             (Z.compare_spec n (1 + Z.of_nat (length l1)))%Z; try reflexivity; lia.
Qed.


Lemma dropGo_spec :
  forall n map lb ub,
  Bounded map lb ub ->
  forall (P : Map e a -> Prop),
  (forall m',
    Bounded m' lb ub /\
    toList m' = List.drop n (toList map) ->
    P m') ->
  P (dropGo n map).
Proof.
  intros ???? HD. revert n.
  induction HD; intros n.
  * intros X HX; apply HX. split.
    + simpl. destruct_match; solve_Bounded e.
    + simpl. do 2 destruct_match; reflexivity.
  * simpl.
    intros X HX; apply HX.
    rewrite toList_Bin.
    unfold op_zlze__ , Ord_Integer___, op_zlze____.
    unfold compare , Ord_Integer___, compare__.
    rewrite size_size.
    apply IHHD1. intros s1' [HBs1' Hs1']. clear IHHD1.
    apply IHHD2. intros s2' [HBs2' Hs2']. clear IHHD2.
    destruct (Z.leb_spec n 0).
    + rewrite drop_neg by assumption. split.
      - solve_Bounded e.
      - rewrite toList_Bin.
        reflexivity.
    + simpl app.
      rewrite drop_app_cons.
      erewrite <- size_spec by eassumption.
      destruct (Z.compare_spec n (size s1)).
      - split.
        ** applyDesc e (@insertMin_Desc e a).
        ** erewrite toList_insertMin  by solve_Precondition e.
           reflexivity.
      - split.
        ** applyDesc e (@link_Desc e a).
        ** erewrite toList_link by solve_Precondition e.
           rewrite Hs1'.
           reflexivity.
      - split.
        ** eapply Bounded_relax_lb; eassumption.
        ** assumption.
Qed.

Lemma toList_drop:
  forall n map lb ub,
  Bounded map lb ub ->
  forall (P : Map e a -> Prop),
  (forall m',
    Bounded m' lb ub /\
    toList m' = List.drop n (toList map) ->
    P m') ->
  P (drop n map).
Proof.
  intros. apply H0.
  unfold drop. fold dropGo.
  unfold op_zgze__ , Ord_Integer___, op_zgze____.
  rewrite size_size.
  destruct (Z.leb_spec (size map) n).
  * split; [solve_Precondition e|].
    rewrite drop_all. reflexivity.
    erewrite <- size_spec by eassumption.
    assumption.
  * eapply dropGo_spec; [solve_Precondition e..|].
    intros. assumption.
Qed.

(** ** Verification of [splitAt] *)

Definition splitAtGo : Int -> Map e a -> (Map e a * Map e a).
Proof.
  let rhs := eval unfold splitAt in (@splitAt e a) in
  match rhs with fun n s => if _ then _ else Datatypes.id (?go _ _)  => exact go end.
Defined.

Lemma splitAtGo_spec :
  forall n s, splitAtGo n s = (takeGo n s, dropGo n s).
Proof.
  intros ??.
  revert n.
  induction s; intros n.
  * simpl.
    repeat destruct_match; try congruence.
  * simpl. repeat destruct_match; reflexivity.
Qed.

End WF.
