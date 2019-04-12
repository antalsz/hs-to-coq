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
Require Import MapProofs.InsertProofs.

Section WF.
Context {e : Type} {a : Type} {HEq : Eq_ e} {HOrd : Ord e} {HEqLaws : EqLaws e}  {HOrdLaws : OrdLaws e}.

(** ** Verification of [fromDistinctAscList] *)

Require Import GHC.DeferredFix.

Definition fromDistinctAscList_create_f : (Int -> list (e * a) -> (Map e a) * list (e * a)) -> 
(Int -> list (e * a) -> Map e a * list ( e * a)).
Proof.
  let rhs := eval unfold fromDistinctAscList in (@fromDistinctAscList e a) in
  lazymatch rhs with context [deferredFix2 ?f] => exact f end.
Defined.

Definition fromDistinctAscList_create : Int -> list (e * a) -> (Map e a) * list (e * a)
  := deferredFix2 (fromDistinctAscList_create_f).

Lemma Z_shiftr_pos:
  forall x, (1 < x -> 1 <= Z.shiftr x 1)%Z.
Proof.
  intros.
  rewrite Z.shiftr_div_pow2 by lia.
  replace (2^1)%Z with 2%Z by reflexivity.
  assert (2 <= x)%Z by lia. clear H.
  apply Z.div_le_mono with (c := 2%Z) in H0.
  apply H0.
  lia.
Qed.

Lemma Z_shiftl_pos:
  forall x, (1 <= x -> 1 <= Z.shiftl x 1)%Z.
Proof.
  intros.
  rewrite Z.shiftl_mul_pow2 by lia.
  lia.
Qed.

Lemma Z_shiftr_lt:
  forall x, (1 <= x -> Z.shiftr x 1 < x)%Z.
Proof.
  intros.
  rewrite Z.shiftr_div_pow2 by lia.
  replace (2^1)%Z with 2%Z by reflexivity.
  apply Z_div_lt; lia.
Qed.

Require Import Coq.Wellfounded.Wellfounded.

Lemma fromDistinctAscList_create_eq:
  forall i xs, (1 <= i)%Z ->
  fromDistinctAscList_create i xs = fromDistinctAscList_create_f fromDistinctAscList_create i xs.
Proof.
  intros.
  change (uncurry fromDistinctAscList_create (i, xs) = uncurry (fromDistinctAscList_create_f fromDistinctAscList_create) (i, xs)).
  apply deferredFix_eq_on with
    (f := fun g => uncurry (fromDistinctAscList_create_f (curry g)))
    (P := fun p => (1 <= fst p)%Z)
    (R := fun x y => (1 <= fst x < fst y)%Z).
  * eapply wf_inverse_image with (R := fun x y => (1 <= x < y)%Z).
    apply Z.lt_wf with (z := 1%Z).
  * clear i xs H.
    intros g h x Px Heq.
    destruct x as [i xs]. simpl in *.
    unfold fromDistinctAscList_create_f.
    destruct_match; try reflexivity.
    repeat replace (#1) with 1%Z by reflexivity.
    unfold op_zeze__, Eq_Integer___, op_zeze____.
    destruct (Z.eqb_spec i 1); try reflexivity.
    unfold curry.
    assert (1 < i)%Z by lia.
    assert (1 <= Z.shiftr i 1)%Z by (apply Z_shiftr_pos; lia).
    assert (Z.shiftr i 1 < i)%Z by (apply Z_shiftr_lt; lia).
    repeat expand_pairs. simpl.
    rewrite Heq by eauto.
    destruct_match; try reflexivity.
    rewrite Heq by eauto.
    reflexivity.
  * simpl; lia.
Qed.

Check length.
(* We need to know that [create] returns no longer list than it receives. *)
Program Fixpoint fromDistinctAscList_create_preserves_length
  i xs {measure (Z.to_nat i)} :
  (1 <= i)%Z ->
  forall (P : Map e a * list (e * a) -> Prop),
  ( forall s ys,
    (length ys <= length xs)%nat ->
    P (s, ys)
  ) ->
  P (fromDistinctAscList_create i xs) := _.
Next Obligation.
  intros.
  rename fromDistinctAscList_create_preserves_length into IH.
  rewrite fromDistinctAscList_create_eq by assumption.
  unfold fromDistinctAscList_create_f.
  destruct xs.
  * apply H0. reflexivity.
  * repeat replace (#1) with 1%Z by reflexivity.
    unfold op_zeze__, Eq_Integer___, op_zeze____.
    destruct (Z.eqb_spec i 1).
    + destruct p. apply H0. simpl. lia.
    + assert (Z.to_nat (Bits.shiftR i #1) < Z.to_nat i)%nat. {
        apply Z2Nat.inj_lt.
        apply Z.shiftr_nonneg. lia.
        lia.
        apply Z_shiftr_lt; lia.
      }
      apply IH.
      - assumption. 
      - apply Z_shiftr_pos; lia.
      - intros.
        destruct_match.
        ** apply H0. simpl in *. lia.
        ** apply IH.
           -- assumption.
           -- apply Z_shiftr_pos; lia.
           -- intros.
               destruct p0. apply H0. simpl in *. lia.
Qed.

Definition fromDistinctAscList_go_f : (Int -> Map e a -> list (e * a) -> Map e a) ->
 (Int -> Map e a -> list (e * a) -> Map e a).
Proof.
  let rhs := eval unfold fromDistinctAscList in (@fromDistinctAscList e a) in
  let rhs := eval fold fromDistinctAscList_create_f in rhs in 
  let rhs := eval fold fromDistinctAscList_create in rhs in 
  lazymatch rhs with context [deferredFix3 ?f] => exact f end.
Defined.

Definition fromDistinctAscList_go : Int -> Map e a -> list (e * a) -> Map e a
  := deferredFix3 (fromDistinctAscList_go_f).

Lemma fromDistinctAscList_go_eq:
  forall i s xs, (0 < i)%Z ->
  fromDistinctAscList_go i s xs = fromDistinctAscList_go_f fromDistinctAscList_go i s xs.
Proof.
  intros.
  change (deferredFix (fun g => uncurry (uncurry (fromDistinctAscList_go_f (curry (curry g))))) (i, s, xs) =
    uncurry (uncurry (fromDistinctAscList_go_f fromDistinctAscList_go)) (i, s, xs)).
  rewrite deferredFix_eq_on with
    (P := fun p => (1 <= fst (fst p))%Z)
    (R := fun x y => (length (snd x) < length (snd y))%nat); only 1: reflexivity.
  * apply well_founded_ltof with (f := fun x => length (snd x)).
  * intros g h p Px Heq.
    destruct p as [[x y] z].
    simpl in *.
    unfold fromDistinctAscList_go_f.
    destruct_match; try reflexivity.
    eapply fromDistinctAscList_create_preserves_length; try lia.
    intros s' ys Hlength. destruct p.
    apply Heq.
    + apply Z_shiftl_pos.
      lia.
    + simpl. lia.
  * simpl. lia.
Qed.

Definition safeHd {a} : list (e * a) -> option e := fun xs =>
  match xs with nil => None | ((x, y)::_) => Some x end.

Lemma mul_pow_sub:
  forall sz, (0 < sz)%Z -> (2 * 2 ^ (sz - 1) = 2^sz)%Z.
Proof.
  intros.
  rewrite <- Z.pow_succ_r by lia.
  f_equal.
  lia.
Qed.

Require Import Coq.Sorting.Sorted.
Require Import SortedUtil.

(*Maps are sorted only by keys*)
Local Definition lt : e * a -> e * a -> Prop
  := fun x1 x2 => let (e1, a1) := x1 in let (e2, a2) := x2 in (e1 < e2) = true.

(*TODO: FIGURE OUT WHY THIS IS NOT WORKING*)
Program Fixpoint fromDistinctAscList_create_Desc
  sz lb xs x {measure (Z.to_nat sz)} :
  (0 <= sz)%Z ->
  StronglySorted lt ((lb, x) :: xs) ->
  forall (P : (Map e a) * list (e * a) -> Prop),
  ( forall (s : Map e a) (ys: list (e * a)),
    Bounded s (Some lb) (safeHd ys) ->
    xs = toList s ++ ys ->
    ys = nil \/ size s = (2*2^sz-1)%Z ->
    P (s, ys)
  ) ->
  P (fromDistinctAscList_create (2^sz)%Z xs) := _.
Next Obligation.
  intros ????? Hnonneg HSorted.  
  rename fromDistinctAscList_create_Desc into IH.
  rewrite fromDistinctAscList_create_eq
    by (enough (0 < 2^sz)%Z by lia; apply Z.pow_pos_nonneg; lia).
  unfold fromDistinctAscList_create_f.
  destruct xs.
  * intros X HX. apply HX. clear HX.
    - solve_Bounded.
    - reflexivity.
    - left. reflexivity.
  * repeat replace (#1) with 1%Z by reflexivity.
    unfold op_zeze__, Eq_Integer___, op_zeze____.

    inversion HSorted. subst.
    inversion H2. subst. clear H2.
    inversion H1. subst.
    destruct p.
    assert (isUB (safeHd xs) e0 = true). {
      destruct xs; try reflexivity.
      inversion H5. subst. unfold safeHd. destruct p. assumption. } 
    
    destruct (Z.eqb_spec (2^sz) 1).
    - intros X HX. apply HX. clear HX.
      ++ solve_Bounded.
      ++ rewrite toList_Bin, toList_Tip, app_nil_r. reflexivity.
      ++ right. rewrite size_Bin. lia.
    - assert (~ (sz = 0))%Z by (intro; subst; simpl in n; congruence).
      assert (sz > 0)%Z by lia.
      replace ((Bits.shiftR (2 ^ sz)%Z 1%Z)) with (2^(sz - 1))%Z.
      Focus 2.
        unfold Bits.shiftR, Bits.instance_Bits_Int.
        rewrite Z.shiftr_div_pow2 by lia.
        rewrite Z.pow_sub_r by lia.
        reflexivity.
      assert (Z.to_nat (sz - 1) < Z.to_nat sz)%nat.
      { rewrite Z2Nat.inj_sub by lia. 
        apply Nat.sub_lt.
        apply Z2Nat.inj_le.
        lia.
        lia.
        lia.
        replace (Z.to_nat 1) with 1 by reflexivity.
        lia.
      }
      eapply IH.
      ++ assumption.
      ++ lia.
      ++ eassumption.
      ++ intros l ys HBounded_l Hlist_l Hsize_l.
         destruct ys.
         + intros X HX. apply HX. clear HX.
           ** solve_Bounded.
           ** assumption.
           ** left; reflexivity.
         + simpl in HBounded_l. destruct p.
           destruct Hsize_l; try congruence.
           eapply IH; clear IH.
           ** assumption.
           ** lia.
           ** rewrite Hlist_l in H1. 
              apply StronglySorted_app in H1.
              destruct H1. 
              eassumption.
           ** intros r zs HBounded_r Hlist_r Hsize_r.
              rewrite Hlist_l in HSorted.
              assert (isLB (Some lb) e1 = true). {
                apply StronglySorted_inv in HSorted.
                destruct HSorted.
                simpl.
                rewrite Forall_forall in H10. unfold lt in H10.
                specialize (H10 (e1, a1)). 
                apply H10.
                apply in_or_app. right. left. reflexivity.
              }
              rewrite Hlist_r in HSorted.
              assert (isUB (safeHd zs) e1 = true). {
                destruct zs; try reflexivity.
                apply StronglySorted_inv in HSorted.
                destruct HSorted.
                apply StronglySorted_app in H10.
                destruct H10.
                apply StronglySorted_inv in H12.
                destruct H12.
                rewrite Forall_forall in H13. specialize (H13 p). unfold isUB. simpl. destruct p.
                unfold lt in H13.
                apply H13.
                apply in_or_app. right. left. reflexivity.
              }
              intros X HX. apply HX. clear HX.
              -- applyDesc link_Desc.
              -- erewrite toList_link by eassumption.
                 rewrite Hlist_l. rewrite Hlist_r.
                 rewrite <- !app_assoc.  reflexivity.
              -- destruct Hsize_r; [left; assumption| right].
                 applyDesc link_Desc.
                 replace (size l). replace (size r).
                 rewrite mul_pow_sub in * by lia.
                 lia.
Qed.

(*The analogue of [sem] for lists - returns the first value associated with
a given key, or None if no such key exists. We will use this to
specify several lemmas in [fromList] rather than List.elem*)
Fixpoint sem_for_lists (l : list (e * a)) (i : e) :=
  match l with
  | nil => None
  | (x,y) :: t => if i == x then Some y else sem_for_lists t i
  end.

Lemma sem_list_app: forall i xs ys,
  sem_for_lists (xs ++ ys) i = sem_for_lists xs i ||| sem_for_lists ys i.
Proof.
  intros. generalize dependent ys. induction xs; intros.
  - simpl. reflexivity.
  - simpl. destruct a0. destruct (i == e0) eqn : ?. reflexivity.
    apply IHxs.
Qed.

Lemma toList_sem'':
  forall s lb ub, Bounded s lb ub ->
  forall i, sem s i = sem_for_lists (toList s) i.
Proof.
  intros. induction H.
  - simpl. reflexivity.
  - simpl. rewrite IHBounded1. rewrite IHBounded2. rewrite toList_Bin.
    rewrite sem_list_app. rewrite app_comm_cons. rewrite sem_list_app.
    simpl. unfold SomeIf. rewrite oro_assoc. reflexivity.
Qed. 

Program Fixpoint fromDistinctAscList_go_Desc
  sz s xs {measure (length xs)} :
  (0 <= sz)%Z ->
  StronglySorted lt xs ->
  Bounded s None (safeHd xs) ->
  xs = nil \/ size s = (2*2^sz-1)%Z ->
  Desc (fromDistinctAscList_go (2^sz)%Z s xs) None None (size s + List.length xs)
    (fun i => sem s i ||| sem_for_lists xs i) := _. 
Next Obligation.
  intros.
  rename fromDistinctAscList_go_Desc into IH.
  rewrite fromDistinctAscList_go_eq by (apply Z.pow_pos_nonneg; lia).
  unfold fromDistinctAscList_go_f.
  destruct xs.
  * replace (List.length nil) with 0%Z by reflexivity.
    rewrite Z.add_0_r.
    solve_Desc.
  * repeat replace (#1) with 1%Z by reflexivity.
    replace ((Bits.shiftL (2 ^ sz)%Z 1))%Z with (2 ^ (1 + sz))%Z.
    Focus 2.
      unfold Bits.shiftL, Bits.instance_Bits_Int.
      rewrite Z.shiftl_mul_pow2 by lia.
      rewrite Z.pow_add_r by lia.
      lia. destruct p.

    destruct H2; try congruence.
    eapply fromDistinctAscList_create_Desc.
    - lia.
    - eassumption.
    - intros.
      subst.
      simpl safeHd in *.
      assert (isUB (safeHd ys) e0 = true). {
        destruct ys; try reflexivity.
        apply StronglySorted_inv in H0.
        destruct H0.
        rewrite Forall_forall in H4. specialize (H4 p). unfold isUB. destruct p. simpl.
        unfold lt in H4.
        apply H4. 
        apply in_or_app. right. left. reflexivity.
      }      
      applyDesc link_Desc.
      eapply IH.
      + simpl. rewrite app_length. lia.
      + lia.
      + apply StronglySorted_inv in H0.
        destruct H0.
        apply StronglySorted_app in H0.
        destruct H0.
        assumption.
      + assumption.
      + destruct H5; [left; assumption | right].
        replace (size s1). replace (size s).  replace (size s0).
        rewrite Z.pow_add_r by lia.
        lia.
      + intros.
        solve_Desc.
        ** replace (size s2). replace (size s1). replace (size s).
           rewrite !List.hs_coq_list_length, !Zlength_correct.
           simpl length.
           rewrite app_length, Nat2Z.inj_succ, Nat2Z.inj_add.
           erewrite <- size_spec by eassumption.
           lia.
        ** simpl. 
           setoid_rewrite sem_list_app.
           setoid_rewrite <- toList_sem''; only 2: eassumption.
           f_solver.
Qed.

Lemma fromDistinctAscList_Desc:
  forall xs,
  StronglySorted lt xs ->
  Desc (fromDistinctAscList xs) None None (List.length xs) (fun i => sem_for_lists xs i).
Proof.
  intros.
  unfold fromDistinctAscList.
  fold fromDistinctAscList_create_f.
  fold fromDistinctAscList_create.
  fold fromDistinctAscList_go_f.
  fold fromDistinctAscList_go.
  destruct xs.
  * solve_Desc.
  * replace (#1) with (2^0)%Z by reflexivity. destruct p.
    eapply fromDistinctAscList_go_Desc.
    + lia.
    + apply StronglySorted_inv in H.
      destruct H.
      assumption.
    + assert (isUB (safeHd xs) e0 = true). {
        destruct xs; try reflexivity.
        apply StronglySorted_inv in H.
        destruct H.
        rewrite Forall_forall in H0. destruct p. unfold isUB. simpl.
        unfold lt in H0. specialize (H0 (e1, a1)). 
        apply H0.
        left. reflexivity.
      }
      solve_Bounded.
    + right. reflexivity.
    + intros.
      rewrite List.hs_coq_list_length, Zlength_cons in *.
      rewrite size_Bin in *.
      solve_Desc. simpl. f_solver.
Qed.

(** ** Verification of [fromDistinctDescList] *)

(** Copy’n’paste from [fromDistinctAscList] *)

Local Definition gt : e * a -> e * a -> Prop
  := fun x1 x2 => let (e1, a1) := x1 in let (e2, a2) := x2 in (e1 > e2) = true.

Definition fromDistinctDescList_create_f : (Int -> list (e * a) -> (Map e a) * list (e * a)) -> 
(Int -> list (e * a) -> Map e a * list ( e * a)).
Proof.
  let rhs := eval unfold fromDistinctDescList in (@fromDistinctDescList e a) in
  lazymatch rhs with context [deferredFix2 ?f] => exact f end.
Defined.

Definition fromDistinctDescList_create : Int -> list (e * a) -> (Map e a) * list (e * a)
  := deferredFix2 (fromDistinctDescList_create_f).

Lemma fromDistinctDescList_create_eq:
  forall i xs, (1 <= i)%Z ->
  fromDistinctDescList_create i xs = fromDistinctDescList_create_f fromDistinctDescList_create i xs.
Proof.
  intros.
  change (uncurry fromDistinctDescList_create (i, xs) = uncurry (fromDistinctDescList_create_f fromDistinctDescList_create) (i, xs)).
  apply deferredFix_eq_on with
    (f := fun g => uncurry (fromDistinctDescList_create_f (curry g)))
    (P := fun p => (1 <= fst p)%Z)
    (R := fun x y => (1 <= fst x < fst y)%Z).
  * eapply wf_inverse_image with (R := fun x y => (1 <= x < y)%Z).
    apply Z.lt_wf with (z := 1%Z).
  * clear i xs H.
    intros g h x Px Heq.
    destruct x as [i xs]. simpl in *.
    unfold fromDistinctDescList_create_f.
    destruct_match; try reflexivity.
    repeat replace (#1) with 1%Z by reflexivity.
    unfold op_zeze__, Eq_Integer___, op_zeze____.
    destruct (Z.eqb_spec i 1); try reflexivity.
    unfold curry.
    assert (1 < i)%Z by lia.
    assert (1 <= Z.shiftr i 1)%Z by (apply Z_shiftr_pos; lia).
    assert (Z.shiftr i 1 < i)%Z by (apply Z_shiftr_lt; lia).
    repeat expand_pairs. simpl.
    rewrite Heq by eauto.
    destruct_match; try reflexivity.
    rewrite Heq by eauto.
    reflexivity.
  * simpl; lia.
Qed.

(* We need to know that [create] returns no longer list than it receives. *)
Program Fixpoint fromDistinctDescList_create_preserves_length
  i xs {measure (Z.to_nat i)} :
  (1 <= i)%Z ->
  forall (P : Map e a * list (e * a) -> Prop),
  ( forall s ys,
    (length ys <= length xs)%nat ->
    P (s, ys)
  ) ->
  P (fromDistinctDescList_create i xs) := _.
Next Obligation.
  intros.
  rename fromDistinctDescList_create_preserves_length into IH.
  rewrite fromDistinctDescList_create_eq by assumption.
  unfold fromDistinctDescList_create_f.
  destruct xs.
  * apply H0. reflexivity.
  * repeat replace (#1) with 1%Z by reflexivity.
    unfold op_zeze__, Eq_Integer___, op_zeze____.
    destruct (Z.eqb_spec i 1).
    + destruct p. apply H0. simpl. lia.
    + assert (Z.to_nat (Bits.shiftR i #1) < Z.to_nat i)%nat. {
        apply Z2Nat.inj_lt.
        apply Z.shiftr_nonneg. lia.
        lia.
        apply Z_shiftr_lt; lia.
      }
      apply IH.
      - assumption. 
      - apply Z_shiftr_pos; lia.
      - intros.
        destruct_match.
        ** apply H0. simpl in *. lia.
        ** apply IH.
           -- assumption.
           -- apply Z_shiftr_pos; lia.
           -- intros.
               destruct p0. apply H0. simpl in *. lia.
Qed.

Definition fromDistinctDescList_go_f : (Int -> Map e a -> list (e * a) -> Map e a) ->
 (Int -> Map e a -> list (e * a) -> Map e a).
Proof.
  let rhs := eval unfold fromDistinctDescList in (@fromDistinctDescList e a) in
  let rhs := eval fold fromDistinctDescList_create_f in rhs in 
  let rhs := eval fold fromDistinctDescList_create in rhs in 
  lazymatch rhs with context [deferredFix3 ?f] => exact f end.
Defined.

Definition fromDistinctDescList_go : Int -> Map e a -> list (e * a) -> Map e a
  := deferredFix3 (fromDistinctDescList_go_f).

Lemma fromDistinctDescList_go_eq:
  forall i s xs, (0 < i)%Z ->
  fromDistinctDescList_go i s xs = fromDistinctDescList_go_f fromDistinctDescList_go i s xs.
Proof.
  intros.
  change (deferredFix (fun g => uncurry (uncurry (fromDistinctDescList_go_f (curry (curry g))))) (i, s, xs) =
    uncurry (uncurry (fromDistinctDescList_go_f fromDistinctDescList_go)) (i, s, xs)).
  rewrite deferredFix_eq_on with
    (P := fun p => (1 <= fst (fst p))%Z)
    (R := fun x y => (length (snd x) < length (snd y))%nat); only 1: reflexivity.
  * apply well_founded_ltof with (f := fun x => length (snd x)).
  * intros g h p Px Heq.
    destruct p as [[x y] z].
    simpl in *.
    unfold fromDistinctDescList_go_f.
    destruct_match; try reflexivity.
    eapply fromDistinctDescList_create_preserves_length; try lia.
    intros s' ys Hlength. destruct p.
    apply Heq.
    + apply Z_shiftl_pos.
      lia.
    + simpl. lia.
  * simpl. lia.
Qed.

Program Fixpoint fromDistinctDescList_create_Desc
  sz ub xs x {measure (Z.to_nat sz)} :
  (0 <= sz)%Z ->
  StronglySorted (fun x y => gt x y) ((ub, x) :: xs) ->
  forall (P : (Map e a) * list (e * a) -> Prop),
  ( forall (s : Map e a) (ys: list (e * a)),
    Bounded s  (safeHd ys) (Some ub)->
    xs = rev(toList s) ++ ys ->
    ys = nil \/ size s = (2*2^sz-1)%Z ->
    P (s, ys)
  ) ->
  P (fromDistinctDescList_create (2^sz)%Z xs) := _.
Next Obligation.
  intros ????? Hnonneg HSorted.  
  rename fromDistinctDescList_create_Desc into IH.
  rewrite fromDistinctDescList_create_eq
    by (enough (0 < 2^sz)%Z by lia; apply Z.pow_pos_nonneg; lia).
  unfold fromDistinctDescList_create_f.
  destruct xs.
  * intros X HX. apply HX. clear HX.
    - solve_Bounded.
    - reflexivity.
    - left. reflexivity.
  * repeat replace (#1) with 1%Z by reflexivity.
    unfold op_zeze__, Eq_Integer___, op_zeze____.

    inversion HSorted. subst.
    inversion H2. subst. clear H2.
    inversion H1. subst.
    destruct p.
    assert (isLB (safeHd xs) e0 = true). {
      destruct xs; try reflexivity.
      inversion H5. subst. unfold safeHd. destruct p. unfold gt in H6.
      unfold isLB. order e. } 
    
    destruct (Z.eqb_spec (2^sz) 1).
    - intros X HX. apply HX. clear HX.
      ++ solve_Bounded. unfold gt in H3. unfold isUB. order e.
      ++ rewrite toList_Bin, toList_Tip, app_nil_r. reflexivity.
      ++ right. rewrite size_Bin. lia.
    - assert (~ (sz = 0))%Z by (intro; subst; simpl in n; congruence).
      assert (sz > 0)%Z by lia.
      replace ((Bits.shiftR (2 ^ sz)%Z 1%Z)) with (2^(sz - 1))%Z.
      Focus 2.
        unfold Bits.shiftR, Bits.instance_Bits_Int.
        rewrite Z.shiftr_div_pow2 by lia.
        rewrite Z.pow_sub_r by lia.
        reflexivity.
      assert (Z.to_nat (sz - 1) < Z.to_nat sz)%nat.
      { rewrite Z2Nat.inj_sub by lia. 
        apply Nat.sub_lt.
        apply Z2Nat.inj_le.
        lia.
        lia.
        lia.
        replace (Z.to_nat 1) with 1 by reflexivity.
        lia.
      }
      eapply IH.
      ++ assumption.
      ++ lia.
      ++ eassumption.
      ++ intros l ys HBounded_l Hlist_l Hsize_l.
         destruct ys.
         + intros X HX. apply HX. clear HX.
           ** solve_Bounded.
           ** assumption.
           ** left; reflexivity.
         + simpl in HBounded_l. destruct p.
           destruct Hsize_l; try congruence.
           eapply IH; clear IH.
           ** assumption.
           ** lia.
           ** rewrite Hlist_l in H1. 
              apply StronglySorted_app in H1.
              destruct H1. 
              eassumption.
           ** intros r zs HBounded_r Hlist_r Hsize_r.
              rewrite Hlist_l in HSorted.
              assert (isUB (Some ub) e1 = true). {
                apply StronglySorted_inv in HSorted.
                destruct HSorted.
                simpl.
                rewrite Forall_forall in H10. unfold gt in H10.
                specialize (H10 (e1, a1)). 
                assert (e1 < ub = true <-> ub > e1 = true) by (order e). rewrite H11.
                apply H10.
                apply in_or_app. right. left. reflexivity.
              }
              rewrite Hlist_r in HSorted.
              assert (isLB (safeHd zs) e1 = true). {
                destruct zs; try reflexivity.
                apply StronglySorted_inv in HSorted.
                destruct HSorted.
                apply StronglySorted_app in H10.
                destruct H10.
                apply StronglySorted_inv in H12.
                destruct H12.
                rewrite Forall_forall in H13. specialize (H13 p). unfold isLB. simpl. destruct p.
                unfold gt in H13. assert (e2 < e1 = true <-> e1 > e2 = true) by (order e).
                rewrite H14.
                apply H13.
                apply in_or_app. right. left. reflexivity.
              }
              intros X HX. apply HX. clear HX.
              -- applyDesc link_Desc.
              -- erewrite toList_link by eassumption.
                 rewrite Hlist_l. rewrite Hlist_r.
                 rewrite !rev_app_distr; simpl.
                 rewrite <- !app_assoc.  simpl. reflexivity.
              -- destruct Hsize_r; [left; assumption| right].
                 applyDesc link_Desc.
                 replace (size l). replace (size r).
                 rewrite mul_pow_sub in * by lia.
                 lia.
Qed.

(*If we look for an element in a map's list, it is the same as looking in the reverse of that list.
This is euivalent to saying that the first key, value pair that matches a given key is the same
as the last pair*)
Lemma sem_list_rev:
  forall m lb ub x,
  Bounded m lb ub ->
  sem_for_lists (toList m) x = sem_for_lists (rev (toList m)) x.
Proof.
  intros. generalize dependent x. induction H; intros.
  - simpl. reflexivity.
  - rewrite toList_Bin. rewrite rev_app_distr.
 simpl. rewrite <- app_assoc. simpl.
    rewrite sem_list_app. rewrite sem_list_app. rewrite <- IHBounded2.
    assert (forall {a} (x : a) l, x :: l = (x :: nil) ++ l). { intros.
    simpl. reflexivity. } rewrite H5. rewrite sem_list_app.
    rewrite (H5 _ _ (rev (toList s1))). rewrite sem_list_app.
    rewrite <- IHBounded1. repeat(erewrite <- toList_sem'').
    destruct (sem s1 x0) eqn : ?. simpl.
    assert (sem s2 x0 = None). { eapply sem_outside_below. apply H0. solve_Bounds. }
    rewrite H6. simpl. assert (x0 == x = false) by solve_Bounds. rewrite H7; reflexivity.
    simpl. destruct (x0 == x) eqn : ?. assert (sem s2 x0 = None). { eapply sem_outside_below.
    apply H0. solve_Bounds. } rewrite H6. reflexivity. simpl. rewrite oro_None_r. reflexivity.
    apply H0. apply H.
Qed.

Program Fixpoint fromDistinctDescList_go_Desc
  sz s xs {measure (length xs)} :
  (0 <= sz)%Z ->
  StronglySorted (fun x y => gt x y) xs ->
  Bounded s (safeHd xs) None  ->
  xs = nil \/ size s = (2*2^sz-1)%Z ->
  Desc (fromDistinctDescList_go (2^sz)%Z s xs) None None (size s + List.length xs)
    (fun i => sem s i ||| sem_for_lists xs i) := _. 
Next Obligation.
  intros.
  rename fromDistinctDescList_go_Desc into IH.
  rewrite fromDistinctDescList_go_eq by (apply Z.pow_pos_nonneg; lia).
  unfold fromDistinctDescList_go_f.
  destruct xs.
  * replace (List.length nil) with 0%Z by reflexivity.
    rewrite Z.add_0_r.
    solve_Desc.
  * repeat replace (#1) with 1%Z by reflexivity.
    replace ((Bits.shiftL (2 ^ sz)%Z 1))%Z with (2 ^ (1 + sz))%Z.
    Focus 2.
      unfold Bits.shiftL, Bits.instance_Bits_Int.
      rewrite Z.shiftl_mul_pow2 by lia.
      rewrite Z.pow_add_r by lia.
      lia. destruct p.

    destruct H2; try congruence.
    eapply fromDistinctDescList_create_Desc.
    - lia.
    - eassumption.
    - intros.
      subst.
      simpl safeHd in *.
      assert (isLB (safeHd ys) e0 = true). {
        destruct ys; try reflexivity.
        apply StronglySorted_inv in H0.
        destruct H0.
        rewrite Forall_forall in H4. specialize (H4 p). unfold isLB. destruct p. simpl.
        unfold gt in H4. assert (e1 < e0 = true <->e0 > e1 = true) by (order e). rewrite H6.
        apply H4. 
        apply in_or_app. right. left. reflexivity.
      }      
      applyDesc link_Desc.
      eapply IH.
      + simpl. rewrite app_length. lia.
      + lia.
      + apply StronglySorted_inv in H0.
        destruct H0.
        apply StronglySorted_app in H0.
        destruct H0.
        assumption.
      + assumption.
      + destruct H5; [left; assumption | right].
        replace (size s1). replace (size s).  replace (size s0).
        rewrite Z.pow_add_r by lia.
        lia.
      + intros.
        solve_Desc.
        ** replace (size s2). replace (size s1). replace (size s).
           rewrite !List.hs_coq_list_length, !Zlength_correct.
           simpl length.
           rewrite app_length, Nat2Z.inj_succ, Nat2Z.inj_add, rev_length.
           erewrite <- size_spec by eassumption.
           lia.
        ** simpl. setoid_rewrite sem_list_app. 
            assert (forall i, sem_for_lists (rev (toList s0)) i = sem_for_lists (toList s0) i).
            setoid_rewrite (sem_list_rev s0 (safeHd ys) (Some e0) _ H3). intros. reflexivity. 
            setoid_rewrite H9.
            setoid_rewrite <- toList_sem''; only 2: eassumption.
            f_solver.
Qed.



Lemma fromDistinctDescList_Desc:
  forall xs,
  StronglySorted (fun x y => gt x y) xs ->
  Desc (fromDistinctDescList xs) None None (List.length xs) (fun i => sem_for_lists xs i).
Proof.
  intros.
  unfold fromDistinctDescList.
  fold fromDistinctDescList_create_f.
  fold fromDistinctDescList_create.
  fold fromDistinctDescList_go_f.
  fold fromDistinctDescList_go.
  destruct xs.
  * solve_Desc.
  * replace (#1) with (2^0)%Z by reflexivity. destruct p.
    eapply fromDistinctDescList_go_Desc.
    + lia.
    + apply StronglySorted_inv in H.
      destruct H.
      assumption.
    + assert (isLB (safeHd xs) e0 = true). {
        destruct xs; try reflexivity.
        apply StronglySorted_inv in H.
        destruct H.
        rewrite Forall_forall in H0. destruct p. unfold isLB. simpl.
        unfold gt in H0. specialize (H0 (e1, a1)). 
        assert (e1 < e0 = true <-> e0 > e1 = true) by (order e). rewrite H1.
        apply H0.
        left. reflexivity.
      }
      solve_Bounded.
    + right. reflexivity.
    + intros.
      rewrite List.hs_coq_list_length, Zlength_cons in *.
      rewrite size_Bin in *.
      solve_Desc. simpl. f_solver.
Qed.

(** ** Verification of [combineEq] *)

(*Since [combineEq'] and [combineEq] are defined inside [fromAscList] (unlike in Data.Set), we define them here
and then prove equivalence*)

Fixpoint combineEq' {e} {a} `{EqLaws e} (x : e * a) (l : list (e * a) ) :=
  match x, l with
  |z, nil => z :: nil
  |(a, b), (c, d) :: t => if a == c then combineEq' (c, d) t else (a,b) :: combineEq' (c,d) t
  end.

(*The combineEq' from Data.Map (defined here to make combineEq'_equiv nicer*)
Definition old_combineEq' :=(fix combineEq' (arg_0__ : e * a) (arg_1__ : list (e * a)) {struct arg_1__} : list (e * a) :=
   let (kz, _) := arg_0__ in
   match arg_1__ with
   | nil => arg_0__ :: nil
   | (kx, xx) as x :: xs' => if _GHC.Base.==_ kx kz then combineEq' (kx, xx) xs' else arg_0__ :: combineEq' x xs'
   end).

Definition combineEq {e} {a} `{EqLaws e} (l : list (e * a)) :=
  match l with
  | nil => nil
  | x :: nil => x :: nil
  | x :: t => combineEq' x t
  end.

Lemma combineEq'_equiv:
  forall l x, combineEq' x l = old_combineEq' x l.
Proof.
  intros. revert x. induction l; intros.
  - simpl. destruct x. reflexivity.
  - simpl. destruct x. destruct a0. destruct (e0 == e1) eqn : ?.
    assert (e1 == e0 = true) by (order e). rewrite H. apply IHl.
    assert (e1 == e0 = false) by (order e). rewrite H. rewrite IHl.
    reflexivity.
Qed.


Definition fromAscList' (l : list (e * a)) :=
  fromDistinctAscList (combineEq l).


Lemma fromAscList_equiv: forall (l : list (e * a)),
  fromAscList' l = fromAscList l.
Proof.
  intros l. unfold fromAscList', fromAscList. destruct l.
  - simpl. reflexivity.
  -  unfold combineEq. rewrite combineEq'_equiv. unfold old_combineEq'.
     reflexivity.
Qed.

Definition fromDescList' (l : list (e * a)) :=
  fromDistinctDescList (combineEq l).

Lemma fromDescList_equiv: forall (l : list (e * a)),
  fromDescList' l = fromDescList l.
Proof.
  intros l. unfold fromDescList', fromDescList. destruct l.
  - simpl. reflexivity.
  -  unfold combineEq. rewrite combineEq'_equiv. unfold old_combineEq'.
     reflexivity.
Qed.

Definition combineEqGo : (e * a) -> list (e * a) -> list (e * a).
Proof.
  intros.
 apply (@combineEq' e a HEq HEqLaws). apply X.  apply X0.
Defined.

(* Too much duplication here *)

(*See if a key is a (key, value) list*)
Fixpoint key_elem (l : list (e * a)) i :=
  match l with
  | nil => false
  | (x, y) :: t => (x == i) || key_elem t i
  end.

(*This finds the last value associated with a key in a list*)
Fixpoint last_value (l : list (e * a)) i:=
  match l with
  | nil => None
  | (x, y) :: t => if (x == i) then match last_value t i with
                               | None => Some y
                               | Some z => Some z
                               end else last_value t i
  end. 

(*This proves that the last_value does in fact find the last value, since it finds
the first value in the reversed list. It also justifies using either
[sem_for_lists (rev l)] or [last_value l] based on which is more convienent. For 
[combineEq] and [fromDescList] (and similar), I use [last_value l], and in
from_list, I use [sem_for_lists (rev l)]*)
Lemma last_sem_equiv: forall l x,
  sem_for_lists (rev l) x = last_value l x.
Proof.
  intros. revert x; induction l; intros.
  - simpl. reflexivity.
  - simpl. destruct a0. rewrite sem_list_app. rewrite IHl.
    simpl. destruct (e0 == x) eqn : ?. assert (x == e0 = true) by (order e).
    rewrite H. destruct (last_value l x) eqn : ?. simpl. reflexivity. simpl. reflexivity.
    assert (x == e0 = false) by (order e). rewrite H. rewrite oro_None_r. reflexivity.
Qed. 

(*An element has a last occurrence iff it is in the list*)
Lemma last_iff_elem: forall l i,
  (exists v, last_value l i = Some v) <-> key_elem l i = true.
Proof.
  intros. revert  i. induction l; split; intros.
  - simpl in H. inversion H. inversion H0.
  - simpl in H. inversion H. 
  - simpl. destruct a0.  simpl in H. destruct (e0 == i) eqn : ?.
    simpl. reflexivity. simpl. eapply IHl. apply H.
  - simpl. destruct a0. simpl in H. destruct (e0  == i) eqn : ?.
    destruct (last_value l i) eqn : ?. exists a1. reflexivity.
    exists a0. reflexivity. simpl in H. apply IHl. apply H.
Qed.

Local Definition le : e * a -> e * a -> Prop
  := fun x1 x2 => let (e1, a1) := x1 in let (e2, a2) := x2 in (e1 <= e2) = true.
  
Lemma Forall_le_elem:
  forall x x0 xs,
  Forall (fun y => le (x, x0) y) xs <-> (forall i, key_elem xs i = true -> x <= i = true).
Proof.
  intros.
  induction xs.
  * split; intro H.
    - intros i Hi; simpl in Hi; congruence.
    - constructor.
  * split; intro H.
    - inversion H; subst; clear H.
      rewrite IHxs in H3; clear IHxs.
      intros i Hi; simpl in Hi. destruct a0. 
      rewrite orb_true_iff in Hi. destruct Hi.
      + unfold le in *.  order e.
      + apply H3; assumption.
    - constructor.
      + unfold le. destruct a0. apply H. simpl. rewrite Eq_Reflexive. simpl. reflexivity.
      + rewrite IHxs; clear IHxs.
        intros i Hi. apply H. simpl. rewrite Hi. destruct a0.  apply orb_true_r.
Qed.

Lemma Forall_le_last:
  forall x x0 xs,
  Forall (fun y => le (x, x0) y) xs <-> (forall i v, last_value xs i = Some v -> x <= i = true).
Proof.
  intros.
  rewrite Forall_le_elem. split; intros.
  - apply H. apply last_iff_elem. exists v. assumption.
  - apply last_iff_elem in H0. destruct H0. apply H in H0. assumption.
Qed. 


Local Definition ge : e * a -> e * a -> Prop
  := fun x1 x2 => let (e1, a1) := x1 in let (e2, a2) := x2 in (e1 >= e2) = true.

Lemma Forall_ge_elem:
  forall x x0 xs,
  Forall (fun y => ge (x, x0) y) xs <-> (forall i, key_elem xs i = true -> x >= i = true).
Proof.
  intros.
  induction xs.
  * split; intro H.
    - intros i Hi; simpl in Hi; congruence.
    - constructor.
  * split; intro H.
    - inversion H; subst; clear H.
      rewrite IHxs in H3; clear IHxs.
      intros i Hi; simpl in Hi. destruct a0. 
      rewrite orb_true_iff in Hi. destruct Hi.
      + unfold ge in *.  order e.
      + apply H3; assumption.
    - constructor.
      + unfold ge. destruct a0. apply H. simpl. rewrite Eq_Reflexive. simpl. reflexivity.
      + rewrite IHxs; clear IHxs.
        intros i Hi. apply H. simpl. rewrite Hi. destruct a0.  apply orb_true_r.
Qed.

Lemma Forall_ge_last:
  forall x x0 xs,
  Forall (fun y => ge (x, x0) y) xs <-> (forall i v, last_value xs i = Some v -> x >= i = true).
Proof.
  intros.
  rewrite Forall_ge_elem. split; intros.
  - apply H. apply last_iff_elem. exists v. assumption.
  - apply last_iff_elem in H0. destruct H0. apply H in H0. assumption.
Qed. 

Lemma Forall_lt_elem:
  forall x x0 xs,
  Forall (fun y => lt (x, x0) y) xs <-> (forall i, key_elem xs i = true -> x < i = true).
Proof.
  intros.
  induction xs.
  * split; intro H.
    - intros i Hi; simpl in Hi; congruence.
    - constructor.
  * split; intro H.
    - inversion H; subst; clear H.
      rewrite IHxs in H3; clear IHxs.
      intros i Hi; simpl in Hi. destruct a0. 
      rewrite orb_true_iff in Hi. destruct Hi.
      + unfold lt in *.  order e.
      + apply H3; assumption.
    - constructor.
      + unfold lt. destruct a0. apply H. simpl. rewrite Eq_Reflexive. simpl. reflexivity.
      + rewrite IHxs; clear IHxs.
        intros i Hi. apply H. simpl. rewrite Hi. destruct a0.  apply orb_true_r.
Qed.

Lemma Forall_lt_last:
  forall x x0 xs,
  Forall (fun y => lt (x, x0) y) xs <-> (forall i v, last_value xs i = Some v -> x < i = true).
Proof.
  intros.
  rewrite Forall_lt_elem. split; intros.
  - apply H. apply last_iff_elem. exists v. assumption.
  - apply last_iff_elem in H0. destruct H0. apply H in H0. assumption.
Qed. 


Lemma Forall_gt_elem:
  forall x x0 xs,
  Forall (fun y => gt (x, x0) y) xs <-> (forall i, key_elem xs i = true -> x > i = true).
Proof.
  intros.
  induction xs.
  * split; intro H.
    - intros i Hi; simpl in Hi; congruence.
    - constructor.
  * split; intro H.
    - inversion H; subst; clear H.
      rewrite IHxs in H3; clear IHxs.
      intros i Hi; simpl in Hi. destruct a0. 
      rewrite orb_true_iff in Hi. destruct Hi.
      + unfold gt in *.  order e.
      + apply H3; assumption.
    - constructor.
      + unfold gt. destruct a0. apply H. simpl. rewrite Eq_Reflexive. simpl. reflexivity.
      + rewrite IHxs; clear IHxs.
        intros i Hi. apply H. simpl. rewrite Hi. destruct a0.  apply orb_true_r.
Qed.

Lemma Forall_gt_last:
  forall x x0 xs,
  Forall (fun y => gt (x, x0) y) xs <-> (forall i v, last_value xs i = Some v -> x > i = true).
Proof.
  intros.
  rewrite Forall_gt_elem. split; intros.
  - apply H. apply last_iff_elem. exists v. assumption.
  - apply last_iff_elem in H0. destruct H0. apply H in H0. assumption.
Qed. 


(*Note: This is significatly different than SetProofs. It is not enough that the keys are preserved,
we must show that each key is matched with its last value in the list*)
Lemma combineEqGo_spec:
  forall x xs,
  StronglySorted (fun x y => le x y) (x :: xs) ->
  forall P : list (e * a) -> Prop,
  (forall (ys: list (e * a)),
     StronglySorted (fun x y => lt x y) ys ->
     (forall i, last_value ys i = last_value (x :: xs) i) ->
     P ys) ->
  P (combineEqGo x xs).
Proof.
  intros x xs Hsorted.
  inversion Hsorted; subst; clear Hsorted.
  revert x H2.
  induction H1; intros x Hlt.
  * intros X HX; apply HX; clear X HX.
    + unfold lt. unfold le in Hlt. unfold combineEqGo. simpl. destruct x.
      constructor; constructor.
    + intro. unfold combineEqGo. simpl. destruct x. simpl. reflexivity.
  * inversion Hlt; subst; clear Hlt.  
    simpl. unfold combineEqGo in *. simpl in *. destruct a0. destruct x.
    destruct_match.
    + eapply IHStronglySorted; only 1: assumption; intros ys Hsortedys Hiys.
      intros X HX; apply HX; clear X HX.
      - assumption.
      - intro i. rewrite Hiys. simpl. 
        destruct (e0 == i) eqn:?, (e1 == i) eqn:?. destruct (last_value l i) eqn : ?.
        reflexivity. reflexivity. reflexivity. order e. reflexivity.
    + assert (Hlt : e1 < e0 = true) by (unfold le in H3; order e). clear H3 Heq.
      eapply IHStronglySorted; only 1: assumption; intros ys Hsortedys Hiys.
      intros X HX; apply HX; clear X HX.
      - constructor.
        ** eapply StronglySorted_R_ext; only 2: apply Hsortedys.
           intros. simpl. order e.
        ** apply Forall_lt_last.
           rewrite Forall_le_last in H.
           intros i v Hi. rewrite Hiys in Hi.  simpl in Hi. unfold lt.
           destruct (e0 == i) eqn : ?. order e. apply H in Hi. unfold le in Hi. order e.
      - intro i. simpl. rewrite Hiys. simpl. reflexivity.
Qed.

Lemma combineEqGo_spec2:
  forall x xs,
  StronglySorted (fun x y => ge x y) (x :: xs) ->
  forall P : list (e * a) -> Prop,
  (forall (ys: list (e * a)),
     StronglySorted (fun x y => gt x y) ys ->
     (forall i, last_value ys i = last_value (x :: xs) i) ->
     P ys) ->
  P (combineEqGo x xs).
Proof.
  intros x xs Hsorted.
  inversion Hsorted; subst; clear Hsorted.
  revert x H2.
  induction H1; intros x Hlt.
  * intros X HX; apply HX; clear X HX.
    + unfold lt. unfold ge in Hlt. unfold combineEqGo. simpl. destruct x.
      constructor; constructor.
    + intro. unfold combineEqGo. simpl. destruct x.  simpl. reflexivity.
  * inversion Hlt; subst; clear Hlt.  
    simpl. unfold combineEqGo in *. simpl in *. destruct a0. destruct x.
    destruct_match.
    + eapply IHStronglySorted; only 1: assumption; intros ys Hsortedys Hiys.
      intros X HX; apply HX; clear X HX.
      - assumption.
      - intro i. rewrite Hiys. simpl. 
        destruct (e0 == i) eqn:?, (e1 == i) eqn:?. destruct (last_value l i) eqn : ?.
        reflexivity. reflexivity. reflexivity. order e. reflexivity.
    + assert (Hlt : e1 > e0 = true) by (unfold ge in H3; order e). clear H3 Heq.
      eapply IHStronglySorted; only 1: assumption; intros ys Hsortedys Hiys.
      intros X HX; apply HX; clear X HX.
      - constructor.
        ** eapply StronglySorted_R_ext; only 2: apply Hsortedys.
           intros. simpl. order e.
        ** apply Forall_gt_last.
           rewrite Forall_ge_last in H.
           intros i v Hi. rewrite Hiys in Hi.  simpl in Hi. unfold lt.
           destruct (e0 == i) eqn : ?. order e. apply H in Hi. unfold ge in Hi. order e.
      - intro i. simpl. rewrite Hiys. simpl. reflexivity.
Qed.

Lemma combineEq_spec:
  forall xs,
  StronglySorted (fun x y => le x  y) xs ->
  forall P : list (e * a) -> Prop,
  (forall ys,
     StronglySorted (fun x y => lt x y) ys ->
     (forall i, last_value ys i = last_value xs i) ->
     P ys) ->
  P (combineEq xs).
Proof.
  intros xs Hsorted.
  inversion Hsorted.
  * intros X HX. apply HX. clear X HX.
    - constructor.
    - intro. reflexivity.
  * rewrite <- H1 in Hsorted. clear xs H0 H1.
    assert (combineEq (a0 :: l) = combineEqGo a0 l). {
    unfold combineEqGo. simpl. destruct l. simpl. destruct a0. reflexivity.
    reflexivity. } rewrite H0.
    apply combineEqGo_spec. assumption.
Qed.

Lemma combineEq_spec2:
  forall xs,
  StronglySorted (fun x y => ge x  y) xs ->
  forall P : list (e * a) -> Prop,
  (forall ys,
     StronglySorted (fun x y => gt x y) ys ->
     (forall i, last_value ys i = last_value xs i) ->
     P ys) ->
  P (combineEq xs).
Proof.
  intros xs Hsorted.
  inversion Hsorted.
  * intros X HX. apply HX. clear X HX.
    - constructor.
    - intro. reflexivity.
  * rewrite <- H1 in Hsorted. clear xs H0 H1.
    assert (combineEq (a0 :: l) = combineEqGo a0 l). {
    unfold combineEqGo. simpl. destruct l. simpl. destruct a0. reflexivity.
    reflexivity. } rewrite H0.
    apply combineEqGo_spec2. assumption.
Qed.


(** ** Verification of [fromAscList] *)

(*See whether a key, value pair is in a list, comparing the keys with Haskell equality
and the values with Coq equality. This will be used in place of List.In in the following
analogues of [Forall_forall]*)
Fixpoint weak_In (l : list (e * a)) (x : e * a) :=
  match l with
  | nil => False
  | (a,b) :: t => let (x0, y0) := x in (a == x0 = true) /\ b = y0 \/ weak_In t x
  end.

Lemma Forall_forall_lt: 
  forall  (l : list (e * a)) t, Forall (lt t) l <-> (forall x, weak_In l x -> lt t x).
Proof.
  intros. split; intros; induction l; intros.
  - simpl in H0. destruct H0.
  - simpl in H0. destruct a0. destruct x. destruct H0. inversion H; subst.
    destruct H0. subst. destruct t. unfold lt in *. order e.
  - apply IHl. inversion H; subst. assumption. apply H0.
  - apply Forall_nil.
  - apply Forall_cons. simpl in H. destruct a0. apply H. left.
    split. apply Eq_Reflexive. reflexivity. simpl in H.
    destruct a0. apply IHl. intros. apply H. destruct x. right. assumption.
Qed.

Lemma Forall_forall_gt: 
  forall  (l : list (e * a)) t, Forall (gt t) l <-> (forall x, weak_In l x -> gt t x).
Proof.
  intros. split; intros; induction l; intros.
  - simpl in H0. destruct H0.
  - simpl in H0. destruct a0. destruct x. destruct H0. inversion H; subst.
    destruct H0. subst. destruct t. unfold gt in *. order e.
  - apply IHl. inversion H; subst. assumption. apply H0.
  - apply Forall_nil.
  - apply Forall_cons. simpl in H. destruct a0. apply H. left.
    split. apply Eq_Reflexive. reflexivity. simpl in H.
    destruct a0. apply IHl. intros. apply H. destruct x. right. assumption.
Qed.

Lemma strongly_sorted_in_sem_lt: forall l x v,
  StronglySorted lt l ->
  sem_for_lists l x = Some v <-> weak_In l (x,v).
Proof.
  intros; revert x v; induction l; intros; split; intros.
  - inversion H0.
  - destruct H0.
  - simpl. simpl in H0. destruct a0. destruct (x == e0) eqn : ?.
    left. split. order e. inversion H0; subst; reflexivity.
    right. apply IHl. inversion H; subst; assumption. apply H0.
  - simpl in H0. simpl. destruct a0.
    destruct H0. destruct H0. subst. assert (x == e0 = true) by (order e).
    rewrite H1. reflexivity. inversion H; subst.
    rewrite Forall_forall_lt in H4. assert (A:=H0). apply H4 in H0. unfold lt in H0.
    assert (x == e0 = false) by (order e). rewrite H1. apply IHl. apply H3. apply A.
Qed.

Lemma strongly_sorted_in_sem_gt: forall l x v,
  StronglySorted gt l ->
  sem_for_lists l x = Some v <-> weak_In l (x,v).
Proof.
  intros; revert x v; induction l; intros; split; intros.
  - inversion H0.
  - destruct H0.
  - simpl. simpl in H0. destruct a0. destruct (x == e0) eqn : ?.
    left. split. order e. inversion H0; subst; reflexivity.
    right. apply IHl. inversion H; subst; assumption. apply H0.
  - simpl in H0. simpl. destruct a0.
    destruct H0. destruct H0. subst. assert (x == e0 = true) by (order e).
    rewrite H1. reflexivity. inversion H; subst.
    rewrite Forall_forall_gt in H4. assert (A:=H0). apply H4 in H0. unfold gt in H0.
    assert (x == e0 = false) by (order e). rewrite H1. apply IHl. apply H3. apply A.
Qed.

Lemma strongly_sorted_last_lt:
  forall l x,
  StronglySorted lt l ->
  last_value l x = sem_for_lists l x.
Proof.
  intros. revert x. induction H; intros.
  - simpl. reflexivity.
  - simpl. destruct a0. destruct (x == e0) eqn : ?.
    rewrite Forall_forall_lt in H0.
    rewrite IHStronglySorted.
    destruct (sem_for_lists l x) eqn : ?. 
    + rewrite strongly_sorted_in_sem_lt in Heqo. apply H0 in Heqo.
      unfold lt in Heqo. order e. apply H. destruct (e0 == x) eqn : ?. reflexivity.
    order e. assert (e0 == x = false) by (order e). rewrite H1. apply IHStronglySorted.
Qed.

Lemma strongly_sorted_last_gt:
  forall l x,
  StronglySorted gt l ->
  last_value l x = sem_for_lists l x.
Proof.
  intros. revert x. induction H; intros.
  - simpl. reflexivity.
  - simpl. destruct a0. destruct (x == e0) eqn : ?.
    rewrite Forall_forall_gt in H0.
    rewrite IHStronglySorted.
    destruct (sem_for_lists l x) eqn : ?. 
    + rewrite strongly_sorted_in_sem_gt in Heqo. apply H0 in Heqo.
      unfold gt in Heqo. order e. apply H. destruct (e0 == x) eqn : ?. reflexivity.
    order e. assert (e0 == x = false) by (order e). rewrite H1. apply IHStronglySorted.
Qed.


Lemma fromAscList_Desc:
  forall xs,
  StronglySorted (fun x y => le x y) xs ->
  Desc' (fromAscList xs) None None (fun i => last_value xs i).
Proof.
  intros. rewrite <- fromAscList_equiv. unfold fromAscList'.
  eapply combineEq_spec; only 1: assumption; intros ys HSorted Helem.
  apply fromDistinctAscList_Desc; only 1: assumption.
  intros s HB Hsz Hf.
  solve_Desc. intros. rewrite <- Helem. rewrite strongly_sorted_last_lt.
  apply Hf. apply HSorted.
Qed.

(** ** Verification of [fromDescList] *)

Lemma fromDescList_Desc:
  forall xs,
  StronglySorted (fun x y => ge x y) xs ->
  Desc' (fromDescList xs) None None (fun i => last_value xs i).
Proof.
  intros. rewrite <- fromDescList_equiv. unfold fromDescList'.
  unfold fromDescList.
  eapply combineEq_spec2;  only 1: assumption; intros ys HSorted Helem.
  apply fromDistinctDescList_Desc; only 1: assumption.
  intros s HB Hsz Hf.
  solve_Desc. intros. rewrite <- Helem. rewrite strongly_sorted_last_gt.
  apply Hf. apply HSorted.
Qed.

(** ** Verification of [fromList] *)

(** The verification of [fromList] should be similar to that of [fromDistinctAscList], only
that the condition is checked and -- if it fails -- we resort to a backup implementation. *)

(* The following definitions are copied from the local definitions of [fromList]; 
   my ltac foo failed to do that automatic.
*)

Definition fromList' :=
          fun (t0: Map e a) (xs: list (e * a)) =>
            let ins :=
              fun arg_2__ arg_3__ =>
                match arg_2__, arg_3__ with
                | t, pair k x => insert k x t
                end in
            Data.Foldable.foldl' ins t0 xs.

Definition not_ordered :=
          fun (arg_7__ : e) (arg_8__: list (e * a)) =>
            match arg_7__, arg_8__ with
            | _, nil => false
            | kx, cons (pair ky _) _ => kx GHC.Base.>= ky
            end .

Definition fromList_create_f : (Int -> list (e * a) -> Map e a * list (e * a) * list (e * a)) -> 
(Int -> list (e * a) -> Map e a * list (e * a)  * list (e * a))
  := (fun create arg_11__ arg_12__ =>
      match arg_11__, arg_12__ with
      | _, nil => pair (pair Tip nil) nil
      | s, (cons xp xss as xs) =>
       if s GHC.Base.== #1 : bool
       then let 'pair kx x := xp in
         if not_ordered kx xss : bool
         then pair (pair (Bin #1 kx x Tip Tip) nil) xss else
         pair (pair (Bin #1 kx x Tip Tip) xss) nil else
         match create (Data.Bits.shiftR s #1) xs with
         | (pair (pair _ nil) _ as res) => res
         | pair (pair l (cons (pair ky y) nil)) zs =>
              pair (pair (insertMax ky y l) nil) zs
         | pair (pair l (cons (pair ky y) yss as ys)) _ =>
             if not_ordered ky yss : bool then pair (pair l nil) ys else
             let 'pair (pair r zs) ws := create (Data.Bits.shiftR s #1) yss in
                       pair (pair (link ky y l r) zs) ws
         end
       end).

Definition fromList_create : Int -> list (e * a) -> Map e a * list (e * a) * list (e * a)
  := deferredFix2 (fromList_create_f).

Definition fromList_go_f :=
  (fun (go: Int -> Map e a -> list (e * a) -> Map e a) (arg_28__ : Int)
   (arg_29__ : Map e a) (arg_30__: list (e * a)) =>
    match arg_28__, arg_29__, arg_30__ with
    | _, t, nil => t
    | _, t, cons (pair kx x) nil => insertMax kx x t
    | s, l, (cons (pair kx x) xss as xs) =>
          if not_ordered kx xss : bool then fromList' l xs else
          match fromList_create s xss with
          | pair (pair r ys) nil => go (Data.Bits.shiftL s #1) (link kx x l r) ys
          | pair (pair r _) ys => fromList' (link kx x l r) ys
          end
   end).

Definition fromList_go := deferredFix3 (fromList_go_f).

(** zeta-reduces exactly one (the outermost) [let] *)
Ltac zeta_one :=
  lazymatch goal with |- context A [let x := ?rhs in @?body x] =>
     let e' := eval cbv beta in (body rhs) in
     let e'' := context A [e'] in
     change e''
  end.

(* Identical to [fromDistinctAscList_create_eq] *)
Lemma fromList_create_eq:
  forall i xs, (1 <= i)%Z ->
  fromList_create i xs = fromList_create_f fromList_create i xs.
Proof.
  intros.
  change (uncurry fromList_create (i, xs) = uncurry (fromList_create_f fromList_create) (i, xs)).
  apply deferredFix_eq_on with
    (f := fun g => uncurry (fromList_create_f (curry g)))
    (P := fun p => (1 <= fst p)%Z)
    (R := fun x y => (1 <= fst x < fst y)%Z).
  * eapply wf_inverse_image with (R := fun x y => (1 <= x < y)%Z).
    apply Z.lt_wf with (z := 1%Z).
  * clear i xs H.
    intros g h x Px Heq.
    destruct x as [i xs]. simpl in *.
    unfold fromList_create_f.
    destruct_match; try reflexivity.
    repeat replace (#1) with 1%Z by reflexivity.
    unfold op_zeze__, Eq_Integer___, op_zeze____.
    destruct (Z.eqb_spec i 1); try reflexivity.
    unfold curry.
    assert (1 < i)%Z by lia.
    assert (1 <= Z.shiftr i 1)%Z by (apply Z_shiftr_pos; lia).
    assert (Z.shiftr i 1 < i)%Z by (apply Z_shiftr_lt; lia).
    repeat expand_pairs. simpl.
    rewrite Heq by eauto.
    destruct_match; try reflexivity.
    rewrite Heq by eauto.
    reflexivity.
  * simpl; lia.
Qed.

(* We need to know that [create] returns no longer list than it receives.
   Like [fromDistinctAscList_create_preserves_length], just a few more cases.
 *)
Program Fixpoint fromList_create_preserves_length
  i xs {measure (Z.to_nat i)} :
  (1 <= i)%Z ->
  forall (P : Map e a * list (e * a) * list (e * a) -> Prop),
  ( forall s ys zs ,
    (length ys <= length xs)%nat ->
    P (s, ys, zs)
  ) ->
  P (fromList_create i xs) := _.
Next Obligation.
  intros.
  rename fromList_create_preserves_length into IH.
  rewrite fromList_create_eq by assumption.
  unfold fromList_create_f.
  destruct xs.
  * apply H0. reflexivity.
  * repeat replace (#1) with 1%Z by reflexivity.
    unfold op_zeze__, Eq_Integer___, op_zeze____.
    destruct (Z.eqb_spec i 1).
    + destruct p. destruct_match.
      - apply H0. simpl. lia.
      - apply H0. simpl. lia.
    + assert (Z.to_nat (Bits.shiftR i #1) < Z.to_nat i)%nat. {
        apply Z2Nat.inj_lt.
        apply Z.shiftr_nonneg. lia.
        lia.
        apply Z_shiftr_lt; lia.
      }
      apply IH.
      - assumption. 
      - apply Z_shiftr_pos; lia.
      - intros.
        destruct_match.
        ** apply H0. simpl in *. lia.
        ** apply IH.
           -- assumption.
           -- apply Z_shiftr_pos; lia.
           -- intros.
              repeat destruct_match.
              ++ apply H0. simpl in *. lia.
              ++ apply H0. simpl in *. lia.
              ++ apply H0. simpl in *. lia.
Qed.

Lemma fromList_go_eq:
  forall i s xs, (0 < i)%Z ->
  fromList_go i s xs = fromList_go_f fromList_go i s xs.
Proof.
  intros.
  change (deferredFix (fun g => uncurry (uncurry (fromList_go_f (curry (curry g))))) (i, s, xs) =
    uncurry (uncurry (fromList_go_f fromList_go)) (i, s, xs)).
  rewrite deferredFix_eq_on with
    (P := fun p => (1 <= fst (fst p))%Z)
    (R := fun x y => (length (snd x) < length (snd y))%nat); only 1: reflexivity.
  * apply well_founded_ltof with (f := fun x => length (snd x)).
  * intros g h p Px Heq.
    destruct p as [[x y] z].
    simpl in *.
    unfold fromList_go_f.
    destruct_match; try reflexivity.
    eapply fromList_create_preserves_length; try lia.
    intros s' ys zs Hlength.
    destruct_match; try reflexivity.
    destruct_match; try reflexivity.
    destruct_match; try reflexivity.
    destruct_match; try reflexivity.
    apply Heq.
    + apply Z_shiftl_pos.
      lia.
    + simpl. simpl in *. lia.
  * simpl. lia.
Qed.

Program Fixpoint fromList_create_Desc
  sz lb xs {measure (Z.to_nat sz)} :
  (0 <= sz)%Z ->
  not_ordered lb xs = false ->
(*   StronglySorted (fun x y => x < y = true) (lb :: xs) -> *)
  forall (P : Map e a * list (e * a) * list (e * a) -> Prop),
  ( forall s ys zs,
    Bounded s (Some lb) (safeHd ys) ->
    isUB (safeHd ys) lb = true ->
    xs = toList s ++ ys ++ zs->
    ys = nil \/ (size s = (2*2^sz-1)%Z /\ zs = nil) ->
    P (s, ys, zs)
  ) ->
  P (fromList_create (2^sz)%Z xs) := _.
Next Obligation.
  intros ???? Hnonneg HheadOrdered.
  rename fromList_create_Desc into IH.
  rewrite fromList_create_eq
    by (enough (0 < 2^sz)%Z by lia; apply Z.pow_pos_nonneg; lia).
  unfold fromList_create_f.
  destruct xs.
  * intros X HX. apply HX. clear HX.
    - solve_Bounded.
    - reflexivity.
    - reflexivity.
    - left. reflexivity.
  * repeat replace (#1) with 1%Z by reflexivity.
    unfold op_zeze__, Eq_Integer___, op_zeze____.
    
    simpl in HheadOrdered. destruct p.

(*     assert (isUB (safeHd xs) e0 = true). {
      destruct xs; try reflexivity.
      inversion H5. assumption.
    } *)

    destruct (Z.eqb_spec (2^sz) 1); [ destruct_match | ].
    - intros X HX. apply HX; clear HX.
      ++ solve_Bounded.
      ++ reflexivity.
      ++ rewrite toList_Bin, toList_Tip, app_nil_r. reflexivity.
      ++ left. reflexivity.
    - intros X HX. apply HX; clear HX.
      ++ destruct xs; simpl in Heq;  solve_Bounded. destruct p. unfold safeHd. unfold isUB. order e.
      ++ destruct xs; simpl in *; solve_Bounds. destruct p. solve_Bounds.
      ++ rewrite toList_Bin, toList_Tip, !app_nil_r, !app_nil_l. reflexivity.
      ++ right. split. rewrite size_Bin. lia. reflexivity.
    - assert (~ (sz = 0))%Z by (intro; subst; simpl in n; congruence).
      assert (sz > 0)%Z by lia.
      replace ((Bits.shiftR (2 ^ sz)%Z 1%Z)) with (2^(sz - 1))%Z.
      Focus 2.
        unfold Bits.shiftR, Bits.instance_Bits_Int.
        rewrite Z.shiftr_div_pow2 by lia.
        rewrite Z.pow_sub_r by lia.
        reflexivity.
      assert (Z.to_nat (sz - 1) < Z.to_nat sz)%nat.
      { rewrite Z2Nat.inj_sub by lia. 
        apply Nat.sub_lt.
        apply Z2Nat.inj_le.
        lia.
        lia.
        lia.
        replace (Z.to_nat 1) with 1 by reflexivity.
        lia.
      }
      eapply IH.
      ++ assumption.
      ++ lia.
      ++ eassumption.
      ++ intros l ys zs HBounded_l HisUB_l Hlist_l Hsize_l.
         destruct ys.
         + intros X HX. apply HX. clear HX.
           ** solve_Bounded.
           ** assumption.
           ** assumption.
           ** left; reflexivity.
         + simpl in HBounded_l.
           destruct Hsize_l as [? | [??]]; try congruence.
           subst. rewrite app_nil_r in Hlist_l. destruct p.
           assert (isLB (Some lb) e1 = true) by solve_Bounds.
           destruct ys; only 2: destruct_match.
           -- intros X HX. apply HX; clear HX.
              ** assert (isUB None e1 = true) by reflexivity.
                 applyDesc insertMax_Desc.
              ** reflexivity.
              ** erewrite toList_insertMax by eassumption.
                 rewrite app_nil_l, <- app_assoc.
                 assumption.
              ** left; reflexivity.
           -- intros X HX. apply HX; clear HX.
              ** solve_Bounded.
              ** reflexivity.
              ** rewrite app_nil_l. simpl in Hlist_l.
                 assumption.
              ** left; reflexivity.
           -- eapply IH; clear IH.
              ** assumption.
              ** lia.
              ** eassumption.
              ** simpl in Heq.
                 intros r zs zs' HBounded_r HisUB_r Hlist_r Hsize_r.
                 intros X HX. apply HX. clear HX.
                 --- applyDesc link_Desc.
                 --- solve_Bounds.
                 --- erewrite toList_link by eassumption.
                     rewrite Hlist_l. rewrite Hlist_r.
                     rewrite <- !app_assoc.  reflexivity.
                 --- destruct Hsize_r; [left; assumption| right].
                     destruct H4.
                     split; only 2: assumption.
                     applyDesc link_Desc.
                     replace (size l). rewrite H4.
                     rewrite mul_pow_sub in * by lia.
                     lia.
Qed.

Lemma foldl_foldl' : forall {b} f (x : b) (l: list (e * a)),
  Foldable.foldl f x l = Foldable.foldl' f x l.
Proof.
  intros.  unfold Foldable.foldl, Foldable.foldl'; unfold Foldable.Foldable__list;
    unfold  Foldable.foldl__ , Foldable.foldl'__ ; 
    unfold Foldable.Foldable__list_foldl', Foldable.Foldable__list_foldl;
    unfold Base.foldl, Base.foldl'. reflexivity.
Qed.

Definition fromList'' :=
          fun (t0: Map e a) (xs: list (e * a)) =>
            let ins :=
              fun arg_2__ arg_3__ =>
                match arg_2__, arg_3__ with
                | t, pair k x => insert k x t
                end in
            Data.Foldable.foldl ins t0 xs.


Lemma fromList'_fromList'': forall m l,
  fromList' m l = fromList'' m l.
Proof.
  intros. unfold fromList'. unfold fromList''. rewrite <- (foldl_foldl' _ m l). reflexivity.
Qed.

Lemma fromList'_Desc:
  forall s l,
  Bounded s None None ->
  Desc' (fromList' s l) None None (fun i => sem_for_lists (rev l) i ||| sem s i).
Proof.
  intros. rewrite fromList'_fromList''.
  unfold fromList''.
  rewrite Foldable.hs_coq_foldl_list.
  revert s H.
  induction l.
  * intros.
    simpl.
    solve_Desc.
  * intros.
    simpl. destruct a0.
    applyDesc insert_Desc.
    applyDesc IHl.
    solve_Desc. f_solver; rewrite sem_list_app in Heqo0.
    + rewrite Heqo1 in Heqo0. inversion Heqo0. reflexivity.
    + rewrite Heqo1 in Heqo0. inversion Heqo0. reflexivity.
    + rewrite Heqo1 in Heqo0. simpl in Heqo0. rewrite Heqb in Heqo0. rewrite Hsem in Hsem0.
      rewrite Hsem0 in Heqo0. assumption.
    + rewrite Heqo1 in Heqo0. simpl in Heqo0. rewrite Heqb in Heqo0. inversion Heqo0.
    + rewrite Heqo2 in Heqo0. inversion Heqo0.
    + rewrite Heqo2 in Heqo0. inversion Heqo0.
    + rewrite Heqo2 in Heqo0. simpl in Heqo0. rewrite Heqb in Heqo0. inversion Heqo0.
    + rewrite Heqo2 in Heqo0. inversion Heqo0.
    + rewrite Heqo2 in Heqo0. inversion Heqo0.
    + rewrite Heqo2 in Heqo0. simpl in Heqo0. rewrite Heqb in Heqo0. inversion Heqo0.
    + rewrite Heqo1 in Heqo0. simpl in Heqo0. rewrite Heqb in Heqo0. inversion Heqo0.
Qed. 

(*In a well formed map, we can only find each key once in the list, so it doesn't matter
if we look in the list or the reverse list*)
Lemma sem_toList_reverse: forall m lb ub i,
  Bounded m lb ub ->
  sem_for_lists (rev (toList m)) i = sem_for_lists (toList m) i.
Proof.
  intros. revert i. induction H; intros.
  - simpl. reflexivity.
  - rewrite toList_Bin. rewrite rev_app_distr. rewrite sem_list_app.
    rewrite sem_list_app. simpl. rewrite sem_list_app. 
    rewrite IHBounded2. simpl. rewrite IHBounded1. repeat (erewrite <- toList_sem'').
    destruct (sem s2 i) eqn : ?. assert (sem s1 i = None). { eapply sem_outside_above.
    apply H. unfold isUB. apply (sem_inside H0) in Heqo. destruct Heqo. order_Bounds. }
    rewrite H5. simpl. assert (i == x = false) by solve_Bounds. rewrite H6. reflexivity.
    simpl. destruct (i == x) eqn : ?. assert (sem s1 i = None). { eapply sem_outside_above.
    apply H. unfold isUB. order_Bounds. } rewrite H5. simpl. reflexivity. simpl.
    rewrite oro_None_r. reflexivity. apply H. apply H0.
Qed.


Program Fixpoint fromList_go_Desc
  sz s xs {measure (length xs)} :
  (0 <= sz)%Z ->
  Bounded s None (safeHd xs) ->
  xs = nil \/ size s = (2*2^sz-1)%Z ->
  Desc' (fromList_go (2^sz)%Z s xs) None None
    (fun i => sem_for_lists (rev xs) i ||| sem s i) := _.
Next Obligation.
  intros.
  rename fromList_go_Desc into IH.
  rewrite fromList_go_eq by (apply Z.pow_pos_nonneg; lia).
  unfold fromList_go_f.
  destruct xs as [ | ? [ | ?? ]].
  * solve_Desc.
  * destruct H1; try congruence.
    simpl safeHd in *. destruct p.
    assert (isUB None e0 = true) by reflexivity.
    applyDesc insertMax_Desc.
    solve_Desc. simpl.
    (*setoid_rewrite elem_cons.*)
    f_solver.
  * destruct H1; try congruence.
    repeat replace (#1) with 1%Z by reflexivity.
    replace ((Bits.shiftL (2 ^ sz)%Z 1))%Z with (2 ^ (1 + sz))%Z.
    Focus 2.
      unfold Bits.shiftL, Bits.instance_Bits_Int.
      rewrite Z.shiftl_mul_pow2 by lia.
      rewrite Z.pow_add_r by lia.
      lia. destruct p.
    destruct_match.
    --  apply Bounded_relax_ub_None in H0. 
        applyDesc fromList'_Desc.
        solve_Desc.
    --  eapply fromList_create_Desc.
        - lia.
        - eassumption.
        - intros.
          subst.
          simpl safeHd in *.

          applyDesc link_Desc.
          destruct zs.
          ++  rewrite app_nil_r in H4.
              eapply IH.
              + rewrite H4. simpl. rewrite app_length. lia.
              + lia.
              + assumption.
              + destruct H5 as [?|[??]]; [left; assumption | right].
                replace (size s1). replace (size s).  replace (size s0).
                rewrite Z.pow_add_r by lia.
                lia.
              + intros.
                rewrite H4.
                solve_Desc. simpl.
                (*setoid_rewrite elem_cons.*)
                setoid_rewrite sem_list_app. setoid_rewrite rev_app_distr.
                setoid_rewrite sem_list_app. 
                setoid_rewrite (sem_toList_reverse s0 _ _ _ H2). 
                setoid_rewrite <- toList_sem''; only 2: eassumption. f_solver.
                ** assert (sem s i = None). { eapply sem_outside_above. apply H0. solve_Bounds. }
                   rewrite H9 in Hsem. simpl in Hsem. assert (i == e0 = false) by solve_Bounds.
                   rewrite H10 in Hsem. simpl in Hsem. rewrite Hsem in H8. inversion H8; reflexivity.
                ** simpl in Heqo2. destruct( i == e0) eqn : ?. simpl in Hsem. 
                   assert (sem s i = None). { eapply sem_outside_above. apply H0.
                   solve_Bounds. } rewrite H9 in Hsem. simpl in Hsem. rewrite Hsem in H8.
                  rewrite Heqo2 in H8. inversion H8; reflexivity.
                ** inversion Heqo2.
                ** simpl in Heqo2. destruct (i == e0) eqn : ?. inversion Heqo2.
                   simpl in Hsem. rewrite Hsem in H8. inversion H8.
                ** destruct (sem s i); simpl in Hsem; inversion Hsem. rewrite H8 in H10.
                   inversion H10. destruct (i == e0); simpl in Hsem; inversion Hsem.
                    rewrite H8 in H11. inversion H11. rewrite H11 in H8. inversion H8.
                ** simpl in Heqo2. destruct (i == e0) eqn : ?. simpl in Hsem.
                   destruct (sem s i); simpl in Hsem. rewrite Hsem in H8. inversion H8.
                    rewrite Hsem in H8; inversion H8. inversion Heqo2.
         ++ destruct H5 as [ ? | [? Habsurd]]; try congruence.
            subst. rewrite app_nil_l in H4.
            rewrite H4.
            apply Bounded_relax_ub_None in HB.
            applyDesc fromList'_Desc.
            solve_Desc. simpl.
            (*setoid_rewrite elem_cons.*)
            setoid_rewrite sem_list_app. setoid_rewrite rev_app_distr. simpl.
            setoid_rewrite sem_list_app. setoid_rewrite (sem_toList_reverse s0 _ _ _ H2). 
            setoid_rewrite <- toList_sem''; only 2: eassumption. simpl in Hsem0.
            f_solver.
            ** assert (sem s i = None). { eapply sem_outside_above. apply H0.
              solve_Bounds. } rewrite H5 in Hsem. simpl in Hsem. 
              assert (i == e0 = false) by solve_Bounds. rewrite H6 in Hsem. simpl in Hsem.
              rewrite Hsem in Hsem0. inversion Hsem0; reflexivity.
            **  assert (sem s i = None). { eapply sem_outside_above. apply H0.
              solve_Bounds. } rewrite H5 in Hsem. simpl in Hsem. rewrite Hsem in Hsem0.
              inversion Hsem0; reflexivity.
            ** destruct (sem s i); simpl in Hsem; rewrite Hsem in Hsem0. inversion Hsem0.
                destruct (i == e0); simpl in Hsem. inversion Hsem0. inversion Hsem0.
            ** destruct (sem s i). simpl in Hsem. rewrite Hsem in Hsem0. inversion Hsem0.
              simpl in Hsem. rewrite Hsem in Hsem0. inversion Hsem0.
Qed.

Lemma fromList_Desc:
  forall xs,
  Desc' (fromList xs) None None (fun i => sem_for_lists (rev xs) i).
Proof.
  intros.
  cbv beta delta [fromList].
  destruct xs as [ | ? [|??] ].
  * solve_Desc.
  * destruct p. solve_Desc.
  * fold fromList'. destruct p.
    zeta_one.
    fold not_ordered.
    zeta_one.
    fold fromList_create_f.
    fold fromList_create.
    zeta_one.
    fold fromList_go_f.
    fold fromList_go.
    zeta_one.
    destruct_match.
    - applyDesc fromList'_Desc.
      solve_Desc. simpl. setoid_rewrite sem_list_app. setoid_rewrite sem_list_app.
       simpl. destruct p0. simpl in Hsem. setoid_rewrite sem_list_app in Hsem. simpl in Hsem.
      (*setoid_rewrite elem_cons.*)
      f_solver.
    - repeat replace (#1) with (2^0)%Z by reflexivity.
      eapply fromList_go_Desc.
      + lia.
      + destruct p0. simpl in Heq. 
        solve_Bounded.
      + right. reflexivity.
      + intros.
        solve_Desc. simpl. setoid_rewrite sem_list_app. setoid_rewrite sem_list_app.
        simpl. simpl in H1. setoid_rewrite sem_list_app in H1. simpl in H1.
        f_solver.
Qed.
