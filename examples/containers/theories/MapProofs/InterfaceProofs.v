Require Import MapProofs.Common.
Set Bullet Behavior "Strict Subproofs".
Require Import MapProofs.Bounds.
Require Import MapProofs.Tactics.
Require Import MapProofs.UnionIntersectDifferenceProofs.
Require Import MapProofs.LookupProofs.
Require Import MapProofs.InsertProofs.
Require Import MapProofs.DeleteUpdateProofs.
Require Import MapProofs.ToListProofs.
Require Import MapProofs.FilterPartitionProofs.
Require Import MapProofs.MaxMinProofs.
Require Import MapProofs.MapFunctionProofs.
Require Import MapProofs.TypeclassProofs.
Require Import MapProofs.ContainerFacts.
(** * Instantiating the [FMapInterface] *)

Require Import Coq.FSets.FMapInterface.
Require Import Coq.Structures.Equalities.
From Coq Require Import ssrbool ssreflect.
Require Import OrdTheories.

Module MapFMap (E : OrderedType)<: WSfun(E) <: WS <: Sfun(E) <: S.
  Module E := E.

  Include OrdTheories.OrdTheories E.
  Definition key := E.t.

  Definition WFMap (e: Type) :=
  {m : Map key e | WF m}.

  Definition t: Type -> Type := WFMap.
Section Types.

  Variable elt : Type.

  Program Definition empty: t elt := empty.
  Next Obligation. constructor. Qed.

  Program Definition is_empty: t elt -> bool := null.

  Program Definition add: key -> elt -> t elt -> t elt := insert.
  Next Obligation. unfold proj1_sig. destruct x1. apply insert_WF; assumption.
  Defined.

  Program Definition find: key -> t elt -> option elt := lookup.

  Program Definition remove: key -> t elt -> t elt := delete.
  Next Obligation. destruct x0. simpl. eapply delete_Desc.
  - apply w.
  - intros. apply H.
  Defined.

  Program Definition mem : key -> t elt -> bool := member.

  Variable elt' elt'' : Type.

  Program Definition map : (elt -> elt') -> t elt -> t elt' := Internal.map.
  Next Obligation. destruct x0. simpl. apply map_preserves_WF. apply w. Defined.

  (*A few lemmas useful in proving mapWithKey's well formdedness*)
  Lemma mapWithKey_pres_size: forall {a : Type} {b : Type} (m: Map key b) (f: key -> b -> a) lb ub,
  Bounded m lb ub ->
  size m = size (mapWithKey f m).
  Proof.
  intros. inversion H; reflexivity.
  Qed.
  Lemma mapWithKey_pres_WF: forall {a : Type} {b : Type} (m: Map key b) (f: key -> b -> a) lb ub,
  Bounded m lb ub ->
  Bounded (mapWithKey f m) lb ub.
  Proof.
    intros. induction H.
    - simpl. constructor.
    - simpl. apply BoundedBin; try(assumption); erewrite <- mapWithKey_pres_size;
      try(erewrite <- mapWithKey_pres_size); try (assumption); try (eassumption).
  Qed.

  Program Definition mapi : (key -> elt -> elt') -> t elt -> t elt' := mapWithKey.
  Next Obligation. destruct x0. simpl. apply mapWithKey_pres_WF. apply w. Defined.

  (*[map2] is a particularly complex function to write, since there is no direct analogue. It is possible
  to write several ways, including folding over both maps in order or folding over the [toList] of the
  two maps. Instead, I defined it by first mapping each map to a map of (key, option elt''), then
  unioning the two together [map2_map], and then folding this combined map into a map of (key, elt''),
  keeping only the values with Some [map2_fix]. This makes the proofs more manageable, though it is not
  particularly efficient*)

  Definition map2_map (m1: Map key elt) (m2: Map key elt') (f: option elt -> option elt' -> option elt'') :
    Map key (option elt'') :=
    union (mapWithKey (fun k v =>(f (sem m1 k)(sem m2 k))) m1)
   (mapWithKey (fun k v => f (sem m1 k) (sem m2 k)) m2).

  Definition map2_fix (m1: Map key (option elt'')) (m2: Map key elt''): Map key elt'' :=
   foldrWithKey (fun k v t => match v with
                             |Some x => insert k x t
                             |None => t
                             end) m2 m1.

(*A few helper lemmas that each of these functions preserve well formed maps*)
  Lemma map2_map_wf : forall m1 m2 f,
    WF m1 ->
    WF m2 ->
    WF (map2_map m1 m2 f).
  Proof.
    intros. unfold map2_map. eapply union_Desc.
    - apply mapWithKey_pres_WF. apply H.
    - apply mapWithKey_pres_WF. apply H0.
    - intros. apply H1.
  Qed.
  Lemma map2_fix_pres_wf: forall m m',
  WF m ->
  WF m' ->
  WF (map2_fix m m').
  Proof.
  intros. unfold map2_fix. generalize dependent m'. induction H; intros.
  - simpl. assumption.
  - simpl. apply IHBounded1. destruct v eqn : ?.
    + eapply insert_Desc. apply IHBounded2. assumption. reflexivity. reflexivity. intros.
      apply H6.
    + apply IHBounded2. apply H5.
Qed.

  Program Definition map2 : (option elt -> option elt' -> option elt'') -> t elt -> t elt' -> t elt'' :=
    fun f m1 m2 =>
    map2_fix (map2_map m1 m2 f) Tip.
  Next Obligation. destruct m1. destruct m2. simpl. apply map2_fix_pres_wf.
  apply map2_map_wf. assumption. assumption. constructor. Defined.

  Program Definition elements : t elt -> list (key * elt) := toList.

  Program Definition cardinal : t elt -> nat := map_size.

  Definition foldlWithKey2 {a} := fun (f : key -> elt -> a -> a) (m : Map key elt) b =>
  foldlWithKey (fun t k v => f k v t) b m.

  Program Definition fold : forall (A : Type), (key -> elt -> A -> A) -> t elt -> A -> A :=
   @foldlWithKey2.

  (*Possibly defined elsewhere, this just compares two lists using a comparison function f
  on the values and checking the keys for (decidable) equality*)
  Fixpoint cmp_list (l1 : list (key * elt)) l2 (f: elt -> elt -> bool) :=
  match l1, l2 with
  | nil, nil => true
  | (k1, v1) :: xs, (k2, v2) :: ys => E.eq_dec k1 k2 && f v1 v2 && cmp_list xs ys f
  | _, _ => false
  end.

  Program Definition equal : (elt -> elt -> bool) -> t elt -> t elt -> bool :=
  fun cmp m1 m2 => cmp_list (toList m1) (toList m2) cmp.

Section Spec.

Variable m m' m'' : t elt.
Variable x y z: key.
Variable e e' : elt.

  Program Definition MapsTo: key -> elt -> t elt -> Prop :=
  fun k v m => sem m k = Some v.

  Definition In (k: key) (m : t elt) : Prop := exists e, MapsTo k e m.

  Definition Empty m := forall (a : key)(e:elt) , ~ MapsTo a e m.

  Definition eq_key (p p':key*elt) := E.eq (fst p) (fst p').

  Definition eq_key_elt (p p':key*elt) :=
          E.eq (fst p) (fst p') /\ (snd p) = (snd p').

  (*Theories*)

  Lemma MapsTo_1: E.eq x y -> MapsTo x e m -> MapsTo y e m.
  Proof.
    intros. unfold MapsTo in *. erewrite sem_resp_eq. apply H0.
    epose proof elt_eqP. inversion H1. symmetry. apply H2.
    apply E.eq_sym in H. contradiction.
  Qed.

  Lemma mem_1 :In x m -> mem x m = true.
  Proof.
    intros. destruct m.  unfold mem. unfold In in H. simpl.
    unfold MapsTo in H. simpl in H. eapply member_spec. apply w. apply H.
  Qed.

  Lemma mem_2 :mem x m = true -> In x m.
  Proof.
    intros. destruct m. unfold mem in H. unfold In. unfold MapsTo. simpl in *.
    eapply member_spec. apply w. apply H.
  Qed.

  Lemma empty_1 : Empty empty.
  Proof.
    unfold Empty. intros. unfold MapsTo. simpl. intro contra. discriminate contra.
  Qed.

  Lemma is_empty_1: Empty m -> is_empty m = true.
  Proof.
    intros. destruct m. unfold Empty in H. unfold is_empty. unfold MapsTo in H. simpl in *.
    assert (forall a, sem x0 a = None). intros. specialize (H a). destruct (sem x0 a) eqn : ?.
    specialize (H e0). contradiction. reflexivity. rewrite null_empty_iff.
    rewrite <- empty_no_elts. apply H0.
  Qed.

  Lemma is_empty_2 :is_empty m = true -> Empty m.
  Proof.
    intros. destruct m. unfold is_empty in H. unfold Empty. unfold MapsTo. simpl in *.
    intros. erewrite null_empty_iff in H. rewrite <- empty_no_elts in H.
    specialize (H a). rewrite H. intro contra. discriminate contra.
  Qed.

  Lemma elt_neq: ~E.eq x y <-> x == y = false.
  Proof.
    intros. split; intros.
    - destruct (x == y) eqn : ?. apply elt_eq in Heqb. contradiction. reflexivity.
    - intro. apply elt_eq in H0. rewrite H0 in H. inversion H.
  Qed.

  Lemma add_1 : E.eq x y -> MapsTo y e (add x e m).
  Proof.
    intros. destruct m. unfold MapsTo. unfold add. simpl. eapply insert_Desc.
    - apply w.
    - reflexivity.
    - reflexivity.
    - intros. specialize (H2 y). apply E.eq_sym in H. apply elt_eq in H.
      rewrite H in H2. simpl in H2. assumption.
  Qed.

  Lemma add_2 :~ E.eq x y -> MapsTo y e m -> MapsTo y e (add x e' m).
  Proof.
    intros. destruct m. unfold MapsTo in *. unfold add. simpl in *. eapply insert_Desc.
    - apply w.
    - reflexivity.
    - reflexivity.
    - intros. specialize (H3 y). assert (EqLaws E.t). apply EqLaws_elt. destruct H4.
      apply elt_neq in H. assert (y == x = false) by (order key). rewrite H4 in H3.
       simpl in H3. rewrite H3.
      assumption.
  Qed.

  Lemma add_3 :~ E.eq x y -> MapsTo y e (add x e' m) -> MapsTo y e m.
  Proof.
    intros. destruct m. unfold MapsTo in *. unfold add in H0. simpl in *.
    erewrite sem_insert in H0.
    - apply elt_neq in H. assert (y == x = false) by (order key). rewrite H1 in H0.
      simpl in H0. assumption.
    - apply w.
    - reflexivity.
    - reflexivity.
  Qed.

  (*A sem rule for delete*)
  Lemma delete_sem: forall (m: Map key elt) k i,
  WF m ->
  sem (delete k m) i = if i == k then None else sem m i.
  Proof.
    intros. eapply delete_Desc.
    - apply H.
    - intros. specialize (H2 i). rewrite H2. reflexivity.
  Qed.

  Lemma remove_1 : E.eq x y -> ~ In y (remove x m).
  Proof.
    intros. destruct m. unfold In. unfold MapsTo. unfold remove. simpl. intro.
    destruct H0. rewrite delete_sem in H0. apply elt_eq in H.
    assert ( x == y = true) by (apply H). assert (y == x = true) by (order key).
     rewrite H2 in H0. inversion H0. apply w.
  Qed.

  Lemma remove_2 : ~ E.eq x y -> MapsTo y e m -> MapsTo y e (remove x m).
  Proof.
    intros. unfold MapsTo in *. unfold remove. destruct m. simpl in *.
    rewrite delete_sem. apply elt_neq in H.  assert (y == x = false) by (order key).
    rewrite H1. assumption. apply w.
  Qed.

  Lemma remove_3 : MapsTo y e (remove x m) -> MapsTo y e m.
  Proof.
    intros. unfold MapsTo in *. destruct m. unfold remove in *. simpl in *.
    rewrite delete_sem in H.  destruct (y == x). inversion H. assumption. apply w.
  Qed.

  Lemma find_1 : MapsTo x e m -> find x m = Some e.
  Proof.
    intros. unfold MapsTo in *. unfold find. destruct m. simpl in *.
    erewrite lookup_spec. apply H. apply w.
  Qed.

  Lemma find_2 : find x m = Some e -> MapsTo x e m.
  Proof.
    intros. unfold find in *. unfold MapsTo. destruct m. simpl in *.
    erewrite lookup_spec in H. assumption. apply w.
  Qed.

  (*Proves the equivalence of Top.In and InA, since both are used in different lemmas*)
  Lemma In_InA_equiv: forall l k v,
    Key_In k v l <-> InA eq_key_elt (k, v) l.
  Proof.
    intros. induction l.
    - simpl. split; intros.
      + destruct H.
      + inversion H.
    - simpl. unfold eq_key_elt in *. split; intros.
      + destruct a. destruct H.
        * destruct H. apply InA_cons_hd. simpl. split.
          apply elt_eq. assert (k == k0 = true) by (order key). apply H1. symmetry.
          apply H0.
        * apply InA_cons_tl. apply IHl. apply H.
      + destruct a. inversion H; subst.
        * simpl in H1. destruct H1. left. split. assert (k == k0 = true) by (apply elt_eq; apply H0).
          order key. symmetry. apply H1.
        * right. apply IHl. apply H1.
  Qed.

(*This is a stronger version of toList_sem that does not require {EqLaws a}. The other
  actually should be implied by this, and can be replaced*)
Lemma toList_sem_again :
  forall (m: Map key elt) lb ub, Bounded m lb ub ->
  forall key value, sem m key = Some value <-> Key_In key value (toList m).
Proof.
  clear.
  intros. generalize dependent value. induction H.
  - simpl. intros. split; intros. discriminate H. destruct H.
  - intros. simpl. rewrite toList_Bin. rewrite elem_or.
    assert (((x, v) :: nil ++ toList s2) = (((x, v) :: nil) ++ toList s2)).
    simpl. reflexivity. simpl.  split; intros.
      + destruct (sem s1 key0) eqn : ?; simpl in H6.
      * apply IHBounded1 in H6. left. apply H6.
      * destruct (key0 == x) eqn : ?; simpl in H6.
        { right. left. simpl. split. order key. inversion H6; subst; reflexivity. }
        { apply IHBounded2 in H6. right. right. assumption. }
     + destruct H6.
      * apply IHBounded1 in H6. rewrite H6. simpl. reflexivity.
      * destruct H6. destruct H6.
        assert (sem s1 key0 = None). { eapply sem_outside_above.
        apply H. unfold isUB. order key. }
        rewrite H8. simpl. apply Eq_Symmetric in H6. rewrite H6. simpl.
        rewrite H7. reflexivity. apply IHBounded2 in H6.
        assert (sem s1 key0 = None). { eapply sem_outside_above. apply H. unfold isUB.
        apply (sem_inside H0 ) in H6. destruct H6. unfold isLB in H6. order key. }
        rewrite H7. assert (key0 == x = false). { apply (sem_inside H0) in H6.
        destruct H6. unfold isLB in H6. order key. } rewrite H8. simpl.
        assumption.
Qed.

  Lemma elements_1 :
        MapsTo x e m -> InA eq_key_elt (x,e) (elements m).
  Proof.
    intros. destruct m. unfold elements. unfold MapsTo in H. simpl in *.
    setoid_rewrite toList_sem_again in H. rewrite <- In_InA_equiv. apply H. apply w.
  Qed.

  Lemma elements_2:
        InA eq_key_elt (x,e) (elements m) -> MapsTo x e m.
  Proof.
    intros. unfold MapsTo. unfold elements in *. destruct m. simpl in *.
    eapply toList_sem_again.  apply w. rewrite In_InA_equiv. apply H.
  Qed.

  Import Coq.Sorting.Sorted.

  (*For proving things about elements, we need to redo some of the sorting lemmas, since the
    assumptions are slightly difference (no OrdLaws a)*)
  Local Definition lt : key * elt -> key * elt -> Prop
  := fun x1 x2 => let (e1, a1) := x1 in let (e2, a2) := x2 in (e1 < e2) = true.

  Lemma All_lt_elem:
  forall x i xs,
  Forall (lt x) xs ->
  InA eq_key i xs->
  lt x i.
  Proof.
    intros. unfold eq_key in H0.
    induction H.
    * inversion H0.
    * destruct x0. destruct i. inversion H0; subst.
      - simpl in H3. unfold lt. unfold lt in H. destruct x1.
        assert (k0 == k1 = true) by (apply elt_eq; apply H3). order key.
      - apply IHForall. apply H3.
  Qed.

  (*Unfortunately, we know that the list is sorted, which is much stronger than than there
    are no duplicates. We must prove one implies the other*)
  Lemma sorted_no_dups: forall (l: list (key * elt)),
  StronglySorted lt l -> NoDupA (eq_key) l.
  Proof.
    intros. induction H.
    - constructor.
    - constructor. intro. pose proof All_lt_elem. specialize (H2 a a l H0 H1).
      unfold lt in H2. destruct a. order key.
      apply IHStronglySorted.
  Qed.

  Lemma elements_3w : NoDupA eq_key (elements m).
  Proof.
    intros. unfold elements. destruct m. simpl. apply sorted_no_dups.
    eapply to_List_sorted. apply w.
  Qed.

  Lemma size_equiv: forall (m: Map key elt),
  WF m ->
  Internal.size m = Z.of_nat (map_size m).
  Proof.
    intros. induction H.
    - simpl. reflexivity.
    - simpl. rewrite Zpos_P_of_succ_nat. rewrite Nat2Z.inj_add.
      rewrite <- IHBounded1. rewrite <- IHBounded2. rewrite size_size. omega.
  Qed.

  Lemma cardinal_1 : cardinal m = length (elements m).
  Proof.
    intros. unfold cardinal. unfold elements. destruct m. simpl.
    assert (Z.of_nat (map_size x0) = Z.of_nat (length (toList x0))). {
    rewrite <- size_equiv. eapply size_spec. apply w. apply w. }
    omega.
  Qed.

Lemma foldlWithKey2_fold_left:
    forall {a} (f: key -> elt -> a -> a) (n : a) (map: Map key elt),
  foldlWithKey2 f map n = fold_left (fun t (x : key * elt) => let (a0, b0) := x in f a0 b0 t) (toList map) n.
Proof.
  intros. revert n. revert f. induction map0; intros.
  - simpl. rewrite IHmap0_1. rewrite IHmap0_2. rewrite toList_Bin. rewrite fold_left_app.
    simpl. reflexivity.
  - simpl. reflexivity.
Qed.

Lemma fold_1 :
        forall (m: t elt) (A : Type) (i : A) (f : key -> elt -> A -> A),
        fold _ f m i = fold_left (fun a p => f (fst p) (snd p) a) (elements m) i.
Proof.
  intros. destruct m0. unfold fold.  unfold elements. simpl.
  rewrite foldlWithKey2_fold_left. unfold fst. unfold snd.  revert i. revert f.
  induction w.
  - simpl. reflexivity.
  - intros. rewrite toList_Bin. simpl. rewrite fold_left_app. rewrite fold_left_app. simpl.
    rewrite IHw1. rewrite IHw2. reflexivity.
Qed.

Definition Equal m m' := forall y, find y m = find y m'.

Definition Equiv (eq_elt: elt -> elt -> Prop) m m' :=
  (forall k, In k m <-> In k m') /\ (forall k e e', MapsTo k e m -> MapsTo k e' m' -> eq_elt e e').

Definition Equivb (cmp: elt -> elt -> bool) := Equiv (Cmp cmp).

Variable cmp: elt -> elt -> bool.

(*If the (key, value) pair is in a list, so is just the key*)
Lemma eq_key_elt_implies_key: forall k v l,
  InA eq_key_elt (k,v) l ->
  InA eq_key (k, v) l.
Proof.
  intros. generalize dependent k. generalize dependent v. induction l; intros.
  - inversion H.
  - inversion H; subst.
    + constructor. unfold eq_key. simpl. unfold eq_key_elt in H1. destruct H1. simpl in H0.
      apply H0.
    + apply InA_cons_tl. apply IHl. apply H1.
Qed.

(*Annoyingly, we cannot use the results about StronglySortedness from before, since they
all deal with haskell equality and require EqLaws a. So we have to prove a similar, but
not quite identical, claim*)
Lemma strongly_sorted_cmp_unique: forall (xs ys : list (key * elt)) (cmp: elt -> elt -> bool),
  StronglySorted lt xs ->
  StronglySorted lt ys ->
  (forall x, ((exists y, Key_In x y xs) <-> (exists z, Key_In x z ys)) /\
   (forall y z, Key_In x y xs /\ Key_In x z ys -> cmp y z = true )) ->
  cmp_list xs ys cmp = true.
Proof.
  clear.
  intros. generalize dependent ys. generalize dependent cmp. induction xs; intros.
  - destruct ys.
    + reflexivity.
    + destruct p. specialize (H1 k). destruct H1. destruct H1. simpl in H3.
      assert (exists (e: elt), False). apply H3. exists e. left. split. apply Eq_Reflexive.
      reflexivity. destruct H4. destruct H4.
  - destruct ys.
    + destruct a. specialize (H1 k). destruct H1. destruct H1. simpl in H1.
      assert (exists (e: elt), False). apply H1. exists e. left. split. apply Eq_Reflexive.
      reflexivity. destruct H4. destruct H4.
    + simpl. destruct a. destruct p. rewrite andb_true_iff. split.
      * rewrite andb_true_iff. split.
        -- inversion H; subst. inversion H0; subst. assert (A:=H1). specialize (H1 k). destruct H1.
           destruct H1. assert (exists z : elt, Key_In k z ((k0, e0) :: ys)). apply H1.
           simpl. exists e. left. split. apply Eq_Reflexive. reflexivity. destruct H8.
           simpl in H8. destruct H8.
           ++ destruct H8. apply elt_eq. apply Eq_Symmetric in H8. apply elt_eq in H8. apply H8.
           ++ specialize (A k0). destruct A. destruct H9. assert (exists y : elt, Key_In k0 y ((k, e) :: xs)).
              apply H11. exists e0. simpl. left. split. apply Eq_Reflexive. reflexivity. destruct H12.
              simpl in H12. destruct H12.
              ** destruct H12. apply H12.
              ** apply (All_lt_elem _ (k, x) _) in H7. apply (All_lt_elem _ (k0, x0) _) in H5.
                  unfold lt in H7. unfold lt in H5. order key.
                  setoid_rewrite (In_InA_equiv xs k0 x0) in H12. setoid_rewrite In_InA_equiv in H8.
                  unfold eq_key_elt in H8. apply eq_key_elt_implies_key. apply H12.
                  apply eq_key_elt_implies_key. apply In_InA_equiv. apply H8.
        -- assert (A:=H1). specialize (H1 k). specialize (A k0). destruct H1. destruct A.
           destruct H1. destruct H3. assert (exists z : elt, Key_In k z ((k0, e0) :: ys)).
           apply H1. exists e. simpl. left. split. apply Eq_Reflexive. reflexivity.
           destruct H7. assert (exists y : elt, Key_In k0 y ((k, e) :: xs)). apply H6.
           exists e0. simpl. left. split. apply Eq_Reflexive. reflexivity. destruct H8.
           simpl in H7. simpl in H8. destruct H7. destruct H8.
           destruct H7. destruct H8. subst. apply H4. split. simpl. left. split. order key.
           reflexivity. simpl. left. split. apply Eq_Reflexive. reflexivity.
            inversion H; subst. apply (All_lt_elem _ (k0, x0) _) in H12. unfold lt in H12.
            order key. apply eq_key_elt_implies_key. apply In_InA_equiv. apply H8.
            inversion H0; subst. apply (All_lt_elem _ (k, x) _) in H12. simpl in H12.
            destruct H8. order key. inversion H; subst. apply (All_lt_elem _ (k0, x0) _) in H14.
            unfold lt in H14. order key. apply eq_key_elt_implies_key. apply In_InA_equiv.
            apply H8. apply eq_key_elt_implies_key. apply In_InA_equiv. apply H7.
      * inversion H; subst. inversion H0; subst. apply IHxs. apply H4. apply H6. intros.
        split.
        -- assert (k == k0 = true). { assert (A:=H1). specialize (H1 k).
              specialize (A k0). destruct H1. destruct H1. destruct A. destruct H8.
              assert (exists z : elt, Key_In k z ((k0, e0) :: ys)). apply H1. exists e.
              simpl. left. split. apply Eq_Reflexive. reflexivity.
              assert (exists y : elt, Key_In k0 y ((k, e) :: xs)). apply H10. exists e0.
              left. split. apply Eq_Reflexive. reflexivity. destruct H11. destruct H12.
              simpl in H11. simpl in H12. destruct H11. order key. destruct H12. order key.
              apply (All_lt_elem _ (k, x0) _ ) in H7. apply (All_lt_elem _ (k0, x1) _ ) in H5.
              unfold lt in *. order key. apply  eq_key_elt_implies_key. apply In_InA_equiv.
              apply H12. apply eq_key_elt_implies_key. apply In_InA_equiv. apply H11. }
              split; intros.
           ++ assert (k < x = true). destruct H3. apply (All_lt_elem _ (x, x0) _) in H5.
              unfold lt in H5. assumption. apply eq_key_elt_implies_key. apply In_InA_equiv.
              apply H3.
              assert (k0 < x = true) by (order key).
              specialize (H1 x). destruct H1. destruct H1.
              assert (exists z : elt, Key_In x z ((k0, e0) :: ys)). apply H1. destruct H3.
              exists x0. simpl. right. assumption. destruct H12. simpl in H12.
              destruct H12. order key. exists x0. assumption.
            ++ assert (k0 < x = true). destruct H3. apply (All_lt_elem _ (x, x0) _) in H7.
                unfold lt in H7. assumption. apply eq_key_elt_implies_key. apply In_InA_equiv.
                apply H3. assert (k < x = true ) by (order key).
                specialize (H1 x). destruct H1. destruct H1.
                assert (exists y : elt, Key_In x y ((k, e) :: xs)). apply H11. destruct H3.
                exists x0. simpl. right. assumption. destruct H12. simpl in H12. destruct H12.
                order key. exists x0. assumption.
          -- intros. specialize (H1 x). destruct H1. apply H3. destruct H2. split.
              ++ simpl. right. assumption.
              ++ simpl. right. assumption.
Qed.


Lemma equal_1: Equivb cmp m m' -> equal cmp m m' = true.
Proof.
  clear.
  intros. unfold equal. unfold Equivb in H. unfold Equiv in H. unfold MapsTo in H.
  unfold Cmp in H. unfold In in H. unfold MapsTo in H. destruct m. destruct m'.
  simpl in *. apply strongly_sorted_cmp_unique. eapply to_List_sorted. apply w.
  eapply to_List_sorted. apply w0. intros. split.
  - setoid_rewrite <- toList_sem_again. destruct H. apply H. apply w. apply w0.
  - intros. destruct H. destruct H0. eapply H1. rewrite toList_sem_again.
    apply H0. apply w. rewrite toList_sem_again. apply H2. apply w0.
Qed.

Lemma eq_list_prop: forall (l: list (key * elt)) l' (cmp: elt -> elt -> bool),
  StronglySorted lt l ->
  StronglySorted lt l' ->
  cmp_list l l' cmp = true ->
  (forall k, (exists v, Key_In k v l) <-> (exists v, Key_In k v l')) /\
  (forall k v v', Key_In k v l /\ Key_In k v' l' -> cmp v v' = true).
Proof.
  clear.
  intros. generalize dependent l'. generalize dependent cmp. induction l; intros.
  - destruct l'.
    + split; intros.
      * simpl. reflexivity.
      * simpl in H2. destruct H2. destruct H2.
    + split; intros.
      * inversion H1.
      * simpl in H2. destruct H2. destruct H2.
  - destruct l'.
    + simpl in H1. destruct a. inversion H1.
    + simpl in H1. destruct a. destruct p. setoid_rewrite andb_true_iff in H1. destruct H1.
      setoid_rewrite andb_true_iff in H1. destruct H1. split; intros.
      * split; intros.
        -- destruct H4. simpl in H4. destruct H4.
           ++ destruct H4. subst. simpl. exists e0. left. split. assert (k == k0 = true). apply elt_eq.
              apply elt_eq in H1. apply H1. order key. reflexivity.
           ++ simpl. apply IHl in H2. destruct H2. assert ((exists v : elt, Key_In k1 v l')).
              apply H2. exists x. assumption. destruct H6. exists x0. right. assumption. inversion H; assumption.
              inversion H0; assumption.
        -- simpl in H4. destruct H4. destruct H4.
           ++ destruct H4. subst. simpl. exists e. left. split. assert (k == k0 = true). apply elt_eq.
              apply elt_eq in H1. apply H1. order key. reflexivity.
           ++ simpl. apply IHl in H2. destruct H2.
              assert (exists v : elt, Key_In k1 v l). apply H2. exists x. assumption. destruct H6.
              exists x0. right. assumption. inversion H; assumption. inversion H0; assumption.
      * simpl in H4. destruct H4. destruct H4.
         -- destruct H5.
            ++ destruct H4. destruct H5. subst. apply H3.
            ++ inversion H0; subst. apply (All_lt_elem _ (k1, v') _) in H9. unfold lt in H9.
               assert (k == k0 = true). apply elt_eq. apply elt_eq in H1. assumption. order key.
               apply eq_key_elt_implies_key. apply In_InA_equiv. apply H5.
          -- inversion H; subst. apply (All_lt_elem _ (k1, v) _) in H9. unfold lt in H9. destruct H5.
             ++ assert (k == k0 = true). apply elt_eq. apply elt_eq in H1. assumption. order key.
             ++ inversion H0; subst. specialize (IHl H8 cmp0 l' H10 H2). destruct IHl.
                eapply H7. split. apply H4. apply H5.
             ++ apply eq_key_elt_implies_key. apply In_InA_equiv. assumption.
Qed.

Lemma equal_2: equal cmp m m' = true -> Equivb cmp m m'.
Proof.
  clear.
  intros. unfold equal in H. unfold Equivb. unfold Cmp. unfold Equiv. unfold In. unfold MapsTo.
  destruct m. destruct m'. simpl in *. apply eq_list_prop in H.
  destruct H. split; intros.
  - specialize (H k). setoid_rewrite toList_sem_again. apply H. apply w. apply w0.
  - eapply H0. setoid_rewrite toList_sem_again in H1. setoid_rewrite toList_sem_again in H2.
    split. apply H1. apply H2. apply w0. apply w.
  - eapply to_List_sorted. apply w.
  - eapply to_List_sorted. apply w0.
Qed.

End Spec.
End Types.


Lemma map_1 :forall (elt elt' : Type) (m: t elt) (x : key) (e : elt) (f: elt -> elt'),
  MapsTo _ x e m -> MapsTo _ x (f e) (map _ _ f m).
Proof.
  intros. unfold MapsTo in *. destruct m. simpl in *. eapply map_Desc.
  apply w. intros. specialize (H2 x). rewrite H in H2. assumption.
Qed.

Lemma map_2: forall (elt elt' : Type) (m : t elt) (x : key) (f : elt -> elt'),
  In _ x (map _ _ f m) -> In _ x m.
Proof.
  intros. unfold In in *. unfold MapsTo in *. destruct m. simpl in *.
  rewrite map_mapWithKey_equiv in H.
  destruct (sem x0 x) eqn : ?.
  - exists e. reflexivity.
  - destruct H. eapply map_none_spec in Heqo. setoid_rewrite H in Heqo. inversion Heqo.
    apply w.
Qed.

(*If sem of the mapped map is Some v, then there was an equivalent (Haskell) key in the
  original map*)
Lemma mapWithKey_reverse: forall (elt elt' : Type) (m: Map key elt) (f: key -> elt -> elt'),
  WF m ->
  (forall i v, sem (mapWithKey f m) i = Some v -> exists i', E.eq i i' /\ exists value, sem m i' = Some value).
Proof.
  intros. generalize dependent f. revert i. revert v. induction H; intros.
  - inversion H0.
  - simpl. simpl in H5. destruct (sem (mapWithKey f s1) i) eqn : ?. inversion H5; subst.
    apply IHBounded1 in Heqo. destruct Heqo. destruct H3. destruct H6. exists i. split. auto with ordered_type.
    exists x1. assert (sem s1 i = Some x1). erewrite sem_resp_eq. apply H6. apply elt_eq. apply H3.
    rewrite H7. reflexivity. eapply map_none_spec in Heqo.
    simpl in H5. destruct (i == x) eqn : ?. simpl in H5. inversion H5. exists x.
    split. apply elt_eq in Heqb. assumption. rewrite Eq_Reflexive. simpl. exists v.
    assert (sem s1 x = None). erewrite sem_resp_eq. apply Heqo. order key. rewrite H6.
    simpl. reflexivity. simpl in H5. exists i. split. auto with ordered_type. apply IHBounded2 in H5.
    destruct H5. destruct H5. destruct H6. exists x1. rewrite Heqo. rewrite Heqb. simpl.
    erewrite sem_resp_eq. apply H6. apply elt_eq. assumption. apply H.
Qed.

Lemma mapi_1: forall (elt elt' : Type) (m: t elt) (x: key) (e: elt) (f: key -> elt -> elt'),
  MapsTo _ x e m -> exists y, E.eq y x /\ MapsTo _ x (f y e) (mapi _ _ f m).
Proof.
  intros. unfold MapsTo in *. destruct m. simpl in *. induction w.
  - inversion H.
  - simpl. simpl in H. destruct (sem s1 x) eqn : ?. simpl in H; inversion H; subst.
    apply IHw1 in H. destruct H. exists x1. destruct H. split. assumption. rewrite H2. simpl. reflexivity.
    simpl in H. destruct (x == x0) eqn : ?. exists x0. split. apply elt_eq in Heqb. auto with ordered_type.
    simpl in H. inversion H; subst. apply (map_none_spec f s1 lb (Some x0)) in Heqo. rewrite Heqo. simpl. reflexivity.
    apply w1. simpl in H. apply IHw2 in H. destruct H. destruct H. exists x1. split.
    auto. apply (map_none_spec f s1 lb (Some x0)) in Heqo. rewrite Heqo. simpl. apply H4. apply w1.
Qed.

Lemma mapi_2: forall (elt elt' : Type) (m: t elt) (x : key) (f: key -> elt -> elt'),
  In _ x (mapi _ _ f m) -> In _ x m.
Proof.
  intros. unfold In in *. unfold MapsTo in *. destruct m. simpl in *. destruct H.
  apply mapWithKey_reverse in H. destruct H. destruct H. destruct H0. exists x3.
  erewrite sem_resp_eq. apply H0. apply elt_eq. apply H. apply w.
Qed.

(*For [map2], there are a lot of lemmas to prove. First, we further split map2_map into two functions
  (proving equivalence) so we can prove things about each of them. This gets a bit redundant, but
  ultimately we want to prove that if a key is is 1 of the two maps, then k, f (sem m1 k) (sem m2 k)
  is in the resulting map, and if it is in neither maps, then k is not in the resulting map *)

Definition map2_map_part1 (elt elt' elt'' : Type) (m1: Map key elt) (m2: Map key elt')
  (f: option elt -> option elt' -> option elt'') :
  Map key (option elt'') :=
  mapWithKey (fun k v => f (sem m1 k) (sem m2 k)) m1.

Definition map2_map_part2 (elt elt' elt'' : Type) (m1: Map key elt) (m2: Map key elt')
  (f: option elt -> option elt' -> option elt'') :
  Map key (option elt'') :=
  mapWithKey (fun k v => f (sem m1 k) (sem m2 k)) m2.

Definition map2_map_alt (elt elt' elt'' : Type) (m1: Map key elt) (m2: Map key elt')
  (f: option elt -> option elt' -> option elt'') : Map key (option elt'') :=
  union (map2_map_part1 _ _ _ m1 m2 f) (map2_map_part2 _ _ _ m1 m2 f).

Lemma map2_map_equiv: forall (elt elt' elt'' : Type) (m1: Map key elt) (m2: Map key elt')
  (f: option elt -> option elt' -> option elt''),
  map2_map _ _ _ m1 m2 f = map2_map_alt _ _ _ m1 m2 f.
Proof.
  intros. unfold map2_map. unfold map2_map_alt. unfold map2_map_part1.
  unfold map2_map_part2. reflexivity.
Qed.

Lemma map2_map_part_1_in : forall (elt elt' elt'' : Type)(m: Map key elt) (m': Map key elt') (x: key)
  (f: option elt -> option elt' -> option elt''),
  WF m ->
  WF m' ->
  (exists v, sem m x = Some v) ->
  sem (map2_map_part1 _ _ _ m m' f) x = Some (f (sem m x) (sem m' x)).
Proof.
  intros. destruct H1. unfold map2_map_part1. erewrite map_spec_coq.
  - reflexivity.
  - apply H.
  - unfold respectful. unfold Proper. intros. assert (sem m x1 = sem m y). {
    apply sem_resp_eq. assumption. }
    assert (sem m' x1 = sem m' y). { apply sem_resp_eq. assumption. }
    rewrite H3. rewrite H4. reflexivity.
  - apply H1.
Qed.

Lemma map2_map_part_1_notin : forall (elt elt' elt'' : Type)(m: Map key elt) (m': Map key elt') (x: key)
  (f: option elt -> option elt' -> option elt''),
  WF m ->
  WF m' ->
  sem m x = None ->
  sem m' x = None ->
  sem (map2_map_part1 _ _ _ m m' f) x = None.
Proof.
  intros. unfold map2_map_part1. apply (map_none_spec (fun k e => f (sem m k)  (sem m' k)) m None None).
  apply H. apply H1.
Qed.

(*See if I can cut down on repetition*)
Lemma map2_map_part_2_in : forall (elt elt' elt'' : Type)(m: Map key elt) (m': Map key elt') (x: key)
  (f: option elt -> option elt' -> option elt''),
  WF m ->
  WF m' ->
  (exists v, sem m' x = Some v) ->
  sem (map2_map_part2 _ _ _ m m' f) x = Some (f (sem m x) (sem m' x)).
Proof.
  intros. destruct H1. unfold map2_map_part2. erewrite map_spec_coq.
  - reflexivity.
  - apply H0.
  - intros. unfold respectful. unfold Proper. intros. assert (sem m x1 = sem m y). { apply sem_resp_eq. assumption. }
    assert (sem m' x1 = sem m' y). { apply sem_resp_eq. assumption. }
    rewrite H4. rewrite H3. reflexivity.
  - apply H1.
Qed.

Lemma map2_map_part_2_notin : forall (elt elt' elt'' : Type)(m: Map key elt) (m': Map key elt') (x: key)
  (f: option elt -> option elt' -> option elt''),
  WF m ->
  WF m' ->
  sem m x = None ->
  sem m' x = None ->
  sem (map2_map_part2 _ _ _ m m' f) x = None.
Proof.
  intros. unfold map2_map_part2. apply (map_none_spec (fun k e => f (sem m k)  (sem m' k)) m' None None).
  apply H0. apply H2.
Qed.

(*Putting the parts together*)

Lemma map2_map_in: forall (elt elt' elt'' : Type)(m: Map key elt) (m': Map key elt') (x: key)
  (f: option elt -> option elt' -> option elt'') x,
  WF m ->
  WF m' ->
  (exists v, sem m x = Some v) \/ (exists v, sem m' x = Some v) ->
  sem (map2_map _ _ _ m m' f) x = Some (f (sem m x) (sem m' x)).
Proof.
  intros. rewrite map2_map_equiv. unfold map2_map_alt.
  erewrite sem_union_equiv. unfold sem_union.
  destruct H1.
  - pose proof (map2_map_part_1_in _ _ _ _ _ _ f H H0 H1).
    rewrite H2. reflexivity.
  - pose proof (map2_map_part_2_in _ _ _ _ _ _ f H H0 H1).
    rewrite H2. destruct (sem m x0) eqn : ?.
    + assert (exists v, sem m x0 = Some v). exists e. assumption.
      pose proof (map2_map_part_1_in _ _ _ _ _ _ f H H0 H3). rewrite H4.
      rewrite Heqo. reflexivity.
    + assert (sem (map2_map_part1 elt0 elt' elt'' m m' f) x0 = None).
      unfold map2_map_part1. rewrite <- map_none_spec. apply Heqo. apply H.
      rewrite H3. reflexivity.
  - unfold map2_map_part1. apply mapWithKey_pres_WF. apply H.
  - unfold map2_map_part2. apply mapWithKey_pres_WF. apply H0.
Qed.


Lemma map2_map_notin: forall (elt elt' elt'' : Type)(m: Map key elt) (m': Map key elt') (x: key)
  (f: option elt -> option elt' -> option elt'') x,
  WF m ->
  WF m' ->
  sem m x = None /\ sem m' x = None ->
  sem (map2_map _ _ _ m m' f) x = None.
Proof.
  intros. rewrite map2_map_equiv. unfold map2_map_alt. erewrite sem_union_equiv.
  unfold sem_union. destruct H1.
  assert (sem (map2_map_part1 elt0 elt' elt'' m m' f) x0 = None). {
  apply map2_map_part_1_notin; assumption. }
  assert (sem (map2_map_part2 elt0 elt' elt'' m m' f) x0 = None). {
  apply map2_map_part_2_notin; assumption. }
  rewrite H3. rewrite H4. reflexivity.
  unfold map2_map_part1. apply mapWithKey_pres_WF. apply H.
  unfold map2_map_part2. apply mapWithKey_pres_WF. apply H0.
Qed.

(*Some lemmas and ltac to prove that any m such that Bounded m lb ub is well formed*)

Lemma expand_bounds_l : forall (a : Type) (m: Map key a) lb x,
  Bounded m lb x ->
  Bounded m None x.
Proof.
  intros. induction H.
  - constructor.
  - constructor; try (reflexivity); try (assumption).
Qed.

Lemma expand_bounds_r : forall (a : Type) (m: Map key a) ub x,
  Bounded m x ub ->
  Bounded m x None.
Proof.
  intros. induction H.
  - constructor.
  - constructor; try (reflexivity); try (assumption).
Qed.

Ltac wf_bounds:= eapply expand_bounds_l; eapply expand_bounds_r; eassumption.

(*Several helper lemmas for map2_fix. We need extremely strong claims to get a general enough
  hypothesis, necessitating lots of extra lemmas. This states that if the base map and the folded map
  both do not contain a key, then the result will not contain it either*)

Lemma map2_fix_none: forall (elt'' : Type) (m: Map key (option elt'')) m' x,
  WF m ->
  WF m' ->
  sem m' x = None ->
  sem m x = None ->
  sem (map2_fix _ m m') x = None.
Proof.
  intros. generalize dependent m'. induction H; intros.
  - simpl. assumption.
  - simpl in H2. simpl. destruct (sem s1 x) eqn : ?. inversion H2.
    destruct (x == x0) eqn : ?. inversion H2. destruct (sem s2 x) eqn : ?.
    inversion H2. apply IHBounded1.
    + reflexivity.
    + destruct v. apply insert_WF. apply map2_fix_pres_wf. wf_bounds. assumption.
      apply map2_fix_pres_wf. wf_bounds. assumption.
    + destruct v.
      * erewrite sem_insert. rewrite Heqb. simpl. apply IHBounded2. assumption.
        assumption. assumption. apply map2_fix_pres_wf. wf_bounds. assumption.
        reflexivity. reflexivity.
      * apply IHBounded2. reflexivity. assumption. assumption.
Qed.

(*If a key is not in the folded map, but it maps to y in the base, then it maps to y in the
  result map. Note that map2 defines the base as Tip, so the premise of this is always false for
  map2. But it is necessary to prove other lemmas*)
Lemma map2_fix_base: forall (elt'' : Type)(m: Map key (option elt'')) m' (x: key) y,
  WF m ->
  WF m' ->
  sem m x = None  ->
  sem m' x = (Some y) <->
  sem (map2_fix _ m m') x = Some y.
Proof.
  intros. generalize dependent m'. induction H; intros; split; intros.
  - simpl. assumption.
  - simpl in H. assumption.
  - simpl. simpl in H1. destruct (sem s1 x) eqn : ?. inversion H1. destruct (x == x0) eqn : ?.
    inversion H1. destruct (sem s2 x) eqn : ?. inversion H1. destruct v.
    + eapply insert_Desc. apply map2_fix_pres_wf. wf_bounds. assumption. reflexivity.
      reflexivity. intros. specialize (H10 x). rewrite Heqb in H10. simpl in H10.
      rewrite <- IHBounded1. rewrite H10. rewrite <- IHBounded2. assumption.
      reflexivity. assumption. reflexivity. assumption.
    + rewrite  <- IHBounded1. rewrite <- IHBounded2. assumption. reflexivity. assumption.
      reflexivity. apply map2_fix_pres_wf. wf_bounds. assumption.
  - simpl in H1. destruct (sem s1 x) eqn : ?. inversion H1. destruct (x == x0) eqn : ?.
    inversion H1. destruct (sem s2 x) eqn : ?. inversion H1.
    simpl in H7. destruct v. rewrite <- IHBounded1 in H7.
    erewrite sem_insert in H7. rewrite Heqb in H7. simpl in H7. apply IHBounded2.
    reflexivity. assumption. assumption. apply map2_fix_pres_wf. wf_bounds. assumption.
    reflexivity. reflexivity. reflexivity. apply insert_WF. apply map2_fix_pres_wf.
    wf_bounds. assumption. rewrite <- IHBounded1 in H7. apply IHBounded2.
    reflexivity. assumption. assumption. reflexivity. apply map2_fix_pres_wf.
    wf_bounds. assumption.
Qed.

(*The main helper lemma: If a key is not in the base map but it maps to (Some (Some y)) in the map
  we are folding over, then it maps to (Some y) in the result*)
Lemma map2_fix_some: forall (elt'' : Type)(m: Map key (option elt'')) m' (x: key) y,
  WF m ->
  WF m' ->
  sem m' x = None ->
  sem m x = Some (Some y) <-> sem (map2_fix _ m m') x = Some y.
Proof.
  intros. revert y. generalize dependent m'. induction H; split; intros.
  - inversion H.
  - inversion H. rewrite H3 in H1. inversion H1.
  - simpl in H7. simpl. destruct (sem s1 x) eqn : ?.
    + simpl in H7. rewrite <- IHBounded1. apply H7. destruct v. apply insert_WF.
      apply map2_fix_pres_wf. wf_bounds. apply H5. eapply map2_fix_pres_wf. wf_bounds. apply H5.
      assert (x < x0 = true). { eapply (sem_inside H) in Heqo. destruct Heqo. unfold isUB in *.
      assumption. } assert (sem s2 x = None). { eapply sem_outside_below. apply H0. unfold isLB.
      order key. } destruct v.
      * erewrite sem_insert. assert (x == x0 = false) by (order key). rewrite H10. simpl.
        apply map2_fix_none. wf_bounds. assumption. assumption. assumption. apply map2_fix_pres_wf.
        wf_bounds. assumption. reflexivity. reflexivity.
      * apply map2_fix_none. wf_bounds. assumption. assumption. assumption.
    + simpl in H7. destruct (x == x0) eqn : ?.
      * inversion H7. eapply insert_Desc. apply map2_fix_pres_wf. wf_bounds. assumption.
        reflexivity. reflexivity. intros. specialize (H11 x). simpl in H7. inversion H7.
        rewrite Heqb in H11. simpl in H11. eapply map2_fix_base in H11. apply H11.
        wf_bounds. assumption. assumption.
      * simpl in H7. destruct v.
        -- eapply insert_Desc. apply map2_fix_pres_wf. wf_bounds. assumption. reflexivity.
          reflexivity. intros. specialize (H10 x). rewrite Heqb in H10. simpl in H10.
          apply map2_fix_base. wf_bounds. assumption. assumption. rewrite H10. apply IHBounded2.
          assumption. assumption. assumption.
        -- apply map2_fix_base. wf_bounds. apply map2_fix_pres_wf. wf_bounds. assumption.
          assumption. apply IHBounded2. assumption. assumption. assumption.
  - simpl in H7. simpl. destruct v.
    + destruct (sem (insert x0 e (map2_fix elt'' s2 m')) x) eqn : ?.
      * setoid_rewrite sem_insert in Heqo. destruct (x == x0) eqn : ?.
        -- simpl. assert (sem s1 x = None). eapply sem_outside_above. eassumption.
            unfold isUB. order key. rewrite H8. simpl. simpl in Heqo.
            apply map2_fix_base in H7. erewrite sem_insert in H7.
            rewrite Heqb in H7. inversion H7. reflexivity.
            apply map2_fix_pres_wf. wf_bounds. assumption. reflexivity.
            reflexivity. wf_bounds. apply insert_WF. apply map2_fix_pres_wf.
            wf_bounds. assumption. assumption.
          -- simpl. simpl in Heqo. rewrite oro_None_r. apply map2_fix_base in H7.
            erewrite sem_insert in H7. rewrite Heqb in H7. simpl in H7. rewrite Heqo in H7.
            inversion H7. rewrite H9 in Heqo. rewrite <- IHBounded2 in Heqo.
            rewrite Heqo. assert (sem s1 x = None). eapply sem_outside_above.
            eassumption. unfold isUB. apply (sem_inside H0) in Heqo.
            destruct Heqo. unfold isLB in H8. order key. rewrite H8. reflexivity.
            assumption. assumption. apply map2_fix_pres_wf. wf_bounds. assumption.
            reflexivity. reflexivity. wf_bounds. apply insert_WF.
            apply map2_fix_pres_wf. wf_bounds. assumption. rewrite <- IHBounded2 in Heqo.
            eapply sem_outside_above. eassumption. unfold isUB. apply (sem_inside H0) in Heqo.
            destruct Heqo. unfold isLB in H9. order key. assumption. assumption.
          -- apply map2_fix_pres_wf. wf_bounds. assumption.
          -- reflexivity.
          -- reflexivity.
      * rewrite <- IHBounded1 in H7. rewrite H7. reflexivity. apply insert_WF.
        apply map2_fix_pres_wf. wf_bounds. assumption. assumption.
   + destruct (sem (map2_fix elt'' s2 m') x) eqn : ?.
     * rewrite <- map2_fix_base in H7. rewrite <- IHBounded2 in H7.
       rewrite H7. assert (x > x0 = true). apply (sem_inside H0) in H7.
       destruct H7. unfold isLB in H7. order key. assert (sem s1 x = None).
       eapply sem_outside_above. eassumption. unfold isUB. order key. rewrite H9.
       assert (x == x0 = false) by (order key). rewrite H10. simpl. reflexivity.
       assumption. assumption. wf_bounds. apply map2_fix_pres_wf. wf_bounds.
       assumption. rewrite <- IHBounded2 in Heqo. eapply sem_outside_above.
       eassumption. unfold isUB. apply (sem_inside H0) in Heqo. destruct Heqo.
        unfold isLB in H8. order key. assumption. assumption.
     * rewrite <- IHBounded1 in H7. rewrite H7. reflexivity. apply map2_fix_pres_wf.
      wf_bounds. assumption. assumption.
Qed.

(*Finally, if the key is not in the base but it maps to Some None in the source map, then it
  does not appear in the output*)
Lemma map2_fix_some_none: forall (elt'' : Type)(m: Map key (option elt'')) m' (x: key),
  WF m ->
  WF m' ->
  sem m' x = None ->
  sem m x = Some None -> sem (map2_fix _ m m') x = None.
Proof.
  intros. generalize dependent m'. induction H; intros.
  - simpl. assumption.
  - simpl in H2. simpl. destruct (sem s1 x) eqn : ?.
    + assert (x < x0 = true). { apply (sem_inside H) in Heqo. destruct Heqo.
      unfold isUB in H9. assumption. }
      inversion H2. rewrite IHBounded1. subst. reflexivity. subst. reflexivity.
      destruct v.  apply insert_WF. apply map2_fix_pres_wf. wf_bounds. assumption.
      apply map2_fix_pres_wf. wf_bounds. assumption. destruct v.
       erewrite sem_insert.
      assert (x == x0 = false) by (order key). rewrite H9. simpl.
      apply map2_fix_none. wf_bounds. assumption. assumption.
      eapply sem_outside_below. eassumption. unfold isLB. order key.
      apply map2_fix_pres_wf. wf_bounds. assumption. reflexivity. reflexivity.
      apply map2_fix_none. wf_bounds. assumption. assumption.
      eapply sem_outside_below. eassumption. unfold isLB. order key.
    + simpl in H2. destruct (x == x0) eqn : ?.
      * simpl in H2. inversion H2. apply map2_fix_none. wf_bounds. apply map2_fix_pres_wf.
        wf_bounds. assumption. apply map2_fix_none. wf_bounds. assumption. assumption.
        eapply sem_outside_below. eassumption. unfold isLB. order key.
        eapply sem_outside_above. eassumption. unfold isUB. order key.
      * simpl in H2. assert (x > x0 = true). { apply (sem_inside H0) in H2. destruct H2.
        unfold isLB in H2. order key. } apply map2_fix_none. wf_bounds.
        destruct v. apply insert_WF. apply map2_fix_pres_wf. wf_bounds. assumption.
        apply map2_fix_pres_wf. wf_bounds. assumption. destruct v.
        erewrite sem_insert. rewrite Heqb. simpl. apply IHBounded2. assumption.
        assumption. assumption. apply map2_fix_pres_wf. wf_bounds. assumption.
        reflexivity. reflexivity. apply IHBounded2. assumption. assumption.
        assumption. assumption.
Qed.

(*Finally, we can prove the properties we want.*)

Lemma map2_1: forall (elt elt' elt'' : Type) (m : t elt) (m': t elt') (x: key)
  (f: option elt -> option elt' -> option elt''),
  In _ x m \/ In _ x m' -> find _ x (map2 _ _ _ f m m') = f (find _ x m) (find _ x m').
Proof.
  intros. unfold find. unfold In in *. unfold MapsTo in *. destruct m. destruct m'. simpl in *.
  erewrite lookup_spec. erewrite lookup_spec. erewrite lookup_spec.
  - apply (map2_map_in elt0 elt' elt'' _ _ x f) in H. destruct (f (sem x0 x) (sem x1 x)) eqn : ?.
    + assert (exists e, sem (map2_map elt0 elt' elt'' x0 x1 f) x = Some (Some e)). { exists e.
      apply H. } rewrite Heqo. rewrite <- (map2_fix_some elt'' _ Tip x).
      * apply H.
      * apply map2_map_wf; assumption.
      * constructor.
      * reflexivity.
    + rewrite Heqo. apply map2_fix_some_none.
      * apply map2_map_wf; assumption.
      * constructor.
      * reflexivity.
      * assumption.
    + assumption.
    + assumption.
  - apply w0.
  - apply w.
  - apply map2_fix_pres_wf. apply map2_map_wf. assumption. assumption. constructor.
Qed.

Lemma map2_2: forall (elt elt' elt'' : Type) (m: t elt) (m': t elt') (x: key) (f: option elt ->
  option elt' -> option elt''),
  In _ x (map2 _ _ _ f m m') -> In _ x m \/ In _ x m'.
Proof.
  intros. unfold In in *. unfold MapsTo in *. destruct m. destruct m'. simpl in *.
  destruct (sem x0 x) eqn : ?. left. exists e. reflexivity.
  destruct (sem x1 x) eqn : ?. right. exists e. reflexivity. destruct H.
  rewrite <- map2_fix_base in H. inversion H. apply map2_map_wf; assumption.
  constructor. apply map2_map_notin. apply x. apply w. apply w0. split; assumption.
Qed.

Section Elt'.

Variable elt: Type.

Definition lt_key (p p': key * elt) := E.lt (fst p) (fst p').

(*These two definitions of lt can only be proved equivalent by functional extensionality,
so instead we prove that if sorted by 1, it is sorted by the other*)
Lemma lt_lt_key_sort: forall (l: list (key * elt)),
  StronglySorted (lt elt) l ->
  StronglySorted lt_key l.
Proof.
  intros. unfold lt in *. unfold lt_key. induction H; subst.
  - constructor.
  - constructor. apply IHStronglySorted. destruct a. simpl.
    induction H0.
    + constructor.
    + constructor. destruct x. simpl. apply elt_lt in H0. apply H0.
      apply IHForall. inversion H; subst. apply H4. inversion IHStronglySorted; subst.
      apply H4.
Qed.

Lemma elements_3:  forall (m : t elt), sort lt_key (elements _ m).
Proof.
  intros. apply StronglySorted_Sorted. unfold elements. apply lt_lt_key_sort.
  destruct m. simpl. eapply to_List_sorted. apply w.
Qed.
End Elt'.
End MapFMap.
