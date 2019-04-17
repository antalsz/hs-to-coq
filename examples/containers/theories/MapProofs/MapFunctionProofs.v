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
Require Import MapProofs.ContainerAxiomsProofs.
Require Import MapProofs.UnionIntersectDifferenceProofs.
Require Import MapProofs.ToListProofs.
Require Import MapProofs.FilterPartitionProofs.
Require Import MapProofs.FromListProofs.
Require Import Coq.Classes.Morphisms.
(** ** Verification of [mapWithKey] *)

Lemma mapWithKey_Desc: forall {e} {a} {b} `{OrdLaws e} (m: Map e a) (f: e -> a -> b) lb ub,
  Bounded m lb ub ->
  Proper ((fun i j : e => _GHC.Base.==_ i j = true) ==> eq) f ->
  Desc (mapWithKey f m) lb ub (size m) (fun i => match (sem m i) with
                                                 | Some x => Some (f i x)
                                                 | None => None end).
Proof.
  intros. induction H0.
  - simpl. solve_Desc e.
  - simpl. applyDesc e IHBounded1. applyDesc e IHBounded2. solve_Desc e. f_solver e.
    assert (f x v = f i v). apply equal_f. apply H1. order e. rewrite H5. reflexivity.
Qed.

(*The following are several other lemmas about [map] and [mapWithKey] that are useful
for [FMapInterface]*)

(*Specification using Coq equality*)

(*The same keys are in both maps*)
Lemma map_none_spec:
  forall {b} {a} {e} `{Eq_ e} `{Ord e} (f: e -> a -> b) (m: Map e a) lb ub,
  Bounded m lb ub ->
  (forall i, sem m i = None <-> sem (mapWithKey f m) i = None).
Proof.
  intros. generalize dependent i. induction H2; intros; split; intros.
  - reflexivity.
  - reflexivity.
  - simpl. simpl in H6. destruct (sem s1 i) eqn : ?. inversion H6. 
    apply IHBounded1 in Heqo. rewrite Heqo. simpl. simpl in H6.
    destruct (i == x) eqn : ?. inversion H6. simpl. simpl in H6.
    apply IHBounded2. apply H6.
  - simpl in H6. simpl. destruct (sem (mapWithKey f s1) i) eqn : ?. inversion H6.
    apply IHBounded1 in Heqo. rewrite Heqo. simpl. destruct (i == x) eqn : ?. inversion H6.
    simpl. simpl in H6. apply IHBounded2. apply H6.
Qed. 

(*Says that if we take any (key, value) pair in the map resulting from mapWithKey, then they
come from a corresponding entry in the original map*)
Lemma map_spec_reverse : 
  forall {b} {a} {e}  `{Ord e} (H : EqLaws e) (f : e -> a -> b) (m : Map e a) lb ub,
  Bounded m lb ub ->
  Proper ((fun i j : e => _GHC.Base.==_ i j = true) ==> eq) f ->
  (forall i v, sem (mapWithKey f m) i = Some v -> exists value, sem m i = Some value /\ v = f i value).
Proof.
  intros. generalize dependent i. generalize dependent v. induction H2; intros.
  - simpl in H4. inversion H4.
  - simpl in H7. simpl. destruct ( sem (mapWithKey f s1) i ) eqn : ?. apply IHBounded1 in Heqo.
    destruct Heqo. exists x0. destruct H8. rewrite H8. simpl. split. reflexivity. inversion H7; subst.
    reflexivity. simpl in H7.  assert (sem s1 i = None). { erewrite map_none_spec. apply Heqo. apply H2_. }
    rewrite H8. destruct (i == x) eqn : ?. simpl in H7. simpl. exists v. split. reflexivity. inversion H7. 
    apply equal_f. apply H3. order e. simpl. simpl in H7. apply IHBounded2. apply H7.
Qed.

(*If (k,v) is in the original map, then (k, f k v) is in the new map*)
Lemma map_spec_coq:
  forall {b} {a} {e} `{OrdLaws e}(f : e -> a -> b) (m : Map e a) lb ub,
  Bounded m lb ub ->
  Proper ((fun i j : e => _GHC.Base.==_ i j = true) ==> eq) f ->
  (forall i v, sem m i = Some v -> sem (mapWithKey f m) i = Some (f i v)).
Proof.
  intros. applyDesc e (@mapWithKey_Desc e a). specialize (Hsem i). rewrite H2 in Hsem. assumption.
Qed. 

(*If f is injective, then (k,v) is in the original map iff (k, f k v) is in the new map*)
Lemma map_spec_coq_injective:
  forall {b} {a} {e} `{OrdLaws e}(f : e -> a -> b) (m : Map e a) lb ub,
  Bounded m lb ub ->
  Proper ((fun i j : e => _GHC.Base.==_ i j = true) ==> eq) f ->
  (forall k k2 v v2, f k v = f k2 v2 -> k == k2 = true /\ v = v2) ->
  (forall i v, sem m i = Some v <-> sem (mapWithKey f m) i = Some (f i v)).
Proof.
  intros. applyDesc e (@mapWithKey_Desc e a). specialize (Hsem i). rewrite Hsem.
  destruct (sem m i); split; intros; inversion H3; try (assumption); try (reflexivity).
  apply H2 in H5. destruct H5; subst; reflexivity.
Qed.

(** Verification of [map] *)
Lemma map_Desc: forall {e} {a} {b} `{OrdLaws e} (m: Map e a) (f: a -> b) lb ub,
  Bounded m lb ub ->
  Desc (map f m) lb ub (size m) (fun i => match (sem m i) with
                                                 | Some x => Some (f x)
                                                 | None => None end).
Proof.
  intros. induction H0.
  - simpl. solve_Desc e.
  - simpl. applyDesc e IHBounded1. applyDesc e IHBounded2. solve_Desc e.
Qed. 

Lemma map_mapWithKey_equiv:  forall {e} {a} {b} `{Ord e} (f : a -> b) (m : Map e a),
  Internal.map f m = mapWithKey (fun k v => f v) m.
Proof.
  intros. induction m.
  - simpl. rewrite IHm1. rewrite IHm2. reflexivity.
  - simpl. reflexivity.
Qed.

(** Vertification of [mapAccumL] *)

(*This turns out to be highly nontrivial to specify and verify. At each step, the new value is calculated
based on a function that uses the old key and the accumulated value through all of the previous keys. 
We can specify the value by stating that it is euivalent to folding the function over the map,
but the resulting map is much harder to specify, and the proof is quite complex*)


Lemma mapAccumL_fst: forall {e} {a} {b : Type} {c : Type} `{OrdLaws e} (m: Map e a) (x : b) 
  (f: b -> e -> a -> (b * c)) lb ub,
   Bounded m lb ub ->
  fst(mapAccumL f x m) = foldlWithKey (fun (t: b) k v => fst (f t k v)) x m.
Proof.
  intros. revert x. induction H0; intros.
  - simpl. reflexivity.
  - simpl. rewrite (surjective_pairing (mapAccumL f x0 s1 )).
    rewrite (surjective_pairing (mapAccumL f x0 s1)). simpl.
    rewrite IHBounded1. 
    rewrite (surjective_pairing (f (foldlWithKey (fun (t : b) (k : e) (v0 : a) => fst (f t k v0)) x0 s1) x v )).
    simpl. 
    rewrite (surjective_pairing (mapAccumL f (fst (f (foldlWithKey (fun (t : b) (k : e) (v0 : a) => 
    fst (f t k v0)) x0 s1) x v)) s2 )). simpl. rewrite IHBounded2. reflexivity.
Qed.

(*In order to specify the resulting map, we need a way to describe the accumulated value. We do this
by claiming that the accumulated value is equivalent to folding the function over every element in the
map less than the current key. To specify this, we define map_lt, which consists of all elements
in the map less than the current key. We then prove a Desc about it*)
Definition map_lt {e} `{Ord e} {a} (m: Map e a) k :=
  fst(partitionWithKey (fun x _ => x < k) m).

Lemma map_lt_Desc: forall {e a} `{OrdLaws e}  (m: Map e a) k lb ub,
  Bounded m lb ub ->
  Desc' (map_lt m k) lb ub (fun i => if i < k then sem m i else None).
Proof.
  intros. unfold map_lt. induction H0.
  - simpl. solve_Desc e. f_solver e.
  - eapply (@partitionWithKey_spec e a). assumption. constructor. apply H0_. apply H0_0.
    assumption. assumption. assumption. assumption. unfold respectful. unfold Proper.
    intros. assert ( _GHC.Base.<_ x0 k =  _GHC.Base.<_ y k ) by (order e). 
    rewrite H5. reflexivity. intros. simpl. applyDesc e H4. solve_Desc e. f_solver e.
    destruct (sem s1 i); simpl in Hsem. inversion Hsem. destruct (i == x); simpl in Hsem.
    inversion Hsem. destruct (sem s2 i); inversion Hsem.
Qed.  

(*The key issue in the resulting proof is that we have something like
[forall i, sem s4 i = sem s1 i ||| SomeIf (i == x) v ||| sem s3 i]
and we want to prove that folding over s1, then x, then s3 is the same as folding over s4.
This turns out to be very complicated, and is slightly easier to reason about if we use lists
instead. The next several lemmas allow us to do this.*) 

(*TODO: Move this to toListProofs. The one in toListProofs is not sufficiently general*)
Lemma foldlWithKey_spec' :
   forall (e a b : Type) (f : b -> e -> a -> b) (n : b) (m : Map e a),
   foldlWithKey f n m = fold_left (fun t (x: e * a) => let (a0, b) := x in f t a0 b) (toList m) n.
Proof.
  intros. generalize dependent n. induction m; intros.
  - simpl. rewrite toList_Bin. rewrite IHm1. rewrite IHm2.
    rewrite fold_left_app. simpl. reflexivity.
  - reflexivity.
Qed.


(*I don't think the {EqLaws a} assumption is strictly necessary, but it is difficult to remove, 
since the proofs rely on theorems about toList and equality that would have to be re-proved
without reference to EqLaws*)
Lemma fold_left_proper: 
  forall {e} {a} {b} `{OrdLaws e} `{EqLaws a} (f: b -> e * a -> b) x (l1 l2: list (e * a)),
  eqlist l1 l2 = true ->
  (forall p1 p2 y, p1 == p2 = true -> f y p1 = f y p2) ->
  (fold_left f l1 x) = (fold_left f l2 x).
Proof.
  intros. revert x. generalize dependent l2. induction l1; intros; destruct l2.
  - reflexivity.
  - inversion H2.
  - inversion H2.
  - simpl. simpl in H2. 
    assert (f x a0 = f x p). apply H3. order e. rewrite H4. apply IHl1. 
    rewrite andb_true_iff in H2. destruct H2. assumption.
Qed.

(*The result we really need about fold: If we have maps that are equivalent sem-wise,
then folding over them gives the same result (assuming the function is Proper)*)
Lemma foldlWithKey_equiv_maps:
  forall {e} {a} {b} `{OrdLaws e} `{EqLaws a} (f: b -> e -> a -> b) x (m1: Map e a) m2, 
  WF m1 ->
  WF m2 ->
  (forall e1 e2 a1 a2 y, a1 == a2 = true -> e1 == e2 = true -> f y e1 a1 = f y e2 a2) ->
  (forall i, sem m1 i = sem m2 i) ->
  (foldlWithKey f x m1) = (foldlWithKey f x m2).
Proof.
  intros. rewrite foldlWithKey_spec'. rewrite foldlWithKey_spec'.
  assert (eqlist (toList m1) (toList m2) = true). { 
  assert ((toList m1) == (toList m2) = true).
  assert (m1 == m2 = true) by (eapply strong_eq1; eassumption).
  unfold "==" in H6. unfold Eq___Map in H6. unfold op_zeze____ in H6.
  unfold Internal.Eq___Map_op_zeze__ in H6. unfold toList. rewrite andb_true_iff in H6.
  destruct H6. assumption. unfold "==" in H6. unfold Eq_list in H6. unfold op_zeze____ in H6.
  apply H6. } apply fold_left_proper. apply H6. intros.
  destruct p1. destruct p2. unfold "==" in H7. unfold Eq_pair___  in H7. 
  unfold op_zeze____  in H7. unfold eq_pair in H7. rewrite andb_true_iff in H7. apply H4.
  order a. order e.
Qed. 


Require Import Coq.Sorting.Sorted.

(*A few lemmas about the Boundedness of lists*)
(*TODO:Move to toListProofs*)
Lemma toList_Bounds_UB: forall {e} {a} `{OrdLaws e} (m: Map e a) lb ub, 
  Bounded m lb ub -> 
  forall k v, In (k,v) (toList m) ->
  isUB ub k = true.
Proof.
  intros. induction H0. inversion H1. rewrite toList_Bin in H1.
  apply in_app_or in H1. destruct H1. apply IHBounded1 in H1. solve_Bounds e. simpl in H1.
  destruct H1. solve_Bounds e. apply IHBounded2. assumption.
Qed. 

Lemma toList_Bounds_LB: forall {e} {a} `{OrdLaws e} (m: Map e a) lb ub, 
  Bounded m lb ub -> 
  forall k v, In (k,v) (toList m) ->
  isLB lb k = true.
Proof.
  intros. induction H0. inversion H1. rewrite toList_Bin in H1.
  apply in_app_or in H1. destruct H1. apply IHBounded1. assumption.  simpl in H1.
  destruct H1. solve_Bounds e. apply IHBounded2 in H1. solve_Bounds e.
Qed.

Lemma eq_list_equiv: forall {a} `{EqLaws a} (l1 l2 : list a),
  l1 == l2 = eqlist l1 l2.
Proof.
  intros. unfold "==". unfold Eq_list. unfold op_zeze____. reflexivity.
Qed.

Set Bullet Behavior "Strict Subproofs".
(*TODO: Also somewhere else*)
(*If a list is sorted, sem_for_lists gives Some x on i iff (i,x) is in the list (the converse is
not true unless the list has unique elements)*)
Lemma sem_to_lists_elem: forall {e} {a} `{OrdLaws e} `{EqLaws a} (l: list (e * a)) i x,
  StronglySorted ToListProofs.lt l ->
 (sem_for_lists l i == Some x) = true <-> List.elem (i, x) l = true.
Proof. 
  intros. revert H2. revert i x. induction l; intros.
    - simpl. split; intros contra; inversion contra. 
    - simpl. destruct a0. split; intros.
      + destruct (i == e0) eqn : ?. 
      rewrite orb_true_iff. left. unfold "==". unfold Eq_pair___. unfold op_zeze____.
      unfold eq_pair. rewrite andb_true_iff. split. assumption. apply Eq_Symmetric.
      rewrite simpl_option_some_eq in H3. apply H3.
      rewrite orb_true_iff. right. erewrite <- IHl. assumption. inversion H2; assumption.
      + rewrite orb_true_iff in H3. destruct H3.
        * unfold "==" in H3. unfold Eq_pair___ in H3. unfold op_zeze____ in H3.
          unfold eq_pair in H3. rewrite andb_true_iff in H3. destruct H3. rewrite H3.
          rewrite simpl_option_some_eq. order a.
        * inversion H2; subst. rewrite Forall_lt in H7. specialize (H7 i x). assert (A:=H3).
          apply H7 in H3. unfold ToListProofs.lt in H3. assert (i == e0 = false) by (order e).
          rewrite H4. rewrite  IHl. apply A. apply H6.
Qed. 

Lemma fromDistinctAscList_toList: forall {e} {a} `{OrdLaws e} `{EqLaws a} (l: list (e * a)), 
  StronglySorted ToListProofs.lt l -> 
  toList(fromDistinctAscList l) == l = true.
Proof.
  intros. apply strongly_sorted_unique.
  - eapply to_List_sorted. eapply fromDistinctAscList_Desc. apply H2. intros. apply H3.
  - apply H2.
  - intros. eapply fromDistinctAscList_Desc. apply H2. intros.
    split; intros.
    + rewrite <- toList_sem' in H6. destruct (sem s x) eqn : ?.
      * apply sem_to_lists_elem. apply H2. rewrite H5 in Heqo. rewrite Heqo. assumption.
      * inversion H6.
      * apply H3.
    + rewrite <- sem_to_lists_elem in H6. destruct (sem_for_lists l x) eqn : ?. specialize (H5 x).
      rewrite <- toList_sem'. rewrite H5. rewrite Heqo. assumption. apply H3. inversion H6. apply H2.
Qed.

Ltac unfold_pair := unfold "==" ; unfold Eq_pair___ ; unfold op_zeze____ ; unfold eq_pair. 


(*Finally, the actual specification, which says that any element is found by computing f on the
accumulated value (value resulting from folding f over all elements less than f) and the key itself.
Again, I'm not sure if the {EqLaws a} assumption is strictly needed*)
Lemma mapAccumL_snd_Desc: forall {e} {a} {b : Type} {c : Type} `{OrdLaws e} `{EqLaws a} (m: Map e a) (x : b) 
  (f: b -> e -> a -> (b * c)) lb ub,
  Proper ((fun (i j : e * a) => _GHC.Base.==_ i j = true) ==> eq) (fun x y => let (a,b) := x in f y a b) ->
  Bounded m lb ub ->
  Desc (snd (mapAccumL f x m)) lb ub (size m) (
  fun i => match (sem m i) with
           | Some y => Some (snd(f (fst (mapAccumL f x (map_lt m i))) i y))
           | None => None
            end).
Proof.
  intros. revert x. induction H3; intros.
  - simpl. solve_Desc e.
  - simpl.  rewrite (surjective_pairing (mapAccumL f x0 s1 )).
    rewrite (surjective_pairing (f (fst (mapAccumL f x0 s1)) x v)).
    rewrite (surjective_pairing ( mapAccumL f (fst (f (fst (mapAccumL f x0 s1)) x v)) s2)).
    simpl. applyDesc e IHBounded1. applyDesc e IHBounded2. solve_Desc e. f_solver e.
    + repeat(applyDesc e (@map_lt_Desc e a)). repeat (erewrite mapAccumL_fst).
      * assert (forall i, sem s4 i = sem s3 i). {
         intros. destruct (_GHC.Base.<_ i0 i) eqn : ?.
          - specialize (Hsem1 i0). rewrite Heqb0 in Hsem1. simpl in Hsem1.
            assert (i0 == x = false) by (solve_Bounds e). assert (sem s2 i0 = None). eapply sem_outside_below.
            eassumption. solve_Bounds e. rewrite H7 in Hsem1. rewrite H5 in Hsem1. simpl in Hsem1. 
            repeat (rewrite oro_None_r in Hsem1). rewrite Hsem1. rewrite Hsem.
            rewrite Heqb0. reflexivity.
          - specialize (Hsem1 i0). specialize (Hsem i0). rewrite Hsem. rewrite Hsem1. rewrite Heqb0. 
            reflexivity. }
        assert ((foldlWithKey (fun (t : b) (k : e) (v0 : a) => fst (f t k v0)) x0 s3) =
           (foldlWithKey (fun (t : b) (k : e) (v0 : a) => fst (f t k v0)) x0 s4)). {
            eapply foldlWithKey_equiv_maps. wf_bounds. wf_bounds. intros.
            assert (f y e1 a1 = f y e2 a2). { unfold respectful in H2. unfold Proper in H2.
            remember (e1, a1). remember (e2, a2). assert (p == p0 = true). unfold_pair.
            subst. rewrite andb_true_iff. split; assumption. apply H2 in H9. subst.
            eapply equal_f in H9. apply H9. } rewrite H9. reflexivity.
            intros. rewrite H5. reflexivity. }
        rewrite H7. reflexivity.
      * eassumption.
      * eassumption.
    + applyDesc e (@map_lt_Desc e a). repeat (erewrite mapAccumL_fst).
      * assert (forall i, sem s1 i = sem s3 i). {
        intros. destruct (_GHC.Base.<_ i0 i) eqn : ?.
        - specialize (Hsem i0). rewrite Heqb1 in Hsem. simpl in Hsem.
          assert (i0 == x = false) by (solve_Bounds e). assert (sem s2 i0 = None). eapply sem_outside_below.
          eassumption. solve_Bounds e. rewrite H8 in Hsem. rewrite H7 in Hsem. simpl in Hsem. 
          repeat (rewrite oro_None_r in Hsem). rewrite Hsem. reflexivity.
        - specialize (Hsem i0). rewrite Hsem.  rewrite Heqb1. eapply sem_outside_above. eassumption.
          solve_Bounds e. }  
        assert ((foldlWithKey (fun (t : b) (k : e) (v0 : a) => fst (f t k v0)) x0 s1) =
           (foldlWithKey (fun (t : b) (k : e) (v0 : a) => fst (f t k v0)) x0 s3)). {
          eapply foldlWithKey_equiv_maps. wf_bounds. wf_bounds. intros.
          assert (f y e1 a1 = f y e2 a2). { unfold respectful in H2. unfold Proper in H2.
          remember (e1, a1). remember (e2, a2). assert (p == p0 = true). unfold_pair.
          subst. rewrite andb_true_iff. split; assumption. apply H2 in H10. subst.
          eapply equal_f in H10. apply H10. } rewrite H10. reflexivity. 
          intros. rewrite H7. reflexivity. }
      rewrite H8. assert (forall z, f z x v = f z i v). { intros. unfold respectful in H2.
        unfold Proper in H2. remember (x, v). remember (i,v).
        assert (p == p0 = true). unfold_pair. subst. rewrite andb_true_iff. split. order e. order a.
        apply H2 in H9. subst. eapply equal_f in H9. apply H9. }
      rewrite H9. reflexivity.
     * eassumption.
     * eassumption.
    + (*This case is the complicated one that involves all sorts of results about fold, toList, and 
        fromDistinctAscList*)
    remember ((1 + size s1 + size s2)%Z) as sz. repeat (applyDesc e (@map_lt_Desc e a)).
    repeat (erewrite mapAccumL_fst). repeat (rewrite foldlWithKey_spec').
    assert
        ((fold_left (fun (t : b) (x1 : e * a) => let (a1, b0) := x1 in fst (f t a1 b0)) 
           (toList s3)
           (fst
              (f (fold_left (fun (t : b) (x1 : e * a) => let (a1, b0) := x1 in fst (f t a1 b0)) (toList s1) x0) x
                 v))) = fold_left (fun (t : b) (x1 : e * a) => let (a1, b0) := x1 in fst (f t a1 b0)) 
                  ((toList s1) ++ ((x, v) :: nil) ++ (toList s3)) x0). { simpl.
    rewrite fold_left_app. simpl. reflexivity. }
    rewrite H5. clear H5. 
    assert ((fold_left (fun (t : b) (x1 : e * a) => let (a1, b0) := x1 in fst (f t a1 b0))
           (toList s1 ++ ((x, v) :: nil) ++ toList s3) x0) = 
    (fold_left (fun (t : b) (x1 : e * a) => let (a1, b0) := x1 in fst (f t a1 b0)) (toList s4) x0) ). {
      assert (StronglySorted ToListProofs.lt (toList s1 ++ ((x, v) :: nil) ++ toList s3)). {
        eapply sorted_append.
        + eapply to_List_sorted. eassumption.
        + simpl. apply SSorted_cons.
          * eapply to_List_sorted. eassumption.
          * rewrite Forall_lt. intros. unfold ToListProofs.lt. rewrite <- toList_sem' in H5.
            destruct (sem s3 x1) eqn : ?.
            - solve_Bounds e.
            - inversion H5.
            - eassumption.
       + intros. assert (isUB (Some x) y = true). eapply toList_Bounds_UB. apply H3_. apply H5. solve_Bounds e.
       + intros. simpl in H5. destruct H5.
          * inversion H5; subst. order e.
          * assert (isLB (Some x) y = true). eapply toList_Bounds_LB. apply HB1. apply H5. solve_Bounds e. }
      eapply fold_left_proper.
      - simpl. remember (fromDistinctAscList ((toList s1 ++ ((x, v) :: nil) ++ toList s3))) as m.
        assert (toList m ==  (toList s1 ++ ((x, v) :: nil) ++ toList s3) = true). { rewrite Heqm.
        eapply fromDistinctAscList_toList. apply H5. }
        rewrite <- eq_list_equiv. eapply Eq_Transitive. apply Eq_Symmetric. apply H7.
        unfold is_true. rewrite <-eq_toList. eapply strong_eq1.
        + subst. eapply fromDistinctAscList_Desc. apply H5. intros. apply H8.
        + wf_bounds.
        + intros. rewrite Hsem0. rewrite Heqm. eapply fromDistinctAscList_Desc. apply H5. intros.
          rewrite H10. simpl. rewrite sem_list_app.
          destruct (i0 < i) eqn : ?.
          * erewrite <- toList_sem''. simpl. unfold SomeIf.  erewrite <- toList_sem''.
            rewrite Hsem. rewrite Heqb1. 
            destruct (sem s1 i0).
            -- reflexivity.
            -- destruct (i0 == x); reflexivity.
            -- eassumption.
            -- eassumption.
          * erewrite <- toList_sem''. destruct (sem s1 i0) eqn : ?.
            -- solve_Bounds e.
            -- simpl. destruct (i0 == x) eqn : ?.
               ++ solve_Bounds e.
               ++ erewrite <- toList_sem''. rewrite Hsem. rewrite Heqb1. reflexivity.
                  eassumption.
            -- eassumption.
        + rewrite Heqm. apply fromDistinctAscList_Desc. apply H5. intros. apply H8.
        + wf_bounds.
      - intros. apply H2 in H7. destruct p1. destruct p2.
        eapply equal_f in H7. rewrite H7. reflexivity. }
    rewrite H5. reflexivity. apply HB2. apply H3_. apply HB1.
Qed. 

(** Verification of [mapAccumWithKey] *)

(*This is much simpler*)
Lemma mapAccumWithKey_mapAccumL: forall {e} {a} {b : Type} {c : Type} `{OrdLaws e} (m: Map e a) (x : b) 
  (f: b -> e -> a -> (b * c)),
  mapAccumWithKey f x m = mapAccumL f x m.
Proof.
  intros. unfold mapAccumWithKey. reflexivity.
Qed.

Lemma mapAccumWithKey_fst: forall {e} {a} {b : Type} {c : Type} `{OrdLaws e} (m: Map e a) (x : b) 
  (f: b -> e -> a -> (b * c)) lb ub,
   Bounded m lb ub ->
  fst(mapAccumWithKey f x m) = foldlWithKey (fun (t: b) k v => fst (f t k v)) x m.
Proof.
  intros. rewrite mapAccumWithKey_mapAccumL. eapply mapAccumL_fst. apply H0.
Qed.

Lemma mapAccumWithKey_snd_Desc: forall {e} {a} {b : Type} {c : Type} `{OrdLaws e} `{EqLaws a} (m: Map e a) (x : b) 
  (f: b -> e -> a -> (b * c)) lb ub,
  Proper ((fun (i j : e * a) => _GHC.Base.==_ i j = true) ==> eq) (fun x y => let (a,b) := x in f y a b) ->
  Bounded m lb ub ->
  Desc (snd (mapAccumWithKey f x m)) lb ub (size m) (
  fun i => match (sem m i) with
           | Some y => Some (snd(f (fst (mapAccumWithKey f x (map_lt m i))) i y))
           | None => None
            end).
Proof.
  intros. repeat(setoid_rewrite mapAccumWithKey_mapAccumL). eapply (@mapAccumL_snd_Desc e a); assumption.
Qed.

(** Verification of [mapAccum] *)
Lemma mapAccum_mapAccumWithKey: forall {e} {a} {b : Type} {c : Type} `{OrdLaws e} (m: Map e a) (x : b) 
  (f: b ->  a -> (b * c)),
  mapAccum f x m = mapAccumWithKey (fun a b c => f a c) x m.
Proof.
  intros. unfold mapAccum. reflexivity.
Qed.

Lemma mapAccum_fst: forall {e} {a} {b : Type} {c : Type} `{OrdLaws e} (m: Map e a) (x : b) 
  (f: b -> a -> (b * c)) lb ub,
   Bounded m lb ub ->
  fst(mapAccum f x m) = foldlWithKey (fun (t: b) k v => fst (f t v)) x m.
Proof.
  intros. rewrite mapAccum_mapAccumWithKey. eapply mapAccumWithKey_fst. apply H0.
Qed.

Lemma mapAccum_snd_Desc: forall {e} {a} {b : Type} {c : Type} `{OrdLaws e} `{EqLaws a} (m: Map e a) (x : b) 
  (f: b -> a -> (b * c)) lb ub,
  Proper ((fun (i j : a) => _GHC.Base.==_ i j = true) ==> eq) (fun x y =>  f y x) ->
  Bounded m lb ub ->
  Desc (snd (mapAccum f x m)) lb ub (size m) (
  fun i => match (sem m i) with
           | Some y => Some (snd(f (fst (mapAccum f x (map_lt m i))) y))
           | None => None
            end).
Proof.
  intros. repeat(setoid_rewrite mapAccum_mapAccumWithKey). eapply (@mapAccumWithKey_snd_Desc e a).
  all: try (assumption). unfold respectful. unfold Proper. unfold_pair. intros. destruct x0. destruct y.
  apply H2. order a. 
Qed.

(** Verification of [mapAccumRWithKey] *)
(*This is the reverse of [mapAccumL] (fold right instead of left)*)
Lemma mapAccumRWithKey_fst: forall {e} {a} {b : Type} {c : Type} `{OrdLaws e} (m: Map e a) (x : b) 
  (f: b -> e -> a -> (b * c)) lb ub,
   Bounded m lb ub ->
  fst(mapAccumRWithKey f x m) = foldrWithKey (fun k v t => fst (f t k v)) x m.
Proof.
  intros. revert x. induction H0; intros.
  - simpl. reflexivity.
  - simpl. rewrite (surjective_pairing (mapAccumRWithKey f x0 s2 )).
    rewrite (surjective_pairing (mapAccumRWithKey f x0 s2)). simpl.
    rewrite IHBounded2. 
    rewrite (surjective_pairing (f (foldrWithKey (fun (k : e) (v0 : a) (t: b) => fst (f t k v0)) x0 s2) x v )).
    simpl. 
    rewrite (surjective_pairing (mapAccumRWithKey f (fst (f (foldrWithKey (fun (k : e) (v0 : a)  (t : b) => 
    fst (f t k v0)) x0 s2) x v)) s1 )). simpl. rewrite IHBounded1. reflexivity.
Qed.

Definition map_gt {e} `{Ord e} {a} (m: Map e a) k :=
  fst(partitionWithKey (fun x _ => x > k) m).

Lemma map_gt_Desc: forall {e a} `{OrdLaws e}  (m: Map e a) k lb ub,
  Bounded m lb ub ->
  Desc' (map_gt m k) lb ub (fun i => if i > k then sem m i else None).
Proof.
  intros. unfold map_gt. induction H0.
  - simpl. solve_Desc e. f_solver e.
  - eapply (@partitionWithKey_spec e a). assumption. constructor. apply H0_. apply H0_0.
    assumption. assumption. assumption. assumption. unfold respectful. unfold Proper.
    intros. assert ( _GHC.Base.>_ x0 k =  _GHC.Base.>_ y k ) by (order e). 
    rewrite H5. reflexivity. intros. simpl. applyDesc e H4. solve_Desc e. f_solver e.
    destruct (sem s1 i); simpl in Hsem. inversion Hsem. destruct (i == x); simpl in Hsem.
    inversion Hsem. destruct (sem s2 i); inversion Hsem.
Qed.  

(*TODO: Move this to toListProofs. The one in toListProofs is not sufficiently general*)
Lemma foldrWithKey_spec' :
   forall (e a b : Type) (f :  e -> a -> b -> b) (n : b) (m : Map e a),
   foldrWithKey f n m = fold_right (fun (x: e * a) t => let (a0, b) := x in f a0 b t) n (toList m).
Proof.
  intros. generalize dependent n. induction m; intros.
  - simpl. rewrite toList_Bin. rewrite IHm1. rewrite IHm2.
    rewrite fold_right_app. simpl. reflexivity.
  - reflexivity.
Qed.


Lemma fold_right_proper: 
  forall {e} {a} {b} `{OrdLaws e} `{EqLaws a} (f: e * a -> b -> b) x (l1 l2: list (e * a)),
  eqlist l1 l2 = true ->
  (forall p1 p2 y, p1 == p2 = true -> f p1 y = f p2 y) ->
  (fold_right f x l1) = (fold_right f x l2).
Proof.
  intros. revert x. generalize dependent l2. induction l1; intros; destruct l2.
  - reflexivity.
  - inversion H2.
  - inversion H2.
  - simpl. simpl in H2. specialize (IHl1 l2). rewrite andb_true_iff in H2.
    destruct H2. rewrite IHl1. apply H3. assumption. assumption. 
Qed. 

Lemma foldRWithKey_equiv_maps:
  forall {e} {a} {b} `{OrdLaws e} `{EqLaws a} (f: e -> a -> b -> b) x (m1: Map e a) m2, 
  WF m1 ->
  WF m2 ->
  (forall e1 e2 a1 a2 y, a1 == a2 = true -> e1 == e2 = true -> f e1 a1 y = f e2 a2 y) ->
  (forall i, sem m1 i = sem m2 i) ->
  (foldrWithKey f x m1) = (foldrWithKey f x m2).
Proof.
  intros. rewrite foldrWithKey_spec'. rewrite foldrWithKey_spec'.
  assert (eqlist (toList m1) (toList m2) = true). { 
  assert ((toList m1) == (toList m2) = true).
  assert (m1 == m2 = true) by (eapply strong_eq1; eassumption).
  unfold "==" in H6. unfold Eq___Map in H6. unfold op_zeze____ in H6.
  unfold Internal.Eq___Map_op_zeze__ in H6. unfold toList. rewrite andb_true_iff in H6.
  destruct H6. assumption. unfold "==" in H6. unfold Eq_list in H6. unfold op_zeze____ in H6.
  apply H6. } apply fold_right_proper. apply H6. intros.
  destruct p1. destruct p2. unfold "==" in H7. unfold Eq_pair___  in H7. 
  unfold op_zeze____  in H7. unfold eq_pair in H7. rewrite andb_true_iff in H7.
  apply H4. 
  order a. order e.
Qed. 

Lemma mapAccumRWithKey_Desc: forall {e} {a} {b : Type} {c : Type} `{OrdLaws e} `{EqLaws a} (m: Map e a) (x : b) 
  (f: b -> e -> a -> (b * c)) lb ub,
  Proper ((fun (i j : e * a) => _GHC.Base.==_ i j = true) ==> eq) (fun x y => let (a,b) := x in f y a b) ->
  Bounded m lb ub ->
  Desc (snd (mapAccumRWithKey f x m)) lb ub (size m) (
  fun i => match (sem m i) with
           | Some y => Some (snd(f (fst (mapAccumRWithKey f x (map_gt m i))) i y))
           | None => None
            end).
Proof.
  intros. revert x. induction H3; intros.
  - simpl. solve_Desc e.
  - simpl.  rewrite (surjective_pairing (mapAccumRWithKey f x0 s2 )).
    rewrite (surjective_pairing (f (fst (mapAccumRWithKey f x0 s2)) x v)).
    rewrite (surjective_pairing ( mapAccumRWithKey f (fst (f (fst (mapAccumRWithKey f x0 s2)) x v)) s1)).
    simpl. applyDesc e IHBounded1. applyDesc e IHBounded2. solve_Desc e. f_solver e.
    + (*This case is the complicated one that involves all sorts of results about fold, toList, and 
        fromDistinctAscList*)
    remember ((1 + size s1 + size s2)%Z) as sz. repeat (applyDesc e (@map_gt_Desc e a)).
    repeat (erewrite mapAccumRWithKey_fst). repeat (rewrite foldrWithKey_spec').
    assert(
        (fold_right (fun (x1 : e * a) (t : b) => let (a1, b0) := x1 in fst (f t a1 b0))
           (fst
              (f (fold_right (fun (x1 : e * a) (t : b) => let (a1, b0) := x1 in fst (f t a1 b0)) x0 (toList s2))
                 x v)) (toList s3)) =
        fold_right (fun (x1 : e * a) (t : b) => let (a1, b0) := x1 in fst (f t a1 b0)) 
         x0 ((toList s3) ++ ((x, v) :: nil) ++ (toList s2))). { simpl. rewrite fold_right_app.
         simpl. reflexivity. }
    rewrite H5. clear H5. 
    assert ((fold_right (fun  (x1 : e * a) (t : b) => let (a1, b0) := x1 in fst (f t a1 b0)) x0
           (toList s3 ++ ((x, v) :: nil) ++ toList s2)) = 
    (fold_right (fun(x1 : e * a)  (t : b)  => let (a1, b0) := x1 in fst (f t a1 b0)) x0 (toList s4)) ). {
      assert (StronglySorted ToListProofs.lt (toList s3 ++ ((x, v) :: nil) ++ toList s2)). {
        eapply sorted_append.
        + eapply to_List_sorted. eassumption.
        + simpl. apply SSorted_cons.
          * eapply to_List_sorted. eassumption.
          * rewrite Forall_lt. intros. unfold ToListProofs.lt. rewrite <- toList_sem' in H5.
            destruct (sem s2 x1) eqn : ?.
            - solve_Bounds e.
            - inversion H5.
            - eassumption.
       + intros. assert (isUB (Some x) y = true). eapply toList_Bounds_UB. apply HB1. apply H5. solve_Bounds e.
       + intros. simpl in H5. destruct H5.
          * inversion H5; subst. order e.
          * assert (isLB (Some x) y = true). eapply toList_Bounds_LB. apply H3_0. apply H5. solve_Bounds e. }
      eapply fold_right_proper.
      - simpl. remember (fromDistinctAscList ((toList s3 ++ ((x, v) :: nil) ++ toList s2))) as m.
        assert (toList m ==  (toList s3 ++ ((x, v) :: nil) ++ toList s2) = true). { rewrite Heqm.
        eapply fromDistinctAscList_toList. apply H5. }
        rewrite <- eq_list_equiv. eapply Eq_Transitive. apply Eq_Symmetric. apply H7.
        unfold is_true. rewrite <-eq_toList. eapply strong_eq1.
        + subst. eapply fromDistinctAscList_Desc. apply H5. intros. apply H8.
        + wf_bounds.
        + intros. rewrite Hsem1. rewrite Heqm. eapply fromDistinctAscList_Desc. apply H5. intros.
          rewrite H10. simpl. rewrite sem_list_app.
          destruct (i0 > i) eqn : ?.
          * erewrite <- toList_sem''. simpl. unfold SomeIf.  erewrite <- toList_sem''.
            rewrite Hsem. rewrite Heqb0. 
            destruct (sem s1 i0).
            -- reflexivity.
            -- destruct (i0 == x); reflexivity.
            -- eassumption.
            -- eassumption.
          * erewrite <- toList_sem''. rewrite Hsem. rewrite Heqb0. simpl.
            -- destruct (i0 == x) eqn : ?.
                ++ solve_Bounds e.
                ++ erewrite <- toList_sem''. eapply sem_outside_below. eassumption. solve_Bounds e.
                   eassumption.
            -- eassumption.
        + rewrite Heqm. apply fromDistinctAscList_Desc. apply H5. intros. apply H8.
        + wf_bounds.
      - intros. apply H2 in H7. destruct p1. destruct p2. 
        eapply equal_f in H7. rewrite H7. reflexivity. }
    rewrite H5. reflexivity. apply HB2. apply H3_0. apply HB1.
    + repeat(applyDesc e (@map_gt_Desc e a)). repeat (erewrite mapAccumRWithKey_fst).
      * assert (forall i, sem s2 i = sem s3 i). {
         intros. destruct (_GHC.Base.>_ i0 i) eqn : ?.
          - specialize (Hsem i0). rewrite Heqb1 in Hsem. simpl in Hsem.
            rewrite Hsem. assert (sem s1 i0 = None). eapply sem_outside_above. eassumption.
            solve_Bounds e. rewrite H7. simpl. assert (i0 == x = false) by (order e). rewrite H8.
            reflexivity.
          - specialize (Hsem i0).  rewrite Hsem. rewrite Heqb1. eapply sem_outside_below. eassumption.
            solve_Bounds e. } 
        assert ((foldrWithKey (fun  (k : e) (v0 : a) (t : b) => fst (f t k v0)) x0 s2) =
           (foldrWithKey (fun (k : e) (v0 : a) (t : b)  => fst (f t k v0)) x0 s3)). {
            eapply foldRWithKey_equiv_maps. wf_bounds. wf_bounds. intros.
            assert (f y e1 a1 = f y e2 a2). { unfold respectful in H2. unfold Proper in H2.
            remember (e1, a1). remember (e2, a2). assert (p == p0 = true). unfold_pair.
            subst. rewrite andb_true_iff. split; assumption. apply H2 in H10. subst.
            eapply equal_f in H10. apply H10. } rewrite H10. reflexivity.
            intros. rewrite H7. reflexivity. }
        rewrite H8.
        assert (forall z,  f z x v = f z i v).  { intros.
        remember (x,v). remember (i,v). assert (p == p0 = true). unfold_pair. subst.
        rewrite andb_true_iff. split. order e. order a. apply H2 in H9. subst. eapply equal_f in H9.
        apply H9. } rewrite H9. reflexivity.
      * eassumption.
      * eassumption.
    + repeat(applyDesc e (@map_gt_Desc e a)). repeat (erewrite mapAccumRWithKey_fst).
      * assert (forall i, sem s4 i = sem s3 i). {
        intros.  destruct (_GHC.Base.>_ i0 i) eqn : ?.
        - rewrite Hsem. rewrite Hsem0. simpl. rewrite Heqb1. assert (sem s1 i0 = None). eapply sem_outside_above.
          eassumption. solve_Bounds e. rewrite H5. simpl. 
          assert (i0 == x = false) by (solve_Bounds e). rewrite H7. reflexivity.
        - rewrite Hsem0. rewrite Hsem. rewrite Heqb1. reflexivity. }
        assert ((foldrWithKey (fun (k : e) (v0 : a)(t : b)  => fst (f t k v0)) x0 s3) =
           (foldrWithKey (fun (k : e) (v0 : a)(t : b)  => fst (f t k v0)) x0 s4)). {
          eapply foldRWithKey_equiv_maps. wf_bounds. wf_bounds. intros.
          assert (f y e1 a1 = f y e2 a2). { unfold respectful in H2. unfold Proper in H2.
          remember (e1, a1). remember (e2, a2). assert (p == p0 = true). unfold_pair.
          subst. rewrite andb_true_iff. split; assumption. apply H2 in H9. subst.
          eapply equal_f in H9. apply H9. } rewrite H9. reflexivity. 
          intros. rewrite H5. reflexivity. }
      rewrite H7. reflexivity. 
     * eassumption.
     * eassumption.
    
Qed. 

(** Vertification of [mapKeys] *)

(*Note: only have None because we do not know the bounds given by fromList*)
(*This is a bit of a lazy specification, but it says that the keys values can be found by looking
  backwards in the list produced by folding the function over the keys*)
Lemma mapKeys_Desc: forall {e e' a} `{OrdLaws e} `{OrdLaws e'} (f: e -> e') (m: Map e a) ub lb,
  Bounded m lb ub ->
  Desc' (mapKeys f m) None None 
  (fun i => sem_for_lists (rev (foldrWithKey (fun k v t => ((f k), v) :: t) nil m)) i).
Proof.
  intros. unfold mapKeys. eapply (@fromList_Desc e' a). apply H0.
Qed.

(*[mapKeysWith] requires fromListWith, so it is not done yet*)
  
(** Verification of [mapKeysMonotonic] *)

Definition f_bound {e e'} (f: e -> e') (b: bound) : bound :=
  match b with
  |None => None
  |Some y => Some (f y)
  end.

Lemma fold_right_map: forall {a b} (l: list a) (f : a -> b),
  fold_right (fun x t => (f x) :: t) nil l = List.map (fun x => f x) l.
Proof.
  intros. induction l.
  - simpl. reflexivity.
  - simpl. rewrite IHl. reflexivity.
Qed.

Lemma fold_right_scope: forall {e e' a} (l: list (e * a)) (f : e -> e'),
    fold_right (fun (x0 : e * a) (t : list (e' * a)) => let (a0, b) := x0 in (f a0, b) :: t) nil l =
    fold_right (fun (x0 : e * a) (t : list (e' * a)) => (let (a0, b) := x0 in (f a0, b)) :: t) nil l.
Proof.
  intros. induction l.
  - reflexivity.
  - simpl. destruct a0. rewrite IHl. reflexivity.
Qed. 

(*Here we can give actual bounds and do not need to reverse the resulting list. The proof is a bit longer
  because the function is not defined using fromList*)
Lemma mapKeysMonotonic_Desc: forall {e e' a} `{OrdLaws e} `{OrdLaws e'} (f: e -> e') (m : Map e a) lb ub,
  Bounded m lb ub ->
  (forall x y, x < y = true -> (f x < f y) = true) ->
  Desc (mapKeysMonotonic f m) (f_bound f lb) (f_bound f ub) (size m) 
  (fun i => sem_for_lists(foldrWithKey (fun k v t => ((f k), v) :: t) nil m) i).
Proof.
  intros. induction H1.
  - simpl. solve_Desc e.
  - simpl. applyDesc e IHBounded1. applyDesc e IHBounded2. solve_Desc e. 
    + destruct lb. assert (e0 < x = true) by (solve_Bounds e). simpl. apply H2. apply H6. reflexivity.
    + destruct ub. assert (x < e0 = true) by (solve_Bounds e). simpl. apply H2. apply H6. reflexivity.
    + intros. repeat (erewrite foldrWithKey_spec'). 
    assert (fold_right (fun (x0 : e * a) (t : list (e' * a)) => let (a0, b) := x0 in (f a0, b) :: t)
     ((f x, v)
      :: fold_right (fun (x0 : e * a) (t : list (e' * a)) => let (a0, b) := x0 in (f a0, b) :: t) nil (toList s2))
     (toList s1) = 
      fold_right (fun (x0 : e * a) (t : list (e' * a)) => let (a0, b) := x0 in (f a0, b) :: t) 
       nil (toList s1 ++ (x, v) :: toList s2)). { rewrite fold_right_app. simpl. reflexivity. }
    rewrite H6. clear H6. 
    assert ((fold_right (fun (x0 : e * a) (t : list (e' * a)) => let (a0, b) := x0 in (f a0, b) :: t) nil
     (toList s1 ++ (x, v) :: toList s2)) = List.map (fun (x0 : e * a) => let (x, y) := x0 in (f x, y))
    (toList s1 ++ (x, v) :: toList s2)). { 
    rewrite <- (fold_right_map (toList s1 ++ (x, v) :: toList s2) (fun x => let (a, b) := x in (f a, b))).
    rewrite fold_right_scope. reflexivity. }
    rewrite H6. rewrite map_app. simpl. rewrite sem_list_app. simpl.
    repeat(rewrite <- fold_right_map). repeat(rewrite <- fold_right_scope). repeat(rewrite <- foldrWithKey_spec').
    rewrite <- Hsem. rewrite <- Hsem0. destruct (sem s i). reflexivity. destruct (i == (f x)); reflexivity.
Qed.

(** Vertification of [foldMapWithKey *)
(*TODO: See if there is a better specification for this*)
(*Note: This is defined here, not in toList proofs, because the specification given in the Haskell
library description uses [mapWithKey]*)
Lemma int_haskell_coq: forall (x y : Z),
  x == y = true <-> x = y.
Proof.
  intros. pose proof Eq_eq_Int .  specialize (H x y). apply reflect_iff in H. symmetry. apply H.
Qed.

Lemma foldMapWithKey_spec: forall {e a c} `{OrdLaws e} `{MonoidLaws c} (f: e -> a -> c) (m: Map e a) lb ub,
  Bounded m lb ub ->
  foldMapWithKey f m = Foldable.fold  (mapWithKey  f m).
Proof.
  intros. induction H9.
  - simpl. unfold Foldable.fold. unfold Foldable__Map. unfold Foldable.fold__.
    unfold Internal.Foldable__Map_fold. reflexivity.
  - simpl. destruct (_GHC.Base.==_ sz 1%Z) eqn : ?.
    + assert (sz = 1%Z). apply int_haskell_coq. assumption. subst. rewrite int_haskell_coq in Heqb.
      assert (size s1 = 0%Z). lia_sizes. assert (size s2 = 0%Z) by lia_sizes. rewrite Heqb. rewrite Eq_Reflexive.
      assert (s1 = Tip). eapply size_0_iff_tip. apply H9_. assumption. rewrite H15.
      assert (s2 = Tip). eapply size_0_iff_tip. apply H9_0. assumption. rewrite H16.
      simpl. unfold Foldable.fold. unfold Foldable__Map. unfold Foldable.fold__.
    unfold Internal.Foldable__Map_fold. rewrite Eq_Reflexive. reflexivity.
    + replace (_GHC.Base.==_ sz 1%Z ) with false. rewrite IHBounded1. rewrite IHBounded2.
      unfold Foldable.fold. unfold Foldable__Map. unfold Foldable.fold__. simpl.
      replace (_GHC.Base.==_ sz 1%Z) with false. reflexivity.
Qed.

