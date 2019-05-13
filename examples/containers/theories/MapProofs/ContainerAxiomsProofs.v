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
Require Import MapProofs.LookupProofs.
Require Import MapProofs.InsertProofs.
Require Import MapProofs.DeleteUpdateProofs.
Require Import MapProofs.ToListProofs.
Require Import MapProofs.FilterPartitionProofs.
Require Import MapProofs.MaxMinProofs.
Require Import Coq.Classes.Morphisms.


Section WF.
Context {e : Type} {a : Type} {HEq : Eq_ e} {HOrd : Ord e} {HEqLaws : EqLaws e}  {HOrdLaws : OrdLaws e}.


(*The following theorems are the axioms from ContainerAxioms. Some are slightly modified, such as adding
  the condition that the function in filter respects equality and using Haskell equality on maps rather
  than Coq equality. I have noted where the definitions are changed
   Also, in nearly every axiom, I had to add the hypothesis that the map is Bounded.  *)

(*First, the following are lemmas that are used in proving various ContainerAxioms*)

(*Simpler definition of lookup*)
Fixpoint lookup' (key : e) (map : Map e a) : option a :=
  match map with
  | Tip => None
  | Bin sz k1 v1 lt rt => match compare key k1 with
                          | Eq => Some v1 
                          | Lt => lookup' key lt 
                          | Gt => lookup' key rt
                          end
 end.  

(*Prove the two definitions are equivalent*)
Lemma lookup_lookup'_equiv : forall  (key : e) (map : Map e a),
    lookup key map = lookup' key map.
Proof.
  intros. induction map.
  - simpl. destruct (compare key k); try (reflexivity); assumption.
  - simpl. reflexivity.
Qed.  

(*Follows from sem_inside, says that if a key is in a map, it is between the bounds*)
Lemma keys_inside_bounds : forall (map: Map e a) key lb ub,
  Bounded map lb ub ->
  member key map = true ->
  isLB lb key = true /\ isUB ub key = true .
Proof.
  intros. eapply member_spec in H0. destruct H0.
  eapply sem_inside. apply H. apply H0. apply H.
Qed.

(*This function represents sem on a filtered map. It is needed when we have goals about filterWithKey
in the hypothesis, since filterWithKey_Desc only works on the goal*)
Fixpoint sem_filter (m: Map e a) f i:=
  match m with
  |Tip => None
  |Bin _ k v m1 m2 => match compare i k with
                     | Lt => sem_filter m1 f i
                     | Eq => SomeIf (f k v) v
                     | Gt => sem_filter m2 f i
                    end
  end.

(*Proves the equivalence of this function with using sem on the filtered map directly*)
Lemma sem_filter_equiv: forall m lb ub key f,
  Bounded m lb ub ->
  Proper ((fun (i j : e) => _GHC.Base.==_ i j = true) ==> eq) f ->
  sem (filterWithKey f m) key = sem_filter m f key.
Proof.
  intros. induction H.
  - simpl. reflexivity.
  - eapply filterWithKey_Desc. apply BoundedBin. apply H. apply H1. apply H2. apply H3.
    apply H4. apply H5. apply H0. intros. simpl in *. specialize (H8 key).
    destruct (compare key x) eqn : ?.
    + assert (key == x = true) by (order e). rewrite H9 in H8.
      assert (sem s1 key = None). eapply sem_outside_above. apply H. solve_Bounds e. rewrite H10 in H8.
      simpl in H8. unfold SomeIf. assert (f x v = f key v). apply equal_f. apply H0. order e.
      rewrite H11. assumption.
    + rewrite <- IHBounded1. eapply filterWithKey_Desc. apply H. apply H0. intros.
      specialize (H11 key). destruct (sem s1 key) eqn : ?. simpl in H8.
      rewrite <- H8 in H11. symmetry. assumption.
      assert (key == x = false) by (order e). rewrite H12 in H8. assert (sem s2 key = None).
      eapply sem_outside_below. apply H1. solve_Bounds e. rewrite H13 in H8. simpl in H8.
      rewrite H8. symmetry. assumption.
    + assert (sem s1 key = None). eapply sem_outside_above. apply H. solve_Bounds e. rewrite H9 in H8.
      simpl in H8. assert (key == x = false) by (order e). rewrite H10 in H8; simpl in H8.
      rewrite <- IHBounded2. eapply filterWithKey_Desc. apply H1. apply H0. intros.
      specialize (H13 key). rewrite <- H13 in H8. apply H8.
Qed.

(*If a key, value pair is in the filtered map, it was in the original map*)
Lemma filterPreservesValues: forall (m: Map e a) lb ub f,
  Bounded m lb ub ->
  Proper ((fun (i j : e) => _GHC.Base.==_ i j = true) ==> eq) f ->
  forall i v, sem (filterWithKey f m) i = Some v -> sem m i = Some v.
Proof.
  intros. rewrite (sem_filter_equiv m lb ub i f H) in H1. induction H.
  - simpl in H1. inversion H1.
  - simpl in H1. simpl. destruct (compare i x) eqn : ?.
    + assert (i == x = true) by (order e). rewrite H7. simpl. assert (sem s1 i = None).
      eapply sem_outside_above. apply H. solve_Bounds e. rewrite H8. unfold SomeIf in H1. simpl.
      destruct (f x v0). assumption. inversion H1.
    + apply IHBounded1 in H1. rewrite H1. reflexivity.
    + assert (sem s1 i = None). eapply sem_outside_above. apply H. solve_Bounds e. rewrite H7.
      assert (i == x = false) by (order e). rewrite H8. simpl. apply IHBounded2.
      assumption.
  - assumption.
Qed.

(*If a key, value pair is in the filtered map, the function returns true on the pair*)
Lemma filter_sem_true: forall (m: Map e a) lb ub f,
  Bounded m lb ub ->
  Proper ((fun (i j : e) => _GHC.Base.==_ i j = true) ==> eq) f ->
  forall i v, sem (filterWithKey f m) i = Some v -> f i v = true.
Proof.
  intros. rewrite (sem_filter_equiv _ lb ub) in H1. induction H.
  - simpl in H1. inversion H1.
  - simpl in H1. destruct (compare i x) eqn : ?.
    + unfold SomeIf in H1. destruct (f x v0) eqn : ?. 
      rewrite <- Heqb. inversion H1; subst. eapply equal_f. apply H0. order e. inversion H1.
    + apply IHBounded1. apply H1.
    + apply IHBounded2. apply H1.
  - assumption.
  - assumption.
Qed.

(*Conversely, if a key, value pair was in the map and not in the filtered map, f k v is false*)
Lemma filter_sem_false: forall (m: Map e a) lb ub f,
  Bounded m lb ub ->
  Proper ((fun (i j : e) => _GHC.Base.==_ i j = true) ==> eq) f ->
  forall i v, sem m i = Some v ->
   sem (filterWithKey f m) i = None -> f i v = false.
Proof.
  intros. rewrite (sem_filter_equiv _ lb ub) in H2. induction H.
  - simpl in H1. inversion H1.
  - simpl in H2. destruct (compare i x) eqn : ?.
    + unfold SomeIf in H2. destruct (f x v0) eqn : ?. inversion H2. 
      rewrite <- Heqb. simpl in H1. assert (sem s1 i = None). { eapply sem_outside_above. apply H.
      solve_Bounds e. } rewrite H8 in H1. simpl in H1. assert (i == x = true) by (order e).
      rewrite H9 in H1. inversion H1; subst. eapply equal_f. apply H0. assumption. 
    + simpl in H1. destruct (sem s1 i) eqn : ?. inversion H1; subst. apply IHBounded1.
      reflexivity. assumption. assert (i == x = false) by (order e). assert (sem s2 i = None). {
      eapply sem_outside_below. apply H3. solve_Bounds e. } rewrite H8 in H1. rewrite H9 in H1.
      inversion H1.
    + simpl in H1. assert (sem s1 i = None). { eapply sem_outside_above. apply H. solve_Bounds e. }
      assert (i == x = false) by (order e). rewrite H8 in H1. rewrite H9 in H1. simpl in H1.
      apply IHBounded2. assumption. assumption.
  - assumption.
  - assumption.
Qed.

(*This is similar for intersection. This allows us to work with [sem (intersection _)] in 
  a hypothesis*)
Definition sem_intersect (m1: Map e a)(m2: Map e a) i :=
  match (sem m1 i), (sem m2 i) with
  | Some v, Some v2 => Some v
  | _, _ => None
  end.

(*Proves equaivalence*)
Lemma sem_intersect_equiv: forall m1 m2 lb ub key,
  Bounded m1 lb ub ->
  Bounded m2 lb ub ->
  sem (intersection m1 m2) key = sem_intersect m1 m2 key.
Proof.
  intros. applyDesc e (@intersection_Desc e a). specialize (Hsem key).
  destruct (sem m1 key ) eqn : ?. destruct (sem m2 key) eqn: ?.
  simpl in Hsem. unfold sem_intersect. rewrite Heqo. rewrite Heqo0. assumption.
  simpl in Hsem. unfold sem_intersect. rewrite Heqo. rewrite Heqo0. assumption.
  unfold sem_intersect. rewrite Heqo. destruct (sem m2 key); simpl in Hsem; assumption.
Qed.

(*Same for [union]*)
Definition sem_union (m1: Map e a)(m2: Map e a) i :=
  match (sem m1 i), (sem m2 i) with
  | Some v, _ => Some v
  | _, Some v2 => Some v2
  | _, _ => None
  end.

Lemma sem_union_equiv: forall m1 m2 lb ub key,
  Bounded m1 lb ub ->
  Bounded m2 lb ub ->
  sem (union m1 m2) key = sem_union m1 m2 key.
Proof.
  intros. applyDesc e (@union_Desc e a). specialize (Hsem key). unfold sem_union.
  destruct (sem m1 key) eqn : ?. destruct (sem m2 key) eqn : ?.
  - simpl in Hsem. assumption.
  - rewrite oro_None_r in Hsem. assumption.
  - simpl in Hsem. rewrite Hsem. destruct (sem m2 key); reflexivity.
Qed.

(*If a value is in a map and f returns true on the key, value, then sem_filter will also
return that value (that is to say, the result is in the filtered map)*)
Lemma sem_filter_in_map: forall key value map lb ub f,
  Bounded map lb ub ->
  Proper ((fun (i j : e) => _GHC.Base.==_ i j = true) ==> eq) f ->
  sem map key = Some value ->
  f key value = true ->
  sem_filter map f key = Some value.
Proof.
  intros. induction H.  
  - inversion H1.
  - simpl. simpl in H1. destruct (compare key x) eqn : ?.
     + assert (sem s1 key = None). eapply sem_outside_above. apply H. solve_Bounds e.
       rewrite H8 in H1. assert (key == x = true) by (order e). rewrite H9 in H1.
        simpl in H1. inversion H1; subst. assert (f x value = f key value).
        apply equal_f. apply H0. order e. rewrite H6.
        rewrite H2. simpl. reflexivity.
      + apply IHBounded1. destruct (sem s1 key). inversion H1; subst; reflexivity.
        destruct (key == x) eqn : ?. order e. destruct (sem s2 key) eqn : ?. solve_Bounds e.
        inversion H1.
      + apply IHBounded2. destruct (sem s1 key) eqn : ?. solve_Bounds e. 
        destruct (key == x) eqn : ?. order e. simpl in H1. apply H1.
Qed. 

Lemma eq_coq_implies_haskell : forall {a} `{EqLaws a} (x y : a),
  x = y -> x == y = true.
Proof.
  intros. subst. apply Eq_Reflexive.
Qed.


Lemma fst_partition_sem: forall m P key lb ub,
  Bounded m lb ub ->
  Proper ((fun (i j : e) => _GHC.Base.==_ i j = true) ==> eq) P ->
  sem (fst (partitionWithKey P m)) key = sem_filter m P key.
Proof.
  intros. induction H.
  - reflexivity.
  - apply (partitionWithKey_spec _ _ lb ub).
    + apply BoundedBin; assumption.
    + assumption.
    + intros. simpl. simpl in H6. apply H6. intros. destruct (compare key x) eqn : ?.
      * specialize (H9 key). assert (sem s1 key = None). eapply sem_outside_above. apply H.
        solve_Bounds e. rewrite H10 in H9. simpl in H9. assert (key == x = true) by (order e).
        rewrite H11 in H9. simpl in H9. unfold SomeIf. assert (P key v = P x v).
        apply equal_f. apply H0. apply H11. rewrite <- H12. apply H9.
      * rewrite <- IHBounded1. eapply partitionWithKey_spec. apply H. apply H0. intros.
        simpl. apply H10. intros. specialize (H13 key). specialize (H9 key).
        destruct (sem s1 key) eqn : ?. simpl in H9.
        rewrite H9. rewrite H13. reflexivity. assert (key == x = false) by (order e).
        assert (sem s2 key = None). eapply sem_outside_below. apply H1. solve_Bounds e. 
        rewrite H14 in H9. rewrite H15 in H9. simpl in H9. rewrite H9. rewrite H13.
        reflexivity.
      * rewrite <- IHBounded2. eapply partitionWithKey_spec. apply H1. apply H0. intros.
        simpl. apply H10. intros. specialize (H13 key). specialize (H9 key).
        assert (sem s1 key = None). eapply sem_outside_above. apply H. solve_Bounds e.
        assert (key == x = false) by (order e). rewrite H14 in H9. rewrite H15 in H9.
        simpl in H9. rewrite H13. rewrite H9. reflexivity.
Qed.

Lemma snd_partition_sem: forall m P key lb ub,
  Bounded m lb ub ->
  Proper ((fun (i j : e) => _GHC.Base.==_ i j = true) ==> eq) P ->
  sem (snd (partitionWithKey P m)) key = sem_filter m (fun a b => negb( P a b)) key.
Proof.
  intros. induction H.
  - reflexivity.
  - apply (partitionWithKey_spec _ _ lb ub).
    + apply BoundedBin; assumption.
    + assumption.
    + intros. simpl. simpl in H6. apply H6. intros. destruct (compare key x) eqn : ?.
      * specialize (H9 key). assert (sem s1 key = None). eapply sem_outside_above. apply H.
        solve_Bounds e. rewrite H10 in H9. simpl in H9. assert (key == x = true) by (order e).
        rewrite H11 in H9. simpl in H9. unfold SomeIf. assert (P key v = P x v).
        apply equal_f. apply H0. apply H11. rewrite <- H12. destruct (P key v) eqn : ?;
        simpl; apply H9.
      * rewrite <- IHBounded1. eapply partitionWithKey_spec. apply H. apply H0. intros.
        simpl. apply H10. intros. specialize (H13 key). specialize (H9 key).
        destruct (sem s1 key) eqn : ?. simpl in H9.
        rewrite H9. rewrite H13. reflexivity. assert (key == x = false) by (order e).
        assert (sem s2 key = None). eapply sem_outside_below. apply H1. solve_Bounds e. 
        rewrite H14 in H9. rewrite H15 in H9. simpl in H9. rewrite H9. rewrite H13.
        reflexivity.
      * rewrite <- IHBounded2. eapply partitionWithKey_spec. apply H1. apply H0. intros.
        simpl. apply H10. intros. specialize (H13 key). specialize (H9 key).
        assert (sem s1 key = None). eapply sem_outside_above. apply H. solve_Bounds e.
        assert (key == x = false) by (order e). rewrite H14 in H9. rewrite H15 in H9.
        simpl in H9. rewrite H13. rewrite H9. reflexivity.
Qed.

Lemma partitionPreservesNone: forall m lb ub f,
  Bounded m lb ub ->
  Proper ((fun (i j : e) => _GHC.Base.==_ i j = true) ==> eq) f ->
  forall i, sem m i = None -> sem_filter m f i = None.
Proof.
  intros. induction H.
  - reflexivity.
  - simpl. simpl in H1. destruct (compare i x) eqn : ?.
   + destruct (sem s1 i). inversion H1. assert (i == x = true) by (order e).
    rewrite H7 in H1. simpl in H1. inversion H1.
   + destruct (sem s1 i). inversion H1. destruct (i == x) eqn : ?.
     inversion H1. order e.
   + destruct (sem s1 i). inversion H1. destruct (i == x) eqn : ?. inversion H1.
     destruct (sem s2 i) eqn : ?. inversion H1. apply IHBounded2. reflexivity.
Qed.

(*If a key, value pair is in the filtered map, it was in the original map*)
Lemma partitionPreservesValues: forall `{EqLaws a} m lb ub f,
  Bounded m lb ub ->
  Proper ((fun (i j : e) => _GHC.Base.==_ i j = true) ==> eq) f ->
  forall i v, sem_filter m f i == Some v = true -> sem m i == Some v = true.
Proof.
  intros. induction H1.
  - simpl in H3. inversion H3.
  - simpl. destruct (compare i x) eqn : ?.
    + assert (sem s1 i = None). eapply sem_outside_above. apply H1_. solve_Bounds e.
      simpl in H3. rewrite Heqc in H3. rewrite H7. simpl. assert (i == x = true) by (order e).
      rewrite H8. simpl. destruct (f x v0). simpl in H3. assumption. inversion H3.
    + simpl in H3. rewrite Heqc in H3. destruct (sem s1 i) eqn : ?. simpl.
      apply IHBounded1. apply H3. eapply partitionPreservesNone in Heqo.
      rewrite Heqo in H3. inversion H3. apply H1_. apply H2.
    + simpl in H3. rewrite Heqc in H3. assert (sem s1 i = None). eapply sem_outside_above.
      apply H1_. solve_Bounds e. rewrite H7. assert (i == x = false) by (order e). rewrite H8.
      simpl. apply IHBounded2. apply H3.
Qed.

(*Same as above, but for intersection*)
Lemma sem_intersection: forall (m1: Map e a) m2 key lb ub,
  Bounded m1 lb ub ->
  Bounded m2 lb ub ->
  sem (intersection m1 m2) key = sem m1 key &&& sem m2 key.
Proof.
  intros. applyDesc e (@intersection_Desc e a). apply Hsem.
Qed.

(*null is true iff m is empty*)
Lemma null_empty_iff: forall (m: Map e a),
  null m = true <-> m = empty.
Proof.
  intros; split; intros.
  - destruct m. inversion H. reflexivity.
  - rewrite H. reflexivity.
Qed.

(*Same as other sem definitions but for insert*)
Lemma sem_insert: forall (m1: Map e a) key value lb ub i,
  Bounded m1 lb ub ->
  isLB lb key = true ->
  isUB ub key = true ->
  sem (insert key value m1) i = SomeIf (i == key) value ||| sem m1 i.
Proof.
  intros. applyDesc e (@insert_Desc e a). unfold SomeIf. apply Hsem.
Qed.

(*Same but for for difference*)
Lemma difference_sem: forall (m1: Map e a) m2 lb ub key,
  Bounded m1 lb ub ->
  Bounded m2 lb ub ->
  sem (difference m1 m2) key = diffo (sem m1 key) (sem m2 key).
Proof.
  intros. eapply difference_Desc. apply H. apply H0. intros.
  rewrite H4. reflexivity.
Qed. 

(*Start of ContainerAxioms*)

(*This lemma says that if two keys are equal, then the result of member is the same when either is called*)
Lemma member_eq: forall {a : Type} (n : e) (n' : e) (m : Map e a),
  n == n' = true ->
  member n m = member n' m.
Proof.
  intros. 
 induction m.
   - simpl. destruct (compare n k) eqn : E.
    + assert (compare n' k = Eq) by (order e). rewrite H0. reflexivity.
    + assert (compare n' k = Lt) by (order e). rewrite H0. assumption.
    + assert (compare n' k = Gt) by (order e). rewrite H0. assumption.
  - reflexivity.
Qed.

(*If we insert a (key, value) in a map, then looking up the key gives the value. *)
Lemma lookup_insert : forall (key: e) (value : a) (map : Map e a) lb ub,
  Bounded map lb ub ->
  isLB lb key = true ->
  isUB ub key = true ->
  lookup key (insert key value map) = Some value.
Proof.
  intros. applyDesc e (@insert_Desc e a). erewrite lookup_spec. specialize (Hsem key). 
  rewrite Eq_Reflexive in Hsem. simpl in Hsem. assumption. apply HB.
Qed. 

(*A more general version that makes it explicit that the keys do not have to be bounded*)
Lemma lookup_insert': forall key value (m: Map e a),
  WF m ->
  lookup key (insert key value m) = Some value.
Proof.
  intros. eapply lookup_insert. apply H. reflexivity. reflexivity. 
Qed.

(*If we lookup a key key1, the result is the same regardless of whether or not we have inserted key2 
(a different key than key1). I had to  change the 4th hypothesis to Haskell equality*)
Lemma lookup_insert_neq : forall (key1: e) (key2: e) (value : a) (map : Map e a) lb ub,
  Bounded map lb ub ->
  isLB lb key2 = true ->
  isUB ub key2 = true ->
  key1 == key2 = false -> 
  lookup key1 (insert key2 value map) = lookup key1 map.
Proof.
  intros. applyDesc e (@insert_Desc e a). specialize (Hsem key1). rewrite H2 in Hsem.
  simpl in Hsem. erewrite lookup_spec.  erewrite lookup_spec. apply Hsem. apply H. apply HB.
Qed.

Lemma lookup_insert_neq': forall key1 key2 value (m: Map e a),
  WF m ->
  key1 == key2 = false ->
  lookup key1 (insert key2 value m) = lookup key1 m.
Proof.
  intros. eapply lookup_insert_neq. apply H. reflexivity. reflexivity. assumption.
Qed.
 
(*States that if we check for key1 in the map in which we have inserted key2, then either
key1 was already in the map, or key1 == key2. *)
Lemma member_insert: forall key1 key2 value (map: Map e a) lb ub,
  Bounded map lb ub ->
  isLB lb key2 = true ->
  isUB ub key2 = true ->
  member key1 (insert key2 value map) = (key1 == key2) || member key1 map. 
Proof.
  intros. applyDesc e (@insert_Desc e a). destruct (member key1 s) eqn : ?.
  - erewrite member_spec in Heqb. destruct Heqb. specialize (Hsem key1). destruct (key1 == key2).
    reflexivity. simpl in Hsem. simpl. symmetry. erewrite member_spec. exists x.
    rewrite <- Hsem. assumption. apply H. apply HB.
  - specialize (Hsem key1). destruct (key1 == key2). simpl in Hsem. 
    assert (member key1 s = true). { erewrite member_spec. exists value. assumption. apply HB. }
    rewrite Heqb in H2. inversion H2. simpl. simpl in Hsem.
    assert (sem s key1 = None). { erewrite <- notMember_spec. unfold notMember. rewrite negb_true_iff.
    assumption. apply HB. } rewrite Hsem in H2. erewrite <- notMember_spec in H2.
    unfold notMember in H2. rewrite negb_true_iff in H2. symmetry. assumption. apply H.
Qed. 

Lemma member_insert': forall key1 key2 value (map: Map e a),
  WF map ->
  member key1 (insert key2 value map) = (key1 == key2) || member key1 map.
Proof.
  intros. eapply member_insert; try (eassumption); try(reflexivity).
Qed. 

(*If we lookup a key that is deleted, we should get None*)
Lemma delete_eq : forall key (map : Map e a) lb ub,
  Bounded map lb ub ->
  lookup key (delete key map) = None.
Proof.
  intros. applyDesc e (@delete_Desc e a). specialize (Hsem key). rewrite Eq_Reflexive in Hsem. rewrite <- Hsem.
  eapply lookup_spec. apply HB.
Qed.

(*If we delete a key key2 and then lookup a different key key1, then it should be the same regardless of
whether or not key2 was deleted. I had the change the 2nd hypothesis to use Haskell equality*)
Lemma delete_neq : forall key1 key2 (map : Map e a) lb ub,
  Bounded map lb ub ->
  key1 == key2 = false ->
  lookup key1 (delete key2 map) = lookup key1 map.
Proof.
  intros. applyDesc e (@delete_Desc e a). erewrite lookup_spec. erewrite lookup_spec. 
  specialize (Hsem key1). rewrite H0 in Hsem. assumption. apply H. apply HB.
Qed.

(*Same as above but for member. I also had to change the 2nd hypothesis to Haskell equality.*)
Lemma member_delete_neq: forall key1 key2 (map: Map e a) lb ub,
  Bounded map lb ub ->
  key1 == key2 = false ->
  member key2 (delete key1 map) = member key2 map.
Proof.
  intros. applyDesc e (@delete_Desc e a). specialize (Hsem key2).
  assert (key2 == key1 = false) by (order e). rewrite H1 in Hsem. destruct (member key2 s) eqn : ?.
  - erewrite member_spec in Heqb. destruct Heqb. rewrite H2 in Hsem. symmetry. erewrite member_spec.
    exists x. symmetry in Hsem. assumption. apply H. apply HB.
  - assert (notMember key2 s = true). { unfold notMember. apply negb_true_iff. assumption. }
    erewrite notMember_spec in H2. rewrite H2 in Hsem. symmetry in Hsem. erewrite <- notMember_spec in Hsem.
    unfold notMember in Hsem. rewrite negb_true_iff in Hsem. symmetry. assumption. apply H. apply HB.
Qed.

(*States that if a key is not in the map, then looking it up will give None, and vice versa. I had to change
the condition to an iff rather than equality.*)
Lemma non_member_lookup :
  forall key (map: Map e a) lb ub,
  Bounded map lb ub ->
  (member key map = false) <-> (lookup key map = None).
Proof.
  intros. assert (notMember key map = true <-> member key map = false). { unfold notMember.
  rewrite negb_true_iff. reflexivity. } rewrite <- H0. erewrite lookup_spec.
  eapply notMember_spec. apply H. apply H.
Qed.

(*If two keys are equal (according to the Eq typeclass), then their values in 
a map are equal*)
Lemma lookup_eq : forall k k' (m : Map e a),
    k == k' = true ->
    lookup k m = lookup k' m.
Proof.
  intros. 
 induction m.
  - simpl. destruct (compare k k0) eqn : E.
    + assert (compare k' k0 = Eq) by (order e). rewrite H0. reflexivity.
    + assert (compare k' k0 = Lt) by (order e). rewrite H0. assumption.
    + assert (compare k' k0 = Gt) by (order e). rewrite H0. assumption.
  - reflexivity.
Qed.

(*This follows almost immediately from member_spec. I also had to change it to an iff rather 
than equality*)
Lemma member_lookup : 
  forall key (map: Map e a) lb ub,
  Bounded map lb ub -> 
  (member key map = true) <-> (exists value, lookup key map = Some value).
Proof.
  intros. assert(A:=H). eapply member_spec in A. eapply lookup_spec in H.
  rewrite <- H in A. apply A.
Qed. 

(** ** Verification of [null] *)
Lemma null_empty: 
    @null e a empty = true.
Proof.
  unfold null. simpl. reflexivity.
Qed. 

(*A key is a member of the union of two maps whenever it is a member of at least one of the maps*)
Lemma member_union :
  forall key (map1: Map e a) map2 lb ub,
  Bounded map1 lb ub ->
  Bounded map2 lb ub ->
  member key (union map1 map2) = member key map2 || member key map1.
Proof.
  intros. applyDesc e (@union_Desc e a). specialize (Hsem key). destruct (member key s) eqn : ?.
  - erewrite member_spec in Heqb. destruct Heqb. rewrite H1 in Hsem. destruct (sem map1 key) eqn : ?.
    inversion Hsem; subst. assert (member key map1 = true). { erewrite member_spec.
    exists a0. assumption. apply H. } rewrite H2. rewrite orb_true_r. reflexivity.
    simpl in Hsem. assert (member key map2 = true). { erewrite member_spec. exists x. symmetry.
    assumption. apply H0. } rewrite H2. reflexivity. apply HB.
  - rewrite <- negb_true_iff in Heqb. assert (notMember key s = true). { unfold notMember.
    assumption. } eapply notMember_spec in H1. rewrite H1 in Hsem. destruct (sem map1 key) eqn : ?.
    inversion Hsem. destruct (sem map2 key) eqn : ?. inversion Hsem. 
    erewrite <- notMember_spec in Heqo. erewrite <- notMember_spec in Heqo0.
    unfold notMember in *. rewrite negb_true_iff in *. rewrite Heqo. rewrite Heqo0. reflexivity.
    apply H0. apply H. apply HB.
Qed.

(*The union of a map with the empty map (in both directions) is itself*)
Lemma union_nil_l : forall (map: Map e a) ub lb,
  Bounded map ub lb ->
  union empty map = map.
Proof.
  intros. unfold empty. induction H.
  - reflexivity.
  - simpl. destruct s1 eqn : ?. reflexivity. destruct s2 eqn : ?. reflexivity.
    unfold insertR. unfold singleton. rewrite H3. simpl. reflexivity.
Qed.

Lemma union_nil_r : forall (map: Map e a) ub lb,
  Bounded map ub lb ->
  union map empty = map.
Proof.
  intros. induction H.
  - simpl. reflexivity.
  - simpl. destruct s1. reflexivity. destruct s2. reflexivity. reflexivity.
Qed.

(*The difference between a map and itself is the empty map*)
Lemma difference_self: forall (map: Map e a) lb ub,
  Bounded map lb ub ->
  difference map map = empty.
Proof.
  intros. 
 eapply difference_Desc. apply H. apply H. intros.
  unfold diffo in H3.
  assert (forall i, sem s i = None). { intros i. specialize (H3 i).
  destruct (sem map i); assumption. } apply empty_no_elts. apply H4.
Qed. 

(*The difference of a map with the empty map is itself*)
Lemma difference_nil_r: forall (B : Type) (map: Map e a) lb ub,
  Bounded map lb ub ->
  difference map (@empty e B) = map.
Proof.
  intros. inversion H.
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed.

(*The difference of the empty map with any map is empty*)
Lemma difference_nil_l: forall  (B : Type) (map: Map e a) lb ub (key : e),
  Bounded map lb ub ->
  difference (@empty e B) map = empty.
Proof.
  intros. inversion H.
  - simpl. reflexivity.
  - simpl. unfold empty. reflexivity.
Qed.

(*If a key is in a map, the difference of the singleton map containing only that key
and the original map is empty*)
Lemma difference_Tip_member: forall (map: Map e a) (key :e) lb ub,
  Bounded map lb ub ->
  member key map = true ->
  forall (value : a), difference (singleton key value) map = empty.
Proof.
  intros. assert (A:=H0). apply (keys_inside_bounds _ _ lb ub) in H0. destruct H0.
  applyDesc e (@singleton_Desc e a). eapply difference_Desc. apply HB. apply H. intros.
  eapply empty_no_elts. intros. specialize (H5 i). specialize (Hsem i).
  destruct (i == key) eqn : ?. simpl in Hsem. rewrite Hsem in H5.
  erewrite member_spec in A. destruct A. erewrite sem_resp_eq in H6.
  rewrite H6 in H5. simpl in H5. assumption. order e. apply H. simpl in Hsem.
  rewrite Hsem in H5. destruct (sem map i); simpl in H5; assumption. apply H.
Qed.

(*For this lemma, I had to change to use Haskell equality. Even though the structure of a singleton map is
unique, we only know the key up to Haskell equality. We also had to add {EqLaws a} in order to compare the 
maps *)
Lemma difference_Tip_non_member: forall `{EqLaws a} (map: Map e a) (key :e) lb ub,
  Bounded map lb ub ->
  isUB ub key = true ->
  isLB lb key = true ->
  member key map = false ->
  forall (value : a), difference (singleton key value) map == (singleton key value) = true.
Proof.
  intros. assert (Bounded (singleton key value) lb ub). apply BoundedBin; try (apply BoundedTip); try(assumption).
  simpl. reflexivity. simpl. unfold balance_prop. simpl. omega. eapply difference_Desc.
  - apply H5.
  - apply H1.
  - intros. unfold diffo in H9.
    assert( forall i : e, sem s i = SomeIf(i == key) value). { intros. specialize (H9 i).
    destruct (i == key) eqn : ?. assert (sem map i = sem map key) by (apply sem_resp_eq; assumption).
    rewrite H10 in H9. assert (sem map key = None). eapply notMember_spec.
    apply H1. unfold notMember. rewrite negb_true_iff. assumption. rewrite H11 in H9.
    unfold SomeIf. rewrite H9. rewrite (sem_resp_eq _ i key). simpl. rewrite Eq_Reflexive.
    simpl. reflexivity. apply Heqb. simpl. destruct(sem map i) eqn : ?.
    assumption. simpl in H9. rewrite Heqb in H9. simpl in H9. assumption. }
    applyDesc e (@singleton_Desc e a). eapply weak_equals_spec. apply H6. apply HB.
    intros. specialize (H10 i). specialize (Hsem i). rewrite H10. rewrite Hsem.
    apply Eq_Reflexive.
Qed.

(*For filterWithKey, we need to add the assumptions that the functions we are concerned with
  respect Haskell equality. Note that the third condition follows from the first two, but only
  if we use functional extensionality. We also need to change the result to Haskell equality and 
  assumpe {EqLaws a}.*)
Lemma filterWithKey_comp: forall `{EqLaws a} f f' (m: Map e a) lb ub ,
  Bounded m lb ub ->
  Proper ((fun (i j : e) => _GHC.Base.==_ i j = true) ==> eq) f ->
  Proper ((fun i j : e => _GHC.Base.==_ i j = true) ==> eq) f' ->
  Proper ((fun i j : e => _GHC.Base.==_ i j = true) ==> eq) (fun v a => f v a && f' v a) ->
  filterWithKey f (filterWithKey f' m) == filterWithKey (fun v a => f v a && f' v a) m = true.
Proof.
  intros. assert (Bounded (filterWithKey f' m) lb ub). apply filterWithKey_Bounded. apply H1.
  eapply filterWithKey_Desc. apply H5. apply H2. intros.
  eapply filterWithKey_Desc. apply H1. apply H4. 
  intros.
  - eapply weak_equals_spec. apply H6. apply H9. intros.
    destruct (sem (filterWithKey f' m) i) eqn : ?. 
    + specialize (H8 i). rewrite Heqo in H8.
      assert (A:= Heqo). eapply filter_sem_true in Heqo. eapply filterPreservesValues in A.
      specialize (H11 i). rewrite A in H11. rewrite Heqo in H11. rewrite andb_true_r in H11.
      rewrite H11. rewrite H8. apply Eq_Reflexive. apply H1. apply H3. apply H1. apply H3.
    + specialize (H8 i). rewrite Heqo in H8. specialize (H11 i). destruct (sem m i) eqn : ?.
      assert (f' i a0 = false). { eapply filter_sem_false. apply H1. apply H3. apply Heqo0.
      apply Heqo. } rewrite H12 in H11. rewrite andb_false_r in H11. rewrite H11. rewrite H8.
      apply Eq_Reflexive. rewrite H8. rewrite H11. apply Eq_Reflexive.
Qed.  

(*We do not need any such assumptions for filter_comp (the version actually in ContainerAxioms). However,
  we do use Haskell equality and assume {EqLaws a}*)
Lemma filter_comp: forall `{EqLaws a} (f: a -> bool) (f': a -> bool) (m: Map e a) lb ub ,
  Bounded m lb ub ->
  Internal.filter f (Internal.filter f' m) == Internal.filter (fun v => f v && f' v) m = true.  
Proof.
  intros. unfold filter. eapply filterWithKey_comp. apply H1. unfold respectful.
  unfold Proper. intros. reflexivity. unfold respectful. unfold Proper.
  intros. reflexivity.
  - unfold respectful. unfold Proper. intros. reflexivity.
Qed.

(*This (commented out) ContainerAxiom is actually false, as long as the type a is inhabited
  by at least 2 nonequal elements. Since the function we use only depends on the value,
  this actually proves that [filter_insert] is false as well*)
Lemma filterWithKey_insert_false:forall `{EqLaws a} (key: e) (v v1: a), v == v1 = false -> 
~(forall  key v lb ub f m,
  Bounded m lb ub ->
  isUB ub key = true ->
  isLB lb key = true ->
  Proper ((fun (i j : e) => _GHC.Base.==_ i j = true) ==> eq) f ->
  filterWithKey f (insert key v m) ==
  (if (f key v) then
    insert key v (filterWithKey f m)
    else filterWithKey f m) = true).
Proof.
  intros. intro contra. remember (singleton key v1) as m1. remember (fun (x : e) value => value == v1) as f1.
  assert (_GHC.Base.==_ (filterWithKey f1 (insert key v m1))
           (if f1 key v then insert key v (filterWithKey f1 m1) else filterWithKey f1 m1) = true).
  apply (contra _ _ None None).  rewrite Heqm1. unfold singleton. apply BoundedBin.
  apply BoundedTip. apply BoundedTip. solve_Bounds e. solve_Bounds e. simpl. reflexivity. simpl.
  unfold balance_prop. omega. solve_Bounds e. solve_Bounds e. rewrite Heqf1. unfold respectful.
  unfold Proper. intros. reflexivity.
  rewrite Heqm1 in H2. rewrite weak_equals_spec in H2. specialize (H2 key).
  erewrite sem_filter_equiv in H2. unfold singleton in H2. unfold insert at 1 in H2.
  assert (compare key key = Eq) by (order e). rewrite H3 in H2.
  assert (PtrEquality.ptrEq v v1 = false). { destruct (PtrEquality.ptrEq v v1) eqn : ?.
  apply PtrEquality.ptrEq_eq in Heqb. subst. rewrite Eq_Reflexive in H1. inversion H1. reflexivity. }
  rewrite H4 in H2. rewrite andb_false_l in H2. assert (f1 key v = false). { rewrite Heqf1. order a. }
  simpl in H2. rewrite H5 in H2. rewrite H3 in H2. simpl in H2.
  assert (f1 key v1 = true). { rewrite Heqf1.  order a. } rewrite H6 in H2.
  destruct (PtrEquality.ptrEq Tip Tip). simpl in H2. rewrite Eq_Reflexive in H2. simpl in H2.
  inversion H2. simpl in H2. rewrite Eq_Reflexive in H2. simpl in H2. inversion H2.
  apply insert_WF. unfold WF. unfold singleton. apply BoundedBin. apply BoundedTip. apply BoundedTip.
  solve_Bounds e. solve_Bounds e. simpl. reflexivity. unfold balance_prop. simpl. omega. 
  unfold respectful. unfold Proper. intros. rewrite Heqf1. reflexivity. apply filterWithKey_Bounded.
  apply insert_WF. applyDesc e (@singleton_Desc e a). assert (isLB None key = true) by (solve_Bounds e).
  apply H3. assert (isUB None key = true) by (solve_Bounds e). apply H3. apply HB.
  destruct (f1 key v). applyDesc e (@singleton_Desc e a). assert (isLB None key = true) by (solve_Bounds e).
  apply H3. assert (isUB None key = true) by (solve_Bounds e). apply H3. 
  apply insert_WF. apply filterWithKey_Bounded. assumption. applyDesc e (@singleton_Desc e a).
   assert (isLB None key = true) by (solve_Bounds e).
  apply H3. assert (isUB None key = true) by (solve_Bounds e). apply H3. apply filterWithKey_Bounded.
  assumption.
Qed.

(*If we lookup a key in the filtered map and get Some value, we will get the same in the original map.
I needed to added the assumption that f is proper*)
Lemma lookup_filterWithKey:
  forall key value (m: Map e a) f lb ub,
  Bounded m lb ub ->
  Proper ((fun (i j : e) => _GHC.Base.==_ i j = true) ==> eq) f ->
  lookup key (filterWithKey f m) = Some value ->
  lookup key m = Some value.
Proof.
  intros. erewrite lookup_spec in H1. eapply filterPreservesValues in H1.
  erewrite lookup_spec. assumption. eassumption. eassumption. eassumption.
  apply filterWithKey_Bounded. eassumption.
Qed.

(*This says that filtering with the function that always returns true gives the original map. I had
  to change the result to equality of maps and add the {EqLaws} assumption due to this. *)
Lemma filter_true: forall `{EqLaws a} (m: Map e a) lb ub,
  Bounded m lb ub ->
  filter (const true) m == m = true.
Proof.
  intros. unfold filter. eapply filterWithKey_Desc. eassumption.
  unfold respectful. unfold Proper. intros. reflexivity. intros.
  eapply weak_equals_spec; try(eassumption). intros.
  simpl in H4. specialize (H4 i). destruct (sem s i). destruct (sem m i).
  inversion H4; subst; apply Eq_Reflexive. inversion H4. destruct (sem m i).
  inversion H4. apply Eq_Reflexive.
Qed.

(*If a key is in both maps, the the value in the intersection is the value in the first map.*)
Lemma lookup_intersection: forall v1 key (m1: Map e a) (m2: Map e a) lb ub,
  Bounded m1 lb ub ->
  Bounded m2 lb ub ->
  lookup key m1 = Some v1 /\ (exists v2, lookup key m2 = Some v2) <->
  lookup key (intersection m1 m2) = Some v1.
Proof.
  intros. split; intros.
  - applyDesc e (@intersection_Desc e a). erewrite lookup_spec. destruct H1.
    erewrite lookup_spec in H1. specialize (Hsem key). rewrite H1 in Hsem.
    destruct H2. erewrite lookup_spec in H2.  rewrite H2 in Hsem. simpl in Hsem.
    assumption. all: eassumption. 
  - erewrite lookup_spec in H1. erewrite sem_intersect_equiv in H1.
    unfold sem_intersect in H1. destruct (sem m1 key) eqn : ?.
    destruct (sem m2 key) eqn : ?. inversion H1; subst.
    split. erewrite lookup_spec. assumption. eassumption. exists a1.
    erewrite lookup_spec. assumption. eassumption. inversion H1. inversion H1.
    eassumption. eassumption. applyDesc e (@intersection_Desc e a). apply HB.
Qed.

(*If a key is in the first or not in the first but in the second, the union contains
  the same value for that key*)
Lemma lookup_union:
  forall key value (m1: Map e a) m2 lb ub,
  Bounded m1 lb ub ->
  Bounded m2 lb ub ->
  lookup key m1 = Some value \/ (lookup key m1 = None /\ lookup key m2 = Some value) <->
  lookup key (union m1 m2) = Some value.
Proof.
  intros. split; intros. 
  - applyDesc e (@union_Desc e a). erewrite lookup_spec. specialize (Hsem key). destruct H1.
    erewrite lookup_spec in H1. rewrite H1 in Hsem. simpl in Hsem. assumption. eassumption.
    destruct H1. erewrite lookup_spec in H1. erewrite lookup_spec in H2. 
    rewrite H1 in Hsem. rewrite H2 in Hsem. simpl in Hsem. assumption. all: eassumption. 
  - erewrite lookup_spec in H1. erewrite sem_union_equiv in H1. unfold sem_union in H1.
    destruct (sem m1 key) eqn : ?.
    + left. erewrite lookup_spec.  inversion H1; subst; assumption. eassumption.
    + destruct (sem m2 key) eqn : ?. right. split. erewrite lookup_spec. 
      assumption. eassumption. erewrite lookup_spec.  inversion H1; subst; assumption. eassumption.
       inversion H1.
   + apply H.
   + apply H0.
    + applyDesc e (@union_Desc e a). apply HB.
Qed.

(*Note: had to change all to Haskell equality since that is the only information equality of maps
gives us*)
(*Also, unfortunately we need another extra hypothesis because of functional extensionality -
that the negation of P is proper as well*)
(*Also, I don't think this is actually true (the reverse direction) - it seems to
say that if lookup key m == Some value = true, then for all maps m',
we have the 3 conditions, which is not true
TODO: ASk*)
Lemma lookup_partition: forall key value `{EqLaws a} (m: Map e a) m' P lb ub,
  Bounded m lb ub ->
  Bounded m' lb ub ->
  Proper ((fun (i j : e) => _GHC.Base.==_ i j = true) ==> eq) P ->
  Proper ((fun (i j : e) => _GHC.Base.==_ i j = true) ==> eq) (fun a b => negb (P a b)) ->
  ((m' == fst (partitionWithKey P m) = true) \/ (m' == snd (partitionWithKey P m) = true)) /\
  lookup key m' == Some value = true -> lookup key m == Some value = true.
Proof.
  intros. 
  - destruct H5. destruct H5.
    + rewrite (weak_equals_spec m') in H5. specialize (H5 key).
      erewrite fst_partition_sem in H5. erewrite lookup_spec.
      erewrite lookup_spec in H6. assert ((sem_filter m P key) == (Some value) = true).
      eapply Eq_Transitive. apply Eq_Symmetric. apply H5. apply H6. 
      eapply partitionPreservesValues. apply H1. apply H3. apply H7. apply H2. apply H1.
      apply H1. apply H3. apply H2. eapply partitionWithKey_spec. apply H1. apply H3.
      intros. simpl. apply H7. intros. apply H8.
    + rewrite weak_equals_spec in H5. specialize (H5 key).
      erewrite snd_partition_sem in H5. erewrite lookup_spec. erewrite lookup_spec in H6.
      assert (sem_filter m (fun a b => negb (P a b)) key == Some value = true). eapply Eq_Transitive.
      apply Eq_Symmetric. apply H5. apply H6. eapply partitionPreservesValues. apply H1.
      apply H4. apply H7. apply H2. apply H1. apply H1. apply H3. apply H2.
      eapply partitionWithKey_spec. apply H1. apply H3. intros. simpl. apply H7.
      intros. apply H8.
Qed.


(*Need to have proven EqLaws for Map first, since we need to show that left = snd Partition
-> left == snd Partition, but we need equality in the hypothesis because equality of
maps does not imply bounds at all*)

Lemma lookup_partition': forall `{EqLaws a} key value map left right f lb ub,
  Bounded map lb ub ->
  Proper ((fun (i j : e) => _GHC.Base.==_ i j = true) ==> eq) f ->
  Proper ((fun (i j : e) => _GHC.Base.==_ i j = true) ==> eq) (fun a b => negb (f a b)) ->
  lookup key map = Some value ->
  (left, right) = partitionWithKey f map  ->
  lookup key left == Some value = true \/ lookup key right == Some value = true.
Proof.
  intros. assert (left = fst (partitionWithKey f map)). unfold fst. rewrite <- H5.
  reflexivity. assert (right = snd (partitionWithKey f map)). unfold snd. rewrite <- H5.
  reflexivity. assert (A :=H6). assert (A1:=H7).
  assert(forall i, sem left i =  sem (fst (partitionWithKey f map)) i). intros. rewrite H6.
  reflexivity. assert (forall i, sem right i = sem (snd (partitionWithKey f map)) i).
  rewrite H7. intros. reflexivity.
  erewrite lookup_spec in H4. erewrite lookup_spec. erewrite lookup_spec.
  - specialize (H8 key). specialize (H9 key). erewrite fst_partition_sem in H8.
    erewrite snd_partition_sem in H9. destruct (f key value) eqn : ?.
    erewrite sem_filter_in_map in H8. rewrite H8. left. apply Eq_Reflexive.
    apply H1. apply H2. apply H4. apply Heqb.
    assert ((fun a b => negb (f a b)) key value = true). rewrite Heqb. reflexivity.
    erewrite sem_filter_in_map in H9. rewrite H9. right. apply Eq_Reflexive.
    apply H1. apply H3. apply H4. apply H10. apply H1. apply H2. apply H1. apply H2.
  - assert (Bounded right lb ub). rewrite H7. eapply partitionWithKey_spec. apply H1.
    apply H2. intros. apply H10. intros. simpl. apply H11. apply H10.
  - assert (Bounded left lb ub). rewrite H6. eapply partitionWithKey_spec. apply H1.
    apply H2. intros. simpl. apply H10. intros. apply H11. apply H10.
  - apply H1.
Qed. 


(*A key is not in m1 and m2 iff it is not in their union*)
Lemma lookup_union_None: forall key (m1: Map e a) m2 lb ub,
  Bounded m1 lb ub ->
  Bounded m2 lb ub ->
  lookup key m1 = None /\ lookup key m2 = None <-> lookup key (union m1 m2) = None.
Proof.
  intros. split; intros.
  - applyDesc e (@union_Desc e a). erewrite lookup_spec in H1. erewrite lookup_spec in H1. destruct H1.
    specialize (Hsem key). rewrite H1 in Hsem. rewrite H2 in Hsem. erewrite lookup_spec. 
    apply Hsem. apply HB. apply H0. apply H.
  - erewrite lookup_spec in H1. erewrite sem_union_equiv in H1. erewrite lookup_spec.
    erewrite lookup_spec. unfold sem_union in H1. destruct (sem m1 key) eqn : ?.
    inversion H1. destruct (sem m2 key). inversion H1. split; reflexivity.
    apply H0. apply H. apply H. apply H0. applyDesc e (@union_Desc e a). apply HB.
Qed.

(*If the key is in the second map, it is not in the difference*)
Lemma lookup_difference_in_snd: forall key (m1: Map e a) (m2: Map e a) value lb ub,
  Bounded m1 lb ub ->
  Bounded m2 lb ub ->
  lookup key m2 = Some value ->
  lookup key (difference m1 m2) = None.
Proof.
  intros. eapply difference_Desc. apply H. apply H0. intros.
  specialize (H5 key). erewrite lookup_spec in H1. rewrite H1 in H5.
  simpl in H5. erewrite lookup_spec. apply H5. apply H2. apply H0.
Qed.

(*If the key is not in the second map, it is in the difference iff it is in the first map, with the same
value*)
Lemma lookup_difference_not_in_snd: forall key (m1: Map e a) (m2: Map e a) lb ub,
  Bounded m1 lb ub ->
  Bounded m2 lb ub ->
  lookup key m2 = None ->
  lookup key (difference m1 m2) = lookup key m1.
Proof.
  intros. eapply difference_Desc. apply H. apply H0. intros.
  erewrite lookup_spec in H1. specialize (H5 key). rewrite H1 in H5.
  simpl in H5. erewrite lookup_spec. erewrite lookup_spec. apply H5.
  apply H. apply H2. apply H0.
Qed.

(*The stronger claim in ContainerAxioms (using Coq equality) is not true, because we may have rebalancing.
  But we do have the weaker version with Haskell equality (and therefore {EqLaws a}) *)
Lemma delete_commute: forall `{EqLaws a} k1 k2 m lb ub,
  Bounded m lb ub ->
  delete k1 (delete k2 m) == delete k2 (delete k1 m) = true.
Proof.
  intros. eapply delete_Desc. 
  - applyDesc e (@delete_Desc e a). apply HB.
  - intros. eapply delete_Desc.
    + applyDesc e (@delete_Desc e a). apply HB.
    + intros. eapply weak_equals_spec. apply H2. apply H5. intros.
      specialize (H4 i). specialize (H7 i). rewrite H4. rewrite H7.
      eapply delete_Desc. apply H1. intros. eapply delete_Desc. apply H1.
      intros. specialize (H10 i). specialize (H13 i). rewrite H10. rewrite H13.
      destruct (i == k1) eqn : ?; (destruct (i == k2); apply Eq_Reflexive).
Qed.

(*The intersection of an empty map with another map is empty*)
Lemma intersection_empty: forall (m1: Map e a) (m2: Map e a) lb ub,
  Bounded m1 lb ub ->
  Bounded m2 lb ub ->
  m2 = empty ->
  null (intersection m1 m2) = true.
Proof.
  intros. applyDesc e (@intersection_Desc e a). assert (forall i, sem m2 i = None).
  intros. rewrite H1. reflexivity. setoid_rewrite H2 in Hsem. simpl in Hsem.
  rewrite null_empty_iff. apply empty_no_elts. assumption.
Qed.

(*This says that the intersection of m1 and insert key value m2 is empty iff key is not in m1 and
  m1 intersection m2 is empty 
  Have to add hypotheses that key are between bounds so that (insert key value m2) is still Bounded*)
Lemma null_intersection_non_member: forall (m1: Map e a) (m2: Map e a) key value lb ub,
  Bounded m1 lb ub ->
  Bounded m2 lb ub ->
  isLB lb key = true ->
  isUB ub key = true ->
  null (intersection m1 (insert key value m2)) = true <->
  member key m1 = false /\ null (intersection m1 m2) = true.
Proof.
  intros. split; intros.
  - applyDesc e (@intersection_Desc e a). rewrite null_empty_iff in H3. rewrite <- empty_no_elts in H3.
    assert (forall i, sem m1 i &&& sem (insert key value m2) i = None). intros.
    erewrite <- sem_intersection. apply H3. apply H. applyDesc e (@insert_Desc e a). 
    assert (forall i, sem m1 i &&& (SomeIf (i == key) value ||| sem m2 i) = None).
    intros. erewrite <- sem_insert. apply H4. apply H0. assumption. assumption. 
    assert (A:=H5). specialize (H5 key). destruct (sem m1 key) eqn : ?.
    rewrite Eq_Reflexive in H5. simpl in H5. inversion H5. split.
    + erewrite <- notMember_spec in Heqo. unfold notMember in Heqo. rewrite negb_true_iff in Heqo.
      apply Heqo. apply H.
    + assert (forall i, sem s i = None). intros. specialize (Hsem i). rewrite Hsem. specialize (A i).
      destruct (sem m1 i). unfold ando in *. destruct (sem m2   i) eqn : ?.
      destruct (i == key); inversion A. reflexivity.
      destruct (sem m2 i); reflexivity.
      rewrite null_empty_iff. apply empty_no_elts. apply H6.
  - applyDesc e (@insert_Desc e a). applyDesc e (@intersection_Desc e a). destruct H3. setoid_rewrite Hsem in Hsem0.
    rewrite null_empty_iff in H4. rewrite <- empty_no_elts in H4. 
    setoid_rewrite (sem_intersection m1 m2 _ lb ub H H0) in H4. 
    assert (forall i, sem s0 i = None). { intros. destruct (i == key) eqn : ?.
    - assert (sem m1 i = None). erewrite <- notMember_spec. unfold notMember.
      assert (forall a b, a == b = true -> member a m1 = member b m1). { intros.
      destruct (member b m1) eqn : ?. erewrite member_spec. erewrite member_spec in Heqb0.
      destruct Heqb0. exists x. erewrite sem_resp_eq. apply H6. apply H5. apply H.
      apply H. rewrite non_member_lookup. rewrite non_member_lookup in Heqb0.
      erewrite lookup_spec. erewrite lookup_spec in Heqb0. erewrite sem_resp_eq.
      apply Heqb0. apply H5. apply H. apply H. apply H. apply H. }
      apply H5 in Heqb. rewrite Heqb. rewrite H3. reflexivity. apply H. 
      specialize (Hsem0 i). rewrite H5 in Hsem0. rewrite Heqb in Hsem0. simpl in Hsem0.
      apply Hsem0.
    - specialize (Hsem0 i). rewrite Heqb in Hsem0. simpl in Hsem0.
      rewrite H4 in Hsem0. apply Hsem0. }
      rewrite null_empty_iff. apply empty_no_elts. apply H5.
Qed.

(*If m2 intersect m2 is emtpy and m1 \ m2 is empty, then so is m1 intersection m3*)
Lemma disjoint_difference: forall (m1: Map e a) (m2: Map e a) (m3: Map e a) lb ub,
  Bounded m1 lb ub ->
  Bounded m2 lb ub ->
  Bounded m3 lb ub ->
  null (intersection m2 m3) = true ->
  null (difference m1 m2) = true ->
  null (intersection m1 m3) = true.
Proof.
  intros. applyDesc e (@intersection_Desc e a). rewrite null_empty_iff in H2.
  rewrite null_empty_iff in H3. rewrite <- empty_no_elts in H2.
  rewrite <- empty_no_elts in H3. setoid_rewrite (sem_intersection m2 m3 _ lb ub H0 H1) in H2.
  setoid_rewrite (difference_sem m1 m2 lb ub _ H H0) in H3.
  assert (forall i, sem s i = None). { intros. specialize (Hsem i).
  specialize (H2 i). specialize (H3 i). rewrite Hsem. destruct (sem m1 i).
  destruct (sem m3 i). simpl in H2. rewrite H2 in H3. simpl in H3. inversion H3.
  simpl. reflexivity. destruct (sem m3 i). simpl. reflexivity. simpl. reflexivity. }
  rewrite null_empty_iff. eapply empty_no_elts. apply H4.
Qed.

End WF. 