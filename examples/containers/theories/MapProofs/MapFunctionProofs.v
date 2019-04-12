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
Require Import MapProofs.ContainerAxiomsProofs.
Require Import MapProofs.UnionIntersectDifferenceProofs.
(** ** Verification of [map] *)

(*Note: for map_spec, the definition we want is not provable:
[(forall i v, sem m i = Some v <-> sem (mapWithKey f m) i = Some (f i v))]

This is because of three problems
1. Even if two keys k1 and k2 are equal (k1 == k2), this does not guarantee
   that (f k = f k2).
2. We cannot compare the results using Haskell equality because neither a not b
   are required to be members of Eq.
3. If f is not injective, then the (<-) is clearly not true (for example, 
   suppose f = \x -> \y -> 1)

This is not an issue in SetProofs because [Ord b] is a necessary condition for the input and the
map function is defined very differently, leading to an entirely different specification.

There are two solutions to this: 
1. Require that if k == k1 and v == v1, then f k v = f k1 v1, which is not true in general
2. Require that [a] and [b] be members of [Eq], which is also not true in general. We also must
   require that k1 == k2 and v1 == v2 -> f k1 v1 == f k2 v2, which should be true in all cases, since
   this is the definition of a pure function in Haskell.

Both cases are proved below. We prove both cases because it could happen that Haskell equality agrees
with Coq equality on the values but the values are not an instance of [Ord] (and this will be used in
[FMapInterface]

*)

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
  forall {b} {a} {t}  `{Ord t} (H : EqLaws t) (f : t -> a -> b) (m : Map t a) lb ub,
  Bounded m lb ub ->
  (forall k k2 v v2, k == k2 = true -> v = v2 -> f k v = f k2 v2) ->
  (forall i v, sem (mapWithKey f m) i = Some v -> exists value, sem m i = Some value /\ v = f i value).
Proof.
  intros. generalize dependent i. generalize dependent v. induction H2; intros.
  - simpl in H4. inversion H4.
  - simpl in H7. simpl. destruct ( sem (mapWithKey f s1) i ) eqn : ?. apply IHBounded1 in Heqo.
    destruct Heqo. exists x0. destruct H8. rewrite H8. simpl. split. reflexivity. inversion H7; subst.
    reflexivity. simpl in H7.  assert (sem s1 i = None). { erewrite map_none_spec. apply Heqo. apply H2_. }
    rewrite H8. destruct (i == x) eqn : ?. simpl in H7. simpl. exists v. split. reflexivity. inversion H7. 
    apply H3. apply Eq_Symmetric. apply Heqb0. reflexivity. simpl. inversion H7. apply IHBounded2.
    assumption.
Qed.

(*If (k,v) is in the original map, then (k, f k v) is in the new map*)
Lemma map_spec_coq:
  forall {b} {a} {e} `{Ord e} (H: EqLaws e) (f : e -> a -> b) (m : Map e a) lb ub,
  Bounded m lb ub ->
  (forall k k2 v v2, k == k2 = true -> v = v2 -> f k v = f k2 v2) ->
  (forall i v, sem m i = Some v -> sem (mapWithKey f m) i = Some (f i v)).
Proof.
  intros.  generalize dependent i. generalize dependent v. induction H2; intros.
  - inversion H4.
  - simpl. simpl in H7. destruct (sem s1 i) eqn : ?.
    * apply IHBounded1 in Heqo. rewrite Heqo. simpl. inversion H7; subst; reflexivity.
    * assert (sem (mapWithKey f s1) i = None). { erewrite <- map_none_spec. assumption. apply H2_. }
      simpl in H7. rewrite H8. simpl. destruct (i == x) eqn : ?.
      + simpl. simpl in H7. inversion H7; subst. erewrite H3. reflexivity. apply Eq_Symmetric.
        apply Heqb0. reflexivity.
      + simpl. apply IHBounded2. simpl in H7. assumption.
Qed.

(*If f is injective, then (k,v) is in the original map iff (k, f k v) is in the new map*)
Lemma map_spec_coq_injective:
  forall {b} {a} {e} `{Ord e} (H: EqLaws e) (f : e -> a -> b) (m : Map e a) lb ub,
  Bounded m lb ub ->
  (forall k k2 v v2, k == k2 = true -> v = v2 -> f k v = f k2 v2) ->
  (forall k k2 v v2, f k v = f k2 v2 -> k == k2 = true /\ v = v2) ->
  (forall i v, sem m i = Some v <-> sem (mapWithKey f m) i = Some (f i v)).
Proof.
  intros. split.
  - intros. eapply map_spec_coq; eassumption.
  - generalize dependent i. generalize dependent v. induction H2; intros.
    + inversion H2.
    + simpl in H8. simpl. destruct (sem (mapWithKey f s1) i) eqn : ?.
      * assert (A:= Heqo). eapply map_spec_reverse in Heqo. destruct Heqo.
        destruct H9. subst. inversion H8. rewrite H9. simpl.
        apply H4 in H10. destruct H10. subst. reflexivity. assumption. apply H2_.
        apply H3.
      * rewrite <- map_none_spec in Heqo. rewrite Heqo. simpl. simpl in H8. destruct (i == x) eqn : ?.
        -- simpl. simpl in H8. inversion H8. apply H4 in H10. destruct H10; subst; reflexivity.
        -- simpl in H8. simpl. apply IHBounded2. assert (A:= H8). eapply map_spec_reverse in H8.
           assumption. assumption. apply H2_0. assumption.
        -- apply H2_.
Qed.

(*Specification using Haskell Equality. This requires several lemmas to replace the use
of [subst] and [rewrite].*)

(*Haskell equality version of [oro_Some_l]*)
Lemma sem_haskell_eq_some : forall {a} {b} `{EqLaws a} `{EqLaws b} (a1: a) (m : Map a b) b1 o,
  sem m a1 == Some b1 = true ->
  (sem m a1 ||| o) == Some b1 = true.
Proof.
  intros. destruct (sem m a1) eqn : ?.
  - simpl. assumption.
  - inversion H3.
Qed.

(*Haskell equality version of [oro_None_l]*)
Lemma sem_haskell_eq_none: forall {a} {b} `{EqLaws a} `{EqLaws b} (a1: a) (m : Map a b) o,
  sem m a1 == None = true ->
  (sem m a1 ||| o) == o = true.
Proof.
  intros. destruct (sem m a1) eqn : ?.
  - inversion H3.
  - simpl. apply Eq_Reflexive.
Qed.

(*Haskell equality version of [map_none_spec] *)
Lemma map_none_spec_haskell:
  forall {b} {a} {e} `{Ord e} (H : EqLaws e) `{EqLaws a} `{EqLaws b} (f: e -> a -> b) (m: Map e a) lb ub,
  Bounded m lb ub ->
  (forall i, sem m i == None = true <-> sem (mapWithKey f m) i == None = true).
Proof.
  intros. generalize dependent i. induction H6; intros; split; intros.
  - simpl. apply Eq_Reflexive. 
  - simpl. apply Eq_Reflexive. 
  - simpl. simpl in H10. destruct (sem s1 i) eqn : ?. simpl in H10. inversion H10. simpl in H10.
    destruct (i == x) eqn : ?. simpl in H10. inversion H10. simpl in H10. destruct (sem s2 i) eqn : ?.
    inversion H10. apply eq_coq_implies_haskell in Heqo. apply eq_coq_implies_haskell in Heqo0.
    apply IHBounded1 in Heqo. apply IHBounded2 in Heqo0. rewrite  oro_assoc. simpl.
    apply (sem_haskell_eq_none _  _ (sem (mapWithKey f s2) i)) in Heqo.
    eapply Eq_Transitive. apply Heqo. apply Heqo0.
  - simpl. simpl in H10. destruct (sem (mapWithKey f s1) i) eqn : ?. inversion H10.
    destruct (i == x) eqn : ?. inversion H10. destruct (sem (mapWithKey f s2) i) eqn : ?.
    inversion H10. apply eq_coq_implies_haskell in Heqo. apply eq_coq_implies_haskell in Heqo0.
    simpl. rewrite oro_assoc. simpl. apply IHBounded1 in Heqo. apply IHBounded2 in Heqo0.
    apply (sem_haskell_eq_none  _ _  (sem s2 i)) in Heqo. eapply Eq_Transitive.
    apply Heqo. apply Heqo0.
Qed.

(*Haskell equality version of [map_spec_reverse]*)
Lemma map_spec_haskell_reverse : 
  forall {b} {a} {t}  `{Ord t} (H : EqLaws t) `{EqLaws b} `{EqLaws a}
   (f : t -> a -> b) (m : Map t a) lb ub,
  Bounded m lb ub ->
  (forall x1 x2 y1 y2, x1 == x2 = true -> y1 == y2 = true -> f x1 y1 == f x2 y2 = true) ->
  (forall i v, sem (mapWithKey f m) i == Some v = true -> 
    exists value, sem m i == Some value = true /\ v == f i value = true).
Proof.
  intros.
  generalize dependent i. generalize dependent v. induction H6; intros.
  - inversion H8.
  - simpl in H11. simpl. destruct (sem (mapWithKey f s1) i) eqn : ?.
    + assert ( _GHC.Base.==_ (sem (mapWithKey f s1) i) (Some b0) = true). { rewrite Heqo.
      apply Eq_Reflexive. } apply IHBounded1 in H12. destruct H12. exists x0.
      destruct H12. split. rewrite oro_assoc. apply sem_haskell_eq_some. 
      apply H12. simpl in H11. rewrite simpl_option_some_eq in H11. eapply Eq_Transitive.
      apply Eq_Symmetric. apply H11. apply H13.
    + simpl in H11. apply eq_coq_implies_haskell in Heqo. rewrite <- map_none_spec_haskell in Heqo.
      destruct (sem s1 i). inversion Heqo. simpl. destruct (i == x) eqn : ?. simpl in H11.
      simpl. exists v. split. apply Eq_Reflexive. rewrite simpl_option_some_eq in H11. 
      assert ((f x v) == (f i v) = true). { apply H7. apply Eq_Symmetric. apply Heqb0. 
      apply Eq_Reflexive. } eapply Eq_Transitive. apply Eq_Symmetric. apply H11. apply H12.
      simpl. simpl in H11. apply IHBounded2 in H11. apply H11. apply H1. apply H5. apply H3.
      apply H6_.
Qed. 

(*A substitute for [rewrite]: If we know a1 == a3, and we have a1 == a2 in the goal, 
we can prove a2 == a3 instead*)
Lemma rewrite_eq_haskell : forall {a} `{EqLaws a} a1 a2 a3,
  a1 == a2 = true -> (a1 == a3 = true <-> a2 == a3 = true).
Proof.
  intros; split; intros.
  - eapply Eq_Transitive. apply Eq_Symmetric. apply H1. apply H2.
  - eapply Eq_Transitive. apply H1. apply H2.
Qed.

(*Specification for mapWithKey using Haskell equality*)
Lemma map_spec_haskell:
  forall {b} {a} {e} `{Ord e} (H: EqLaws e) `{EqLaws b} `{EqLaws a} (f : e -> a -> b) (m : Map e a) lb ub,
  Bounded m lb ub ->
  (forall x1 x2 y1 y2, x1 == x2 = true -> y1 == y2 = true -> f x1 y1 == f x2 y2 = true) ->
  (forall i v, sem m i == Some v = true -> sem (mapWithKey f m) i == Some (f i v) = true).
Proof.
  intros.  generalize dependent i. generalize dependent v. induction H6; intros.
  - inversion H8.
  - simpl. simpl in H11. destruct (sem s1 i) eqn : ?.
    * apply eq_coq_implies_haskell in Heqo. apply IHBounded1 in Heqo. rewrite oro_assoc.
      eapply sem_haskell_eq_some. simpl in H11. rewrite simpl_option_some_eq in H11.
      assert (f i a0 == f i v0 = true). { apply H7. apply Eq_Reflexive. apply H11. }
      eapply Eq_Transitive. apply Heqo. rewrite simpl_option_some_eq. apply H12.
    * apply eq_coq_implies_haskell in Heqo. erewrite map_none_spec_haskell in Heqo.
      rewrite oro_assoc. eapply (sem_haskell_eq_none i (mapWithKey f s1)
      (SomeIf (_GHC.Base.==_ i x) (f x v) ||| sem (mapWithKey f s2) i)) in Heqo.
      (*rewrite to make the goal simpler*)
      assert (_GHC.Base.==_ (sem (mapWithKey f s1) i ||| 
      (SomeIf (_GHC.Base.==_ i x) (f x v) ||| sem (mapWithKey f s2) i))
      (Some (f i v0)) = true <-> ((SomeIf (_GHC.Base.==_ i x) (f x v) ||| 
      sem (mapWithKey f s2) i) == Some (f i v0) = true)).
      apply rewrite_eq_haskell. apply Heqo. rewrite H12. clear H12.
      destruct (i == x) eqn : ?. simpl. simpl in H11. rewrite simpl_option_some_eq.
      apply H7. apply Eq_Symmetric. apply Heqb0. rewrite simpl_option_some_eq in H11. apply H11.
      simpl. apply IHBounded2. simpl in H11. apply H11. assumption. assumption. assumption.
      apply H6_.
Qed.

(*Once again. if f is injective, we get a stronger claim*)
Lemma map_spec_haskell_injective:
  forall {b} {a} {e} `{Ord e} (H: EqLaws e) `{EqLaws b} `{EqLaws a} (f : e -> a -> b) (m : Map e a) lb ub,
  Bounded m lb ub ->
  (forall x1 x2 y1 y2, x1 == x2 = true -> y1 == y2 = true -> f x1 y1 == f x2 y2 = true) ->
  (forall k k2 v v2, f k v == f k2 v2 = true -> k == k2 = true /\ v = v2) ->
  (forall i v, sem m i == Some v = true <-> sem (mapWithKey f m) i == Some (f i v) = true).
Proof.
  intros. split.
  - intros. eapply map_spec_haskell; eassumption.
  - generalize dependent i. generalize dependent v. induction H6; intros.
    + inversion H6.
    + simpl in H12. simpl. destruct (sem (mapWithKey f s1) i) eqn : ?.
      * assert (A:= Heqo). apply eq_coq_implies_haskell in Heqo. eapply map_spec_haskell_reverse in Heqo.
        destruct Heqo. destruct H13. simpl in H12. 
        apply eq_coq_implies_haskell in A. assert ( (sem (mapWithKey f s1) i) == (Some (f i v0)) = true).
        { eapply Eq_Transitive. apply A. apply H12. } apply IHBounded1 in H15.
         rewrite oro_assoc. eapply sem_haskell_eq_some. apply H15. assumption. assumption.
        apply H5. apply H6_. assumption.
      * apply eq_coq_implies_haskell in Heqo. rewrite <- map_none_spec_haskell in Heqo.
        destruct (sem s1 i). inversion Heqo. simpl. simpl in H12. destruct (i== x) eqn : ?.
        -- simpl. simpl in H12. apply H8 in H12. destruct H12; subst; apply Eq_Reflexive.
        -- simpl. simpl in H12. apply IHBounded2. apply H12.
        -- assumption.
        -- apply H5.
        -- assumption.
        -- apply H6_.
Qed.

Lemma map_no_key_spec :  forall {e} {a} {b} `{Ord e} (f : a -> b) (m : Map e a),
  Internal.map f m = mapWithKey (fun k v => f v) m.
Proof.
  intros. induction m.
  - simpl. rewrite IHm1. rewrite IHm2. reflexivity.
  - simpl. reflexivity.
Qed.