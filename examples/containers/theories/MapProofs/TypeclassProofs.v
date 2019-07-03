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
Require Import MapProofs.MapFunctionProofs.
Require Import MapProofs.ToListProofs.
Require Import MapProofs.UnionIntersectDifferenceProofs.
(** ** [Maps]s with [WF] *)

Definition WFMap  (e : Type) `{Ord e} (a: Type)  : Type := {m : Map e a | WF m}.
Definition pack   {e : Type} {a} `{Ord e} : forall (m : Map e a), WF m -> WFMap e a  := exist _.
Definition unpack {e : Type} {a} `{Ord e} : WFMap e a                  -> Map e a := @proj1_sig _ _.


(** * Type classes *)

(** Because a [Map e a] is only useful if it well-formed, we instantiate
the law classes with a subset type. *)

Require Import Proofs.GHC.Base.

Section TypeClassLaws.
Context {e : Type} {a : Type} {HEq : Eq_ e} {HOrd : Ord e} {HEqLaws : EqLaws e}  {HOrdLaws : OrdLaws e}.


(*First, we need lawful [Eq] and [Ord] instances for pairs*)
Global Instance EqLaws_Pair {a} {b} `{EqLaws a} `{EqLaws b} : EqLaws (a * b).
Proof.
  constructor.
  - unfold "==". unfold Eq_pair___. unfold op_zeze____. unfold eq_pair. unfold ssrbool.reflexive.
    intros. destruct x. unfold is_true. rewrite andb_true_iff. split; apply Eq_Reflexive.
  - unfold "==". unfold Eq_pair___. unfold op_zeze____. unfold eq_pair. unfold ssrbool.symmetric.
    intros. destruct x. destruct y. rewrite prop_bool. apply Eq_Tuple_Sym.
  - unfold "==". unfold Eq_pair___. unfold op_zeze____. unfold eq_pair. unfold ssrbool.transitive.
    intros. destruct x. destruct y. destruct z. unfold is_true in *.
    rewrite andb_true_iff in H3. rewrite andb_true_iff in H4. destruct H3. destruct H4.
    eapply Eq_Tuple_Trans. rewrite eq_tuple_prop. split. apply H3. apply H5. rewrite eq_tuple_prop.
    split. apply H4. apply H6.
  - intros. unfold "==", "/=". unfold Eq_pair___. unfold op_zeze____ , op_zsze____ .
    destruct (eq_pair x y). reflexivity. reflexivity.
Qed.

(*If a and b are lawful members of [Ord], then so is a * b*)
Instance OrdLaws_Pair {a} {b} `{OrdLaws a} `{OrdLaws b} : OrdLaws (a * b).
Proof.
  constructor.
  - intros. destruct a1. destruct b0. unfold "<=", "==" in *. unfold Ord_pair___, Eq_pair___ in *.
    unfold ord_default, op_zeze____  in *. simpl in *. rewrite andb_true_iff.  rewrite negb_true_iff in *. 
    destruct (compare a2 a1) eqn : ?. destruct (compare b0 b1) eqn : ?.
    rewrite compare_Eq in Heqc. rewrite compare_Eq in Heqc0. split.
    apply Eq_Symmetric. apply Heqc. apply Eq_Symmetric. apply Heqc0.
    inversion Heqc0. inversion H1. rewrite compare_Eq in Heqc. apply Eq_Symmetric in Heqc.
    unfold is_true in Heqc. rewrite <- compare_Eq in Heqc. rewrite Heqc in H2.
    inversion H0. apply Ord_compare_Gt in Heqc0. apply Ord_compare_Lt in Heqc0.
    rewrite Heqc0 in H2. inversion H2. inversion H1. inversion H. rewrite Ord_compare_Gt in Heqc.
    apply Ord_compare_Lt in Heqc. rewrite Heqc in H2. inversion H2.
  - intros. destruct a1. destruct c. destruct b0. unfold "<=" in *. unfold Ord_pair___  in *.
    unfold compare_pair in *. unfold ord_default in *. simpl in *. rewrite negb_true_iff in *.
    repeat (try (destruct (compare a2 a1) eqn : ?); try (destruct (compare b2 b1) eqn : ?);
    try (destruct (compare a3 a1) eqn : ?); try (destruct (compare b0 b1) eqn : ?);
    try (destruct (compare a2 a3) eqn : ?); try (destruct (compare b2 b0) eqn : ?); 
    try (order b); try (order a0)).
  - intros. destruct a1. destruct b0. unfold "<=" in *. unfold Ord_pair___ in *. unfold compare_pair in *.
    unfold ord_default. unfold ord_default in *. simpl. rewrite negb_true_iff. rewrite negb_true_iff.
    destruct (compare a2 a1) eqn : ?. assert (compare a1 a2 = Eq) by (order a0). rewrite H1.
    destruct (compare b0 b1) eqn : ?. left. reflexivity. right. assert (compare b1 b0 <> Lt) by (order b).
    destruct (compare b1 b0). reflexivity. contradiction. reflexivity. left. reflexivity.
    right. destruct (compare a1 a2) eqn : ?. order a0. order a0. reflexivity.
    left. reflexivity.
  - intros. unfold compare.   unfold "<=" in *. unfold Ord_pair___ in *. unfold compare_pair in *.
    unfold ord_default. simpl. rewrite negb_false_iff. destruct a1. destruct b0. 
    split; intros. destruct (compare a1 a2). rewrite H1. reflexivity. reflexivity. inversion H1.
    destruct (compare a1 a2). destruct (compare b1 b0). inversion H1. reflexivity. inversion H1.
    reflexivity. inversion H1.
  - intros. unfold compare. unfold "==". unfold Ord_pair___ , Eq_pair___ . unfold compare_pair,op_zeze____ .
    unfold ord_default, eq_pair. simpl. destruct a1. destruct b0. split; intros. destruct (compare a1 a2) eqn : ?.
    inversion H. rewrite Ord_compare_Eq in Heqc. inversion H0. rewrite Ord_compare_Eq0 in H1. rewrite andb_true_iff.
    split; assumption. inversion H1. inversion H1. rewrite andb_true_iff in H1. destruct H1.
    inversion H. inversion H0. apply Ord_compare_Eq in H1. apply Ord_compare_Eq0 in H2. rewrite H1. assumption.
  - intros. unfold compare. unfold Ord_pair___ , "<=". unfold compare_pair. unfold ord_default. simpl.
    destruct a1. destruct b0. split; intros. rewrite negb_false_iff.  
    destruct (compare a1 a2) eqn : ?. assert (compare a2 a1 = Eq) by (order a0). rewrite H2.
    assert (compare b0 b1 = Lt) by (order b). rewrite H3. reflexivity. inversion H1. inversion H1.
    assert (compare a2 a1 = Lt) by (order a0). rewrite H2. reflexivity.
    rewrite negb_false_iff in H1. destruct (compare a2 a1) eqn : ?.
    assert (compare a1 a2 = Eq) by (order a0). rewrite H2. destruct (compare b0 b1) eqn : ?.
    inversion H1. order b. inversion H1. assert (compare a1 a2 = Gt) by (order a0). rewrite H2.
    reflexivity. inversion H1.
  - intros. unfold "<", "<=". unfold Ord_pair___.  unfold compare_pair; unfold ord_default; simpl.
    rewrite negb_involutive. reflexivity.
  - intros. unfold "<=", ">=". unfold Ord_pair___. unfold compare_pair; unfold ord_default; simpl.
    reflexivity.
  - intros. unfold ">", "<=". unfold Ord_pair___.  unfold compare_pair; unfold ord_default; simpl.
    rewrite negb_involutive. reflexivity.
Qed.


(** ** Verification of [Eq] *)
Global Program Instance Eq_Map_WF `{ Eq_ a } : Eq_ (WFMap e a) := fun _ k => k
  {| op_zeze____ := @op_zeze__ (Map e a) _
   ; op_zsze____ := @op_zsze__ (Map e a) _
  |}.

Local Ltac unfold_WFMap_Eq :=
  unfold "_==_", "_/=_", Eq_Map_WF, op_zeze____; simpl;
  unfold "_==_", "_/=_", Eq___Map; simpl;
  unfold Internal.Eq___Map_op_zeze__, Internal.Eq___Map_op_zsze__ ; simpl.

Global Instance EqLaws_Map `{EqLaws a} : EqLaws (WFMap e a).
Proof.
  constructor.
  - unfold_WFMap_Eq. unfold ssrbool.reflexive. intros. unfold is_true. rewrite andb_true_iff.
    split. apply Eq_Reflexive. apply Eq_Reflexive.
  - unfold_WFMap_Eq. unfold ssrbool.symmetric. intros. rewrite prop_bool. split; intros; rewrite andb_true_iff in *.
    + destruct H1. split; apply Eq_Symmetric; assumption.
    + destruct H1. split; apply Eq_Symmetric; assumption.
  - unfold_WFMap_Eq. unfold ssrbool.transitive. intros. unfold is_true in *. rewrite andb_true_iff in *.
    destruct H1. destruct H2. split. eapply Eq_Transitive. apply H1. apply H2. eapply Eq_Transitive.
    apply H3. apply H4.
  - intros. unfold_WFMap_Eq. unfold Internal.Eq___Map_op_zeze__. rewrite negb_involutive . reflexivity.
Qed.

(** ** Verification of [ord] *)
Global Program Instance Ord_Map_WF `{OrdLaws a} : Ord (WFMap e a) := fun _ k => k
  {| op_zlze____ := @op_zlze__ (Map e a) _ _
   ; op_zgze____ := @op_zgze__ (Map e a) _ _
   ; op_zl____ := @op_zl__ (Map e a) _ _
   ; op_zg____ := @op_zg__ (Map e a) _ _
   ; compare__ := @compare (Map e a) _ _
   ; min__ := @min (Map e a) _ _
   ; max__ := @max (Map e a) _ _
  |}.
Next Obligation.
  destruct x. destruct x0. simpl.
  unfold max. unfold Ord__Map. unfold max__. unfold Internal.Ord__Map_max.
   destruct Internal.Ord__Map_op_zlze__; assumption.
Qed.
Next Obligation.
  destruct x. destruct x0. simpl.
  unfold min, Ord__Map, min__, Internal.Ord__Map_min.
  destruct (Internal.Ord__Map_op_zlze__ _ _); assumption.
Qed.


Lemma compare_neq_gt_iff_le {t} `{OrdLaws t} (l1 l2 : t) :
  (compare l1 l2 /= Gt = true) <-> (l1 <= l2) = true.
Proof.
  rewrite Neq_inv, negb_true_iff.
  destruct (_ <= _) eqn:LE; simpl.
  - split; trivial; intros _.
    enough ((compare l1 l2 == Gt) = false <-> compare l1 l2 <> Gt) as OK.
    + now apply OK; rewrite Ord_compare_Gt, LE.
    + now rewrite (ssrbool.rwP (Eq_eq _ Gt)); unfold is_true; rewrite not_true_iff_false.
  - now rewrite <-Ord_compare_Gt in LE; rewrite LE.
Qed.

Lemma WFMap_eq_size_length' (m : WFMap e a) :
  Data.Map.Internal.size (proj1_sig m) = Z.of_nat (Datatypes.length (toAscList (proj1_sig m))).
Proof.
  destruct m as [m WFm]; unfold "==", Eq_Map_WF; simpl.
  rewrite size_size; erewrite size_spec; trivial; exact WFm.
Qed.

Lemma WFMap_eq_size_length (m : WFMap e a) :
  Data.Map.Internal.size (unpack m) = Z.of_nat (Datatypes.length (toAscList (unpack m))).
Proof. apply WFMap_eq_size_length'. Qed.

Local Ltac unfold_WFMap_Ord :=
  unfold "_<=_", "_<_", "_>=_", "_>_", compare, Ord_Map_WF; simpl;
  unfold "_<=_", "_<_", "_>=_", "_>_", compare, Ord__Map; simpl;
  unfold Data.Map.Internal.Ord__Map_op_zlze__, (*Data.Map.Internal.Ord_Map_op_zl__*)
         Data.Map.Internal.Ord__Map_op_zgze__, (*Data.Map.Internal.Ord_Map__op_zg__*)
         Data.Map.Internal.Ord__Map_compare; simpl.

Local Ltac hideToAscList a :=
  let la := fresh "l" a in
  let EQ := fresh "EQ"  in
  remember (toAscList (unpack a)) as la eqn:EQ; try clear a EQ.

Global Instance OrdLaws_Map `{OrdLaws a} : OrdLaws (WFMap e a).
Proof.
  constructor; unfold_WFMap_Eq; unfold_WFMap_Ord.
  - intros a0 b; rewrite !compare_neq_gt_iff_le => LEab LEba.
    generalize (Ord_antisym _ _ LEab LEba) => EQab.
    match goal with |- context[?b = true] => fold (is_true b) end.
    rewrite <-(ssrbool.rwP ssrbool.andP); split; trivial.
    rewrite !WFMap_eq_size_length'; rewrite <-(ssrbool.rwP (Eq_eq _ _)).
    rewrite Nat2Z.inj_iff; apply eqlist_length, EQab.
  - intros a0 b c; rewrite !compare_neq_gt_iff_le; order (list (e * a)).
  - intros a0 b; rewrite !compare_neq_gt_iff_le; apply Ord_total.
  - intros a0 b; rewrite Ord_compare_Lt,Neq_inv,negb_false_iff.
    match goal with |- context[?b = true] => fold (is_true b) end.
    rewrite <-(ssrbool.rwP (Eq_eq _ _)).
    order (list (e * a)).
  - intros a0 b; rewrite Ord_compare_Eq.
    repeat match goal with |- context[?b = true] => fold (is_true b) end.
    rewrite <-(ssrbool.rwP ssrbool.andP), <-(ssrbool.rwP (Eq_eq _ _)).
    split; [intros EQ | intros [LIST EQ]]; rewrite EQ; trivial.
    split; trivial. rewrite !WFMap_eq_size_length'.
    rewrite Nat2Z.inj_iff; apply eqlist_length, EQ. apply Eq_refl.
    apply Eq_refl.
  - intros a0 b; rewrite Ord_compare_Gt,Neq_inv,negb_false_iff.
    match goal with |- context[?b = true] => fold (is_true b) end.
    rewrite <-(ssrbool.rwP (Eq_eq _ _)).
    order (list (e * a)).
  - intros. unfold Internal.Ord__Map_op_zl__, "/=". unfold Internal.Ord__Map_compare, 
    Eq_comparison___. unfold op_zsze____ . rewrite negb_involutive. destruct (compare _ _) eqn : ?;
    unfold eq_comparison; unfold proj1_sig in *; destruct a0; destruct b. 
    assert (compare (toAscList x0) (toAscList x) = Eq) by (order (list (e * a))). rewrite H0.
    reflexivity.  assert (compare (toAscList x0) (toAscList x) = Gt) by (order (list (e * a))).
    rewrite H0. reflexivity. assert (compare (toAscList x0) (toAscList x) = Lt) by (order (list (e * a))).
    rewrite H0. reflexivity.
  - now intros a0 b; rewrite !Neq_inv,                  compare_flip; destruct (compare _ _).
  - intros. unfold Internal.Ord__Map_op_zg__ , "/=". unfold Internal.Ord__Map_compare, Eq_comparison___.
    unfold op_zsze____ . rewrite negb_involutive. reflexivity.
Qed.

(** ** Verification of [Semigroup] *)

Ltac unfold_Monoid_Map :=
  unfold mappend, mconcat, mempty, Monoid__Map, mappend__, mconcat__, mempty__,
         Internal.Monoid__Map_mappend, Internal.Monoid__Map_mconcat, Internal.Monoid__Map_mempty,
         op_zlzlzgzg__,  Semigroup__Map, op_zlzlzgzg____,
         Internal.Semigroup__Map_op_zlzlzgzg__
    in *.

Global Program Instance Semigroup_WF : Semigroup (WFMap e a) := fun _ k => k
  {| op_zlzlzgzg____  := @mappend (Map e a) _ _ |}.
Next Obligation.
  destruct x as [s1 HB1], x0 as [s2 HB2]. simpl.
  unfold_Monoid_Map.
  eapply union_Desc; try eassumption. intuition.
Qed.

(*I'm not sure why, but SemigroupLaws requires that (WFMap e a) be a member of [Eq], so we need
the [EqLaws a] condition*)
Global Instance SemigroupLaws_Map `{EqLaws a} : SemigroupLaws (WFMap e a).
Proof.
  constructor.
  intros.
  destruct x as [s1 HB1], y as [s2 HB2], z as [s3 HB3].
  unfold op_zeze__, Eq_Map_WF, op_zeze____, proj1_sig.
  unfold op_zlzlzgzg__, Semigroup_WF, op_zlzlzgzg____.
  unfold mappend, Monoid__Map, mappend__.
  unfold Internal.Monoid__Map_mappend.
  unfold proj1_sig.
  unfold op_zlzlzgzg__, Semigroup__Map, op_zlzlzgzg____.
  unfold Internal.Semigroup__Map_op_zlzlzgzg__.
  eapply (union_Desc s1 s2); try eassumption. intros s12 Hs12 _ Hsem12.
  eapply (union_Desc s2 s3); try eassumption. intros s23 Hs23 _ Hsem23.
  eapply (union_Desc s1 s23); try eassumption. intros s1_23 Hs1_23 _ Hsem1_23.
  eapply (union_Desc s12 s3); try eassumption. intros s12_3 Hs12_3 _ Hsem12_3.
  rewrite -> weak_equals_spec by eassumption.
  intro i. rewrite Hsem12_3,Hsem1_23,Hsem23,Hsem12.
  rewrite oro_assoc. apply Eq_Reflexive.
Qed.

(** ** Verification of [Monoid] *)

Global Program Instance Monoid_WF : Monoid (WFMap e a) := fun _ k => k
  {| mempty__   := @mempty (Map e a) _ _
   ; mappend__  := @mappend (Map e a) _ _
   ; mconcat__  xs := @mconcat (Map e a) _ _ (List.map (fun x => unpack x) xs)
  |}.
Next Obligation.
  destruct x as [s1 HB1], x0 as [s2 HB2]. simpl. unfold mappend.
  unfold_Monoid_Map.
  eapply union_Desc; try eassumption. intuition.
Qed.
Next Obligation.
  unfold mconcat.
  unfold_Monoid_Map.
  eapply unions_Desc.
  * induction xs.
    + constructor.
    + destruct a0 as [s HB]. simpl. constructor. apply HB. apply IHxs.
  * intros. assumption.
Qed.
Next Obligation.
  unfold mempty. unfold Monoid__Map. unfold mempty__. unfold Internal.Monoid__Map_mempty.
  eapply empty_Desc. intros. apply H0.
Qed.

(*Some lemmas about [map] for functor*)
Lemma map_preserves_size: forall {b} {c} (m : Map e b) (f : b -> c) lb ub,
  Bounded m lb ub ->
  size m = size (map f m).
Proof.
  intros. inversion H.
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed.

Lemma map_bounded: forall {b} {c} (m : Map e b) (f: b -> c) lb ub,
  Bounded m lb ub ->
  Bounded (map f m) lb ub.
Proof.
  intros. induction H.
  - simpl. apply BoundedTip.
  - simpl. apply BoundedBin. apply IHBounded1. apply IHBounded2. apply H1.
    apply H2. erewrite <- map_preserves_size. erewrite <- map_preserves_size. apply H3.
    apply H0. apply H. erewrite <- map_preserves_size. erewrite <- map_preserves_size.
    apply H4. apply H0. apply H.
Qed. 

Lemma map_preserves_WF : forall {b} {c} (m : Map e b) (f : b -> c),
  WF m -> WF (map f m).
Proof. 
  intros. unfold WF in *. apply map_bounded. apply H.
Qed. 


Definition Functor__Map_fmap 
   : forall {a} {b}, (a -> b) -> (Map e) a -> (Map e) b :=
  fun {a} {b} => fun f m => map f m.

Local Definition Functor__map_op_zlzd__
   : forall {a} {b}, a -> Map e b -> Map e a :=
  fun {a} {b} => Functor__Map_fmap ∘ const.

Lemma const_WF: forall {b} {a: Type} (x : a) (m: Map e b),
  WF m -> WF (map (const x) m).
Proof.
  intros. apply map_preserves_WF. apply H. 
Qed.


Global Program Instance Functor_Map : Functor (WFMap e) :=
  fun _ k => 
  k {| GHC.Base.fmap__ := fun {a} => @fmap (Map e) _ _ ;
        GHC.Base.op_zlzd____ := fun {a} {b} x => @fmap (Map e) _ b a (@const a b _) |}.
Next Obligation.
  unfold proj1_sig. destruct x1. apply map_preserves_WF. apply w.
Qed.
Next Obligation.
  unfold proj1_sig. destruct x0. apply const_WF. apply w.
Qed.

Global Instance FunctorLaws_MapWF: FunctorLaws (WFMap e).
  constructor.
  - intros. destruct x. unfold fmap. unfold fmap__.  unfold Functor_Map. 
    apply ProofIrrelevance.ProofIrrelevanceTheory.subset_eq_compat. unfold proj1_sig.
    unfold fmap. unfold fmap__. unfold Functor__Map. unfold Internal.Functor__Map_fmap.
    induction w. 
    + simpl. reflexivity.
    + simpl. rewrite IHw1. rewrite IHw2. reflexivity.
  - intros. destruct x. unfold fmap in *. unfold fmap__ in *.
    unfold Functor_Map in *. apply ProofIrrelevance.ProofIrrelevanceTheory.subset_eq_compat.
    unfold proj1_sig in *. unfold fmap. unfold Functor__Map. unfold fmap__. 
    unfold Internal.Functor__Map_fmap. simpl. induction w.
    + simpl. reflexivity.
    + simpl. rewrite IHw1. rewrite IHw2. reflexivity.
Qed. 


(** ** Verification of [Eq1] - NOT COMPLETE*)
Require Import Data.Functor.Classes.
Require Import Proofs.Data.Functor.Classes.
Global Instance Eq1Laws_list: Eq1Laws list (@Eq_list).
Proof.
  constructor.
  intros ? ? xs ys.
  unfold liftEq, Eq1__list, liftEq__.
  replace (xs == ys) with (eqlist xs ys) by reflexivity.
  revert ys.
  induction xs; intros ys.
  * reflexivity.
  * destruct ys.
    - reflexivity.
    - simpl. rewrite IHxs. reflexivity.
Qed.


(*copied from Internal.v for now*)
Local Definition Eq2__Map_liftEq2
   : forall {a} {b} {c} {d},
     (a -> b -> bool) -> (c -> d -> bool) -> Map a c -> Map b d -> bool :=
  fun {a} {b} {c} {d} =>
    fun eqk eqv m n =>
      andb (size m GHC.Base.== size n) (Data.Functor.Classes.liftEq
            (Data.Functor.Classes.liftEq2 eqk eqv) (toList m) (toList n)).

(*Eq2 does not seem to have any laws yet*)
Global Instance Eq2_Map : Eq2 (Map).
Proof.
unfold Eq2. intros. apply X. apply Eq2__Dict_Build.
intros. eapply Eq2__Map_liftEq2. apply X0. apply X1.
apply X2. apply X3.
Qed.

End TypeClassLaws.
