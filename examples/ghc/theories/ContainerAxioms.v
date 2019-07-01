(* When these things get proven, they ought to move to [containers] *)

From Coq Require Import ssreflect ssrfun ssrbool.

Require Import Coq.Logic.ProofIrrelevance.

Require Import GHC.Base.

Require Import Proofs.Prelude.
Require Import MapProofs.ContainerAxiomsProofs.
Require IntMap.

Ltac destruct_IntMap :=
  repeat match goal with
  | [x : IntMap.IntMap _ |- _ ] =>
    destruct x; try solve [simpl; eassumption]
  end.

Lemma member_eq : forall A k k' (i : IntMap.IntMap A),
    k == k' ->
    IntMap.member k i = IntMap.member k' i.
Proof.
  intros. cbn in H. apply N.eqb_eq in H; subst. reflexivity.
Qed.

Lemma lookup_insert : forall A key (val:A) i, 
    IntMap.lookup key (IntMap.insert key val i) = Some val.
Proof.
  intros. eapply lookup_insert'. destruct_IntMap.
Qed.

Lemma lookup_singleton_key : forall {A} x y (a b : A),
    IntMap.lookup x (IntMap.singleton y a) = Some b -> x == y.
Proof.
  unfold IntMap.singleton, IntMap.lookup. simpl. intros.
  destruct (compare x y) eqn:Hc;
    rewrite Hc in H; inversion H.
  apply Bounds.compare_Eq => //.
Qed.

Lemma lookup_singleton_val : forall {A} x y (a b : A),
    IntMap.lookup x (IntMap.singleton y a) = Some b -> a = b.
Proof.
  unfold IntMap.singleton, IntMap.lookup. simpl. intros.
  destruct (compare x y) eqn:Hc;
    rewrite Hc in H; inversion H.
  reflexivity.
Qed.

Lemma lookup_insert_neq : 
  forall b key1 key2 (val:b) m, 
    key1 <> key2 ->
    IntMap.lookup key1 (IntMap.insert key2 val m) = IntMap.lookup key1 m.
Proof.
  intros. apply lookup_insert_neq'; destruct_IntMap.
  apply /Eq_eq; assumption.
Qed.

Lemma member_insert : forall A k k' v (i : IntMap.IntMap A),
IntMap.member k (IntMap.insert k' v i) =
  (k == k') || IntMap.member k i.
Proof.
  intros. apply member_insert'; destruct_IntMap.
Qed.

Lemma delete_eq : forall key b (i : IntMap.IntMap b),
    IntMap.lookup key (IntMap.delete key i) = None.
Proof.
  intros. eapply delete_eq; destruct_IntMap.
Qed.

Lemma delete_neq : forall key1 key2 b (i : IntMap.IntMap b),
    key1 <> key2 ->
    IntMap.lookup key1 (IntMap.delete key2 i) = IntMap.lookup key1 i.
Proof.
  intros. eapply delete_neq; destruct_IntMap.
  apply /Eq_eq =>//.
Qed.

Lemma member_delete_neq : forall k1 k2 b (i: IntMap.IntMap b), k1 <> k2 ->
  IntMap.member k2 (IntMap.delete k1 i) =
  IntMap.member k2 i.
Proof.
  intros. eapply member_delete_neq; destruct_IntMap.
  apply /Eq_eq =>//.
Qed.

Lemma non_member_lookup :
   forall (A : Type)
     (key : Internal.Key) 
     (i : IntMap.IntMap A),
   (IntMap.member key i = false) <-> (IntMap.lookup key i = None).
Proof.
  intros. eapply non_member_lookup.
  destruct_IntMap.
Qed.

Lemma lookup_eq : forall A k k' (i : IntMap.IntMap A),
    k == k'->
    IntMap.lookup k i = IntMap.lookup k' i.
Proof.
  intros. eapply lookup_eq. assumption.
Qed.

Lemma member_lookup :
   forall (A : Type)
     (key : Internal.Key) 
     (i : IntMap.IntMap A),
   (is_true (IntMap.member key i)) <-> (exists val, IntMap.lookup key i = Some val).
Proof.
  intros. eapply member_lookup. destruct_IntMap.
Qed.

Lemma null_empty : forall A,
    (@IntMap.null A IntMap.empty).
Proof.
  intros. cbv. reflexivity.
Qed.


(* ------------------------------------------------------- *)

Lemma member_union :
   forall (A : Type)
     (key : Internal.Key) 
     (i i0 : IntMap.IntMap A),
   (IntMap.member key (IntMap.union i i0)) = 
   (IntMap.member key i0 || IntMap.member key i).
Proof.
  intros. eapply member_union; destruct_IntMap.
Qed.
  
(*
Axiom union_nil_l : forall A (i : IntMap.IntMap A),
    IntMap.union IntMap.Nil i = i.

Axiom union_nil_r : forall A (i : IntMap.IntMap A),
    IntMap.union i IntMap.Nil = i.
*)
(*
Axiom difference_self : forall A (i : IntMap.IntMap A),
    IntMap.difference i i = IntMap.empty.
*)

Lemma difference_nil_r : forall A B (i : IntMap.IntMap A),
    IntMap.difference i (@IntMap.empty B) = i.
Proof.
  intros. destruct_IntMap.
  unfold IntMap.empty, IntMap.difference.
  apply subset_eq_compat.
  eapply difference_nil_r.
  eassumption.
Qed.
  
Lemma difference_nil_l : forall B A (i : IntMap.IntMap A),
    IntMap.difference (@IntMap.empty B) i = 
    (@IntMap.empty B).
Proof.
  intros. destruct_IntMap.
  unfold IntMap.empty, IntMap.difference.
  apply subset_eq_compat.
  eapply difference_nil_l.
  eassumption.
Qed.
  
(*
Axiom difference_Tip_member:
  forall A (i : IntMap.IntMap A) (n : IntMap.Key),
    (IntMap.member n i) ->
    forall x:A, IntMap.difference
        (IntMap.Tip n x) i = IntMap.Nil.

Axiom difference_Tip_non_member: 
    forall A (i : IntMap.IntMap A) (n : IntMap.Key),
      (IntMap.member n i) = false ->
      forall x : A, IntMap.difference (IntMap.Tip n x) i =
        IntMap.Tip n x.
*)

(* Do we need to know that f respects == for A ? *)
Lemma filter_comp : forall A `{EqLaws A} f f' (i : IntMap.IntMap A),
    IntMap.filter f (IntMap.filter f' i) ==
    IntMap.filter (fun v => f v && f' v) i.
Proof.
  intros. eapply filter_comp. destruct_IntMap.
Qed.  

(*
Axiom filter_insert: forall A f key (v:A) i,
  IntMap.filter f (IntMap.insert key v i) =
  (if (f v)
   then IntMap.insert key v (IntMap.filter f i)
   else IntMap.filter f i).
*)

Lemma lookup_filterWithKey : 
  forall b key (val:b) m f, IntMap.lookup key (IntMap.filterWithKey f m) = Some val ->
                       IntMap.lookup key m = Some val.
Proof.
  intros. eapply lookup_filterWithKey with (f0:=f); destruct_IntMap.
  intros i j Heq. f_equal. apply /Eq_eq. assumption.
Qed.

Lemma filter_true : forall (A:Type) `{EqLaws A} (m:IntMap.IntMap A), 
    IntMap.filter (const true) m == m.
Proof.
  intros. eapply filter_true; destruct_IntMap.
Qed.

(** TODO: a more general theorem is needed (where the second map can
    have a different value type. *)
Lemma lookup_intersection :
  forall a key (val1:a) m1 m2, 
    IntMap.lookup key m1 = Some val1 /\
    (exists (val2:a), IntMap.lookup key m2 = Some val2) <-> 
    IntMap.lookup key (IntMap.intersection m1 m2) = Some val1.
Proof.
  intros. eapply lookup_intersection; destruct_IntMap.
Qed.

Lemma lookup_union :
  forall (A:Type) key (val:A) (m1 m2: IntMap.IntMap A), 
    (IntMap.lookup key m1 = Some val \/ (IntMap.lookup key m1 = None /\ IntMap.lookup key m2 = Some val)) <->
    IntMap.lookup key (IntMap.union m1 m2) = Some val.
Proof.
  intros. eapply lookup_union; destruct_IntMap.
Qed.

Lemma lookup_partition :
  forall (A:Type) key (val:A) (m m': IntMap.IntMap A) (P: A -> bool), 
    ((m' = fst (IntMap.partition P m) \/
      m' = snd (IntMap.partition P m)) /\
     IntMap.lookup key m' = Some val) ->
    IntMap.lookup key m  = Some val.
Proof.
  intros. destruct_IntMap.
  eapply lookup_partition with (P0:=P); try eassumption.
  unfold IntMap.partition in H; intuition.
  - left. inversion H; reflexivity.
  - right. inversion H; reflexivity.
Qed.

(*
Axiom lookup_partition :
  forall (key : IntMap.Key) (b : Type) (i left right: IntMap b)(f:b -> bool)(y : b), 
    lookup key i = Some y ->
    (left, right) = partition f i -> 
    lookup key left = Some y \/ lookup key right = Some y.    
*)
(*
Axiom lookup_union_None:
  forall (A : Type)
    (key : IntMap.Key)
    (m1 m2 : IntMap.IntMap A),
    IntMap.lookup key m1 = None /\
    IntMap.lookup key m2 = None <->
    IntMap.lookup key
             (IntMap.union m1 m2) = None.
*)

Axiom lookup_difference_in_snd:
  forall (key : Internal.Key) (b : Type) (i i': IntMap.IntMap b) (y:b),
    IntMap.lookup key i' = Some y -> 
    IntMap.lookup key (IntMap.difference i i') = None.

Axiom lookup_difference_not_in_snd:
  forall (key : Internal.Key) (b : Type) (i i': IntMap.IntMap b)(y:b),
    IntMap.lookup key i' = None ->
    IntMap.lookup key (IntMap.difference i i') = IntMap.lookup key i.


(* This is a pretty strong property about the representation of 
   IntMaps. I hope that it is true. *)
Axiom delete_commute :
  forall (A : Type)
    (kx ky : Internal.Key) 
    (i : IntMap.IntMap A),
  IntMap.delete ky (IntMap.delete kx i) =
  IntMap.delete kx (IntMap.delete ky i).

Axiom intersection_empty :
  forall A B (i : IntMap.IntMap A) (j : IntMap.IntMap B),
    (j = IntMap.empty) ->
    IntMap.null (IntMap.intersection i j).

Axiom null_intersection_non_member: forall b k (v : b)(i1 i2 : IntMap.IntMap b),
  IntMap.null
    (IntMap.intersection i1 (IntMap.insert k v i2)) <->
  IntMap.member k i1 = false /\
  IntMap.null (IntMap.intersection i1 i2).

Axiom disjoint_difference: forall  b (i1 i2 i3 : IntMap.IntMap b),
  IntMap.null (IntMap.intersection i2 i3) ->
  IntMap.null (IntMap.difference i1 i2) ->
  IntMap.null (IntMap.intersection i1 i3).


Axiom null_intersection_eq : forall b (x1 x2 y1 y2 : IntMap.IntMap b), 
  (forall a, IntMap.member a x1 <-> IntMap.member a y1) ->
  (forall a, IntMap.member a x2 <-> IntMap.member a y2) ->
  IntMap.null (IntMap.intersection x1 x2) = IntMap.null (IntMap.intersection y1 y2).




(*
This is a QuickChick setup to test the above axioms
(as bugs easily lurk there).

Unfortunately, we have to wait for 
https://github.com/QuickChick/QuickChick/issues/87
to be fixed, as currently the programs that QuickChick extracts to
test stuff do not compile...

From QuickChick Require Import QuickChick.
Import QcDefaultNotation. Open Scope qc_scope.
Import GenLow GenHigh.
From QuickChick Require Import Instances.
Set Warnings "-extraction-opaque-accessed,-extraction".

Global Instance genKey : GenSized IntMap.Key := 
  {| arbitrarySized n := fmap N.of_nat (arbitrarySized n) |}.

Global Instance genIntMap {A} `{GenSized A} : GenSized (IntMap A) := 
  {| arbitrarySized n := fmap IntMap.fromList (arbitrarySized n) |}.

Global Instance shrinkIntMap {A} : Shrink (IntMap A) := 
  {| shrink := fun _ => nil |}.

Global Instance shrinkKey : Shrink IntMap.Key := 
  {| shrink := fun _ => nil |}.

Global Instance showKey : Show IntMap.Key :=
  {| show := fun s => show (N.to_nat s) |}.

Global Instance showIntMap {A} `{Show A} : Show (IntMap A) :=
  {| show := fun s => show (IntMap.toList s) |}.

QuickCheck delete_eq.
*)
