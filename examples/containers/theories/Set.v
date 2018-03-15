(* This is the "wrapped" version of the Set data structure. 
   Compared to the Internal version, some of the operations 
   require that the type be a lawful instance of the Ord class. 
   (Otherwise, we cannot show that the resulting set 
   is well-formed. Clients may either use this interface or 
   the Internal interface. *)

Require Data.Set.Internal.
Require Import GHC.Base.
Require Import Proofs.GHC.Base.
Require Import OrdTactic.
Require Import SetProofs.

(* TODO: move the type class instances to this file from SetProofs. *)

Set Bullet Behavior "Strict Subproofs".

(*

** Status

This is the annotated export list of Set. The first column says:

 V verified
 F verified according to the FMapInterface specification
 P skipped, because of partiality
 S skipped, for other reasons
 N nothing to be done (for *this* file)

            -- * Set type
V            Set

            -- * Operators
             , (\\)

            -- * Query
V            , S.null
V            , size
V            , member
V            , notMember
N            , lookupLT
N            , lookupGT
N            , lookupLE
N            , lookupGE
V            , isSubsetOf
N            , isProperSubsetOf
V            , disjoint

            -- * Construction
V            , empty
V            , singleton
V            , insert
V            , delete
            , powerSet

            -- * Combine
V            , union
V            , unions
V            , difference
V            , intersection
            , cartesianProduct
            , disjointUnion

            -- * Filter
V            , S.filter
            , takeWhileAntitone
            , dropWhileAntitone
            , spanAntitone
V            , partition
V            , split
V            , splitMember
            , splitRoot

            -- * Indexed
            , lookupIndex
P            , findIndex
P            , elemAt
P            , deleteAt
V            , S.take
V            , S.drop
            , S.splitAt

            -- * Map
            , S.map
V           , mapMonotonic

            -- * Folds
V            , S.foldr
V            , S.foldl
            -- ** Strict folds
V            , foldr'
V            , foldl'
            -- ** Legacy folds
V            , fold

            -- * Min\/Max
V            , lookupMin
V            , lookupMax
P            , findMin
P            , findMax
V            , deleteMin
V            , deleteMax
P            , deleteFindMin
P            , deleteFindMax
V            , maxView
V            , minView

            -- * Conversion

            -- ** List
V            , elems
V            , toList
            , fromList

            -- ** Ordered list
V            , toAscList
            , toDescList
            , fromAscList
            , fromDescList
V            , fromDistinctAscList
            , fromDistinctDescList

            -- * Debugging
S            , showTree
S            , showTreeWith
N            , valid

            ) where
*)


(* Already defined in SetProofs: instance Eq, instance Eq1, instance Monoid, instance Ord, instance Ord1, instance Semigroup *)

Definition Set_ (a:Type) `{Base.Ord a} := WFSet a.


Program Definition null {a}`{Base.Ord a} (x:Set_ a) : bool := Internal.null x.
Program Definition size {a}`{Base.Ord a} (x:Set_ a) : Num.Int := Internal.size x.
Program Definition member {a}`{Base.Ord a} (x:a) (s:Set_ a) : bool := 
  Internal.member x s.
Program Definition notMember {a}`{Base.Ord a} (x:a) (s:Set_ a) : bool := 
  Internal.notMember x s.

Program Definition lookupLT {a}`{Base.Ord a} :  a -> Set_ a -> option a :=
  Internal.lookupLT.
Program Definition lookupLE {a}`{Base.Ord a} :  a -> Set_ a -> option a :=
  Internal.lookupLE.
Program Definition lookupGT {a}`{Base.Ord a} :  a -> Set_ a -> option a :=
  Internal.lookupGT.
Program Definition lookupGE {a}`{Base.Ord a} :  a -> Set_ a -> option a :=
  Internal.lookupGE.


Program Definition isSubsetOf {a}`{Base.Ord a} : Set_ a -> Set_ a -> bool := 
  Internal.isSubsetOf.
Program Definition disjoint {a}`{Base.Ord a} : Set_ a -> Set_ a -> bool := 
  Internal.disjoint.

Program Definition isProperSubsetOf {a}`{Base.Ord a} : Set_ a -> Set_ a -> bool := 
  Internal.isProperSubsetOf.

Program Definition empty {a}`{Base.Ord a} : Set_ a := 
  exist _ Internal.empty SetProofs.empty_WF.

Definition singleton {a} `{Base.Ord a} (x:a) : Set_ a := 
  exist _ (Internal.singleton x) (SetProofs.singleton_WF x).

Program Definition insert {a}`{OrdLaws a} : a -> Set_ a -> Set_ a := 
  Internal.insert.
Next Obligation.
  destruct x0. simpl.
  eapply SetProofs.insert_Desc with (ub := None) (lb := None); intuition.
Defined.

Program Definition delete {a}`{OrdLaws a} : a -> Set_ a -> Set_ a := Internal.delete.
Next Obligation.
  destruct x0.
  eapply SetProofs.delete_Desc with (ub := None)(lb:= None); intuition.
Defined.

Program Definition union {a}`{OrdLaws a} : Set_ a -> Set_ a -> Set_ a := Internal.union.
Next Obligation.
  destruct x, x0. simpl.
  eapply SetProofs.union_Desc with (ub := None) (lb := None); intuition.
Defined.

Program Definition unions {a}`{OrdLaws a} (xs : list (Set_ a)) : Set_ a := 
  Internal.unions (List.map unpack xs).
Next Obligation.
  eapply SetProofs.unions_Desc with  (ub := None) (lb := None); intuition.
  unfold unpack.
  apply List.Forall_forall.
  intros.
  edestruct List.in_map_iff as [h0 _]. 
  destruct (h0 H0).
  destruct x0. 
  simpl in *.
  destruct H1. subst.
  unfold SetProofs.WF in w.
  auto.
Qed.

Program Definition difference {a}`{OrdLaws a} : Set_ a -> Set_ a -> Set_ a := 
  Internal.difference.
Next Obligation.
  destruct x, x0. simpl.
  eapply SetProofs.difference_Desc with (ub := None) (lb := None); intuition.
Defined.

Program Definition intersection {a}`{OrdLaws a} : Set_ a -> Set_ a -> Set_ a := 
  Internal.intersection.
Next Obligation.
  destruct x, x0. simpl.
  eapply SetProofs.intersection_Desc with (ub := None) (lb := None); intuition.
Defined.



Program Definition filter  {a}`{OrdLaws a} : (a -> bool) -> Set_ a -> Set_ a := 
  Internal.filter.
Next Obligation.
  destruct x0. simpl.
  eapply SetProofs.filter_Bounded with (ub := None) (lb := None); assumption.
Qed.

Program Definition partition  {a}`{OrdLaws a} : (a -> bool) -> Set_ a -> Set_ a * Set_ a 
  := Internal.partition.
Next Obligation.
  destruct x0. simpl.
  eapply SetProofs.partition_Bounded with (ub := None) (lb := None); intuition.
Qed.
Next Obligation.
  destruct x0. simpl.
  eapply SetProofs.partition_Bounded with (ub := None) (lb := None); intuition.
Qed.

Program Definition splitMember {a} `{OrdLaws a}
   : a -> Set_ a -> (Set_ a * bool * Set_ a)%type :=  Internal.splitMember.
Next Obligation.
  destruct x0. simpl.
  eapply SetProofs.splitMember_Desc with (ub := None) (lb := None); intuition.
  simpl.
  eapply Bounded_relax_ub_None.
  eapply Bounded_relax_lb_None.
  eassumption.
Defined.
Next Obligation.
  destruct x0. simpl.
  eapply SetProofs.splitMember_Desc with (ub := None) (lb := None); intuition.
  simpl.
  eapply Bounded_relax_ub_None.
  eapply Bounded_relax_lb_None.
  eassumption.
Defined.

Program Definition lookupIndex {a} `{Ord a} : a -> Set_ a -> option Int :=
  Internal.lookupIndex.

Definition Monotonic {a}{b}`{Ord a}`{Ord b} (f : a -> b) :=
   (forall x y, (f x < f y) = (x < y)) /\ (forall x y, (f x == f y) = (x == y)).

Program Definition mapMonotonic {a} `{OrdLaws a} {b}`{OrdLaws b} : 
  forall (f: a -> b), Monotonic f -> Set_ a -> Set_ b :=
  fun f _ s => Internal.mapMonotonic f s.
Next Obligation.
  destruct s. simpl.
  unfold Monotonic in *.
  eapply SetProofs.mapMonotonic_Desc with (f:=f)(ub := None) (lb := None);
    intuition.
Defined.
  
Program Definition take {a}`{OrdLaws a} : Int -> Set_ a -> Set_ a := Internal.take.
Next Obligation.
  destruct x0. simpl.
  eapply toList_take with (ub := None) (lb := None); intuition.
Qed.

Program Definition drop {a}`{OrdLaws a} : Int -> Set_ a -> Set_ a := Internal.drop.
Next Obligation.
  destruct x0. simpl.
  eapply toList_drop with (ub := None) (lb := None); intuition.
Qed.

 Program Definition foldl {a}`{OrdLaws a}: forall A : Type, (a -> A -> A) -> Set_ a -> A -> A
    := fun a k s n => Internal.foldl (fun x e => k e x) n s.
 Program Definition foldl' {a}`{OrdLaws a}: forall A : Type, (a -> A -> A) -> Set_ a -> A -> A
    := fun a k s n => Internal.foldl' (fun x e => k e x) n s.
 Program Definition foldr {a}`{OrdLaws a}: forall A : Type, (A -> a -> A) -> Set_ a -> A -> A
    := fun a k s n => Internal.foldr (fun x e => k e x) n s.
 Program Definition foldr' {a}`{OrdLaws a}: forall A : Type, (A -> a -> A) -> Set_ a -> A -> A
    := fun a k s n => Internal.foldr' (fun x e => k e x) n s.
 Program Definition fold {a}`{OrdLaws a}: forall A : Type, (A -> a -> A) -> Set_ a -> A -> A
    := fun a k s n => Internal.fold (fun x e => k e x) n s.

Program Definition lookupMin {a}`{OrdLaws a} : Set_ a -> option a := 
  Internal.lookupMin.

Program Definition lookupMax {a}`{OrdLaws a} : Set_ a -> option a := 
  Internal.lookupMax.

Program Definition deleteMin {a}`{OrdLaws a} : Set_ a -> Set_ a := 
  Internal.deleteMin.
Next Obligation.
  destruct x. simpl.
  rewrite SetProofs.deleteMin_Desc with (lb:=None)(ub:=None); intuition.
  pose proof (SetProofs.lookupMin_Desc x None None w) as HLookup.
  destruct Internal.lookupMin; auto.
  destruct HLookup.
  eapply SetProofs.delete_Desc with (lb:=None)(ub:=None); intuition.
Qed.  


Program Definition deleteMax {a}`{OrdLaws a} : Set_ a -> Set_ a := 
  Internal.deleteMax.
Next Obligation.
  destruct x.
  rewrite SetProofs.deleteMax_Desc with (lb:=None)(ub:=None); intuition.
  pose proof (SetProofs.lookupMax_Desc x None None w) as HLookup.
  destruct Internal.lookupMax; auto.
  destruct HLookup.
  eapply SetProofs.delete_Desc with (lb:=None)(ub:=None); intuition.
Qed.  



Program Definition maxView {a}`{OrdLaws a} : Set_ a -> option( a * Set_ a) :=
  fun x => 
    match Internal.maxView x with
      | Some (y,z) => Some(y, z)
      | None => None
    end.
Next Obligation.
  destruct x. simpl in *.
  generalize Heq_anonymous.
  eapply SetProofs.maxView_Desc with (lb :=None) (ub:=None); intuition.
  inversion Heq_anonymous0. subst.
  eapply Desc_WF'; eauto.
  inversion Heq_anonymous0.
Defined.

Program Definition minView {a}`{OrdLaws a} : Set_ a -> option( a * Set_ a) :=
  fun x => 
    match Internal.minView x with
      | Some (y,z) => Some(y, z)
      | None => None
    end.
Next Obligation.
  destruct x. simpl in *.
  generalize Heq_anonymous.
  eapply SetProofs.minView_Desc with (lb :=None) (ub:=None); intuition.
  inversion Heq_anonymous0. subst.
  eapply Desc_WF'; eauto.
  inversion Heq_anonymous0.
Defined.


Program Definition toList {a} `{OrdLaws a} : Set_ a -> list a := 
  Internal.toList.

Program Definition toAscList {a} `{OrdLaws a} : Set_ a -> list a := 
  Internal.toDescList.

Program Definition toDescList {a} `{OrdLaws a} : Set_ a -> list a := 
  Internal.toDescList.

Program Definition fromDistinctAscList {a} `{OrdLaws a} : forall x
   {_ : Sorted.StronglySorted (fun x0 y : a => Base.op_zl__ x0 y = true) x},
   Set_ a :=  fun x y => Internal.fromDistinctAscList x.
Next Obligation.
  eapply SetProofs.fromDistinctAscList_Desc; intuition.
Defined.



