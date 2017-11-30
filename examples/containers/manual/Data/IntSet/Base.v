Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Coq.MSets.MSetRBT.
Require Coq.MSets.MSetGenTree.
Require Coq.Structures.OrdersEx.

Require Import GHC.Base.

(** We are using Coq's red-black tree implementation, namely
    [MSetRBT], as the underlying data structure for IntSet. *)
Module IS := MSetRBT.Make(Coq.Structures.OrdersEx.Z_as_OT).
(** Some operations which are not provided by [MSetInterface] require
    knowledge of [IntSet]'s underlying data representation, therefore
    we need to use the [Raw] module. *)
Module ISR := IS.Raw.

Definition IntSet := ISR.t.
Definition Key := Int.

(** * Query *)
Definition null (x:IntSet) : bool := ISR.is_empty x.
Definition size (x:IntSet) : Int := Z.of_nat (ISR.cardinal x).
Definition member (k:Key) (x:IntSet) : bool := ISR.mem k x.
Definition notMember (k:Key) (x:IntSet) := negb (member k x).

(** The following four functions are inefficient (an ideal
    implementation should be O(log n)), but we don't care. *)
Definition lookupLT (k:Key) (x:IntSet) : option Key :=
  ISR.max_elt (ISR.filter (Z.gtb k) x).
Definition lookupGT (k:Key) (x:IntSet) : option Key :=
  ISR.min_elt (ISR.filter (Z.ltb k) x).
Definition lookupLE (k:Key) (x:IntSet) : option Key :=
  ISR.max_elt (ISR.filter (Z.geb k) x).
Definition lookupGE (k:Key) (x:IntSet) : option Key :=
  ISR.min_elt (ISR.filter (Z.leb k) x).

Definition isSubsetOf : IntSet -> IntSet -> bool := ISR.subset.
Definition isProperSubsetOf (x1 x2:IntSet) : bool :=
  andb (ISR.subset x1 x2) (negb (ISR.equal x1 x2)).

(** * Construction *)
Definition empty : IntSet := ISR.empty.
Definition singleton : Key -> IntSet := ISR.singleton.
Definition insert : Key -> IntSet -> IntSet := ISR.add.
Definition delete : Key -> IntSet -> IntSet := ISR.remove.

(** * Combine *)
Definition union : IntSet -> IntSet -> IntSet := ISR.union.
Definition unions (l: list IntSet) : IntSet := fold_right union empty l.
Definition difference : IntSet -> IntSet -> IntSet := ISR.diff.
Definition intersection : IntSet -> IntSet -> IntSet := ISR.inter.

(** * Filter *)
Definition filter : (Key -> bool) -> IntSet -> IntSet := ISR.filter.
Definition partition : (Key -> bool) -> IntSet -> (IntSet * IntSet) := ISR.partition.
Definition split (k:Key) (x:IntSet) : (IntSet * IntSet) :=
  match partition (Z.gtb k) x with
  | (x1, x2) => (x1, delete k x2)
  end. (* Inefficient! *)
Definition splitMember (k:Key) (x:IntSet) : (IntSet * bool * IntSet) :=
  match split k x with
  | (x1, x2) => (x1, member k x, x2)
  end. (* Inefficient! *)

Definition splitRoot (x:IntSet) : list IntSet :=
  match x with
  | ISR.Leaf => nil
  | ISR.Node _ l _ r => 
    l :: r :: nil
  end.

(** * Map *)
Fixpoint map (f:Key -> Key) (x:IntSet) : IntSet :=
  match x with
  | ISR.Leaf => ISR.Leaf
  | ISR.Node c l k r =>
    ISR.Node c (map f l) (f k) (map f r)
  end.

(** * Folds *)
Definition foldl {A} (f:A -> Key -> A) (base:A) (x:IntSet) : A :=
  ISR.fold (fun k x => f x k) x base.

Fixpoint foldr {A} (f:Key -> A -> A) (base:A) (x:IntSet) : A :=
  match x with
  | ISR.Leaf => base
  | ISR.Node c l k r =>
    foldr f (f k (foldr f base r)) l
  end.

(** Strict folds. They are the same because we only have inductive
    data types and total, terminating functions -- and the semantics
    of strict and lazy evaluation coincide here. *)
Definition foldl' {A} := @foldl A.
Definition foldr' {A} := @foldr A.

(** The legacy [fold]. Notice that this is equivalent to [foldr],
    while the [fold] defined by [MSetRBT] (or more precisely,
    [MSetGenTree]) is equivalent to [foldl]! *)
Definition fold {A} : (Key -> A -> A) -> A -> IntSet -> A := foldr.

(** findMin and findMax are omitted because they are partial. *)

(** * Min/Max *)
Definition deleteMin (x:IntSet) : IntSet :=
  match ISR.remove_min x with
  | None => x
  | Some (_, x') => x'
  end.

Definition deleteMax (x:IntSet) : IntSet :=
  match ISR.max_elt x with
  | None => x
  | Some k => delete k x
  end.

(** deleteFindMin and deleteFindMax are omitted because they are partial. *)

Definition minView : IntSet -> option (Key * IntSet) :=
  ISR.remove_min.

Definition maxView (x:IntSet) : option (Key * IntSet) :=
  match ISR.max_elt x with
  | None => None
  | Some k => Some (k, delete k x)
  end.

(** * Conversion  *)
(** [elems] returns the elements of a set in ascending order. *)
Definition elems (x:IntSet) : list Key :=
  ISR.fold cons x nil.

(** There is no specification for the order of the list returned by
    [toList]. *)
Definition toList : IntSet -> list Key := ISR.elements.
  
Definition fromList : list Key -> IntSet := ISR.treeify.

Definition toAscList : IntSet -> list Key := elems.

Definition toDescList : IntSet -> list Key := foldr cons nil.

Definition fromAscList : list Key -> IntSet := fromList. (* Inefficient! *)

Definition fromDistinctAscList : list Key -> IntSet := fromList. (* Inefficient! *)

Instance instance_Eq_IntSet : GHC.Base.Eq_ IntSet := fun _ k => k {|
  GHC.Base.op_zeze____ := ISR.equal;
  GHC.Base.op_zsze____ := fun x y => negb (ISR.equal x y)
|}.

Instance instance_Monoid_IntSet : GHC.Base.Monoid IntSet := fun _ k => k {|
  GHC.Base.mempty__ := empty;
  GHC.Base.mappend__ := union;
  GHC.Base.mconcat__ := unions;
|}.
