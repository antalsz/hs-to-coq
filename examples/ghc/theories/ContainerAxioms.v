(* When these things get proven, they ought to move to [containers] *)

Require Import GHC.Base.
Require Import Data.IntMap.Internal.

Axiom member_eq : forall A k k' (i : IntMap.Internal.IntMap A),
    k == k' = true ->
    IntMap.Internal.member k i = IntMap.Internal.member k' i.

Axiom member_insert : forall A k k' v (i : IntMap.Internal.IntMap A),
IntMap.Internal.member k (IntMap.Internal.insert k' v i) =
  (k == k')
  || IntMap.Internal.member k i.

Axiom union_nil_l : forall A (i : IntMap.Internal.IntMap A),
    IntMap.Internal.union IntMap.Internal.Nil i = i.

Axiom union_nil_r : forall A (i : IntMap.Internal.IntMap A),
    IntMap.Internal.union i IntMap.Internal.Nil = i.

Axiom difference_self : forall A (i : IntMap.Internal.IntMap A),
    IntMap.Internal.difference i i = IntMap.Internal.empty.

Axiom difference_nil_r : forall A B (i : IntMap.Internal.IntMap A),
    IntMap.Internal.difference i (@IntMap.Internal.Nil B) = i.

Axiom difference_nil_l : forall B A (i : IntMap.Internal.IntMap A),
    IntMap.Internal.difference (@IntMap.Internal.Nil B) i = 
    (@IntMap.Internal.Nil B).

Axiom difference_Tip_member:
  forall A (i : Internal.IntMap A) (n : Internal.Key),
    (IntMap.Internal.member n i) = true ->
    forall x:A,
      IntMap.Internal.difference
        (IntMap.Internal.Tip n x) i = Internal.Nil.

Axiom difference_Tip_non_member: 
    forall A (i : Internal.IntMap A) (n : Internal.Key),
      (IntMap.Internal.member n i) = false ->
      forall x : A,
        IntMap.Internal.difference
          (IntMap.Internal.Tip n x) i =
        IntMap.Internal.Tip n x.

Axiom null_empty : forall A,
    (@IntMap.Internal.null A IntMap.Internal.empty) = true.

Axiom filter_comp : forall A f f' (i : IntMap.Internal.IntMap A),
    IntMap.Internal.filter f (IntMap.Internal.filter f' i) =
    IntMap.Internal.filter (fun v => f v && f' v) i.

Axiom lookup_insert : forall A key (val:A) i, 
    IntMap.Internal.lookup key (IntMap.Internal.insert key val i) = Some val.

Axiom lookup_insert_neq : 
  forall b key1 key2 (val:b) m, 
    key1 <> key2 ->
    Internal.lookup key1 (Internal.insert key2 val m) = Internal.lookup key1 m.

Axiom lookup_filterWithKey : 
  forall b key (val:b) m f, Internal.lookup key (Internal.filterWithKey f m) = Some val ->
                       Internal.lookup key m = Some val.

Axiom lookup_intersection :
  forall a b key (val1:a) m1 m2, 
    Internal.lookup key m1 = Some val1 /\
    (exists (val2:b), Internal.lookup key m2 = Some val2) <-> 
    Internal.lookup key (Internal.intersection m1 m2) = Some val1.

Axiom delete_eq : forall key b (i : IntMap b),
  lookup key (delete key i) = None.

Axiom delete_neq : forall key1 key2 b (i : IntMap b),
    key1 <> key2 ->
    lookup key1 (delete key2 i) = lookup key1 i.

Axiom lookup_union :
  forall (A:Type) key (val:A) (m1 m2: IntMap A), 
    (lookup key m1 = Some val \/ lookup key m2 = Some val) <->
    lookup key (union m1 m2) = Some val.

Axiom lookup_difference_in_snd:
  forall (key : Internal.Key) (b : Type) (i i': IntMap b) (y:b),
    lookup key i' = Some y -> 
    lookup key (difference i i') = None.

Axiom lookup_difference_not_in_snd:
  forall (key : Internal.Key) (b : Type) (i i': IntMap b)(y:b),
    lookup key i' = None ->
    lookup key (difference i i') = lookup key i.