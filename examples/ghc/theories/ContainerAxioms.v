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
    IntMap.Internal.difference (@IntMap.Internal.Nil B) i = (@IntMap.Internal.Nil B).

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
