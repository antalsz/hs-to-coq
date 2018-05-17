(* When these things get proven, they ought to move to [containers] *)

Require Import GHC.Base.
Require Import Data.IntMap.Internal.

Axiom member_insert : forall A k k' v (i : IntMap.Internal.IntMap A),
IntMap.Internal.member k (IntMap.Internal.insert k' v i) =
  (k == k')
  || IntMap.Internal.member k i.

Axiom difference_self : forall A (i : IntMap.Internal.IntMap A),
    IntMap.Internal.difference i i = IntMap.Internal.empty.

Axiom null_empty : forall A,
    (@IntMap.Internal.null A IntMap.Internal.empty) = true.