
Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Coq.FSets.FMapAVL.
Require Coq.Structures.OrderedTypeEx.



Module IntMap := FMapAVL.Make(Coq.Structures.OrderedTypeEx.Nat_as_OT).

Definition IntMap (a:Type) := IntMap.t.

Definition singleton {a} k (v :a) := IntMap.add k v (@IntMap.empty a).
