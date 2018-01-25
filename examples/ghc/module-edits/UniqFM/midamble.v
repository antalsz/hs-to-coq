Require Data.IntSet.Internal.

Axiom ufmToSet_Directly : forall {elt}, UniqFM elt -> Data.IntSet.Internal.IntSet.

Require Panic.

Instance Default_UniqFM {a} : Panic.Default (UniqFM a) :=
  Panic.Build_Default _ (UFM Data.IntMap.Internal.empty).
