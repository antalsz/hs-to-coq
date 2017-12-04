Require Data.IntSet.Base.

Axiom ufmToSet_Directly : forall {elt}, UniqFM elt -> Data.IntSet.Base.IntSet.

Require Panic.

Instance Default_UniqFM {a} : Panic.Default (UniqFM a) :=
  Panic.Build_Default _ (UFM Data.IntMap.Base.empty).
