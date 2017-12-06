Require Import Data.Map.Base.

Require Import Coq.FSets.FMapInterface.

Module Foo (E : DecidableType) : WSfun(E).
  Local Instance Eq_t : GHC.Base.Eq_ E.t. Admitted.
  Local Instance Ord_t : GHC.Base.Ord E.t. Admitted.

  Definition elt := E.t.
  Definition t := Map elt.
  Definition empty {b} : t b := empty.
  
  
End Foo.