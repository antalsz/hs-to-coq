Require Import Data.Set.Base.

Require Import Coq.FSets.FSetInterface.

Module Foo (E : DecidableType) : WSfun(E).
  Local Instance Eq_t : GHC.Base.Eq_ E.t. Admitted.
  Local Instance Ord_t : GHC.Base.Ord E.t. Admitted.

  Definition elt := E.t.
  Definition t := Set_ elt.
  Definition In x s := member x s = true. 
  Definition empty : t := empty.
  
  
End Foo.