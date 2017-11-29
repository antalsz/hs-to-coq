Require Import GHC.Base.

Module GHC.
  Module Err.
    Axiom undefined : forall {a}, a.
    Axiom error : forall {a}, String -> a.
  End Err.
End GHC.
