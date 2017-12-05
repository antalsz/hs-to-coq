Require GHC.Base.

Module GHC.
  Module Err.
    Axiom undefined : forall {a}, a.
    Axiom error : forall {a}, GHC.Base.String -> a.
  End Err.
End GHC.
