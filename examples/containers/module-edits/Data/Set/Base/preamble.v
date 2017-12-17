Require GHC.Base.

Module GHC.
  Module Err.
    Axiom error : forall {a}, GHC.Base.String -> a.
  End Err.
End GHC.
