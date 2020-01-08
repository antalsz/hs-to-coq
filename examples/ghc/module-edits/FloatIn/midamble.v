Instance Default_FloatBind : GHC.Err.Default MkCore.FloatBind.
Admitted.

Instance Default_FloatInBind : GHC.Err.Default FloatInBind :=
  GHC.Err.Build_Default _ (FB GHC.Err.default GHC.Err.default GHC.Err.default).
