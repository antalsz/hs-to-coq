(* ------------- VarEnv midamble.v ------------ *)
Require GHC.Err.

Instance Default__InScopeSet : GHC.Err.Default InScopeSet :=
  GHC.Err.Build_Default _ (InScope GHC.Err.default GHC.Err.default).
Instance Default__RnEnv2 : GHC.Err.Default RnEnv2 :=
  GHC.Err.Build_Default _ (RV2 GHC.Err.default GHC.Err.default GHC.Err.default).
Instance Default__TidyEnv : GHC.Err.Default TidyEnv :=
  GHC.Err.Build_Default _ (pair GHC.Err.default GHC.Err.default).


