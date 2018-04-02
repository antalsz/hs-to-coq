Require GHC.Err.

Instance Default__OverlapMode : GHC.Err.Default OverlapMode :=
  GHC.Err.Build_Default _ (NoOverlap GHC.Err.default).
Instance Default__OverlapFlag : GHC.Err.Default OverlapFlag :=
  GHC.Err.Build_Default _ (Mk_OverlapFlag GHC.Err.default GHC.Err.default).
Instance Default__Fixity : GHC.Err.Default Fixity :=
  GHC.Err.Build_Default _ (Mk_Fixity GHC.Err.default GHC.Err.default GHC.Err.default).
Instance Default__InlinePragma : GHC.Err.Default InlinePragma :=
  GHC.Err.Build_Default _ (Mk_InlinePragma GHC.Err.default GHC.Err.default GHC.Err.default GHC.Err.default GHC.Err.default).
