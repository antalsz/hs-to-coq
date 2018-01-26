Require GHC.Err.


Instance Default_Origin : GHC.Err.Default Origin :=
  GHC.Err.Build_Default _ Generated.

Instance Default_OverlapMode : GHC.Err.Default OverlapMode :=
  GHC.Err.Build_Default _ (NoOverlap GHC.Err.default).

Instance Default_RecFlag : GHC.Err.Default RecFlag :=
  GHC.Err.Build_Default _ Recursive.

Instance Default_RuleMatchInfo : GHC.Err.Default RuleMatchInfo :=
  GHC.Err.Build_Default _ ConLike.


Instance Default_SuccessFlag : GHC.Err.Default SuccessFlag :=
  GHC.Err.Build_Default _ Succeeded.


Instance Default_SwapFlag : GHC.Err.Default SwapFlag :=
  GHC.Err.Build_Default _ NotSwapped.


Instance Default_TopLevelFlag : GHC.Err.Default TopLevelFlag :=
  GHC.Err.Build_Default _ TopLevel.


Instance Default_TupleSort : GHC.Err.Default TupleSort :=
  GHC.Err.Build_Default _ BoxedTuple.

Instance Default_OverlapFlag : GHC.Err.Default OverlapFlag :=
  GHC.Err.Build_Default _ (Mk_OverlapFlag GHC.Err.default GHC.Err.default).

Instance Default_OneShotInfo : GHC.Err.Default OneShotInfo :=
  GHC.Err.Build_Default _ NoOneShotInfo.


Instance Default_IntWithInf : GHC.Err.Default IntWithInf :=
  GHC.Err.Build_Default _ Infinity.


Instance Default_OccInfo : GHC.Err.Default OccInfo :=
  GHC.Err.Build_Default _ NoOccInfo.


Instance Default_InlineSpec : GHC.Err.Default InlineSpec :=
  GHC.Err.Build_Default _ Inline.



Instance Default_FixityDirection : GHC.Err.Default FixityDirection :=
  GHC.Err.Build_Default _ InfixL.


Instance Default_Fixity : GHC.Err.Default Fixity :=
  GHC.Err.Build_Default _ (Mk_Fixity GHC.Err.default GHC.Err.default GHC.Err.default).



Instance Default_DefMethSpec {ty} : GHC.Err.Default (DefMethSpec ty) :=
  GHC.Err.Build_Default _ VanillaDM.

Instance Default_CompilerPhase : GHC.Err.Default CompilerPhase :=
  GHC.Err.Build_Default _ InitialPhase.



Instance Default_Boxity : GHC.Err.Default Boxity :=
  GHC.Err.Build_Default _ Boxed.


Instance Default_Activation : GHC.Err.Default Activation :=
  GHC.Err.Build_Default _ NeverActive.


Instance Default_InlinePragma : GHC.Err.Default InlinePragma :=
  GHC.Err.Build_Default _ (Mk_InlinePragma GHC.Err.default GHC.Err.default GHC.Err.default GHC.Err.default GHC.Err.default).
