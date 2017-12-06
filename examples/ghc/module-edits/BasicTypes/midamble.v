Require Panic.


Instance Default_Origin : Panic.Default Origin :=
  Panic.Build_Default _ Generated.

Instance Default_OverlapMode : Panic.Default OverlapMode :=
  Panic.Build_Default _ (NoOverlap Panic.default).

Instance Default_RecFlag : Panic.Default RecFlag :=
  Panic.Build_Default _ Recursive.

Instance Default_RuleMatchInfo : Panic.Default RuleMatchInfo :=
  Panic.Build_Default _ ConLike.


Instance Default_SuccessFlag : Panic.Default SuccessFlag :=
  Panic.Build_Default _ Succeeded.


Instance Default_SwapFlag : Panic.Default SwapFlag :=
  Panic.Build_Default _ NotSwapped.


Instance Default_TopLevelFlag : Panic.Default TopLevelFlag :=
  Panic.Build_Default _ TopLevel.


Instance Default_TupleSort : Panic.Default TupleSort :=
  Panic.Build_Default _ BoxedTuple.

Instance Default_OverlapFlag : Panic.Default OverlapFlag :=
  Panic.Build_Default _ (Mk_OverlapFlag Panic.default Panic.default).

Instance Default_OneShotInfo : Panic.Default OneShotInfo :=
  Panic.Build_Default _ NoOneShotInfo.


Instance Default_IntWithInf : Panic.Default IntWithInf :=
  Panic.Build_Default _ Infinity.


Instance Default_OccInfo : Panic.Default OccInfo :=
  Panic.Build_Default _ NoOccInfo.


Instance Default_InlineSpec : Panic.Default InlineSpec :=
  Panic.Build_Default _ Inline.



Instance Default_FixityDirection : Panic.Default FixityDirection :=
  Panic.Build_Default _ InfixL.


Instance Default_Fixity : Panic.Default Fixity :=
  Panic.Build_Default _ (Mk_Fixity Panic.default Panic.default Panic.default).



Instance Default_DefMethSpec {ty} : Panic.Default (DefMethSpec ty) :=
  Panic.Build_Default _ VanillaDM.

Instance Default_CompilerPhase : Panic.Default CompilerPhase :=
  Panic.Build_Default _ InitialPhase.



Instance Default_Boxity : Panic.Default Boxity :=
  Panic.Build_Default _ Boxed.


Instance Default_Activation : Panic.Default Activation :=
  Panic.Build_Default _ NeverActive.


Instance Default_InlinePragma : Panic.Default InlinePragma :=
  Panic.Build_Default _ (Mk_InlinePragma Panic.default Panic.default Panic.default Panic.default Panic.default).
