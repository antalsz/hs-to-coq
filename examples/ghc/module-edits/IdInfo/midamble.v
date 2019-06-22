(*  IdInfo: midamble *)

Require GHC.Err.

(* --------------------- *)


(*****)

Instance Default_RuleInfo : GHC.Err.Default RuleInfo :=
  GHC.Err.Build_Default _ EmptyRuleInfo.

Instance Default_Unfolding : GHC.Err.Default Unfolding :=
  GHC.Err.Build_Default _ NoUnfolding.

Instance Default_TickBoxOp : GHC.Err.Default TickBoxOp :=
  GHC.Err.Build_Default _ (TickBox GHC.Err.default GHC.Err.default).

Instance Default_CafInfo : GHC.Err.Default CafInfo :=
  GHC.Err.Build_Default _ MayHaveCafRefs.

Instance Default_Termination {r} : GHC.Err.Default (Termination r) :=
  GHC.Err.Build_Default _ Diverges.

Instance Default_DmdType : GHC.Err.Default DmdType :=
  GHC.Err.Build_Default _ (Mk_DmdType GHC.Err.default GHC.Err.default GHC.Err.default).

Instance Default_StrictSig : GHC.Err.Default StrictSig :=
  GHC.Err.Build_Default _ (Mk_StrictSig GHC.Err.default).

Instance Default_JointDmd `{GHC.Err.Default a} `{GHC.Err.Default b} : GHC.Err.Default (JointDmd a b) :=
  GHC.Err.Build_Default _ (JD GHC.Err.default GHC.Err.default).

Instance Default_Str {s} : GHC.Err.Default (Str s) :=
  GHC.Err.Build_Default _ Lazy.
Instance Default_Use {s} : GHC.Err.Default (Use s) :=
  GHC.Err.Build_Default _ Abs.

Instance Default_IdInfo : GHC.Err.Default IdInfo :=
  GHC.Err.Build_Default _ (Mk_IdInfo GHC.Err.default GHC.Err.default GHC.Err.default
                         GHC.Err.default GHC.Err.default GHC.Err.default GHC.Err.default
                         GHC.Err.default GHC.Err.default GHC.Err.default GHC.Err.default).

Instance Default_TyCon : GHC.Err.Default TyCon :=
  GHC.Err.Build_Default _ (PrimTyCon GHC.Err.default GHC.Err.default nil tt tt GHC.Err.default GHC.Err.default GHC.Err.default GHC.Err.default ).

Instance Default_RecSelParent : GHC.Err.Default RecSelParent :=
  GHC.Err.Build_Default _ (RecSelData GHC.Err.default).

Instance Default__Var : GHC.Err.Default Var := GHC.Err.Build_Default _ (Mk_Id GHC.Err.default GHC.Err.default GHC.Err.default GHC.Err.default GHC.Err.default GHC.Err.default).

Instance Default__DataCon : GHC.Err.Default DataCon :=
 Err.Build_Default _ (MkData GHC.Err.default GHC.Err.default GHC.Err.default GHC.Err.default nil nil nil nil tt tt nil tt nil nil GHC.Err.default GHC.Err.default GHC.Err.default GHC.Err.default GHC.Err.default tt GHC.Err.default GHC.Err.default).
