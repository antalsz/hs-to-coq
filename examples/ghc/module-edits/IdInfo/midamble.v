(*  IdInfo: midamble *)

Require GHC.Err.

(* --------------------- *)


(*****)

Instance Default__RuleInfo : GHC.Err.Default RuleInfo :=
  GHC.Err.Build_Default _ EmptyRuleInfo.

Instance Default__TickBoxOp : GHC.Err.Default TickBoxOp :=
  GHC.Err.Build_Default _ (TickBox GHC.Err.default GHC.Err.default).

Instance Default__Termination {r} : GHC.Err.Default (Termination r) :=
  GHC.Err.Build_Default _ Diverges.

Instance Default__DmdType : GHC.Err.Default DmdType :=
  GHC.Err.Build_Default _ (Mk_DmdType GHC.Err.default GHC.Err.default GHC.Err.default).

Instance Default__StrictSig : GHC.Err.Default StrictSig :=
  GHC.Err.Build_Default _ (Mk_StrictSig GHC.Err.default).

Instance Default__JointDmd `{GHC.Err.Default a} `{GHC.Err.Default b} : GHC.Err.Default (JointDmd a b) :=
  GHC.Err.Build_Default _ (JD GHC.Err.default GHC.Err.default).

Instance Default__Str {s} : GHC.Err.Default (Str s) :=
  GHC.Err.Build_Default _ Lazy.
Instance Default__Use {s} : GHC.Err.Default (Use s) :=
  GHC.Err.Build_Default _ Abs.

Instance Default__IdInfo : GHC.Err.Default IdInfo :=
  GHC.Err.Build_Default _ (Mk_IdInfo GHC.Err.default GHC.Err.default GHC.Err.default
                         GHC.Err.default GHC.Err.default GHC.Err.default GHC.Err.default
                         GHC.Err.default GHC.Err.default GHC.Err.default GHC.Err.default).

Instance Default__RecSelParent : GHC.Err.Default RecSelParent :=
  GHC.Err.Build_Default _ (RecSelData GHC.Err.default).


Instance Default__Var : GHC.Err.Default Var := GHC.Err.Build_Default _ (Mk_Id GHC.Err.default GHC.Err.default GHC.Err.default GHC.Err.default GHC.Err.default GHC.Err.default).


Instance Default__DataCon : GHC.Err.Default DataCon :=
 Err.Build_Default _ (MkData GHC.Err.default GHC.Err.default GHC.Err.default GHC.Err.default nil nil nil nil GHC.Err.default GHC.Err.default nil GHC.Err.default nil nil GHC.Err.default GHC.Err.default GHC.Err.default GHC.Err.default GHC.Err.default GHC.Err.default GHC.Err.default GHC.Err.default).
