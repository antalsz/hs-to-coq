(* Default settings (from HsToCoq.Coq.Preamble) *)
(* These are the parts of IdInfo that require recursive modules. *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Coq.Program.Tactics.
Require Coq.Program.Wf.

Require BasicTypes.
Require Class.
Require CoreSyn.
Require DataCon.
Require Demand.
Require GHC.Base.
Require GHC.Num.
Require Module.
Require PatSyn.
Require VarSet.
Import GHC.Base.Notations.

Require Import IdInfo.

(* Record selectors *)
Parameter demandInfo        : IdInfo -> Demand.Demand.
Parameter strictnessInfo    : IdInfo -> Demand.StrictSig.
Parameter unfoldingInfo     : IdInfo -> CoreSyn.Unfolding.

Parameter setDemandInfo     : IdInfo -> Demand.Demand -> IdInfo.
Parameter setStrictnessInfo : IdInfo -> Demand.StrictSig -> IdInfo.
Parameter setUnfoldingInfo  : IdInfo -> CoreSyn.Unfolding -> IdInfo.

Parameter setUnfoldingInfoLazily : IdInfo -> CoreSyn.Unfolding -> IdInfo.

Parameter ruleInfoFreeVars : RuleInfo -> VarSet.DVarSet.
Parameter ruleInfoRules : RuleInfo -> list CoreSyn.CoreRule.
