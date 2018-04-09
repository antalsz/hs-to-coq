(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Coq.Program.Tactics.
Require Coq.Program.Wf.

(* Preamble *)

Require Import CoreSyn.

(* Converted imports: *)

Require BasicTypes.
Require CoreSyn.
Require FV.
Require NameSet.
Require TyCon.
Require Var.
Require VarSet.

(* Converted type declarations: *)

Definition FVAnn :=
  VarSet.DVarSet%type.

Definition CoreExprWithFVs' :=
  (CoreSyn.AnnExpr' Var.Id FVAnn)%type.

Definition CoreExprWithFVs :=
  (AnnExpr Var.Id FVAnn)%type.

Definition CoreBindWithFVs :=
  (CoreSyn.AnnBind Var.Id FVAnn)%type.

Definition CoreAltWithFVs :=
  (AnnAlt Var.Id FVAnn)%type.
(* Midamble *)


(* Converted value declarations: *)

Axiom exprFreeVars : CoreSyn.CoreExpr -> VarSet.VarSet.

Axiom exprsFreeVarsList : list CoreSyn.CoreExpr -> list Var.Var.

Axiom exprsFreeVars : list CoreSyn.CoreExpr -> VarSet.VarSet.

Axiom exprsFVs : list CoreSyn.CoreExpr -> FV.FV.

Axiom exprFreeVarsList : CoreSyn.CoreExpr -> list Var.Var.

Axiom exprFreeVarsDSet : CoreSyn.CoreExpr -> VarSet.DVarSet.

Axiom exprFVs : CoreSyn.CoreExpr -> FV.FV.

Axiom exprFreeIds : CoreSyn.CoreExpr -> VarSet.IdSet.

Axiom exprFreeIdsDSet : CoreSyn.CoreExpr -> VarSet.DIdSet.

Axiom exprFreeIdsList : CoreSyn.CoreExpr -> list Var.Id.

Axiom exprsFreeIdsDSet : list CoreSyn.CoreExpr -> VarSet.DIdSet.

Axiom exprsFreeIdsList : list CoreSyn.CoreExpr -> list Var.Id.

Axiom bindFreeVars : CoreSyn.CoreBind -> VarSet.VarSet.

Axiom exprSomeFreeVars : FV.InterestingVarFun ->
                         CoreSyn.CoreExpr -> VarSet.VarSet.

Axiom exprSomeFreeVarsList : FV.InterestingVarFun ->
                             CoreSyn.CoreExpr -> list Var.Var.

Axiom exprSomeFreeVarsDSet : FV.InterestingVarFun ->
                             CoreSyn.CoreExpr -> VarSet.DVarSet.

Axiom exprsSomeFreeVars : FV.InterestingVarFun ->
                          list CoreSyn.CoreExpr -> VarSet.VarSet.

Axiom exprsSomeFreeVarsList : FV.InterestingVarFun ->
                              list CoreSyn.CoreExpr -> list Var.Var.

Axiom exprsSomeFreeVarsDSet : FV.InterestingVarFun ->
                              list CoreSyn.CoreExpr -> VarSet.DVarSet.

Axiom stableUnfoldingVars : CoreSyn.Unfolding -> option VarSet.VarSet.

Axiom idUnfoldingVars : Var.Id -> VarSet.VarSet.

Axiom freeVars : CoreSyn.CoreExpr -> CoreExprWithFVs.

Axiom freeVarsBind : CoreSyn.CoreBind ->
                     VarSet.DVarSet -> (CoreBindWithFVs * VarSet.DVarSet)%type.

Axiom bndrRuleAndUnfoldingVarsDSet : Var.Id -> VarSet.DVarSet.

Axiom dIdFreeVars : Var.Id -> VarSet.DVarSet.

Axiom idFreeVars : Var.Id -> VarSet.VarSet.

Axiom idFVs : Var.Id -> FV.FV.

Axiom vectsFreeVars : list CoreSyn.CoreVect -> VarSet.VarSet.

Axiom idRuleRhsVars : (BasicTypes.Activation -> bool) ->
                      Var.Id -> VarSet.VarSet.

Axiom ruleRhsFreeVars : CoreSyn.CoreRule -> VarSet.VarSet.

Axiom ruleLhsFreeIdsList : CoreSyn.CoreRule -> list Var.Var.

Axiom ruleLhsFreeIds : CoreSyn.CoreRule -> VarSet.VarSet.

Axiom ruleLhsFVIds : CoreSyn.CoreRule -> FV.FV.

Axiom rulesFreeVarsDSet : list CoreSyn.CoreRule -> VarSet.DVarSet.

Axiom rulesFVs : list CoreSyn.CoreRule -> FV.FV.

Axiom rulesFreeVars : list CoreSyn.CoreRule -> VarSet.VarSet.

Axiom ruleFreeVars : CoreSyn.CoreRule -> VarSet.VarSet.

Axiom ruleFVs : CoreSyn.CoreRule -> FV.FV.

Axiom exprs_fvs : list CoreSyn.CoreExpr -> FV.FV.

Axiom stableUnfoldingFVs : CoreSyn.Unfolding -> option FV.FV.

Axiom idUnfoldingFVs : Var.Id -> FV.FV.

Axiom bndrRuleAndUnfoldingFVs : Var.Id -> FV.FV.

Axiom rhs_fvs : (Var.Id * CoreSyn.CoreExpr)%type -> FV.FV.

Axiom expr_fvs : CoreSyn.CoreExpr -> FV.FV.

Axiom addBndrs : list CoreSyn.CoreBndr -> FV.FV -> FV.FV.

Axiom addBndr : CoreSyn.CoreBndr -> FV.FV -> FV.FV.

(* tickish_fvs skipped *)

Axiom exprsOrphNames : list CoreSyn.CoreExpr -> NameSet.NameSet.

(* exprOrphNames skipped *)

(* orphNamesOfFamInst skipped *)

Axiom orphNamesOfAxiom : forall {br}, list br -> NameSet.NameSet.

Axiom orphNamesOfCos : list unit -> NameSet.NameSet.

(* orphNamesOfProv skipped *)

(* orphNamesOfCo skipped *)

Axiom orphNamesOfTypes : list unit -> NameSet.NameSet.

(* orphNamesOfType skipped *)

(* orphNamesOfCoAxBranch skipped *)

(* orphNamesOfCoAxBranches skipped *)

(* orphNamesOfCoCon skipped *)

Axiom orphNamesOfTyCon : TyCon.TyCon -> NameSet.NameSet.

Axiom orphNamesOfThings : forall {a},
                          (a -> NameSet.NameSet) -> list a -> NameSet.NameSet.

Axiom freeVarsOf : CoreExprWithFVs -> VarSet.DIdSet.

Axiom freeVarsOfAnn : FVAnn -> VarSet.DIdSet.

Axiom noFVs : VarSet.VarSet.

Axiom aFreeVar : Var.Var -> VarSet.DVarSet.

Axiom delBindersFV : list Var.Var -> VarSet.DVarSet -> VarSet.DVarSet.

Axiom delBinderFV : Var.Var -> VarSet.DVarSet -> VarSet.DVarSet.

Axiom unionFVs : VarSet.DVarSet -> VarSet.DVarSet -> VarSet.DVarSet.

Axiom unionFVss : list VarSet.DVarSet -> VarSet.DVarSet.

Axiom varTypeTyCoVars : Var.Var -> VarSet.TyCoVarSet.

Axiom dVarTypeTyCoVars : Var.Var -> VarSet.DTyCoVarSet.

Axiom varTypeTyCoFVs : Var.Var -> FV.FV.

Axiom idRuleVars : Var.Id -> VarSet.VarSet.

Axiom idRuleFVs : Var.Id -> FV.FV.

(* External variables:
     AnnAlt AnnExpr bool list op_zt__ option unit BasicTypes.Activation
     CoreSyn.AnnBind CoreSyn.AnnExpr' CoreSyn.CoreBind CoreSyn.CoreBndr
     CoreSyn.CoreExpr CoreSyn.CoreRule CoreSyn.CoreVect CoreSyn.Unfolding FV.FV
     FV.InterestingVarFun NameSet.NameSet TyCon.TyCon Var.Id Var.Var VarSet.DIdSet
     VarSet.DTyCoVarSet VarSet.DVarSet VarSet.IdSet VarSet.TyCoVarSet VarSet.VarSet
*)
