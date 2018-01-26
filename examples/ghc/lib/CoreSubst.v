(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Coq.Program.Tactics.
Require Coq.Program.Wf.

(* Preamble *)

Require Import Core.

(* Converted imports: *)

Require Core.
Require CoreSyn.
Require DataCon.
Require GHC.Base.
Require IdInfo.
Require Literal.
Require Name.
Require TyCoRep.
Require UniqSupply.
Require Unique.
Require Var.
Require VarEnv.
Require VarSet.

(* Converted type declarations: *)

Definition OutVar :=
  Core.Var%type.

Definition OutId :=
  Var.Id%type.

Definition OutExpr :=
  CoreSyn.CoreExpr%type.

Definition InVar :=
  Core.Var%type.

Definition InId :=
  Var.Id%type.

Definition InExpr :=
  CoreSyn.CoreExpr%type.

Definition IdSubstEnv :=
  (VarEnv.IdEnv CoreSyn.CoreExpr)%type.

Inductive Subst : Type := Mk_Subst
                         : VarEnv.InScopeSet -> IdSubstEnv -> TyCoRep.TvSubstEnv -> TyCoRep.CvSubstEnv -> Subst.

Inductive ConCont : Type := CC : list
                                 CoreSyn.CoreExpr -> Core.Coercion -> ConCont.
(* Converted value declarations: *)

Axiom substUnfoldingSC : Subst -> CoreSyn.Unfolding -> CoreSyn.Unfolding.

Axiom substBindSC : Subst -> CoreSyn.CoreBind -> (Subst *
                    CoreSyn.CoreBind)%type.

Axiom substExprSC : unit -> Subst -> CoreSyn.CoreExpr -> CoreSyn.CoreExpr.

Axiom isEmptySubst : Subst -> bool.

(* simpleOptPgm skipped *)

Axiom deShadowBinds : CoreSyn.CoreProgram -> CoreSyn.CoreProgram.

Axiom emptySubst : Subst.

Axiom exprIsLambda_maybe : CoreSyn.InScopeEnv -> CoreSyn.CoreExpr -> option
                           (Core.Var * CoreSyn.CoreExpr * list (CoreSyn.Tickish Var.Id))%type.

Axiom pushCoercionIntoLambda
        : VarEnv.InScopeSet -> Core.Var -> CoreSyn.CoreExpr -> Core.Coercion -> option
          (Core.Var * CoreSyn.CoreExpr)%type.

Axiom simpleOptExpr : CoreSyn.CoreExpr -> CoreSyn.CoreExpr.

Axiom substVects : Subst -> list CoreSyn.CoreVect -> list CoreSyn.CoreVect.

Axiom substVect : Subst -> CoreSyn.CoreVect -> CoreSyn.CoreVect.

Axiom simpleOptExprWith : Subst -> InExpr -> OutExpr.

Axiom simple_opt_bind' : Subst -> CoreSyn.CoreBind -> (Subst * option
                         CoreSyn.CoreBind)%type.

Axiom simple_opt_bind : Subst -> CoreSyn.CoreBind -> (Subst * option
                        CoreSyn.CoreBind)%type.

Axiom simple_app : Subst -> InExpr -> list OutExpr -> CoreSyn.CoreExpr.

Axiom simple_opt_expr : Subst -> InExpr -> OutExpr.

Axiom exprIsConApp_maybe : CoreSyn.InScopeEnv -> CoreSyn.CoreExpr -> option
                           (DataCon.DataCon * list Core.Type_ * list CoreSyn.CoreExpr)%type.

Axiom mkEmptySubst : VarEnv.InScopeSet -> Subst.

Axiom mkSubst
        : VarEnv.InScopeSet -> TyCoRep.TvSubstEnv -> TyCoRep.CvSubstEnv -> IdSubstEnv -> Subst.

Axiom substInScope : Subst -> VarEnv.InScopeSet.

Axiom zapSubstEnv : Subst -> Subst.

Axiom simple_opt_out_bind : Subst -> (InVar * OutExpr)%type -> (Subst * option
                            CoreSyn.CoreBind)%type.

Axiom maybe_substitute : Subst -> InVar -> OutExpr -> option Subst.

Axiom extendSubstWithVar : Subst -> Core.Var -> Core.Var -> Subst.

Axiom extendSubstList : Subst -> list (Core.Var *
                                      CoreSyn.CoreArg)%type -> Subst.

Axiom extendSubst : Subst -> Core.Var -> CoreSyn.CoreArg -> Subst.

Axiom extendIdSubst : Subst -> Var.Id -> CoreSyn.CoreExpr -> Subst.

Axiom extendIdSubstList : Subst -> list (Var.Id *
                                        CoreSyn.CoreExpr)%type -> Subst.

Axiom extendTvSubstList : Subst -> list (TyVar * Core.Type_)%type -> Subst.

Axiom extendTvSubst : Subst -> TyVar -> Core.Type_ -> Subst.

Axiom extendCvSubst : Subst -> CoVar -> Core.Coercion -> Subst.

Axiom substRulesForImportedIds : Subst -> list CoreSyn.CoreRule -> list
                                 CoreSyn.CoreRule.

Axiom add_info : Subst -> InVar -> OutVar -> OutVar.

Axiom cloneRecIdBndrs : Subst -> UniqSupply.UniqSupply -> list Var.Id -> (Subst
                        * list Var.Id)%type.

Axiom cloneBndrs : Subst -> UniqSupply.UniqSupply -> list Core.Var -> (Subst *
                   list Core.Var)%type.

Axiom cloneBndr : Subst -> Unique.Unique -> Core.Var -> (Subst * Core.Var)%type.

Axiom cloneIdBndrs : Subst -> UniqSupply.UniqSupply -> list Var.Id -> (Subst *
                     list Var.Id)%type.

Axiom cloneIdBndr : Subst -> UniqSupply.UniqSupply -> Var.Id -> (Subst *
                    Var.Id)%type.

Axiom clone_id : Subst -> Subst -> (Var.Id * Unique.Unique)%type -> (Subst *
                 Var.Id)%type.

Axiom substRecBndrs : Subst -> list Var.Id -> (Subst * list Var.Id)%type.

Axiom substRule
        : Subst -> (Name.Name -> Name.Name) -> CoreSyn.CoreRule -> CoreSyn.CoreRule.

Axiom substSpec : Subst -> Var.Id -> IdInfo.RuleInfo -> IdInfo.RuleInfo.

Axiom substBndrs : Subst -> list Core.Var -> (Subst * list Core.Var)%type.

Axiom substExpr : unit -> Subst -> CoreSyn.CoreExpr -> CoreSyn.CoreExpr.

Axiom substUnfolding : Subst -> CoreSyn.Unfolding -> CoreSyn.Unfolding.

Axiom substIdInfo : Subst -> Var.Id -> IdInfo.IdInfo -> option IdInfo.IdInfo.

Axiom substIdBndr : unit -> Subst -> Subst -> Var.Id -> (Subst * Var.Id)%type.

Axiom substBndr : Subst -> Core.Var -> (Subst * Core.Var)%type.

Axiom substBind : Subst -> CoreSyn.CoreBind -> (Subst * CoreSyn.CoreBind)%type.

Axiom subst_expr : unit -> Subst -> CoreSyn.CoreExpr -> CoreSyn.CoreExpr.

Axiom substTickish : Subst -> CoreSyn.Tickish Var.Id -> CoreSyn.Tickish Var.Id.

Axiom substDVarSet : Subst -> VarSet.DVarSet -> VarSet.DVarSet.

Axiom substIdOcc : Subst -> Var.Id -> Var.Id.

Axiom lookupIdSubst : unit -> Subst -> Var.Id -> CoreSyn.CoreExpr.

Axiom lookupTCvSubst : Subst -> TyVar -> Core.Type_.

Axiom delBndr : Subst -> Core.Var -> Subst.

Axiom delBndrs : Subst -> list Core.Var -> Subst.

Axiom mkOpenSubst : VarEnv.InScopeSet -> list (Core.Var *
                                              CoreSyn.CoreArg)%type -> Subst.

Axiom isInScope : Core.Var -> Subst -> bool.

Axiom addInScopeSet : Subst -> VarSet.VarSet -> Subst.

Axiom extendInScope : Subst -> Core.Var -> Subst.

Axiom extendInScopeList : Subst -> list Core.Var -> Subst.

Axiom extendInScopeIds : Subst -> list Var.Id -> Subst.

Axiom setInScope : Subst -> VarEnv.InScopeSet -> Subst.

Axiom subst_opt_bndrs : Subst -> list InVar -> (Subst * list OutVar)%type.

Axiom subst_opt_bndr : Subst -> InVar -> (Subst * OutVar)%type.

Axiom substTyVarBndr : Subst -> TyVar -> (Subst * TyVar)%type.

Axiom cloneTyVarBndr : Subst -> TyVar -> Unique.Unique -> (Subst * TyVar)%type.

Axiom substCoVarBndr : Subst -> TyVar -> (Subst * TyVar)%type.

Axiom subst_opt_id_bndr : Subst -> InId -> (Subst * OutId)%type.

Axiom substIdType : Subst -> Var.Id -> Var.Id.

Axiom substTy : Subst -> Core.Type_ -> Core.Type_.

Axiom substCo : Subst -> Core.Coercion -> Core.Coercion.

Axiom getTCvSubst : Subst -> TyCoRep.TCvSubst.

Axiom simpleUnfoldingFun : CoreSyn.IdUnfoldingFun.

Axiom dealWithStringLiteral
        : Core.Var -> GHC.Base.String -> Core.Coercion -> option (DataCon.DataCon * list
                                                                 Core.Type_ * list CoreSyn.CoreExpr)%type.

Axiom dealWithCoercion : Core.Coercion -> DataCon.DataCon -> list
                         CoreSyn.CoreExpr -> option (DataCon.DataCon * list Core.Type_ * list
                                                    CoreSyn.CoreExpr)%type.

Axiom exprIsLiteral_maybe : CoreSyn.InScopeEnv -> CoreSyn.CoreExpr -> option
                            Literal.Literal.

(* Unbound variables:
     CoVar TyVar bool list op_zt__ option unit Core.Coercion Core.Type_ Core.Var
     CoreSyn.CoreArg CoreSyn.CoreBind CoreSyn.CoreExpr CoreSyn.CoreProgram
     CoreSyn.CoreRule CoreSyn.CoreVect CoreSyn.IdUnfoldingFun CoreSyn.InScopeEnv
     CoreSyn.Tickish CoreSyn.Unfolding DataCon.DataCon GHC.Base.String IdInfo.IdInfo
     IdInfo.RuleInfo Literal.Literal Name.Name TyCoRep.CvSubstEnv TyCoRep.TCvSubst
     TyCoRep.TvSubstEnv UniqSupply.UniqSupply Unique.Unique Var.Id VarEnv.IdEnv
     VarEnv.InScopeSet VarSet.DVarSet VarSet.VarSet
*)
