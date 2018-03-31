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

Require CoreSyn.
Require CoreType.
Require DataCon.
Require GHC.Base.
Require IdInfo.
Require Literal.
Require Name.
Require UniqSupply.
Require Unique.
Require VarEnv.
Require VarSet.

(* Converted type declarations: *)

Definition OutVar :=
  CoreType.Var%type.

Definition OutId :=
  CoreType.Id%type.

Definition OutExpr :=
  CoreSyn.CoreExpr%type.

Definition InVar :=
  CoreType.Var%type.

Definition InId :=
  CoreType.Id%type.

Definition InExpr :=
  CoreSyn.CoreExpr%type.

Definition IdSubstEnv :=
  (VarEnv.IdEnv CoreSyn.CoreExpr)%type.

Inductive Subst : Type
  := Mk_Subst
   : VarEnv.InScopeSet ->
     IdSubstEnv -> CoreType.TvSubstEnv -> CoreType.CvSubstEnv -> Subst.

Inductive ConCont : Type
  := CC : list CoreSyn.CoreExpr -> CoreType.Coercion -> ConCont.
(* Converted value declarations: *)

Axiom substUnfoldingSC : Subst -> CoreSyn.Unfolding -> CoreSyn.Unfolding.

Axiom substBindSC : Subst ->
                    CoreSyn.CoreBind -> (Subst * CoreSyn.CoreBind)%type.

Axiom substExprSC : unit -> Subst -> CoreSyn.CoreExpr -> CoreSyn.CoreExpr.

Axiom isEmptySubst : Subst -> bool.

(* simpleOptPgm skipped *)

Axiom deShadowBinds : CoreSyn.CoreProgram -> CoreSyn.CoreProgram.

Axiom emptySubst : Subst.

Axiom exprIsLambda_maybe : CoreSyn.InScopeEnv ->
                           CoreSyn.CoreExpr ->
                           option (CoreType.Var * CoreSyn.CoreExpr *
                                   list (CoreSyn.Tickish CoreType.Id))%type.

Axiom pushCoercionIntoLambda : VarEnv.InScopeSet ->
                               CoreType.Var ->
                               CoreSyn.CoreExpr ->
                               CoreType.Coercion -> option (CoreType.Var * CoreSyn.CoreExpr)%type.

Axiom simpleOptExpr : CoreSyn.CoreExpr -> CoreSyn.CoreExpr.

Axiom substVects : Subst -> list CoreSyn.CoreVect -> list CoreSyn.CoreVect.

Axiom substVect : Subst -> CoreSyn.CoreVect -> CoreSyn.CoreVect.

Axiom simpleOptExprWith : Subst -> InExpr -> OutExpr.

Axiom simple_opt_bind' : Subst ->
                         CoreSyn.CoreBind -> (Subst * option CoreSyn.CoreBind)%type.

Axiom simple_opt_bind : Subst ->
                        CoreSyn.CoreBind -> (Subst * option CoreSyn.CoreBind)%type.

Axiom simple_app : Subst -> InExpr -> list OutExpr -> CoreSyn.CoreExpr.

Axiom simple_opt_expr : Subst -> InExpr -> OutExpr.

Axiom exprIsConApp_maybe : CoreSyn.InScopeEnv ->
                           CoreSyn.CoreExpr ->
                           option (DataCon.DataCon * list CoreType.Type_ * list CoreSyn.CoreExpr)%type.

Axiom mkEmptySubst : VarEnv.InScopeSet -> Subst.

Axiom mkSubst : VarEnv.InScopeSet ->
                CoreType.TvSubstEnv -> CoreType.CvSubstEnv -> IdSubstEnv -> Subst.

Axiom substInScope : Subst -> VarEnv.InScopeSet.

Axiom zapSubstEnv : Subst -> Subst.

Axiom simple_opt_out_bind : Subst ->
                            (InVar * OutExpr)%type -> (Subst * option CoreSyn.CoreBind)%type.

Axiom maybe_substitute : Subst -> InVar -> OutExpr -> option Subst.

Axiom extendSubstWithVar : Subst -> CoreType.Var -> CoreType.Var -> Subst.

Axiom extendSubstList : Subst ->
                        list (CoreType.Var * CoreSyn.CoreArg)%type -> Subst.

Axiom extendSubst : Subst -> CoreType.Var -> CoreSyn.CoreArg -> Subst.

Axiom extendIdSubst : Subst -> CoreType.Id -> CoreSyn.CoreExpr -> Subst.

Axiom extendIdSubstList : Subst ->
                          list (CoreType.Id * CoreSyn.CoreExpr)%type -> Subst.

Axiom extendTvSubstList : Subst ->
                          list (CoreType.TyVar * CoreType.Type_)%type -> Subst.

Axiom extendTvSubst : Subst -> CoreType.TyVar -> CoreType.Type_ -> Subst.

Axiom extendCvSubst : Subst -> CoreType.CoVar -> CoreType.Coercion -> Subst.

Axiom substRulesForImportedIds : Subst ->
                                 list CoreSyn.CoreRule -> list CoreSyn.CoreRule.

Axiom add_info : Subst -> InVar -> OutVar -> OutVar.

Axiom cloneRecIdBndrs : Subst ->
                        UniqSupply.UniqSupply -> list CoreType.Id -> (Subst * list CoreType.Id)%type.

Axiom cloneBndrs : Subst ->
                   UniqSupply.UniqSupply -> list CoreType.Var -> (Subst * list CoreType.Var)%type.

Axiom cloneBndr : Subst ->
                  Unique.Unique -> CoreType.Var -> (Subst * CoreType.Var)%type.

Axiom cloneIdBndrs : Subst ->
                     UniqSupply.UniqSupply -> list CoreType.Id -> (Subst * list CoreType.Id)%type.

Axiom cloneIdBndr : Subst ->
                    UniqSupply.UniqSupply -> CoreType.Id -> (Subst * CoreType.Id)%type.

Axiom clone_id : Subst ->
                 Subst -> (CoreType.Id * Unique.Unique)%type -> (Subst * CoreType.Id)%type.

Axiom substRecBndrs : Subst ->
                      list CoreType.Id -> (Subst * list CoreType.Id)%type.

Axiom substRule : Subst ->
                  (Name.Name -> Name.Name) -> CoreSyn.CoreRule -> CoreSyn.CoreRule.

Axiom substSpec : Subst -> CoreType.Id -> IdInfo.RuleInfo -> IdInfo.RuleInfo.

Axiom substBndrs : Subst ->
                   list CoreType.Var -> (Subst * list CoreType.Var)%type.

Axiom substExpr : unit -> Subst -> CoreSyn.CoreExpr -> CoreSyn.CoreExpr.

Axiom substUnfolding : Subst -> CoreSyn.Unfolding -> CoreSyn.Unfolding.

Axiom substIdInfo : Subst ->
                    CoreType.Id -> IdInfo.IdInfo -> option IdInfo.IdInfo.

Axiom substIdBndr : unit ->
                    Subst -> Subst -> CoreType.Id -> (Subst * CoreType.Id)%type.

Axiom substBndr : Subst -> CoreType.Var -> (Subst * CoreType.Var)%type.

Axiom substBind : Subst -> CoreSyn.CoreBind -> (Subst * CoreSyn.CoreBind)%type.

Axiom subst_expr : unit -> Subst -> CoreSyn.CoreExpr -> CoreSyn.CoreExpr.

Axiom substTickish : Subst ->
                     CoreSyn.Tickish CoreType.Id -> CoreSyn.Tickish CoreType.Id.

Axiom substDVarSet : Subst -> VarSet.DVarSet -> VarSet.DVarSet.

Axiom substIdOcc : Subst -> CoreType.Id -> CoreType.Id.

Axiom lookupIdSubst : unit -> Subst -> CoreType.Id -> CoreSyn.CoreExpr.

Axiom lookupTCvSubst : Subst -> CoreType.TyVar -> CoreType.Type_.

Axiom delBndr : Subst -> CoreType.Var -> Subst.

Axiom delBndrs : Subst -> list CoreType.Var -> Subst.

Axiom mkOpenSubst : VarEnv.InScopeSet ->
                    list (CoreType.Var * CoreSyn.CoreArg)%type -> Subst.

Axiom isInScope : CoreType.Var -> Subst -> bool.

Axiom addInScopeSet : Subst -> VarSet.VarSet -> Subst.

Axiom extendInScope : Subst -> CoreType.Var -> Subst.

Axiom extendInScopeList : Subst -> list CoreType.Var -> Subst.

Axiom extendInScopeIds : Subst -> list CoreType.Id -> Subst.

Axiom setInScope : Subst -> VarEnv.InScopeSet -> Subst.

Axiom subst_opt_bndrs : Subst -> list InVar -> (Subst * list OutVar)%type.

Axiom subst_opt_bndr : Subst -> InVar -> (Subst * OutVar)%type.

Axiom substTyVarBndr : Subst -> CoreType.TyVar -> (Subst * CoreType.TyVar)%type.

Axiom cloneTyVarBndr : Subst ->
                       CoreType.TyVar -> Unique.Unique -> (Subst * CoreType.TyVar)%type.

Axiom substCoVarBndr : Subst -> CoreType.TyVar -> (Subst * CoreType.TyVar)%type.

Axiom subst_opt_id_bndr : Subst -> InId -> (Subst * OutId)%type.

Axiom substIdType : Subst -> CoreType.Id -> CoreType.Id.

Axiom substTy : Subst -> CoreType.Type_ -> CoreType.Type_.

Axiom substCo : Subst -> CoreType.Coercion -> CoreType.Coercion.

Axiom getTCvSubst : Subst -> CoreType.TCvSubst.

Axiom simpleUnfoldingFun : CoreSyn.IdUnfoldingFun.

Axiom dealWithStringLiteral : CoreType.Var ->
                              GHC.Base.String ->
                              CoreType.Coercion ->
                              option (DataCon.DataCon * list CoreType.Type_ * list CoreSyn.CoreExpr)%type.

Axiom dealWithCoercion : CoreType.Coercion ->
                         DataCon.DataCon ->
                         list CoreSyn.CoreExpr ->
                         option (DataCon.DataCon * list CoreType.Type_ * list CoreSyn.CoreExpr)%type.

Axiom exprIsLiteral_maybe : CoreSyn.InScopeEnv ->
                            CoreSyn.CoreExpr -> option Literal.Literal.

(* Unbound variables:
     bool list op_zt__ option unit CoreSyn.CoreArg CoreSyn.CoreBind CoreSyn.CoreExpr
     CoreSyn.CoreProgram CoreSyn.CoreRule CoreSyn.CoreVect CoreSyn.IdUnfoldingFun
     CoreSyn.InScopeEnv CoreSyn.Tickish CoreSyn.Unfolding CoreType.CoVar
     CoreType.Coercion CoreType.CvSubstEnv CoreType.Id CoreType.TCvSubst
     CoreType.TvSubstEnv CoreType.TyVar CoreType.Type_ CoreType.Var DataCon.DataCon
     GHC.Base.String IdInfo.IdInfo IdInfo.RuleInfo Literal.Literal Name.Name
     UniqSupply.UniqSupply Unique.Unique VarEnv.IdEnv VarEnv.InScopeSet
     VarSet.DVarSet VarSet.VarSet
*)
