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
Require IdInfo.
Require Name.
Require UniqSupply.
Require Unique.
Require VarEnv.
Require VarSet.

(* Converted type declarations: *)

Definition IdSubstEnv :=
  (VarEnv.IdEnv CoreSyn.CoreExpr)%type.

Inductive Subst : Type
  := Mk_Subst
   : VarEnv.InScopeSet ->
     IdSubstEnv -> CoreType.TvSubstEnv -> CoreType.CvSubstEnv -> Subst.
(* Converted value declarations: *)

Axiom substUnfoldingSC : Subst -> CoreSyn.Unfolding -> CoreSyn.Unfolding.

Axiom substBindSC : Subst ->
                    CoreSyn.CoreBind -> (Subst * CoreSyn.CoreBind)%type.

Axiom substExprSC : unit -> Subst -> CoreSyn.CoreExpr -> CoreSyn.CoreExpr.

Axiom isEmptySubst : Subst -> bool.

Axiom deShadowBinds : CoreSyn.CoreProgram -> CoreSyn.CoreProgram.

Axiom emptySubst : Subst.

Axiom mkEmptySubst : VarEnv.InScopeSet -> Subst.

Axiom mkSubst : VarEnv.InScopeSet ->
                CoreType.TvSubstEnv -> CoreType.CvSubstEnv -> IdSubstEnv -> Subst.

Axiom substInScope : Subst -> VarEnv.InScopeSet.

Axiom zapSubstEnv : Subst -> Subst.

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

Axiom substTyVarBndr : Subst -> CoreType.TyVar -> (Subst * CoreType.TyVar)%type.

Axiom cloneTyVarBndr : Subst ->
                       CoreType.TyVar -> Unique.Unique -> (Subst * CoreType.TyVar)%type.

Axiom substCoVarBndr : Subst -> CoreType.TyVar -> (Subst * CoreType.TyVar)%type.

Axiom substIdType : Subst -> CoreType.Id -> CoreType.Id.

Axiom substTy : Subst -> CoreType.Type_ -> CoreType.Type_.

Axiom substCo : Subst -> CoreType.Coercion -> CoreType.Coercion.

Axiom getTCvSubst : Subst -> CoreType.TCvSubst.

(* External variables:
     bool list op_zt__ option unit CoreSyn.CoreArg CoreSyn.CoreBind CoreSyn.CoreExpr
     CoreSyn.CoreProgram CoreSyn.CoreRule CoreSyn.Tickish CoreSyn.Unfolding
     CoreType.CoVar CoreType.Coercion CoreType.CvSubstEnv CoreType.Id
     CoreType.TCvSubst CoreType.TvSubstEnv CoreType.TyVar CoreType.Type_ CoreType.Var
     IdInfo.IdInfo IdInfo.RuleInfo Name.Name UniqSupply.UniqSupply Unique.Unique
     VarEnv.IdEnv VarEnv.InScopeSet VarSet.DVarSet VarSet.VarSet
*)
