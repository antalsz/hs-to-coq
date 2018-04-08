(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Coq.Program.Tactics.
Require Coq.Program.Wf.

(* Preamble *)



(* Converted imports: *)

Require CoreSyn.
Require IdInfo.
Require Name.
Require UniqSupply.
Require Unique.
Require Var.
Require VarEnv.
Require VarSet.

(* Converted type declarations: *)

Definition IdSubstEnv :=
  (VarEnv.IdEnv CoreSyn.CoreExpr)%type.

Inductive Subst : Type
  := Mk_Subst
   : VarEnv.InScopeSet ->
     IdSubstEnv -> TyCoRep.TvSubstEnv -> TyCoRep.CvSubstEnv -> Subst.
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
                TyCoRep.TvSubstEnv -> TyCoRep.CvSubstEnv -> IdSubstEnv -> Subst.

Axiom substInScope : Subst -> VarEnv.InScopeSet.

Axiom zapSubstEnv : Subst -> Subst.

Axiom extendSubstWithVar : Subst -> Var.Var -> Var.Var -> Subst.

Axiom extendSubstList : Subst -> list (Var.Var * CoreSyn.CoreArg)%type -> Subst.

Axiom extendSubst : Subst -> Var.Var -> CoreSyn.CoreArg -> Subst.

Axiom extendIdSubst : Subst -> Var.Id -> CoreSyn.CoreExpr -> Subst.

Axiom extendIdSubstList : Subst ->
                          list (Var.Id * CoreSyn.CoreExpr)%type -> Subst.

Axiom extendTvSubstList : Subst -> list (Var.TyVar * unit)%type -> Subst.

Axiom extendTvSubst : Subst -> Var.TyVar -> unit -> Subst.

Axiom extendCvSubst : Subst -> Var.CoVar -> unit -> Subst.

Axiom substRulesForImportedIds : Subst ->
                                 list CoreSyn.CoreRule -> list CoreSyn.CoreRule.

Axiom cloneRecIdBndrs : Subst ->
                        UniqSupply.UniqSupply -> list Var.Id -> (Subst * list Var.Id)%type.

Axiom cloneBndrs : Subst ->
                   UniqSupply.UniqSupply -> list Var.Var -> (Subst * list Var.Var)%type.

Axiom cloneBndr : Subst -> Unique.Unique -> Var.Var -> (Subst * Var.Var)%type.

Axiom cloneIdBndrs : Subst ->
                     UniqSupply.UniqSupply -> list Var.Id -> (Subst * list Var.Id)%type.

Axiom cloneIdBndr : Subst ->
                    UniqSupply.UniqSupply -> Var.Id -> (Subst * Var.Id)%type.

Axiom clone_id : Subst ->
                 Subst -> (Var.Id * Unique.Unique)%type -> (Subst * Var.Id)%type.

Axiom substRecBndrs : Subst -> list Var.Id -> (Subst * list Var.Id)%type.

Axiom substRule : Subst ->
                  (Name.Name -> Name.Name) -> CoreSyn.CoreRule -> CoreSyn.CoreRule.

Axiom substSpec : Subst -> Var.Id -> IdInfo.RuleInfo -> IdInfo.RuleInfo.

Axiom substBndrs : Subst -> list Var.Var -> (Subst * list Var.Var)%type.

Axiom substExpr : unit -> Subst -> CoreSyn.CoreExpr -> CoreSyn.CoreExpr.

Axiom substUnfolding : Subst -> CoreSyn.Unfolding -> CoreSyn.Unfolding.

Axiom substIdInfo : Subst -> Var.Id -> IdInfo.IdInfo -> option IdInfo.IdInfo.

Axiom substIdBndr : unit -> Subst -> Subst -> Var.Id -> (Subst * Var.Id)%type.

Axiom substBndr : Subst -> Var.Var -> (Subst * Var.Var)%type.

Axiom substBind : Subst -> CoreSyn.CoreBind -> (Subst * CoreSyn.CoreBind)%type.

Axiom subst_expr : unit -> Subst -> CoreSyn.CoreExpr -> CoreSyn.CoreExpr.

Axiom substTickish : Subst -> CoreSyn.Tickish Var.Id -> CoreSyn.Tickish Var.Id.

Axiom substDVarSet : Subst -> VarSet.DVarSet -> VarSet.DVarSet.

Axiom substIdOcc : Subst -> Var.Id -> Var.Id.

Axiom lookupIdSubst : unit -> Subst -> Var.Id -> CoreSyn.CoreExpr.

Axiom lookupTCvSubst : Subst -> Var.TyVar -> unit.

Axiom delBndr : Subst -> Var.Var -> Subst.

Axiom delBndrs : Subst -> list Var.Var -> Subst.

Axiom mkOpenSubst : VarEnv.InScopeSet ->
                    list (Var.Var * CoreSyn.CoreArg)%type -> Subst.

Axiom isInScope : Var.Var -> Subst -> bool.

Axiom addInScopeSet : Subst -> VarSet.VarSet -> Subst.

Axiom extendInScope : Subst -> Var.Var -> Subst.

Axiom extendInScopeList : Subst -> list Var.Var -> Subst.

Axiom extendInScopeIds : Subst -> list Var.Id -> Subst.

Axiom setInScope : Subst -> VarEnv.InScopeSet -> Subst.

Axiom substTyVarBndr : Subst -> Var.TyVar -> (Subst * Var.TyVar)%type.

Axiom cloneTyVarBndr : Subst ->
                       Var.TyVar -> Unique.Unique -> (Subst * Var.TyVar)%type.

Axiom substCoVarBndr : Subst -> Var.TyVar -> (Subst * Var.TyVar)%type.

Axiom substIdType : Subst -> Var.Id -> Var.Id.

Axiom substTy : Subst -> unit -> unit.

Axiom substCo : Subst -> unit -> unit.

Axiom getTCvSubst : Subst -> TyCoRep.TCvSubst.

(* External variables:
     bool list op_zt__ option unit CoreSyn.CoreArg CoreSyn.CoreBind CoreSyn.CoreExpr
     CoreSyn.CoreProgram CoreSyn.CoreRule CoreSyn.Tickish CoreSyn.Unfolding
     IdInfo.IdInfo IdInfo.RuleInfo Name.Name TyCoRep.CvSubstEnv TyCoRep.TCvSubst
     TyCoRep.TvSubstEnv UniqSupply.UniqSupply Unique.Unique Var.CoVar Var.Id
     Var.TyVar Var.Var VarEnv.IdEnv VarEnv.InScopeSet VarSet.DVarSet VarSet.VarSet
*)
