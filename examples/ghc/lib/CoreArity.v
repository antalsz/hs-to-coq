(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Coq.Program.Tactics.
Require Coq.Program.Wf.

(* Converted imports: *)

Require BasicTypes.
Require Core.
Require CoreSubst.
Require CoreSyn.
Require CoreUtils.
Require Demand.
Require DynFlags.
Require GHC.Num.
Require Var.
Require VarEnv.

(* Converted type declarations: *)

Inductive EtaInfo : Type := EtaVar : Core.Var -> EtaInfo
                         |  EtaCo : Core.Coercion -> EtaInfo.

Definition CheapFun :=
  (CoreSyn.CoreExpr -> option Core.Type_ -> bool)%type.

Inductive ArityType : Type := ATop : list BasicTypes.OneShotInfo -> ArityType
                           |  ABot : BasicTypes.Arity -> ArityType.

Inductive ArityEnv : Type := AE : CheapFun -> bool -> ArityEnv.

Definition ae_cheap_fn (arg_0__ : ArityEnv) :=
  match arg_0__ with
    | AE ae_cheap_fn _ => ae_cheap_fn
  end.

Definition ae_ped_bot (arg_1__ : ArityEnv) :=
  match arg_1__ with
    | AE _ ae_ped_bot => ae_ped_bot
  end.
(* Converted value declarations: *)

Axiom manifestArity : CoreSyn.CoreExpr -> BasicTypes.Arity.

Axiom exprArity : CoreSyn.CoreExpr -> BasicTypes.Arity.

Axiom findRhsArity
        : DynFlags.DynFlags -> Var.Id -> CoreSyn.CoreExpr -> BasicTypes.Arity -> BasicTypes.Arity.

Axiom rhsEtaExpandArity
        : DynFlags.DynFlags -> CoreUtils.CheapAppFun -> CoreSyn.CoreExpr -> BasicTypes.Arity.

Axiom exprEtaExpandArity
        : DynFlags.DynFlags -> CoreSyn.CoreExpr -> BasicTypes.Arity.

Axiom exprBotStrictness_maybe : CoreSyn.CoreExpr -> option (BasicTypes.Arity *
                                                           Demand.StrictSig)%type.

Axiom arityType : ArityEnv -> CoreSyn.CoreExpr -> ArityType.

Axiom typeArity : Core.Type_ -> list BasicTypes.OneShotInfo.

Axiom vanillaArityType : ArityType.

Axiom getBotArity : ArityType -> option BasicTypes.Arity.

Axiom mk_cheap_fn : DynFlags.DynFlags -> CoreUtils.CheapAppFun -> CheapFun.

Axiom arityLam : Var.Id -> ArityType -> ArityType.

Axiom arityApp : ArityType -> bool -> ArityType.

Axiom floatIn : bool -> ArityType -> ArityType.

Axiom andArityType : ArityType -> ArityType -> ArityType.

Axiom etaExpand : BasicTypes.Arity -> CoreSyn.CoreExpr -> CoreSyn.CoreExpr.

Axiom etaInfoApp : CoreSubst.Subst -> CoreSyn.CoreExpr -> list
                   EtaInfo -> CoreSyn.CoreExpr.

Axiom pushCoercion : Core.Coercion -> list EtaInfo -> list EtaInfo.

Axiom etaInfoAbs : list EtaInfo -> CoreSyn.CoreExpr -> CoreSyn.CoreExpr.

Axiom mkEtaWW
        : BasicTypes.Arity -> CoreSyn.CoreExpr -> VarEnv.InScopeSet -> Core.Type_ -> (VarEnv.InScopeSet
          * list EtaInfo)%type.

Axiom subst_expr : CoreSubst.Subst -> CoreSyn.CoreExpr -> CoreSyn.CoreExpr.

Axiom subst_bind : CoreSubst.Subst -> CoreSyn.CoreBind -> (CoreSubst.Subst *
                   CoreSyn.CoreBind)%type.

Axiom freshEtaVar
        : GHC.Num.Int -> TyCoRep.TCvSubst -> Core.Type_ -> (TyCoRep.TCvSubst *
          Core.Var)%type.

(* Unbound variables:
     bool list op_zt__ option BasicTypes.Arity BasicTypes.OneShotInfo Core.Coercion
     Core.Type_ Core.Var CoreSubst.Subst CoreSyn.CoreBind CoreSyn.CoreExpr
     CoreUtils.CheapAppFun Demand.StrictSig DynFlags.DynFlags GHC.Num.Int
     TyCoRep.TCvSubst Var.Id VarEnv.InScopeSet
*)
