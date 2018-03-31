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
Require CoreSubst.
Require CoreSyn.
Require CoreType.
Require CoreUtils.
Require Demand.
Require DynFlags.
Require GHC.Num.
Require VarEnv.

(* Converted type declarations: *)

Inductive EtaInfo : Type
  := EtaVar : CoreType.Var -> EtaInfo
  |  EtaCo : CoreType.Coercion -> EtaInfo.

Definition CheapFun :=
  (CoreSyn.CoreExpr -> option CoreType.Type_ -> bool)%type.

Inductive ArityType : Type
  := ATop : list BasicTypes.OneShotInfo -> ArityType
  |  ABot : BasicTypes.Arity -> ArityType.

Inductive ArityEnv : Type := AE : CheapFun -> bool -> ArityEnv.

Definition ae_cheap_fn (arg_0__ : ArityEnv) :=
  let 'AE ae_cheap_fn _ := arg_0__ in
  ae_cheap_fn.

Definition ae_ped_bot (arg_1__ : ArityEnv) :=
  let 'AE _ ae_ped_bot := arg_1__ in
  ae_ped_bot.
(* Converted value declarations: *)

Axiom manifestArity : CoreSyn.CoreExpr -> BasicTypes.Arity.

Axiom exprArity : CoreSyn.CoreExpr -> BasicTypes.Arity.

Axiom findRhsArity : DynFlags.DynFlags ->
                     CoreType.Id -> CoreSyn.CoreExpr -> BasicTypes.Arity -> BasicTypes.Arity.

Axiom rhsEtaExpandArity : DynFlags.DynFlags ->
                          CoreUtils.CheapAppFun -> CoreSyn.CoreExpr -> BasicTypes.Arity.

Axiom exprEtaExpandArity : DynFlags.DynFlags ->
                           CoreSyn.CoreExpr -> BasicTypes.Arity.

Axiom exprBotStrictness_maybe : CoreSyn.CoreExpr ->
                                option (BasicTypes.Arity * Demand.StrictSig)%type.

Axiom arityType : ArityEnv -> CoreSyn.CoreExpr -> ArityType.

Axiom typeArity : CoreType.Type_ -> list BasicTypes.OneShotInfo.

Axiom vanillaArityType : ArityType.

Axiom getBotArity : ArityType -> option BasicTypes.Arity.

Axiom mk_cheap_fn : DynFlags.DynFlags -> CoreUtils.CheapAppFun -> CheapFun.

Axiom arityLam : CoreType.Id -> ArityType -> ArityType.

Axiom arityApp : ArityType -> bool -> ArityType.

Axiom floatIn : bool -> ArityType -> ArityType.

Axiom andArityType : ArityType -> ArityType -> ArityType.

Axiom etaExpand : BasicTypes.Arity -> CoreSyn.CoreExpr -> CoreSyn.CoreExpr.

Axiom etaInfoApp : CoreSubst.Subst ->
                   CoreSyn.CoreExpr -> list EtaInfo -> CoreSyn.CoreExpr.

Axiom pushCoercion : CoreType.Coercion -> list EtaInfo -> list EtaInfo.

Axiom etaInfoAbs : list EtaInfo -> CoreSyn.CoreExpr -> CoreSyn.CoreExpr.

Axiom mkEtaWW : BasicTypes.Arity ->
                CoreSyn.CoreExpr ->
                VarEnv.InScopeSet -> CoreType.Type_ -> (VarEnv.InScopeSet * list EtaInfo)%type.

Axiom subst_expr : CoreSubst.Subst -> CoreSyn.CoreExpr -> CoreSyn.CoreExpr.

Axiom subst_bind : CoreSubst.Subst ->
                   CoreSyn.CoreBind -> (CoreSubst.Subst * CoreSyn.CoreBind)%type.

Axiom freshEtaVar : GHC.Num.Int ->
                    CoreType.TCvSubst -> CoreType.Type_ -> (CoreType.TCvSubst * CoreType.Var)%type.

(* Unbound variables:
     bool list op_zt__ option BasicTypes.Arity BasicTypes.OneShotInfo CoreSubst.Subst
     CoreSyn.CoreBind CoreSyn.CoreExpr CoreType.Coercion CoreType.Id
     CoreType.TCvSubst CoreType.Type_ CoreType.Var CoreUtils.CheapAppFun
     Demand.StrictSig DynFlags.DynFlags GHC.Num.Int VarEnv.InScopeSet
*)
