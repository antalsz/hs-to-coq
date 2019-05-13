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
Require CoreUtils.
Require DynFlags.
Require GHC.Err.

(* Converted type declarations: *)

Inductive EtaInfo : Type
  := EtaVar : Core.Var -> EtaInfo
  |  EtaCo : unit -> EtaInfo.

Definition CheapFun :=
  (Core.CoreExpr -> option unit -> bool)%type.

Inductive ArityType : Type
  := ATop : list BasicTypes.OneShotInfo -> ArityType
  |  ABot : BasicTypes.Arity -> ArityType.

Inductive ArityEnv : Type
  := AE (ae_cheap_fn : CheapFun) (ae_ped_bot : bool) : ArityEnv.

Instance Default__ArityEnv : GHC.Err.Default ArityEnv :=
  GHC.Err.Build_Default _ (AE GHC.Err.default GHC.Err.default).

Definition ae_cheap_fn (arg_0__ : ArityEnv) :=
  let 'AE ae_cheap_fn _ := arg_0__ in
  ae_cheap_fn.

Definition ae_ped_bot (arg_0__ : ArityEnv) :=
  let 'AE _ ae_ped_bot := arg_0__ in
  ae_ped_bot.

(* Converted value declarations: *)

Axiom vanillaArityType : ArityType.

Axiom typeArity : unit -> list BasicTypes.OneShotInfo.

Axiom subst_expr : CoreSubst.Subst -> Core.CoreExpr -> Core.CoreExpr.

Axiom pushCoercion : unit -> list EtaInfo -> list EtaInfo.

Axiom mk_cheap_fn : DynFlags.DynFlags -> CoreUtils.CheapAppFun -> CheapFun.

Axiom mkEtaWW : BasicTypes.Arity ->
                Core.CoreExpr ->
                Core.InScopeSet -> unit -> (Core.InScopeSet * list EtaInfo)%type.

Axiom manifestArity : Core.CoreExpr -> BasicTypes.Arity.

Axiom joinRhsArity : Core.CoreExpr -> BasicTypes.JoinArity.

Axiom getBotArity : ArityType -> option BasicTypes.Arity.

Axiom freshEtaId : nat -> unit -> unit -> (unit * Core.Id)%type.

Axiom floatIn : bool -> ArityType -> ArityType.

Axiom findRhsArity : DynFlags.DynFlags ->
                     Core.Id -> Core.CoreExpr -> BasicTypes.Arity -> (BasicTypes.Arity * bool)%type.

Axiom exprEtaExpandArity : DynFlags.DynFlags ->
                           Core.CoreExpr -> BasicTypes.Arity.

Axiom exprBotStrictness_maybe : Core.CoreExpr ->
                                option (BasicTypes.Arity * Core.StrictSig)%type.

Axiom exprArity : Core.CoreExpr -> BasicTypes.Arity.

Axiom etaInfoAppTy : unit -> list EtaInfo -> unit.

Axiom etaInfoApp : CoreSubst.Subst ->
                   Core.CoreExpr -> list EtaInfo -> Core.CoreExpr.

Axiom etaInfoAbs : list EtaInfo -> Core.CoreExpr -> Core.CoreExpr.

Axiom etaExpandToJoinPointRule : BasicTypes.JoinArity ->
                                 Core.CoreRule -> Core.CoreRule.

Axiom etaExpandToJoinPoint : BasicTypes.JoinArity ->
                             Core.CoreExpr -> (list Core.CoreBndr * Core.CoreExpr)%type.

Axiom etaExpand : BasicTypes.Arity -> Core.CoreExpr -> Core.CoreExpr.

Axiom etaBodyForJoinPoint : nat ->
                            Core.CoreExpr -> (list Core.CoreBndr * Core.CoreExpr)%type.

Axiom arityType : ArityEnv -> Core.CoreExpr -> ArityType.

Axiom arityLam : Core.Id -> ArityType -> ArityType.

Axiom arityApp : ArityType -> bool -> ArityType.

Axiom andArityType : ArityType -> ArityType -> ArityType.

(* Skipping all instances of class `Outputable.Outputable', including
   `CoreArity.Outputable__ArityType' *)

(* Skipping all instances of class `Outputable.Outputable', including
   `CoreArity.Outputable__EtaInfo' *)

(* External variables:
     bool list nat op_zt__ option unit BasicTypes.Arity BasicTypes.JoinArity
     BasicTypes.OneShotInfo Core.CoreBndr Core.CoreExpr Core.CoreRule Core.Id
     Core.InScopeSet Core.StrictSig Core.Var CoreSubst.Subst CoreUtils.CheapAppFun
     DynFlags.DynFlags GHC.Err.Build_Default GHC.Err.Default GHC.Err.default
*)
