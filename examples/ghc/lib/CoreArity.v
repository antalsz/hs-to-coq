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

(* Converted type declarations: *)

Inductive EtaInfo : Type
  := EtaVar : Core.Var -> EtaInfo
  |  EtaCo : unit -> EtaInfo.

Definition CheapFun :=
  (Core.CoreExpr -> option unit -> bool)%type.

Inductive ArityType : Type
  := ATop : list BasicTypes.OneShotInfo -> ArityType
  |  ABot : nat -> ArityType.

Inductive ArityEnv : Type := AE : CheapFun -> bool -> ArityEnv.

Definition ae_cheap_fn (arg_0__ : ArityEnv) :=
  let 'AE ae_cheap_fn _ := arg_0__ in
  ae_cheap_fn.

Definition ae_ped_bot (arg_0__ : ArityEnv) :=
  let 'AE _ ae_ped_bot := arg_0__ in
  ae_ped_bot.
(* Converted value declarations: *)

(* Skipping instance Outputable__EtaInfo of class Outputable *)

(* Skipping instance Outputable__ArityType of class Outputable *)

Axiom manifestArity : Core.CoreExpr -> nat.

Axiom joinRhsArity : Core.CoreExpr -> BasicTypes.JoinArity.

Axiom exprArity : Core.CoreExpr -> nat.

Axiom findRhsArity : DynFlags.DynFlags ->
                     Core.Var -> Core.CoreExpr -> nat -> (nat * bool)%type.

Axiom exprEtaExpandArity : DynFlags.DynFlags -> Core.CoreExpr -> nat.

Axiom exprBotStrictness_maybe : Core.CoreExpr ->
                                option (nat * Core.StrictSig)%type.

Axiom arityType : ArityEnv -> Core.CoreExpr -> ArityType.

Axiom typeArity : unit -> list BasicTypes.OneShotInfo.

Axiom vanillaArityType : ArityType.

Axiom getBotArity : ArityType -> option nat.

Axiom mk_cheap_fn : DynFlags.DynFlags -> CoreUtils.CheapAppFun -> CheapFun.

Axiom arityLam : Core.Var -> ArityType -> ArityType.

Axiom arityApp : ArityType -> bool -> ArityType.

Axiom floatIn : bool -> ArityType -> ArityType.

Axiom andArityType : ArityType -> ArityType -> ArityType.

Axiom etaExpand : nat -> Core.CoreExpr -> Core.CoreExpr.

Axiom mkEtaWW : nat ->
                Core.CoreExpr ->
                Core.InScopeSet -> unit -> (Core.InScopeSet * list EtaInfo)%type.

Axiom etaInfoApp : CoreSubst.Subst ->
                   Core.CoreExpr -> list EtaInfo -> Core.CoreExpr.

Axiom pushCoercion : unit -> list EtaInfo -> list EtaInfo.

Axiom etaInfoAbs : list EtaInfo -> Core.CoreExpr -> Core.CoreExpr.

Axiom etaInfoAppTy : unit -> list EtaInfo -> unit.

Axiom subst_expr : CoreSubst.Subst -> Core.CoreExpr -> Core.CoreExpr.

Axiom etaExpandToJoinPoint : BasicTypes.JoinArity ->
                             Core.CoreExpr -> (list Core.CoreBndr * Core.CoreExpr)%type.

Axiom etaExpandToJoinPointRule : BasicTypes.JoinArity ->
                                 Core.CoreRule -> Core.CoreRule.

Axiom etaBodyForJoinPoint : nat ->
                            Core.CoreExpr -> (list Core.CoreBndr * Core.CoreExpr)%type.

Axiom freshEtaId : nat -> unit -> unit -> (unit * Core.Var)%type.

(* External variables:
     bool list nat op_zt__ option unit BasicTypes.JoinArity BasicTypes.OneShotInfo
     Core.CoreBndr Core.CoreExpr Core.CoreRule Core.InScopeSet Core.StrictSig
     Core.Var CoreSubst.Subst CoreUtils.CheapAppFun DynFlags.DynFlags
*)
