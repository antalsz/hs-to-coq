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
Require Combined.
Require CoreSubst.
Require CoreUtils.
Require Demand.
Require DynFlags.
Require GHC.Num.

(* Converted type declarations: *)

Inductive EtaInfo : Type
  := EtaVar : Combined.Var -> EtaInfo
  |  EtaCo : unit -> EtaInfo.

Definition CheapFun :=
  (Combined.CoreExpr -> option unit -> bool)%type.

Inductive ArityType : Type
  := ATop : list BasicTypes.OneShotInfo -> ArityType
  |  ABot : BasicTypes.Arity -> ArityType.

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

Axiom manifestArity : Combined.CoreExpr -> BasicTypes.Arity.

Axiom joinRhsArity : Combined.CoreExpr -> BasicTypes.JoinArity.

Axiom exprArity : Combined.CoreExpr -> BasicTypes.Arity.

Axiom findRhsArity : DynFlags.DynFlags ->
                     Combined.Var ->
                     Combined.CoreExpr -> BasicTypes.Arity -> (BasicTypes.Arity * bool)%type.

Axiom exprEtaExpandArity : DynFlags.DynFlags ->
                           Combined.CoreExpr -> BasicTypes.Arity.

Axiom exprBotStrictness_maybe : Combined.CoreExpr ->
                                option (BasicTypes.Arity * Demand.StrictSig)%type.

Axiom arityType : ArityEnv -> Combined.CoreExpr -> ArityType.

Axiom typeArity : unit -> list BasicTypes.OneShotInfo.

Axiom vanillaArityType : ArityType.

Axiom getBotArity : ArityType -> option BasicTypes.Arity.

Axiom mk_cheap_fn : DynFlags.DynFlags -> CoreUtils.CheapAppFun -> CheapFun.

Axiom arityLam : Combined.Var -> ArityType -> ArityType.

Axiom arityApp : ArityType -> bool -> ArityType.

Axiom floatIn : bool -> ArityType -> ArityType.

Axiom andArityType : ArityType -> ArityType -> ArityType.

Axiom etaExpand : BasicTypes.Arity -> Combined.CoreExpr -> Combined.CoreExpr.

Axiom mkEtaWW : BasicTypes.Arity ->
                Combined.CoreExpr ->
                Combined.InScopeSet -> unit -> (Combined.InScopeSet * list EtaInfo)%type.

Axiom etaInfoApp : CoreSubst.Subst ->
                   Combined.CoreExpr -> list EtaInfo -> Combined.CoreExpr.

Axiom pushCoercion : unit -> list EtaInfo -> list EtaInfo.

Axiom etaInfoAbs : list EtaInfo -> Combined.CoreExpr -> Combined.CoreExpr.

Axiom etaInfoAppTy : unit -> list EtaInfo -> unit.

Axiom subst_expr : CoreSubst.Subst -> Combined.CoreExpr -> Combined.CoreExpr.

Axiom etaExpandToJoinPoint : BasicTypes.JoinArity ->
                             Combined.CoreExpr -> (list Combined.CoreBndr * Combined.CoreExpr)%type.

Axiom etaExpandToJoinPointRule : BasicTypes.JoinArity ->
                                 Combined.CoreRule -> Combined.CoreRule.

Axiom etaBodyForJoinPoint : GHC.Num.Int ->
                            Combined.CoreExpr -> (list Combined.CoreBndr * Combined.CoreExpr)%type.

Axiom freshEtaId : GHC.Num.Int -> unit -> unit -> (unit * Combined.Var)%type.

(* External variables:
     bool list op_zt__ option unit BasicTypes.Arity BasicTypes.JoinArity
     BasicTypes.OneShotInfo Combined.CoreBndr Combined.CoreExpr Combined.CoreRule
     Combined.InScopeSet Combined.Var CoreSubst.Subst CoreUtils.CheapAppFun
     Demand.StrictSig DynFlags.DynFlags GHC.Num.Int
*)
