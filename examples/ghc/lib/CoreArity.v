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
Require CoreSyn.
Require Var.

(* Converted type declarations: *)

Inductive EtaInfo : Type := EtaVar : Var.Var -> EtaInfo
                         |  EtaCo : unit -> EtaInfo.

Definition CheapFun :=
  (CoreSyn.CoreExpr -> option unit -> bool)%type.

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

Axiom manifestArity : forall {A : Type}, A.

Axiom exprArity : forall {A : Type}, A.

Axiom findRhsArity : forall {A : Type}, A.

Axiom rhsEtaExpandArity : forall {A : Type}, A.

Axiom exprEtaExpandArity : forall {A : Type}, A.

Axiom exprBotStrictness_maybe : forall {A : Type}, A.

Axiom arityType : forall {A : Type}, A.

Axiom typeArity : forall {A : Type}, A.

Axiom vanillaArityType : forall {A : Type}, A.

Axiom getBotArity : forall {A : Type}, A.

Axiom mk_cheap_fn : forall {A : Type}, A.

Axiom arityLam : forall {A : Type}, A.

Axiom arityApp : forall {A : Type}, A.

Axiom floatIn : forall {A : Type}, A.

Axiom andArityType : forall {A : Type}, A.

Axiom etaExpand : forall {A : Type}, A.

Axiom etaInfoApp : forall {A : Type}, A.

Axiom pushCoercion : forall {A : Type}, A.

Axiom etaInfoAbs : forall {A : Type}, A.

Axiom mkEtaWW : forall {A : Type}, A.

Axiom subst_expr : forall {A : Type}, A.

Axiom subst_bind : forall {A : Type}, A.

Axiom freshEtaVar : forall {A : Type}, A.

(* Unbound variables:
     bool list option unit BasicTypes.Arity BasicTypes.OneShotInfo CoreSyn.CoreExpr
     Var.Var
*)
