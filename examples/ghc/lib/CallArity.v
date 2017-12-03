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
Require UnVarGraph.
Require VarEnv.

(* Converted type declarations: *)

Definition CallArityRes :=
  (UnVarGraph.UnVarGraph * VarEnv.VarEnv BasicTypes.Arity)%type%type.
(* Converted value declarations: *)

Axiom callArityAnalProgram : forall {A : Type}, A.

Axiom callArityTopLvl : forall {A : Type}, A.

Axiom callArityRHS : forall {A : Type}, A.

Axiom callArityBind : forall {A : Type}, A.

Axiom callArityAnal : forall {A : Type}, A.

Axiom boringBinds : forall {A : Type}, A.

Axiom addInterestingBinds : forall {A : Type}, A.

Axiom interestingBinds : forall {A : Type}, A.

Axiom isInteresting : forall {A : Type}, A.

Axiom callArityRecEnv : forall {A : Type}, A.

Axiom trimArity : forall {A : Type}, A.

Axiom lubRess : forall {A : Type}, A.

Axiom emptyArityRes : forall {A : Type}, A.

Axiom unitArityRes : forall {A : Type}, A.

Axiom resDelList : forall {A : Type}, A.

Axiom resDel : forall {A : Type}, A.

Axiom both : forall {A : Type}, A.

Axiom calledMultipleTimes : forall {A : Type}, A.

Axiom domRes : forall {A : Type}, A.

Axiom lookupCallArityRes : forall {A : Type}, A.

Axiom calledWith : forall {A : Type}, A.

Axiom addCrossCoCalls : forall {A : Type}, A.

Axiom lubRes : forall {A : Type}, A.

Axiom lubArityEnv : forall {A : Type}, A.

(* Unbound variables:
     op_zt__ BasicTypes.Arity UnVarGraph.UnVarGraph VarEnv.VarEnv
*)
