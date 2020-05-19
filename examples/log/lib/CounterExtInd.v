(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Coq.Program.Tactics.
Require Coq.Program.Wf.

(* Converted imports: *)

Require Counter.
Require Freer.
Require GHC.Base.
Import GHC.Base.Notations.

(* Converted type declarations: *)

Inductive CounterMethods : Type -> Type := | Inc : CounterMethods unit.

Definition CounterExt :=
  (Freer.Freer CounterMethods)%type.

(* Converted value declarations: *)

Fixpoint interp_ext {a} (arg_0__ : CounterExt a) : Counter.Counter a
           := match arg_0__ with
              | Freer.Ret a => GHC.Base.return_ a
              | Freer.Vis Inc k => Counter.inc GHC.Base.>> interp_ext (k tt)
              end.

Definition inc : CounterExt unit :=
  Freer.Vis Inc Freer.Ret.

(* External variables:
     Type tt unit Counter.Counter Counter.inc Freer.Freer Freer.Ret Freer.Vis
     GHC.Base.op_zgzg__ GHC.Base.return_
*)
