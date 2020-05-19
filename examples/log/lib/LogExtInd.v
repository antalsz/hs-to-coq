(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Coq.Program.Tactics.
Require Coq.Program.Wf.

(* Converted imports: *)

Require Freer.
Require GHC.Base.
Require GHC.Char.
Require Log.
Import GHC.Base.Notations.

(* Converted type declarations: *)

Inductive LogMethods : Type -> Type := | Out : GHC.Char.Char -> LogMethods unit.

Definition OutputExt :=
  (Freer.Freer LogMethods)%type.

(* Converted value declarations: *)

Definition out : GHC.Char.Char -> OutputExt unit :=
  fun c => Freer.Vis (Out c) Freer.Ret.

Definition interp_ext {a} : OutputExt a -> Log.Output a :=
  fix interp_ext (arg_0__ : OutputExt a) : Log.Output a
        := match arg_0__ with
           | Freer.Ret a => GHC.Base.return_ a
           | Freer.Vis (Out c) k => Log.out c GHC.Base.>> interp_ext (k tt)
           end.

Definition collect : OutputExt unit -> GHC.Base.String :=
  fun o => Log.collect (interp_ext o).

(* External variables:
     Type tt unit Freer.Freer Freer.Ret Freer.Vis GHC.Base.String GHC.Base.op_zgzg__
     GHC.Base.return_ GHC.Char.Char Log.Output Log.collect Log.out
*)
