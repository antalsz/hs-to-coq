(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Coq.Program.Tactics.
Require Coq.Program.Wf.

(* Converted imports: *)

Require GHC.Base.
Import GHC.Base.Notations.

(* No type declarations to convert. *)

(* Converted value declarations: *)

Fixpoint isSubsequenceOf {a} `{(GHC.Base.Eq_ a)} (arg_0__ arg_1__ : list a)
           : bool
           := match arg_0__, arg_1__ with
              | nil, _ => true
              | _, nil => false
              | (cons x a' as a), cons y b =>
                  if x GHC.Base.== y : bool then isSubsequenceOf a' b else
                  isSubsequenceOf a b
              end.

(* External variables:
     bool cons false list nil true GHC.Base.Eq_ GHC.Base.op_zeze__
*)
