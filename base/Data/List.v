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

Definition isSubsequenceOf {a} `{(GHC.Base.Eq_ a)} : list a -> list a -> bool :=
  fix isSubsequenceOf arg_0__ arg_1__
        := match arg_0__ , arg_1__ with
             | nil , _ => true
             | _ , nil => false
             | (cons x a' as a) , cons y b => let j_2__ := isSubsequenceOf a b in
                                              if x GHC.Base.== y : bool
                                              then isSubsequenceOf a' b
                                              else j_2__
           end.

(* Unbound variables:
     bool cons false list nil true GHC.Base.Eq_ GHC.Base.op_zeze__
*)
