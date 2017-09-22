(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Set Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Let us be a bit explicit by having multiple axoims around *)
(* This one is for untranslatable expressions: *)
Local Axiom missingValue : forall {a}, a.
(* This one is for pattern match failures: *)
Local Axiom patternFailure : forall {a}, a.

(* Preamble *)


(* Converted imports: *)

Require GHC.Base.

(* Converted declarations: *)

Definition op_za__ {a} {b} : a -> ((a -> b) -> b) :=
  fun arg_0__ arg_1__ => match arg_0__ , arg_1__ with | x , f => f x end.

Infix "&" := (op_za__) (at level 99).

Notation "'_&_'" := (op_za__).
