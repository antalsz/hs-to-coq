(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Coq.Program.Tactics.
Require Coq.Program.Wf.

(* Preamble *)


(* No imports to convert. *)

(* No type declarations to convert. *)
(* Converted value declarations: *)

Definition curry {a} {b} {c} : ((a * b)%type -> c) -> a -> b -> c :=
  fun f x y => f (pair x y).

Definition fst {a} {b} : (a * b)%type -> a :=
  fun arg_0__ => match arg_0__ with | pair x _ => x end.

Definition snd {a} {b} : (a * b)%type -> b :=
  fun arg_0__ => match arg_0__ with | pair _ y => y end.

Definition uncurry {a} {b} {c} : (a -> b -> c) -> ((a * b)%type -> c) :=
  fun f p => f (fst p) (snd p).

Definition swap {a} {b} : (a * b)%type -> (b * a)%type :=
  fun arg_0__ => match arg_0__ with | pair a b => pair b a end.

(* Unbound variables:
     op_zt__ pair
*)
