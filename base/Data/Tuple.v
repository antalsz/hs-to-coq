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

Definition fst {a} {b} : (a * b)%type -> a :=
  fun '(pair x _) => x.

Definition snd {a} {b} : (a * b)%type -> b :=
  fun '(pair _ y) => y.

Definition curry {a} {b} {c} : ((a * b)%type -> c) -> a -> b -> c :=
  fun f x y => f (pair x y).

Definition uncurry {a} {b} {c} : (a -> b -> c) -> ((a * b)%type -> c) :=
  fun f p => f (fst p) (snd p).

Definition swap {a} {b} : (a * b)%type -> (b * a)%type :=
  fun '(pair a b) => pair b a.

(* External variables:
     op_zt__ pair
*)
