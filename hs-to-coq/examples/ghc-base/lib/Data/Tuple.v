(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Set Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Preamble *)


(* No imports to convert. *)

(* Converted declarations: *)

Definition curry {a} {b} {c} : (a * b -> c) -> a -> b -> c :=
  fun arg_3__ arg_4__ arg_5__ =>
    match arg_3__ , arg_4__ , arg_5__ with
      | f , x , y => f (pair x y)
    end.

Definition fst {a} {b} : a * b -> a :=
  fun arg_10__ => match arg_10__ with | (pair x _) => x end.

Definition snd {a} {b} : a * b -> b :=
  fun arg_8__ => match arg_8__ with | (pair _ y) => y end.

Definition uncurry {a} {b} {c} : (a -> b -> c) -> (a * b -> c) :=
  fun arg_12__ arg_13__ =>
    match arg_12__ , arg_13__ with
      | f , p => f (fst p) (snd p)
    end.

Definition swap {a} {b} : a * b -> b * a :=
  fun arg_0__ => match arg_0__ with | (pair a b) => pair b a end.

(* Unbound variables:
     * pair
*)
