Require Import GHC.Num.

(* Characters *)

Require Import Coq.Strings.Ascii.

Definition Char := Ascii.ascii.
Bind Scope char_scope   with Ascii.ascii.

(* Notation for literal characters in Coq source. *)
Definition hs_char__ : Ascii.ascii -> Char := fun c => c.
Notation "'&#' c" := (hs_char__ c) (at level 1, format "'&#' c").

Definition chr : Int -> Char := fun i => ascii_of_N (Z.to_N i).
