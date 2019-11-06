Require Import GHC.Num.

(* Characters *)

Require Import NArith.
Definition Char := N.
Bind Scope char_scope   with N.

(* Notation for literal characters in Coq source. *)
Require Import Coq.Strings.Ascii.
Definition hs_char__ : Ascii.ascii -> Char := N_of_ascii.
Notation "'&#' c" := (hs_char__ c) (at level 1, format "'&#' c").


Definition chr : Int -> Char := Z.to_N.

(* newline character *)
Definition newline := hs_char__ "010".