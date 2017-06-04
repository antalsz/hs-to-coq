Require Import GHC.Num.

(* Characters *)

(*
Require Import Coq.Strings.Ascii.
Definition Char := Ascii.ascii.
Bind Scope char_scope   with Ascii.ascii.

(* Notation for literal characters in Coq source. *)
Definition hs_char__ : Ascii.ascii -> Char := fun c => c.
Notation "'&#' c" := (hs_char__ c) (at level 1, format "'&#' c").

Definition chr : Int -> Char := fun i => ascii_of_N (Z.to_N i).
Definition ord : Char -> Int := fun i => Z.of_N (N_of_ascii i).
*)

Require Import NArith.
Definition Char := N.
Bind Scope char_scope   with N.

(* Notation for literal characters in Coq source. *)
Require Import Coq.Strings.Ascii.
Definition hs_char__ : Ascii.ascii -> Char := N_of_ascii.
Notation "'&#' c" := (hs_char__ c) (at level 1, format "'&#' c").

Definition chr : Int -> Char := Z.to_N.
Definition ord : Char -> Int := Z.of_N.
