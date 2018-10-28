(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Coq.Program.Tactics.
Require Coq.Program.Wf.

(* Preamble *)


Require Import CTZ.
Require Import Coq.ZArith.ZArith.
Require Import Data.Bits.

Definition shiftLL (n: N) (s : N) : N := Coq.NArith.BinNat.N.shiftl n s.
Definition shiftRL (n: N) (s : N) : N := Coq.NArith.BinNat.N.shiftr n s.

Definition bit_N s := shiftLL 1%N (Coq.ZArith.BinInt.Z.to_N s).

Definition highestBitMask (n: N) : N := N.pow 2%N (N.log2 n).
Definition lowestBitMask  (n: N) : N := N.pow 2%N (N_ctz n).

Definition bitcount : Coq.Numbers.BinNums.N -> Coq.Numbers.BinNums.N -> Coq.Numbers.BinNums.N :=
  fun a x => (a + N_popcount x)%N.

(* No imports to convert. *)

(* No type declarations to convert. *)

(* No value declarations to convert. *)
