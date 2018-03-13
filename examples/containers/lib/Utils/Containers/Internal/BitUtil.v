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
Require Import Popcount.
Require Import Coq.ZArith.ZArith.
Require Data.Bits.

Definition shiftLL (n: N) (s : N) : N := Coq.NArith.BinNat.N.shiftl n s.
Definition shiftRL (n: N) (s : N) : N := Coq.NArith.BinNat.N.shiftr n s.

Definition highestBitMask (n: N) : N := N.pow 2 (N.log2 n).
Definition lowestBitMask  (n: N) : N := N.pow 2 (N_ctz n).

Definition bit_N s := shiftLL 1%N (Coq.ZArith.BinInt.Z.to_N s).

Definition bitcount : Coq.Numbers.BinNums.N -> Coq.Numbers.BinNums.N -> Coq.Numbers.BinNums.N :=
  fun a x => (a + N_popcount x)%N.


Instance Bits__N : Data.Bits.Bits N :=  {
  op_zizazi__ := N.land ;
  op_zizbzi__ := N.lor ;
  bit := bit_N;
  bitSizeMaybe := fun _ => None ;
  clearBit := fun n i => N.clearbit n (Coq.ZArith.BinInt.Z.to_N i) ;
  complement := fun _ => 0%N  ; (* Not legally possible with N *)
  complementBit := fun x i => N.lxor x (bit_N i) ;
  isSigned := fun x => true ;
  popCount := fun n => Z.of_N (N_popcount n);
  rotate  := fun n s => Coq.NArith.BinNat.N.shiftl n (Coq.ZArith.BinInt.Z.to_N s);
  rotateL := fun n s => Coq.NArith.BinNat.N.shiftl n (Coq.ZArith.BinInt.Z.to_N s);
  rotateR := fun n s => Coq.NArith.BinNat.N.shiftr n (Coq.ZArith.BinInt.Z.to_N s);
  setBit := fun x i => N.lor x (bit_N i);
  shift  := fun n s => Coq.NArith.BinNat.N.shiftl n (Coq.ZArith.BinInt.Z.to_N s);
  shiftL := fun n s => Coq.NArith.BinNat.N.shiftl n (Coq.ZArith.BinInt.Z.to_N s);
  shiftR := fun n s => Coq.NArith.BinNat.N.shiftr n (Coq.ZArith.BinInt.Z.to_N s);
  testBit := fun x i => N.testbit x (Coq.ZArith.BinInt.Z.to_N i);
  unsafeShiftL := fun n s => Coq.NArith.BinNat.N.shiftl n (Coq.ZArith.BinInt.Z.to_N s);
  unsafeShiftR := fun n s => Coq.NArith.BinNat.N.shiftr n (Coq.ZArith.BinInt.Z.to_N s);
  xor := N.lxor;
  zeroBits := 0;
}.

(* No imports to convert. *)

(* No type declarations to convert. *)
(* No value declarations to convert. *)
