
Require Import CTZ.
Require Import Popcount.
Require Import Coq.ZArith.ZArith.
Require Data.Bits.

Definition shiftLL (n: N) (s : Z) : N :=
	Coq.NArith.BinNat.N.shiftl n (Coq.ZArith.BinInt.Z.to_N s).
Definition shiftRL (n: N) (s : Z) : N :=
	Coq.NArith.BinNat.N.shiftr n (Coq.ZArith.BinInt.Z.to_N s).

Definition highestBitMask (n: N) : N := N.pow 2 (N.log2 n).
Definition lowestBitMask  (n: N) : N := N.pow 2 (N_ctz n).

Definition bit_N := shiftLL 1%N.

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
  rotate := shiftLL;
  rotateL := shiftRL;
  rotateR := shiftRL;
  setBit := fun x i => N.lor x (bit_N i);
  shift := shiftLL;
  shiftL := shiftLL;
  shiftR := shiftRL;
  testBit := fun x i => N.testbit x (Coq.ZArith.BinInt.Z.to_N i);
  unsafeShiftL := shiftLL;
  unsafeShiftR := shiftRL;
  xor := N.lxor;
  zeroBits := 0;
}.
