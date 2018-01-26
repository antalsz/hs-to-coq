Require Coq.ZArith.Zcomplements.
Require Import Coq.Numbers.BinNums.

Definition shiftLL (n: Nat) (s : BinInt.Z) : Nat :=
	Coq.NArith.BinNat.N.shiftl n (Coq.ZArith.BinInt.Z.to_N s).
Definition shiftRL (n: Nat) (s : BinInt.Z) : Nat :=
	Coq.NArith.BinNat.N.shiftr n (Coq.ZArith.BinInt.Z.to_N s).

Definition highestBitMask (n: Nat) : Nat := Coq.NArith.BinNat.N.pow 2 (Coq.NArith.BinNat.N.log2 n).

Require Import NArith.
Definition bit_N := shiftLL 1%N.

Definition popCount_N : N -> Z := unsafeFix (fun popCount x =>
  if Coq.NArith.BinNat.N.eqb x 0
  then 0%Z
  else Coq.ZArith.BinInt.Z.succ (popCount (Coq.NArith.BinNat.N.ldiff x (Coq.NArith.BinNat.N.pow 2 (Coq.NArith.BinNat.N.log2 x))))).

Definition bitCount_N (a : GHC.Num.Int) (x : N) := a GHC.Num.+ (popCount_N x).

Instance Bits__N : Data.Bits.Bits N :=  {
  op_zizazi__ := N.land ;
  op_zizbzi__ := N.lor ;
  bit := bit_N;
  bitSizeMaybe := fun _ => None ;
  clearBit := fun n i => N.clearbit n (Coq.ZArith.BinInt.Z.to_N i) ;
  complement := fun _ => 0%N  ; (* Not legally possible with N *)
  complementBit := fun x i => N.lxor x (bit_N i) ;
  isSigned := fun x => true ;
  popCount := popCount_N ;
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


Fixpoint size_nat (t : IntSet) : nat :=
  match t with
  | Bin _ _ l r => S (size_nat l + size_nat r)%nat
  | Tip _ bm => 0
  | Nil => 0
  end.

Require Omega.
Ltac termination_by_omega :=
  Coq.Program.Tactics.program_simpl;
  simpl;Omega.omega.


(* Z.ones 6 = 64-1 *)
Definition suffixBitMask : GHC.Num.Int := (Coq.ZArith.BinInt.Z.ones 6)%Z.
