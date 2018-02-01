Require Coq.ZArith.Zcomplements.
Require Import Coq.ZArith.Zpower.
Require Import Coq.Numbers.BinNums.

Require Import NArith.
Definition bit_N := fun s => Coq.NArith.BinNat.N.shiftl 1%N (Coq.ZArith.BinInt.Z.to_N s).

Definition popCount_N : N -> Z := unsafeFix (fun popCount x =>
  if Coq.NArith.BinNat.N.eqb x 0
  then 0%Z
  else Coq.ZArith.BinInt.Z.succ (popCount (Coq.NArith.BinNat.N.ldiff x (Coq.NArith.BinNat.N.pow 2 (Coq.NArith.BinNat.N.log2 x))))).

Instance Bits__N : Data.Bits.Bits N :=  {
  op_zizazi__   := N.land ;
  op_zizbzi__   := N.lor ;
  bit           := bit_N;
  bitSizeMaybe  := fun _ => None ;
  clearBit      := fun n i => N.clearbit n (Coq.ZArith.BinInt.Z.to_N i) ;
  complement    := fun _ => 0%N  ; (* Not legally possible with N *)
  complementBit := fun x i => N.lxor x (bit_N i) ;
  isSigned      := fun x => true ;
  popCount      := popCount_N ;
  rotate        := fun n s => Coq.NArith.BinNat.N.shiftl n (Coq.ZArith.BinInt.Z.to_N s);
  rotateL       := fun n s => Coq.NArith.BinNat.N.shiftl n (Coq.ZArith.BinInt.Z.to_N s);
  rotateR       := fun n s => Coq.NArith.BinNat.N.shiftr n (Coq.ZArith.BinInt.Z.to_N s);
  setBit        := fun x i => N.lor x (bit_N i);
  shift         := fun n s => Coq.NArith.BinNat.N.shiftl n (Coq.ZArith.BinInt.Z.to_N s);
  shiftL        := fun n s => Coq.NArith.BinNat.N.shiftl n (Coq.ZArith.BinInt.Z.to_N s);
  shiftR        := fun n s => Coq.NArith.BinNat.N.shiftr n (Coq.ZArith.BinInt.Z.to_N s);
  testBit       := fun x i => N.testbit x (Coq.ZArith.BinInt.Z.to_N i);
  unsafeShiftL  := fun n s => Coq.NArith.BinNat.N.shiftl n (Coq.ZArith.BinInt.Z.to_N s);
  unsafeShiftR  := fun n s => Coq.NArith.BinNat.N.shiftr n (Coq.ZArith.BinInt.Z.to_N s);
  xor           := N.lxor;
  zeroBits      := 0;
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


(** ** [Int64] *)

Definition shiftLL (n: Int64.int) (s : BinInt.Z) : Int64.int :=
	Int64.shl n (Int64.repr s).
Definition shiftRL (n: Int64.int) (s : BinInt.Z) : Int64.int :=
	Int64.shr n (Int64.repr s).

(*  indexOfTheOnlyBit uses pointers and ugly stuff *)
Definition indexOfTheOnlyBit : Int64.int -> BinInt.Z :=
 fun x => match Int64.is_power2 x with
	| Some i => Int64.unsigned i
	| None => 0%Z
        end.

Fixpoint last_or_0 (l : list Z) : Z := match l with
  | nil        => 0
  | cons i nil => i
  | cons i xs  => last_or_0 xs
  end.

Definition highestBitPos (x: Int64.int) : Z :=
  last_or_0 (Int64.Z_one_bits Int64.wordsize (Int64.unsigned x) 0).

Definition highestBitMask (x: Int64.int) : Int64.int :=
  Int64.repr (two_p (highestBitPos x)).

Definition popCount_64 (x : Int64.int) :=
  BinInt.Z.of_nat (length (Int64.Z_one_bits Int64.wordsize (Int64.unsigned x) 0)).

Definition bit_64 (x : Z) := Int64.repr (two_p x).

(* We treat the Int64.int as unsigned here *)
Instance Num__Int64 : GHC.Num.Num Int64.int  := {
    op_zp__ := Int64.add;
    op_zm__ := Int64.sub;
    op_zt__ := Int64.mul;
    abs := id;
    fromInteger := Int64.repr;
    negate := Int64.neg;
    signum := id;
}.

Instance Eq__Int64 : GHC.Base.Eq_ Int64.int  := fun _ k => k {|
    GHC.Base.op_zeze____ := Int64.eq;
    GHC.Base.op_zsze____ := (fun x y => Int64.eq x y);
|}.

Instance Bits__Int64 : Data.Bits.Bits Int64.int :=  {
  op_zizazi__   := Int64.and ;
  op_zizbzi__   := Int64.or ;
  bit           := bit_64;
  bitSizeMaybe  := fun _ => None ;
  clearBit      := fun n i => Int64.and n (bit_64 i);
  complement    := Int64.not;
  complementBit := fun x i => Int64.xor x (bit_64 i);
  isSigned      := fun x => true;
  popCount      := popCount_64 ;
  rotate        := fun n s => Int64.shl  n (Int64.repr s);
  rotateL       := fun n s => Int64.shl  n (Int64.repr s);
  rotateR       := fun n s => Int64.shru n (Int64.repr s);
  setBit        := fun x i => Int64.or x (bit_64 i);
  shift         := fun n s => Int64.shl  n (Int64.repr s);
  shiftL        := fun n s => Int64.shl  n (Int64.repr s);
  shiftR        := fun n s => Int64.shru n (Int64.repr s);
  testBit       := fun x i => Int64.testbit x i;
  unsafeShiftL  := fun n s => Int64.shl  n (Int64.repr s);
  unsafeShiftR  := fun n s => Int64.shru n (Int64.repr s);
  xor           := Int64.xor;
  zeroBits      := Int64.zero;
}.

