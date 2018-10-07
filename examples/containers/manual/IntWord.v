Require Import Coq.ZArith.BinInt.
Require Import Coq.NArith.BinNat.
Require Import GHC.Base.
Require Import Data.Bits.
(* Require Import Popcount. *)


(** 
This module defines fixed-width [Word] and [Int] types, as subset types
of [Z].

The approach is similar to http://compcert.inria.fr/doc/html/Integers.html. So why
do we roll our own? 
 * Their library is too generic: We only care about one fixed width.
 * They provide a single type ([int64]) with different operations for signed 
   and unsigned arithmetic. This is not a good match for translation from Haskell
   where type classes select signed/unsigned operations, so we need two types.

Because most of the operations in the [IntSet] module treat the bits of an [Int]
uniformly, and bit-operations are more common than arithmetic operations,
we use an [N] as the basic value, and convert appropriately.

The plan is to do very little on these types, i.e. just provide the necessary
operations for the translation, and in the proofs go to [N] as soon as possible.

Defining [Word] and [Int] as a subset typehere seems to be confusing to
[Program Definition] in the translated code, so let’s use a record type.
*)

Open Scope N_scope.

Definition WIDTH:=64.

(** The fundamental types *)
Record Word := MkWord { wordToN : N; wordInRange: 0 <= wordToN < 2^WIDTH }.

Definition MININT := (-2^((Z.of_N WIDTH) - 1))%Z.
Definition MAXINTPLUS1 := (2^(Z.of_N WIDTH-1))%Z.
Record Int := MkInt  { intToZ : Z; intInRange: (MININT <= intToZ < MAXINTPLUS1)% Z}.

(** Basic conversion *)

(* Definition wordToN : Word -> N. Admitted. *)
Definition NToWord : N -> Word. Admitted.

(* This maps -1 to MAXINT+1, preserving the bit structure (for bit operations) *)
Definition intToN : Int -> N. Admitted.
Definition NToInt : N -> Int. Admitted.

(* This is to used for arithmetic and ordering *)
(* Definition intToZ : Int -> Z. Admitted. *)
Definition ZToInt : Z -> Int. Admitted.


Definition intFromWord (w : Word) : Int :=
  NToInt (wordToN w).
Definition wordFromInt (i : Int) : Word :=
  NToWord (intToN i).

(* For termination arguments *)
Definition wordTonat (w : Word) : nat :=
  N.to_nat (wordToN w).

(** Instances *)

Instance Eq___Word : Eq_ Word := fun _ k => k
  {| op_zeze____ x y := N.eqb (wordToN x) (wordToN y);
     op_zsze____ x y := negb (N.eqb (wordToN x) (wordToN y))
  |}.

Program Instance Ord__Word : Ord Word := fun _ k => k
  {| compare__   x y := N.compare (wordToN x) (wordToN y)
  ;  op_zl____   x y := N.ltb (wordToN x) (wordToN y)
  ;  op_zg____   x y := N.ltb (wordToN y) (wordToN x)
  ;  op_zlze____ x y := N.leb (wordToN x) (wordToN y)
  ;  op_zgze____ x y := N.leb (wordToN y) (wordToN x)
  ;  min__       x y := if N.leb (wordToN x) (wordToN y) then x else y
  ;  max__       x y := if N.leb (wordToN x) (wordToN y) then y else x
  |}.

Instance Num__Word : Num Word := 
  {| op_zp__     x y := NToWord (wordToN x + wordToN y);
     op_zm__     x y := NToWord (wordToN x - wordToN y);
     op_zt__     x y := NToWord (wordToN x * wordToN y);
     abs         x   := NToWord (abs (wordToN x));
     fromInteger x   := NToWord (Z.to_N x);
     negate      x   := NToWord (negate (wordToN x));
     signum      x   := if N.eqb (wordToN x) 0 then NToWord 0 else NToWord 1
  |}.

Instance Bits__Word : Bits Word :=
  { op_zizazi__  x y  := NToWord (N.land (wordToN x) (wordToN y));
    op_zizbzi__  x y  := NToWord (N.lor  (wordToN x) (wordToN y));
    bit          x    := NToWord (2^(Z.to_N x));
    bitSizeMaybe  _   := Some (Z.of_N WIDTH);
    clearBit     x i  := NToWord (N.land (wordToN x) (N.lnot (2^(Z.to_N i)) WIDTH));
    complement   x    := NToWord (N.lnot (wordToN x) WIDTH);
    complementBit x i := NToWord (N.lxor (wordToN x) (2^(Z.to_N i)));
    isSigned     x    := false;
    popCount     x    := Z.of_N (N_popcount (wordToN x));
    rotate       x i  := NToWord 42; (* TODO (unused in containers) *)
    rotateL      x i  := NToWord 42; (* TODO (unused in containers) *)
    rotateR      x i  := NToWord 42; (* TODO (unused in containers) *)
    setBit       x i  := NToWord (N.lor (wordToN x) (2^(Z.to_N i)));
    shift        x i  := NToWord 42; (* TODO (unused in containers) *)
    shiftL       x i  := NToWord 42; (* TODO (unused in containers) *)
    shiftR       x i  := NToWord 42; (* TODO (unused in containers) *)
    testBit      x i  := N.testbit (wordToN x)  (Z.to_N i);
    unsafeShiftL x i  := NToWord 42; (* TODO (unused in containers) *)
    unsafeShiftR x i  := NToWord 42; (* TODO (unused in containers) *)
    xor          x y  := NToWord (N.lxor  (wordToN x) (wordToN y));
    zeroBits          := NToWord 0 }.

Instance Eq___Int : Eq_ Int := fun _ k => k
  {| op_zeze____ x y := N.eqb (intToN x) (intToN y);
     op_zsze____ x y := negb (N.eqb (intToN x) (intToN y))
  |}.

Program Instance Ord__Int : Ord Int := fun _ k => k
  {| compare__   x y := Z.compare (intToZ x) (intToZ y)
  ;  op_zl____   x y := Z.ltb (intToZ x) (intToZ y)
  ;  op_zg____   x y := Z.ltb (intToZ y) (intToZ x)
  ;  op_zlze____ x y := Z.leb (intToZ x) (intToZ y)
  ;  op_zgze____ x y := Z.leb (intToZ y) (intToZ x)
  ;  min__       x y := if Z.leb (intToZ x) (intToZ y) then x else y
  ;  max__       x y := if Z.leb (intToZ x) (intToZ y) then y else x
  |}.

Instance Num__Int : Num Int := 
  {| op_zp__     x y := ZToInt (intToZ x + intToZ y);
     op_zm__     x y := ZToInt (intToZ x - intToZ y);
     op_zt__     x y := ZToInt (intToZ x * intToZ y);
     abs         x   := ZToInt (abs (intToZ x));
     fromInteger x   := ZToInt x;
     negate      x   := ZToInt (negate (intToZ x));
     signum      x   := if Z.ltb (intToZ x) 0 then ZToInt (-1) else
                        if Z.eqb (intToZ x) 0 then ZToInt 0 else ZToInt 1
  |}.

Instance Bits__Int : Bits Int :=
  { op_zizazi__  x y  := NToInt (N.land (intToN x) (intToN y));
    op_zizbzi__  x y  := NToInt (N.lor  (intToN x) (intToN y));
    bit          x    := NToInt (2^(Z.to_N x));
    bitSizeMaybe  _   := Some (Z.of_N WIDTH);
    clearBit     x i  := NToInt (N.land (intToN x) (N.lnot (2^(Z.to_N i)) WIDTH));
    complement   x    := NToInt (N.lnot (intToN x) WIDTH);
    complementBit x i := NToInt (N.lxor (intToN x) (2^(Z.to_N i)));
    isSigned     x    := false;
    popCount     x    := Z.of_N (N_popcount (intToN x));
    rotate       x i  := NToInt 42; (* TODO (unused in containers) *)
    rotateL      x i  := NToInt 42; (* TODO (unused in containers) *)
    rotateR      x i  := NToInt 42; (* TODO (unused in containers) *)
    setBit       x i  := NToInt (N.lor (intToN x) (2^(Z.to_N i)));
    shift        x i  := NToInt 42; (* TODO (unused in containers) *)
    shiftL       x i  := NToInt 42; (* TODO (unused in containers) *)
    shiftR       x i  := NToInt 42; (* TODO (unused in containers) *)
    testBit      x i  := N.testbit (intToN x)  (Z.to_N i);
    unsafeShiftL x i  := NToInt 42; (* TODO (unused in containers) *)
    unsafeShiftR x i  := NToInt 42; (* TODO (unused in containers) *)
    xor          x y  := NToInt (N.lxor  (intToN x) (intToN y));
    zeroBits          := NToInt 0 }.


(** Other operations *)

Definition shiftLWord (x : Word) (i : Int) : Word :=
  NToWord (N.shiftl (wordToN x) (intToN i)).
 (* If i is negative, then intToN is very large, and we get 0 
    as the result. *)

Definition shiftRWord (x : Word) (i : Int) : Word :=
  NToWord (N.shiftr (wordToN x) (intToN i)).

Axiom indexOfTheOnlyBit : Word -> Int.
Axiom highestBitMask : Word -> Word.

(* with accumulator *)
Definition bitcount (a : Int) (w : Word) : Int :=
  ZToInt (intToZ a + Z.of_N (N_popcount (wordToN w)))%Z.
