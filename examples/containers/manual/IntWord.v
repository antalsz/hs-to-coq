Require Import Coq.ZArith.BinInt.
Require Import GHC.Base.
Require Import Data.Bits.

(** 
This module defines fixed-width [Word] and [Int] types, as subset types
of [Z].

The approach is similar to http://compcert.inria.fr/doc/html/Integers.html. So why
do we roll our own? 
 * Their library is too generic: We only care about one fixed width.
 * They provide a single type ([int64]) with different operations for signed 
   and unsigned arithmetic. This is not a good match for translation from Haskell
   where type classes select signed/unsigned operations, so we need two types.

The plan is to do very little on these types, i.e. just provide the necessary
operations for the translation, and in the proofs go to [Z] as soon as possible
(by unpacking the sigma type).
*)

Open Scope Z_scope.

Definition WIDTH:=64.
Definition MININT := -2^(WIDTH-1).
Definition MAXINTPLUS1 := 2^(WIDTH-1).

(** Signed integers *)

Record Int: Type := MkInt { intToZ: Z; intRange: MININT <= intToZ < MAXINTPLUS1 }.

Instance Eq___Int : Eq_ Int.
Admitted.

Instance Ord__Int : Ord Int.
Admitted.

Instance Num__Int : Num Int.
Admitted.

Instance Bits__Int : Bits Int.
Admitted.

(** Unsigned integers *)

Record Word: Type := MkWord { wordToZ: Z; wordRange: 0 <= wordToZ < 2 ^ WIDTH }.

Instance Eq___Word : Eq_ Word.
Admitted.

Instance Ord__Word : Ord Word.
Admitted.

Instance Num__Word : Num Word.
Admitted.

Instance Bits__Word : Bits Word.
Admitted.


Axiom shiftLWord : Word -> Int -> Word.
Axiom shiftRWord : Word -> Int -> Word.

Axiom indexOfTheOnlyBit : Word -> Int.
Axiom highestBitMask : Word -> Word.
Axiom intFromWord : Word -> Int.
Axiom wordFromInt : Int -> Word.
Axiom wordTonat : Word -> nat.

(* with accumulator *)
Axiom bitcount : Int -> Word -> Int.