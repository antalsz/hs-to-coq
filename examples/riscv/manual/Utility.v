Require Import Coq.ZArith.BinInt.
Require Import bbv.Word.
Require Import riscv.util.Monads.

(* Meaning of MachineInt: an integer big enough to hold an integer of a RISCV machine,
   no matter whether it's a 32-bit or 64-bit machine. *)
Definition MachineInt := Z.

Definition bitSlice(x: Z)(start eend: Z): Z :=
  Z.land (Z.shiftr x start) (Z.lnot (Z.shiftl (-1) (eend - start))).

Definition signExtend(l: Z)(n: Z): Z :=
  if Z.testbit n (l-1) then (n - (Z.setbit 0 l)) else n.


Class MachineWidth(t: Set) := mkMachineWidth {
  (* constants *)
  zero: t;
  one: t;

  (* arithmetic operations (inherited from Integral in Haskell) *)
  add: t -> t -> t;
  sub: t -> t -> t;
  mul: t -> t -> t;
  div: t -> t -> t;
  rem: t -> t -> t;

  (* comparison operators (inherited from Eq and Ord in Haskell) *)
  signed_less_than: t -> t -> bool;
  signed_eqb: t -> t -> bool;

  (* logical operations (inherited from Bits in Haskell) *)
  xor: t -> t -> t;
  or: t -> t -> t;
  and: t -> t -> t;

  (* operations also defined in MachineWidth in Haskell: *)

  fromImm: MachineInt -> t;

  regToInt8: t -> word 8;
  regToInt16: t -> word 16;
  regToInt32: t -> word 32;
  regToInt64: t -> word 64;

  uInt8ToReg: word 8 -> t;
  uInt16ToReg: word 16 -> t;
  uInt32ToReg: word 32 -> t;
  uInt64ToReg: word 64 -> t;

  int8ToReg: word 8 -> t;
  int16ToReg: word 16 -> t;
  int32ToReg: word 32 -> t;
  int64ToReg: word 64 -> t;

  s32: t -> t;
  u32: t -> t;

  regToZ_signed: t -> Z;
  regToZ_unsigned: t -> Z;

  sll: t -> Z -> t;
  srl: t -> Z -> t;
  sra: t -> Z -> t;

  ltu: t -> t -> bool;
  divu: t -> t -> t;
  remu: t -> t -> t;

  maxSigned: t;
  maxUnsigned: t;
  minSigned: t;

  regToShamt5: t -> Z;
  regToShamt: t -> Z;

  highBits: Z -> t;
}.


Notation "a <|> b" := (or a b)  (at level 50, left associativity) : alu_scope.
Notation "a <&> b" := (and a b) (at level 40, left associativity) : alu_scope.
Notation "a + b"   := (add a b) (at level 50, left associativity) : alu_scope.
Notation "a - b"   := (sub a b) (at level 50, left associativity) : alu_scope.
Notation "a * b"   := (mul a b) (at level 40, left associativity) : alu_scope.

Notation "a /= b" := (negb (signed_eqb a b))        (at level 38, no associativity) : alu_scope.
Notation "a == b" := (signed_eqb a b)               (at level 38, no associativity) : alu_scope.
Notation "a < b"  := (signed_less_than a b)         (at level 70, no associativity) : alu_scope.
Notation "a >= b" := (negb (signed_less_than a b))  (at level 70, no associativity) : alu_scope.
Notation "'when' a b" := (if a then b else Return tt)
  (at level 60, a at level 0, b at level 0) : alu_scope.


Section Constants.

  Context {t: Set}.
  Context {MW: MachineWidth t}.

  Local Open Scope alu_scope.

  Definition two: t := one + one.

  Definition four: t := two + two.

  Definition eight: t := four + four.

  Definition minusone: t := zero - one.

End Constants.


Instance MachineWidth32: MachineWidth (word 32) := {|
  zero := $0;
  one := $1;
  add := @wplus 32;
  sub := @wminus 32;
  mul := @wmult 32;
  div x y := @ZToWord 32 (Z.div (wordToZ x) (wordToZ y));
  rem x y := @ZToWord 32 (Z.modulo (wordToZ x) (wordToZ y));
  signed_less_than a b := if wslt_dec a b then true else false;
  signed_eqb := @weqb 32;
  xor := @wxor 32;
  or := @wor 32;
  and := @wand 32;
  fromImm := ZToWord 32;
  regToInt8 := split1 8 24;
  regToInt16 := split1 16 16;
  regToInt32 := id;
  regToInt64 x := combine x (wzero 32);
  uInt8ToReg x := zext x 24;
  uInt16ToReg x := zext x 16;
  uInt32ToReg := id;
  uInt64ToReg := split1 32 32; (* unused *)
  int8ToReg x := sext x 24;
  int16ToReg x := sext x 16;
  int32ToReg := id;
  int64ToReg := split1 32 32; (* unused *)
  s32 := id;
  u32 := id;
  regToZ_signed := @wordToZ 32;
  regToZ_unsigned x := Z.of_N (wordToN x);
  sll w n := wlshift w (Z.to_nat n);
  srl w n := wrshift w (Z.to_nat n);
  sra w n := wrshift w (Z.to_nat n);
  ltu a b := if wlt_dec a b then true else false;
  divu := @wdiv 32;
  remu := @wmod 32;
  maxSigned := combine (wones 31) (wzero 1);
  maxUnsigned := wones 32;
  minSigned := wones 32;
  regToShamt5 x := Z.of_N (wordToN (split1 5 27 x));
  regToShamt  x := Z.of_N (wordToN (split1 5 27 x));
  highBits x := ZToWord 32 (bitSlice x 32 64);
|}.

Instance MachineWidth64: MachineWidth (word 64) := {|
  zero := $0;
  one := $1;
  add := @wplus 64;
  sub := @wminus 64;
  mul := @wmult 64;
  div x y := @ZToWord 64 (Z.div (wordToZ x) (wordToZ y));
  rem x y := @ZToWord 64 (Z.modulo (wordToZ x) (wordToZ y));
  signed_less_than a b := if wslt_dec a b then true else false;
  signed_eqb := @weqb 64;
  xor := @wxor 64;
  or := @wor 64;
  and := @wand 64;
  fromImm := ZToWord 64;
  regToInt8 := split1 8 56;
  regToInt16 := split1 16 48;
  regToInt32 := split1 32 32;
  regToInt64 := id;
  uInt8ToReg x := zext x 56;
  uInt16ToReg x := zext x 48;
  uInt32ToReg x := zext x 32;
  uInt64ToReg := id;
  int8ToReg x := sext x 56;
  int16ToReg x := sext x 48;
  int32ToReg x := sext x 32;
  int64ToReg := id;
  s32 x := sext (split1 32 32 x) 32;
  u32 x := zext (split1 32 32 x) 32;
  regToZ_signed := @wordToZ 64;
  regToZ_unsigned x := Z.of_N (wordToN x);
  sll w n := wlshift w (Z.to_nat n);
  srl w n := wrshift w (Z.to_nat n);
  sra w n := wrshift w (Z.to_nat n);
  ltu a b := if wlt_dec a b then true else false;
  divu := @wdiv 64;
  remu := @wmod 64;
  maxSigned := combine (wones 63) (wzero 1);
  maxUnsigned := wones 64;
  minSigned := wones 64;
  regToShamt5 x := Z.of_N (wordToN (split1 5 59 x));
  regToShamt  x := Z.of_N (wordToN (split1 6 58 x));
  highBits x := ZToWord 64 (bitSlice x 64 128);
|}.
