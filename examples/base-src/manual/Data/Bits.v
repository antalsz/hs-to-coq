(* Preamble *)

(* Issues with:
     - Level 60 is already declared right associative while it is now expected to be left associative.
       (changed to 61)
     - .&. and .|. can't be used as Coq notations.
       (replaced with :&: and :|: )
     - pattern guards
     - type (sub)class and implicit arguments
*)
Require Import Data.Maybe.
Require Import GHC.Enum.
Require Import GHC.Num.
Require Import GHC.Base.
Require Import GHC.Real.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Converted data type declarations: *)
Class Bits a `{Eq_ a} := {
  op_zizazi__ : a -> a -> a ;
  op_zizbzi__ : a -> a -> a ;
  bit : Int -> a ;
(*   bitSize : a -> Int ; *)
  bitSizeMaybe : a -> option Int ;
  clearBit : a -> Int -> a ;
  complement : a -> a ;
  complementBit : a -> Int -> a ;
  isSigned : a -> bool ;
  popCount : a -> Int ;
  rotate : a -> Int -> a ;
  rotateL : a -> Int -> a ;
  rotateR : a -> Int -> a ;
  setBit : a -> Int -> a ;
  shift : a -> Int -> a ;
  shiftL : a -> Int -> a ;
  shiftR : a -> Int -> a ;
  testBit : a -> Int -> bool ;
  unsafeShiftL : a -> Int -> a ;
  unsafeShiftR : a -> Int -> a ;
  xor : a -> a -> a ;
  zeroBits : a }.

Infix ".&." := (op_zizazi__) (left associativity, at level 40).

Notation "'_.&._'" := (op_zizazi__).

Infix ".|." := (op_zizbzi__) (left associativity, at level 61).

Notation "'_.|._'" := (op_zizbzi__).

Class FiniteBits b `{Bits b} := {
  countLeadingZeros : b -> Int ;
  countTrailingZeros : b -> Int ;
  finiteBitSize : b -> Int }.

(* Converted value declarations: *)
Definition testBitDefault {a} `{Bits a} `{Num a} : a -> Int -> bool :=
  (fun arg_27__
       arg_28__ =>
    (match arg_27__ , arg_28__ with
      | x , i => (((x .&.(**) bit i)) /= #0)
    end)).


Definition isBitSubType {a} {b} `{Bits a} `{Bits b} : a -> b -> bool :=
  fun arg_65__ arg_66__ =>
    match arg_65__ , arg_66__ with
      | x , y => let ySigned := isSigned y in
                 let yWidth := bitSizeMaybe y in
                 let xSigned := isSigned x in
                 let xWidth := bitSizeMaybe x in
                 let j_71__ :=
                   if andb (negb xSigned) ySigned
                   then match xWidth with
                          | (Some xW) => match yWidth with
                                           | (Some yW) => op_zl__ xW yW
                                           | _ => false
                                         end
                          | _ => false
                        end
                   else false in
                 let j_72__ :=
                   if GHC.Base.op_zeze__ xSigned ySigned
                   then match xWidth with
                          | (Some xW) => match yWidth with
                                           | (Some yW) => op_zlze__ xW yW
                                           | _ => j_71__
                                         end
                          | _ => j_71__
                        end
                   else j_71__ in
                 let j_73__ :=
                   if andb (negb xSigned) (andb (negb ySigned) (GHC.Base.op_zeze__ None yWidth))
                   then true
                   else j_72__ in
                 let j_74__ :=
                   if andb ySigned (GHC.Base.op_zeze__ None yWidth)
                   then true
                   else j_73__ in
                 if andb (GHC.Base.op_zeze__ xWidth yWidth) (GHC.Base.op_zeze__ xSigned ySigned)
                 then true
                 else j_74__
    end.


Definition toIntegralSized {a} {b} `{GHC.Real.Integral a} `{GHC.Real.Integral b}
                           `{Bits a} `{Bits b} : a -> option b :=
  fun arg_77__ =>
    match arg_77__ with
      | x => let xWidth := bitSizeMaybe x in
             let y := GHC.Real.fromIntegral x in
             let yWidth := bitSizeMaybe y in
             let yMinBound :=
               let j_81__ :=
                 if andb (isSigned x) (isSigned y)
                 then match yWidth with
                        | (Some yW) => Some (GHC.Base.op_zd__ GHC.Num.negate (bit (GHC.Num.op_zm__ yW
                                                                                                   (GHC.Num.fromInteger
                                                                                                   1))))
                        | _ => None
                      end
                 else None in
               let j_82__ :=
                 if andb (isSigned x) (negb (isSigned y))
                 then Some (GHC.Num.fromInteger 0)
                 else j_81__ in
               if isBitSubType x y
               then None
               else j_82__ in
             let yMaxBound :=
               let j_84__ :=
                 match yWidth with
                   | (Some yW) => if isSigned y
                                  then Some (GHC.Num.op_zm__ (bit (GHC.Num.op_zm__ yW (GHC.Num.fromInteger 1)))
                                                             (GHC.Num.fromInteger 1))
                                  else Some (GHC.Num.op_zm__ (bit yW) (GHC.Num.fromInteger 1))
                   | _ => None
                 end in
               let j_85__ :=
                 if andb (isSigned x) (negb (isSigned y))
                 then match xWidth with
                        | (Some xW) => match yWidth with
                                         | (Some yW) => if op_zlze__ xW (GHC.Num.op_zp__ yW (GHC.Num.fromInteger 1))
                                                        then None
                                                        else j_84__
                                         | _ => j_84__
                                       end
                        | _ => j_84__
                      end
                 else j_84__ in
               if isBitSubType x y
               then None
               else j_85__ in
             if andb (Data.Maybe.maybe true (fun arg_87__ => op_zlze__ arg_87__ x)
                     yMinBound) (Data.Maybe.maybe true (fun arg_88__ => op_zlze__ x arg_88__)
                     yMaxBound)
             then Some y
             else None
    end.


Definition bitDefault {a} `{Bits a} `{Num a} : Int -> a := (fun arg_26__ =>
    (match arg_26__ with
      | i => shiftL #1 i
    end)).

Definition bit_bool : Int -> bool := (fun num_43__ => (if (num_43__ == #0)
                                     then true
                                     else false)).
Definition rotate_bool: bool -> Int -> bool :=
(fun arg_41__  arg_42__ =>
    (match arg_41__ , arg_42__ with
      | x , _ => x
    end)).

Definition shift_bool : bool -> Int -> bool
  := (fun x num_38__  => (if (num_38__ == #0)
                       then x
                       else false)).

Definition clearBit_bool : bool -> Int -> bool :=
(fun arg_6__
                   arg_7__ =>
    (match arg_6__ , arg_7__ with
      | x , i => (andb x (negb (bit_bool i)))
    end)).

(* Converted type class instance declarations: *)
Instance instance_Bits_bool_37__ : Bits bool := {
  op_zizazi__ := andb ;
  op_zizbzi__ := orb ;
  xor := _/=_ ;
  complement := negb ;
  shift := shift_bool;
  rotate := rotate_bool;
  bit := bit_bool;
  testBit := (fun x num_45__ => (if (num_45__ == #0)
                        then x
                        else false)) ;
  bitSizeMaybe := (fun arg_48__ => (match arg_48__ with | _ => Some #1 end)) ;
(*   bitSize := (fun arg_49__ => (match arg_49__ with | _ => #1 end)) ; *)
  isSigned := (fun arg_50__ => (match arg_50__ with | _ => false end)) ;
  popCount := (fun arg_51__ =>
    (match arg_51__ with
      | false => #0
      | true => #1
    end)) ;
  clearBit := clearBit_bool ;
  complementBit := (fun arg_8__
                        arg_9__ =>
    (match arg_8__ , arg_9__ with
      | x , i => x /= (bit_bool i)
    end)) ;
  rotateL := (fun arg_18__
                  arg_19__ =>
    (match arg_18__ , arg_19__ with
      | x , i => rotate_bool x i
    end)) ;
  rotateR := (fun arg_20__
                  arg_21__ =>
    (match arg_20__ , arg_21__ with
      | x , i => rotate_bool x (negate i)
    end)) ;
  setBit := (fun arg_4__
                 arg_5__ =>
    (match arg_4__ , arg_5__ with
      | x , i => (orb x (bit_bool i))
    end)) ;
  shiftL := (fun arg_10__
                 arg_11__ =>
    (match arg_10__ , arg_11__ with
      | x , i => shift_bool x i
    end)) ;
  shiftR := (fun arg_14__
                 arg_15__ =>
    (match arg_14__ , arg_15__ with
      | x , i => shift_bool x (negate i)
    end)) ;
  unsafeShiftL := (fun arg_12__
                       arg_13__ =>
    (match arg_12__ , arg_13__ with
      | x , i => shift_bool x i
    end)) ;
  unsafeShiftR := (fun arg_16__
                       arg_17__ =>
    (match arg_16__ , arg_17__ with
      | x , i => shift_bool x i
    end)) ;
  zeroBits := clearBit_bool (bit_bool #0) #0 }.

Instance instance_FiniteBits_bool_52__ : FiniteBits bool := {
  finiteBitSize := (fun arg_53__ => (match arg_53__ with | _ => #1 end)) ;
  countTrailingZeros := (fun arg_54__ =>
    (match arg_54__ with
      | x => (if x
             then #0
             else #1)
    end)) ;
  countLeadingZeros := (fun arg_55__ =>
    (match arg_55__ with
      | x => (if x
             then #0
             else #1)
    end)) }.

Definition shiftL_Int := Z.shiftl.
Definition bit_Int := shiftL_Int #1.
Definition complementBit_Int x i := Z.lor x (bit_Int i).

Definition complement_Int : Int -> Int := Z.lnot.
Definition popCount_Int : Int -> Int := fun x => #0.   (* TODO *)
Definition shift_Int (x:Int) (i:Int) :=
  if x < #0 then Z.shiftr x (-i)
  else if x > #0 then Z.shiftl x i
       else x.

Instance instance_Bits_Int : Bits Int :=  {
  op_zizazi__ := Z.land ;
  op_zizbzi__ := Z.lor ;
  bit := bit_Int;
  bitSizeMaybe := fun _ => None ;
  clearBit := fun x i => Z.land x (complement_Int (bit_Int i)) ;
  complement := complement_Int ;
  complementBit := complementBit_Int ;
  isSigned := fun x => true ;
  popCount := popCount_Int ;
  rotate := shiftL_Int;
  rotateL := shiftL_Int;
  rotateR := Z.shiftr;
  setBit := fun x i => Z.lor x (bit_Int i);
  shift := shift_Int;
  shiftL := Z.shiftl;
  shiftR := Z.shiftr;
  testBit := Z.testbit;
  unsafeShiftL := Z.shiftl;
  unsafeShiftR := Z.shiftr;
  xor := Z.lxor;
  zeroBits := #0;
}.



Definition shiftLL (n: N) (s : N) : N := Coq.NArith.BinNat.N.shiftl n s.
Definition shiftRL (n: N) (s : N) : N := Coq.NArith.BinNat.N.shiftr n s.

Definition bit_N s := shiftLL 1%N (Coq.ZArith.BinInt.Z.to_N s).

Fixpoint Pos_popcount (p : positive) : positive :=
  match p with
  | 1%positive => 1%positive
  | (p~1)%positive => Pos.succ (Pos_popcount p)
  | (p~0)%positive => Pos_popcount p
  end.


Definition N_popcount (a : N) : N :=
  match a with
  | 0%N => 0%N
  | N.pos p => N.pos (Pos_popcount p)
  end.


Instance Bits__N : Bits N :=  {
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
  zeroBits := 0%N;
}.


Module Notations.
Notation "'_Data.Bits..&._'" := (op_zizazi__).
Infix "Data.Bits..&." := (op_zizazi__) (at level 99).
Notation "'_Data.Bits..|._'" := (op_zizbzi__).
Infix "Data.Bits..|." := (op_zizbzi__) (at level 99).
End Notations.
