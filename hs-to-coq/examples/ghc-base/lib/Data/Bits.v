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


Set Implicit Arguments.
Generalizable All Variables.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Converted data type declarations: *)
Class Bits a `{Eq_ a} := {
  op_zizazi__ : a -> a -> a ;
  op_zizbzi__ : a -> a -> a ;
  bit : Int -> a ;
  bitSize : a -> Int ;
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

Infix ":&:" := (op_zizazi__) (left associativity, at level 40).

Notation "'_:&:_'" := (op_zizazi__).

Infix ":|:" := (op_zizbzi__) (left associativity, at level 61).

Notation "'_:|:_'" := (op_zizbzi__).

Class FiniteBits b `{Bits b} := {
  countLeadingZeros : b -> Int ;
  countTrailingZeros : b -> Int ;
  finiteBitSize : b -> Int }.

(* Converted value declarations: *)
Definition testBitDefault {a} `{Bits a} `{Num a} : a -> Int -> bool :=
  (fun arg_27__
       arg_28__ =>
    (match arg_27__ , arg_28__ with
      | x , i => (((x :&: bit i)) /= #0)
    end)).

(* Pattern guard, also not structurally terminating.
Definition popCountDefault {a} `{Bits a} `{Num a} : a -> Int := (let go :=
    (fix go arg_30__ arg_31__ := (match arg_30__ , arg_31__ with
                                   | c , num_29__ => (if (num_29__ == #0)
                                                     then c
                                                     else _(*MissingValue*))
                                   | c , w => go (c + #1) ((w :&: (w - #1)))
                                 end))
  in go #0). *)

(* many UNDEFINED EVARS: *)
Definition isBitSubType {a} {b} `{Bits a} `{Bits b} : a -> b -> bool.
Admitted.
(*
  (fun arg_35__
       arg_36__ =>
    (match arg_35__ , arg_36__ with
      | x , y => (let xWidth := bitSizeMaybe x
                 in (let xSigned := isSigned x
                    in (let yWidth := bitSizeMaybe y
                       in (let ySigned := isSigned y
                          in (if andb (xWidth == yWidth) (xSigned == ySigned)
                             then true
                             else (if andb ySigned (None == yWidth)
                                  then true
                                  else (if andb (negb xSigned) (andb (negb ySigned) (None == yWidth))
                                       then true
                                       else (if (xSigned == ySigned)
                                            then (match xWidth with
                                                   | (Some xW) => (match yWidth with
                                                                    | (Some yW) => (xW <=? yW)
                                                                    | _ => (if andb (negb xSigned) ySigned
                                                                           then (match xWidth with
                                                                                  | (Some xW) => (match yWidth with
                                                                                                   | (Some yW) => (xW <?
                                                                                                                  yW)
                                                                                                   | _ => false
                                                                                                 end)
                                                                                  | _ => false
                                                                                end)
                                                                           else false)
                                                                  end)
                                                   | _ => (if andb (negb xSigned) ySigned
                                                          then (match xWidth with
                                                                 | (Some xW) => (match yWidth with
                                                                                  | (Some yW) => (xW <? yW)
                                                                                  | _ => false
                                                                                end)
                                                                 | _ => false
                                                               end)
                                                          else false)
                                                 end)
                                            else (if andb (negb xSigned) ySigned
                                                 then (match xWidth with
                                                        | (Some xW) => (match yWidth with
                                                                         | (Some yW) => (xW <? yW)
                                                                         | _ => false
                                                                       end)
                                                        | _ => false
                                                      end)
                                                 else false)))))))))
    end)).
*)

(* many UNDEFINED EVARS: *)
Definition toIntegralSized {a} {b} `{Integral a} `{Integral b} `{Bits a} `{Bits
                           b} : a -> option b.
Admitted.
(*
 (fun arg_34__ =>
    (match arg_34__ with
      | x => (let y := fromIntegral x
             in (let xWidth := bitSizeMaybe x
                in (let yWidth := bitSizeMaybe y
                   in (let yMinBound :=
                        (if isBitSubType x y
                        then None
                        else (if andb (isSigned x) (negb (isSigned y))
                             then Some #0
                             else (if andb (isSigned x) (isSigned y)
                                  then (match yWidth with
                                         | (Some yW) => Some ((negate $ bit (yW - #1)))
                                         | _ => None
                                       end)
                                  else None)))
                      in (let yMaxBound :=
                           (if isBitSubType x y
                           then None
                           else (if andb (isSigned x) (negb (isSigned y))
                                then (match xWidth with
                                       | (Some xW) => (match yWidth with
                                                        | (Some yW) => (if (xW <=? yW) + #1
                                                                       then None
                                                                       else (match yWidth with
                                                                              | (Some yW) => (if isSigned y
                                                                                             then Some (bit (yW - #1) -
                                                                                                       #1)
                                                                                             else Some (bit yW - #1))
                                                                              | _ => None
                                                                            end))
                                                        | _ => (match yWidth with
                                                                 | (Some yW) => (if isSigned y
                                                                                then Some (bit (yW - #1) - #1)
                                                                                else Some (bit yW - #1))
                                                                 | _ => None
                                                               end)
                                                      end)
                                       | _ => (match yWidth with
                                                | (Some yW) => (if isSigned y
                                                               then Some (bit (yW - #1) - #1)
                                                               else Some (bit yW - #1))
                                                | _ => None
                                              end)
                                     end)
                                else (match yWidth with
                                       | (Some yW) => (if isSigned y
                                                      then Some (bit (yW - #1) - #1)
                                                      else Some (bit yW - #1))
                                       | _ => None
                                     end)))
                         in (if andb (maybe true ((fun arg_32__ => (arg_32__ <=? x))) yMinBound) (maybe
                                     true ((fun arg_33__ => (x <=? arg_33__))) yMaxBound)
                            then Some y
                            else None))))))
    end)).
*)

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
Instance instance_Bits_bool_37__ : !Bits bool := {
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
  bitSize := (fun arg_49__ => (match arg_49__ with | _ => #1 end)) ;
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

Instance instance_FiniteBits_bool_52__ : !FiniteBits bool := {
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

(*
Instance instance_Bits_Int_56__ : Bits Int := {
  zeroBits := #0 ;
  bit := bitDefault ;
  testBit := testBitDefault ;
  op_zizazi__ := (fun arg_57__
                      arg_58__ =>
    (match arg_57__ , arg_58__ with
      | (I# x#) , (I# y#) => _I#_ ((_x#_ andI# _y#_))
    end)) ;
  op_zizbzi__ := (fun arg_59__
                      arg_60__ =>
    (match arg_59__ , arg_60__ with
      | (I# x#) , (I# y#) => _I#_ ((_x#_ orI# _y#_))
    end)) ;
  xor := (fun arg_61__
              arg_62__ =>
    (match arg_61__ , arg_62__ with
      | (I# x#) , (I# y#) => _I#_ ((_x#_ xorI# _y#_))
    end)) ;
  complement := (fun arg_63__ =>
    (match arg_63__ with
      | (I# x#) => _I#_ (_notI#_ _x#_)
    end)) ;
  shift := (fun arg_64__
                arg_65__ =>
    (match arg_64__ , arg_65__ with
      | (I# x#) , (I# i#) => (if _isTrue#_ ((_i#_ >=# 0))
                             then _I#_ ((_x#_ iShiftL# _i#_))
                             else _I#_ ((_x#_ iShiftRA# _negateInt#_ _i#_)))
    end)) ;
  shiftL := (fun arg_66__
                 arg_67__ =>
    (match arg_66__ , arg_67__ with
      | (I# x#) , (I# i#) => _I#_ ((_x#_ iShiftL# _i#_))
    end)) ;
  unsafeShiftL := (fun arg_68__
                       arg_69__ =>
    (match arg_68__ , arg_69__ with
      | (I# x#) , (I# i#) => _I#_ ((_x#_ uncheckedIShiftL# _i#_))
    end)) ;
  shiftR := (fun arg_70__
                 arg_71__ =>
    (match arg_70__ , arg_71__ with
      | (I# x#) , (I# i#) => _I#_ ((_x#_ iShiftRA# _i#_))
    end)) ;
  unsafeShiftR := (fun arg_72__
                       arg_73__ =>
    (match arg_72__ , arg_73__ with
      | (I# x#) , (I# i#) => _I#_ ((_x#_ uncheckedIShiftRA# _i#_))
    end)) ;
  rotate := (fun arg_74__
                 arg_75__ =>
    (match arg_74__ , arg_75__ with
      | (I# x#) , (I# i#) => (match (_i#_ andI# ((wsib -# 1))) with
                               | i'# => (match 64 with
                                          | wsib => _I#_ ((((_x#_ uncheckedIShiftL# _i'#_)) orI# ((_x#_
                                                         uncheckedIShiftRL# ((wsib -# _i'#_))))))
                                        end)
                             end)
    end)) ;
  bitSizeMaybe := (fun arg_76__ =>
    (match arg_76__ with
      | i => Some (finiteBitSize i)
    end)) ;
  bitSize := (fun arg_77__ => (match arg_77__ with | i => finiteBitSize i end)) ;
  popCount := (fun arg_78__ =>
    (match arg_78__ with
      | (I# x#) => _I#_ (_word2Int#_ (_popCnt#_ (_int2Word#_ _x#_)))
    end)) ;
  isSigned := (fun arg_79__ => (match arg_79__ with | _ => true end)) ;
  clearBit := (fun arg_6__
                   arg_7__ =>
    (match arg_6__ , arg_7__ with
      | x , i => (x :&: complement (bit i))
    end)) ;
  complementBit := (fun arg_8__
                        arg_9__ =>
    (match arg_8__ , arg_9__ with
      | x , i => xor x (bit i)
    end)) ;
  rotateL := (fun arg_18__
                  arg_19__ =>
    (match arg_18__ , arg_19__ with
      | x , i => rotate x i
    end)) ;
  rotateR := (fun arg_20__
                  arg_21__ =>
    (match arg_20__ , arg_21__ with
      | x , i => rotate x (negate i)
    end)) ;
  setBit := (fun arg_4__
                 arg_5__ =>
    (match arg_4__ , arg_5__ with
      | x , i => (x :|: bit i)
    end)) }.

Instance instance_FiniteBits_Int_80__ : FiniteBits Int := {
  finiteBitSize := (fun arg_81__ => (match arg_81__ with | _ => #64 end)) ;
  countLeadingZeros := (fun arg_82__ =>
    (match arg_82__ with
      | (I# x#) => _I#_ (_word2Int#_ (_clz#_ (_int2Word#_ _x#_)))
    end)) ;
  countTrailingZeros := (fun arg_83__ =>
    (match arg_83__ with
      | (I# x#) => _I#_ (_word2Int#_ (_ctz#_ (_int2Word#_ _x#_)))
    end)) }.

Instance instance_Bits_Word_84__ : Bits Word := {
  op_zizazi__ := (fun arg_85__
                      arg_86__ =>
    (match arg_85__ , arg_86__ with
      | (W# x#) , (W# y#) => _W#_ ((_x#_ and# _y#_))
    end)) ;
  op_zizbzi__ := (fun arg_87__
                      arg_88__ =>
    (match arg_87__ , arg_88__ with
      | (W# x#) , (W# y#) => _W#_ ((_x#_ or# _y#_))
    end)) ;
  xor := (fun arg_89__
              arg_90__ =>
    (match arg_89__ , arg_90__ with
      | (W# x#) , (W# y#) => _W#_ ((_x#_ xor# _y#_))
    end)) ;
  complement := (fun arg_91__ =>
    (match arg_91__ with
      | (W# x#) => (match maxBound with
                     | (W# mb#) => _W#_ ((_x#_ xor# _mb#_))
                   end)
    end)) ;
  shift := (fun arg_92__
                arg_93__ =>
    (match arg_92__ , arg_93__ with
      | (W# x#) , (I# i#) => (if _isTrue#_ ((_i#_ >=# 0))
                             then _W#_ ((_x#_ shiftL# _i#_))
                             else _W#_ ((_x#_ shiftRL# _negateInt#_ _i#_)))
    end)) ;
  shiftL := (fun arg_94__
                 arg_95__ =>
    (match arg_94__ , arg_95__ with
      | (W# x#) , (I# i#) => _W#_ ((_x#_ shiftL# _i#_))
    end)) ;
  unsafeShiftL := (fun arg_96__
                       arg_97__ =>
    (match arg_96__ , arg_97__ with
      | (W# x#) , (I# i#) => _W#_ ((_x#_ uncheckedShiftL# _i#_))
    end)) ;
  shiftR := (fun arg_98__
                 arg_99__ =>
    (match arg_98__ , arg_99__ with
      | (W# x#) , (I# i#) => _W#_ ((_x#_ shiftRL# _i#_))
    end)) ;
  unsafeShiftR := (fun arg_100__
                       arg_101__ =>
    (match arg_100__ , arg_101__ with
      | (W# x#) , (I# i#) => _W#_ ((_x#_ uncheckedShiftRL# _i#_))
    end)) ;
  rotate := (fun arg_102__
                 arg_103__ =>
    (match arg_102__ , arg_103__ with
      | (W# x#) , (I# i#) => (match (_i#_ andI# ((wsib -# 1))) with
                               | i'# => (match 64 with
                                          | wsib => (if _isTrue#_ ((_i'#_ ==# 0))
                                                    then _W#_ _x#_
                                                    else _W#_ ((((_x#_ uncheckedShiftL# _i'#_)) or# ((_x#_
                                                              uncheckedShiftRL# ((wsib -# _i'#_)))))))
                                        end)
                             end)
    end)) ;
  bitSizeMaybe := (fun arg_104__ =>
    (match arg_104__ with
      | i => Some (finiteBitSize i)
    end)) ;
  bitSize := (fun arg_105__ =>
    (match arg_105__ with
      | i => finiteBitSize i
    end)) ;
  isSigned := (fun arg_106__ => (match arg_106__ with | _ => false end)) ;
  popCount := (fun arg_107__ =>
    (match arg_107__ with
      | (W# x#) => _I#_ (_word2Int#_ (_popCnt#_ _x#_))
    end)) ;
  bit := bitDefault ;
  testBit := testBitDefault ;
  clearBit := (fun arg_6__
                   arg_7__ =>
    (match arg_6__ , arg_7__ with
      | x , i => (x :&: complement (bit i))
    end)) ;
  complementBit := (fun arg_8__
                        arg_9__ =>
    (match arg_8__ , arg_9__ with
      | x , i => xor x (bit i)
    end)) ;
  rotateL := (fun arg_18__
                  arg_19__ =>
    (match arg_18__ , arg_19__ with
      | x , i => rotate x i
    end)) ;
  rotateR := (fun arg_20__
                  arg_21__ =>
    (match arg_20__ , arg_21__ with
      | x , i => rotate x (negate i)
    end)) ;
  setBit := (fun arg_4__
                 arg_5__ =>
    (match arg_4__ , arg_5__ with
      | x , i => (x :|: bit i)
    end)) ;
  zeroBits := clearBit (bit #0) #0 }.

Instance instance_FiniteBits_Word_108__ : FiniteBits Word := {
  finiteBitSize := (fun arg_109__ => (match arg_109__ with | _ => #64 end)) ;
  countLeadingZeros := (fun arg_110__ =>
    (match arg_110__ with
      | (W# x#) => _I#_ (_word2Int#_ (_clz#_ _x#_))
    end)) ;
  countTrailingZeros := (fun arg_111__ =>
    (match arg_111__ with
      | (W# x#) => _I#_ (_word2Int#_ (_ctz#_ _x#_))
    end)) }.

Instance instance_Bits_Integer_112__ : Bits Integer := {
  op_zizazi__ := andInteger ;
  op_zizbzi__ := orInteger ;
  xor := xorInteger ;
  complement := complementInteger ;
  shift := (fun arg_113__
                arg_114__ =>
    (match arg_113__ , arg_114__ with
      | x , ((I# i#) as i) => (if (i >=? #0)
                              then shiftLInteger x _i#_
                              else shiftRInteger x (_negateInt#_ _i#_))
    end)) ;
  testBit := (fun arg_115__
                  arg_116__ =>
    (match arg_115__ , arg_116__ with
      | x , (I# i) => testBitInteger x i
    end)) ;
  zeroBits := #0 ;
  bit := (fun arg_117__ =>
    (match arg_117__ with
      | (I# i#) => bitInteger _i#_
    end)) ;
  popCount := (fun arg_118__ =>
    (match arg_118__ with
      | x => _I#_ (popCountInteger x)
    end)) ;
  rotate := (fun arg_119__
                 arg_120__ =>
    (match arg_119__ , arg_120__ with
      | x , i => shift x i
    end)) ;
  bitSizeMaybe := (fun arg_121__ => (match arg_121__ with | _ => None end)) ;
  bitSize := (fun arg_122__ =>
    (match arg_122__ with
      | _ => errorWithoutStackTrace &"Data.Bits.bitSize(Integer)"
    end)) ;
  isSigned := (fun arg_123__ => (match arg_123__ with | _ => true end)) ;
  clearBit := (fun arg_6__
                   arg_7__ =>
    (match arg_6__ , arg_7__ with
      | x , i => (x :&: complement (bit i))
    end)) ;
  complementBit := (fun arg_8__
                        arg_9__ =>
    (match arg_8__ , arg_9__ with
      | x , i => xor x (bit i)
    end)) ;
  rotateL := (fun arg_18__
                  arg_19__ =>
    (match arg_18__ , arg_19__ with
      | x , i => rotate x i
    end)) ;
  rotateR := (fun arg_20__
                  arg_21__ =>
    (match arg_20__ , arg_21__ with
      | x , i => rotate x (negate i)
    end)) ;
  setBit := (fun arg_4__
                 arg_5__ =>
    (match arg_4__ , arg_5__ with
      | x , i => (x :|: bit i)
    end)) ;
  shiftL := (fun arg_10__
                 arg_11__ =>
    (match arg_10__ , arg_11__ with
      | x , i => shift x i
    end)) ;
  shiftR := (fun arg_14__
                 arg_15__ =>
    (match arg_14__ , arg_15__ with
      | x , i => shift x (negate i)
    end)) ;
  unsafeShiftL := (fun arg_12__
                       arg_13__ =>
    (match arg_12__ , arg_13__ with
      | x , i => shiftL x i
    end)) ;
  unsafeShiftR := (fun arg_16__
                       arg_17__ =>
    (match arg_16__ , arg_17__ with
      | x , i => shiftR x i
    end)) }.
*)

(* Unbound variables:
     $ + - -# /= <=? <? == ==# >=# >=? Eq_ I# Int Integer Integral None Num Some W#
     Word _/=_ _I#_ _W#_ _clz#_ _ctz#_ _i#_ _i'#_ _int2Word#_ _isTrue#_ _mb#_
     _negateInt#_ _notI#_ _popCnt#_ _word2Int#_ _x#_ _y#_ and# andI# andInteger andb
     bitInteger bool complementInteger errorWithoutStackTrace false fromIntegral
     iShiftL# iShiftRA# maxBound maybe negate negb option or# orI# orInteger orb
     popCountInteger shiftL# shiftLInteger shiftRInteger shiftRL# testBitInteger true
     uncheckedIShiftL# uncheckedIShiftRA# uncheckedIShiftRL# uncheckedShiftL#
     uncheckedShiftRL# wsib xor# xorI# xorInteger
*)
