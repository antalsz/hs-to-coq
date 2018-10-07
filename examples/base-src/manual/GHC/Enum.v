(* Preamble *)
Require Import GHC.Base.
Require Import GHC.Char.
Require Import GHC.Num.

Require Import GHC.Err.

Set Implicit Arguments.
Generalizable All Variables.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

From Coq Require Import ssreflect.

(* Note: we will only be able to make instances of this class for bounded
   types so that we can support enumFrom and still terminate.

   We cheat on Int and N.

   Furthermore, we need to remove `enumFromThen` and `enumFromThenTo` as they
   don't terminate when the first two arguments are equal.

*)
Class Enum a := {
  enumFrom : (a -> (list a)) ;
(*  enumFromThen : (a -> (a -> (list a))) ;
  enumFromThenTo : (a -> (a -> (a -> (list a)))) ; *)
  enumFromTo : (a -> (a -> (list a))) ;
  fromEnum : (a -> Int) ;
  pred : (a -> a) ;
  succ : (a -> a) ;
  toEnum : (Int -> a) }.

Class Bounded a := {
  maxBound : a ;
  minBound : a }.

(* haha *)
Definition maxIntWord : N := N.pow 2%N 31%N.

(* Converted type class instance declarations: *)
Instance instance__Bounded_unit__141__ : (Bounded unit) := {
  minBound := tt ;
  maxBound := tt }.

Instance instance__Enum_unit__142__ : (Enum unit) := {
  succ := GHC.Err.default;
  pred := GHC.Err.default;
  toEnum := fun _ => tt ;
  fromEnum := (fun arg_146__ => (match arg_146__ with | tt => #0 end)) ;
  enumFrom := (fun arg_147__ => (match arg_147__ with | tt => (tt :: nil) end)) ;
  enumFromTo := (fun arg_150__ arg_151__ =>
    (match arg_150__ , arg_151__ with
      | tt , tt => (tt :: nil)
    end)) ;
}.

Instance instance__forall____Bounded_a______Bounded_b_____Bounded__a___b____155__
  : (forall `{(Bounded a)} `{(Bounded b)}, (Bounded (a * b))) := {
  minBound := (pair minBound minBound) ;
  maxBound := (pair maxBound maxBound) }.

Instance instance__forall____Bounded_a______Bounded_b______Bounded_c_____Bounded___a___b____c____156__
  : (forall `{(Bounded a)} `{(Bounded b)} `{(Bounded c)},
                 (Bounded ((a * b) * c))) := {
                                              minBound := (pair (pair minBound minBound) minBound) ;
                                              maxBound := (pair (pair maxBound maxBound) maxBound) }.

Instance instance__forall____Bounded_a______Bounded_b______Bounded_c______Bounded_d_____Bounded____a___b____c____d____157__
  : (forall `{(Bounded a)}
            `{(Bounded b)}
            `{(Bounded c)}
            `{(Bounded d)},
      (Bounded (((a * b) * c) * d))) := {
  minBound := (pair (pair (pair minBound minBound) minBound) minBound) ;
  maxBound := (pair (pair (pair maxBound maxBound) maxBound) maxBound) }.

Instance instance__forall____Bounded_a______Bounded_b______Bounded_c______Bounded_d______Bounded_e_____Bounded_____a___b____c____d____e____158__
  : (forall `{(Bounded a)}
            `{(Bounded b)}
            `{(Bounded c)}
            `{(Bounded d)}
            `{(Bounded e)},
      (Bounded ((((a * b) * c) * d) * e))) := {
  minBound := (pair (pair (pair (pair minBound minBound) minBound) minBound)
                    minBound) ;
  maxBound := (pair (pair (pair (pair maxBound maxBound) maxBound) maxBound)
                    maxBound) }.

Instance instance__forall____Bounded_a______Bounded_b______Bounded_c______Bounded_d______Bounded_e______Bounded_f_____Bounded______a___b____c____d____e____f____159__
  : (forall `{(Bounded a)}
            `{(Bounded b)}
            `{(Bounded c)}
            `{(Bounded d)}
            `{(Bounded e)}
            `{(Bounded f)},
      (Bounded (((((a * b) * c) * d) * e) * f))) := {
  minBound := (pair (pair (pair (pair (pair minBound minBound) minBound) minBound)
                          minBound) minBound) ;
  maxBound := (pair (pair (pair (pair (pair maxBound maxBound) maxBound) maxBound)
                          maxBound) maxBound) }.

Instance instance__forall____Bounded_a______Bounded_b______Bounded_c______Bounded_d______Bounded_e______Bounded_f______Bounded_g_____Bounded_______a___b____c____d____e____f____g____160__
  : (forall `{(Bounded a)}
            `{(Bounded b)}
            `{(Bounded c)}
            `{(Bounded d)}
            `{(Bounded e)}
            `{(Bounded f)}
            `{(Bounded g)},
      (Bounded ((((((a * b) * c) * d) * e) * f) * g))) := {
  minBound := (pair (pair (pair (pair (pair (pair minBound minBound) minBound)
                                      minBound) minBound) minBound) minBound) ;
  maxBound := (pair (pair (pair (pair (pair (pair maxBound maxBound) maxBound)
                                      maxBound) maxBound) maxBound) maxBound) }.

Instance instance__forall____Bounded_a______Bounded_b______Bounded_c______Bounded_d______Bounded_e______Bounded_f______Bounded_g______Bounded_h_____Bounded________a___b____c____d____e____f____g____h____161__
  : forall a b c d e f g h, (forall `{(Bounded a)}
            `{(Bounded b)}
            `{(Bounded c)}
            `{(Bounded d)}
            `{(Bounded e)}
            `{(Bounded f)}
            `{(Bounded g)}
            `{(Bounded h)},
      (Bounded (((((((a * b) * c) * d) * e) * f) * g) * h))) := {
  minBound := (pair (pair (pair (pair (pair (pair (pair minBound minBound)
                                                  minBound) minBound) minBound) minBound) minBound) minBound) ;
  maxBound := (pair (pair (pair (pair (pair (pair (pair maxBound maxBound)
                                                  maxBound) maxBound) maxBound) maxBound) maxBound) maxBound) }.

Instance instance__forall____Bounded_a______Bounded_b______Bounded_c______Bounded_d______Bounded_e______Bounded_f______Bounded_g______Bounded_h______Bounded_i_____Bounded_________a___b____c____d____e____f____g____h____i____162__
  : (forall `{(Bounded a)}
            `{(Bounded b)}
            `{(Bounded c)}
            `{(Bounded d)}
            `{(Bounded e)}
            `{(Bounded f)}
            `{(Bounded g)}
            `{(Bounded h)}
            `{(Bounded i)},
      (Bounded ((((((((a * b) * c) * d) * e) * f) * g) * h) * i))) := {
  minBound := (pair (pair (pair (pair (pair (pair (pair (pair minBound minBound)
                                                        minBound) minBound) minBound) minBound) minBound) minBound)
                    minBound) ;
  maxBound := (pair (pair (pair (pair (pair (pair (pair (pair maxBound maxBound)
                                                        maxBound) maxBound) maxBound) maxBound) maxBound) maxBound)
                    maxBound) }.

Instance instance__forall____Bounded_a______Bounded_b______Bounded_c______Bounded_d______Bounded_e______Bounded_f______Bounded_g______Bounded_h______Bounded_i______Bounded_j_____Bounded__________a___b____c____d____e____f____g____h____i____j____163__
  : (forall `{(Bounded a)}
            `{(Bounded b)}
            `{(Bounded c)}
            `{(Bounded d)}
            `{(Bounded e)}
            `{(Bounded f)}
            `{(Bounded g)}
            `{(Bounded h)}
            `{(Bounded i)}
            `{(Bounded j)},
      (Bounded (((((((((a * b) * c) * d) * e) * f) * g) * h) * i) * j))) := {
  minBound := (pair (pair (pair (pair (pair (pair (pair (pair (pair minBound
                                                                    minBound) minBound) minBound) minBound) minBound)
                                      minBound) minBound) minBound) minBound) ;
  maxBound := (pair (pair (pair (pair (pair (pair (pair (pair (pair maxBound
                                                                    maxBound) maxBound) maxBound) maxBound) maxBound)
                                      maxBound) maxBound) maxBound) maxBound) }.

Instance instance__forall____Bounded_a______Bounded_b______Bounded_c______Bounded_d______Bounded_e______Bounded_f______Bounded_g______Bounded_h______Bounded_i______Bounded_j______Bounded_k_____Bounded___________a___b____c____d____e____f____g____h____i____j____k____164__
  : (forall `{(Bounded a)}
            `{(Bounded b)}
            `{(Bounded c)}
            `{(Bounded d)}
            `{(Bounded e)}
            `{(Bounded f)}
            `{(Bounded g)}
            `{(Bounded h)}
            `{(Bounded i)}
            `{(Bounded j)}
            `{(Bounded k)},
      (Bounded ((((((((((a * b) * c) * d) * e) * f) * g) * h) * i) * j) * k))) := {
  minBound := (pair (pair (pair (pair (pair (pair (pair (pair (pair (pair minBound
                                                                          minBound) minBound) minBound) minBound)
                                                  minBound) minBound) minBound) minBound) minBound) minBound) ;
  maxBound := (pair (pair (pair (pair (pair (pair (pair (pair (pair (pair maxBound
                                                                          maxBound) maxBound) maxBound) maxBound)
                                                  maxBound) maxBound) maxBound) maxBound) maxBound) maxBound) }.

Instance instance__forall____Bounded_a______Bounded_b______Bounded_c______Bounded_d______Bounded_e______Bounded_f______Bounded_g______Bounded_h______Bounded_i______Bounded_j______Bounded_k______Bounded_l_____Bounded____________a___b____c____d____e____f____g____h____i____j____k____l____165__
  : (forall `{(Bounded a)}
            `{(Bounded b)}
            `{(Bounded c)}
            `{(Bounded d)}
            `{(Bounded e)}
            `{(Bounded f)}
            `{(Bounded g)}
            `{(Bounded h)}
            `{(Bounded i)}
            `{(Bounded j)}
            `{(Bounded k)}
            `{(Bounded l)},
      (Bounded (((((((((((a * b) * c) * d) * e) * f) * g) * h) * i) * j) * k) *
               l))) := {
  minBound := (pair (pair (pair (pair (pair (pair (pair (pair (pair (pair (pair
                                                                          minBound minBound) minBound) minBound)
                                                              minBound) minBound) minBound) minBound) minBound)
                                minBound) minBound) minBound) ;
  maxBound := (pair (pair (pair (pair (pair (pair (pair (pair (pair (pair (pair
                                                                          maxBound maxBound) maxBound) maxBound)
                                                              maxBound) maxBound) maxBound) maxBound) maxBound)
                                maxBound) maxBound) maxBound) }.

Instance instance__forall____Bounded_a______Bounded_b______Bounded_c______Bounded_d______Bounded_e______Bounded_f______Bounded_g______Bounded_h______Bounded_i______Bounded_j______Bounded_k______Bounded_l______Bounded_m_____Bounded_____________a___b____c____d____e____f____g____h____i____j____k____l____m____166__
  : (forall `{(Bounded a)}
            `{(Bounded b)}
            `{(Bounded c)}
            `{(Bounded d)}
            `{(Bounded e)}
            `{(Bounded f)}
            `{(Bounded g)}
            `{(Bounded h)}
            `{(Bounded i)}
            `{(Bounded j)}
            `{(Bounded k)}
            `{(Bounded l)}
            `{(Bounded m)},
      (Bounded ((((((((((((a * b) * c) * d) * e) * f) * g) * h) * i) * j) * k) * l) *
               m))) := {
  minBound := (pair (pair (pair (pair (pair (pair (pair (pair (pair (pair (pair
                                                                          (pair minBound minBound) minBound) minBound)
                                                                    minBound) minBound) minBound) minBound) minBound)
                                      minBound) minBound) minBound) minBound) ;
  maxBound := (pair (pair (pair (pair (pair (pair (pair (pair (pair (pair (pair
                                                                          (pair maxBound maxBound) maxBound) maxBound)
                                                                    maxBound) maxBound) maxBound) maxBound) maxBound)
                                      maxBound) maxBound) maxBound) maxBound) }.

Instance instance__forall____Bounded_a______Bounded_b______Bounded_c______Bounded_d______Bounded_e______Bounded_f______Bounded_g______Bounded_h______Bounded_i______Bounded_j______Bounded_k______Bounded_l______Bounded_m______Bounded_n_____Bounded______________a___b____c____d____e____f____g____h____i____j____k____l____m____n____167__
  : (forall `{(Bounded a)}
            `{(Bounded b)}
            `{(Bounded c)}
            `{(Bounded d)}
            `{(Bounded e)}
            `{(Bounded f)}
            `{(Bounded g)}
            `{(Bounded h)}
            `{(Bounded i)}
            `{(Bounded j)}
            `{(Bounded k)}
            `{(Bounded l)}
            `{(Bounded m)}
            `{(Bounded n)},
      (Bounded (((((((((((((a * b) * c) * d) * e) * f) * g) * h) * i) * j) * k) * l) *
               m) * n))) := {
  minBound := (pair (pair (pair (pair (pair (pair (pair (pair (pair (pair (pair
                                                                          (pair (pair minBound minBound) minBound)
                                                                          minBound) minBound) minBound) minBound)
                                                        minBound) minBound) minBound) minBound) minBound) minBound)
                    minBound) ;
  maxBound := (pair (pair (pair (pair (pair (pair (pair (pair (pair (pair (pair
                                                                          (pair (pair maxBound maxBound) maxBound)
                                                                          maxBound) maxBound) maxBound) maxBound)
                                                        maxBound) maxBound) maxBound) maxBound) maxBound) maxBound)
                    maxBound) }.

Instance instance__forall____Bounded_a______Bounded_b______Bounded_c______Bounded_d______Bounded_e______Bounded_f______Bounded_g______Bounded_h______Bounded_i______Bounded_j______Bounded_k______Bounded_l______Bounded_m______Bounded_n______Bounded_o_____Bounded_______________a___b____c____d____e____f____g____h____i____j____k____l____m____n____o____168__
  : (forall `{(Bounded a)}
            `{(Bounded b)}
            `{(Bounded c)}
            `{(Bounded d)}
            `{(Bounded e)}
            `{(Bounded f)}
            `{(Bounded g)}
            `{(Bounded h)}
            `{(Bounded i)}
            `{(Bounded j)}
            `{(Bounded k)}
            `{(Bounded l)}
            `{(Bounded m)}
            `{(Bounded n)}
            `{(Bounded o)},
      (Bounded ((((((((((((((a * b) * c) * d) * e) * f) * g) * h) * i) * j) * k) * l)
               * m) * n) * o))) := {
  minBound := (pair (pair (pair (pair (pair (pair (pair (pair (pair (pair (pair
                                                                          (pair (pair (pair minBound minBound) minBound)
                                                                                minBound) minBound) minBound) minBound)
                                                              minBound) minBound) minBound) minBound) minBound)
                                minBound) minBound) minBound) ;
  maxBound := (pair (pair (pair (pair (pair (pair (pair (pair (pair (pair (pair
                                                                          (pair (pair (pair maxBound maxBound) maxBound)
                                                                                maxBound) maxBound) maxBound) maxBound)
                                                              maxBound) maxBound) maxBound) maxBound) maxBound)
                                maxBound) maxBound) maxBound) }.
Definition minInt := Z.opp (Z.pow 2%Z 32%Z).
Definition maxInt := Z.pow 2%Z 32%Z.
Instance instance__Bounded_Int__183__ : (Bounded Int) := {
  minBound := minInt ;
  maxBound := maxInt }.

Lemma eftInt_aux_pf (y x : Int) :
  (x <= y)%Z ->
  x <> y ->
  (x+1 <= y)%Z.
Proof. unfold Int in *; omega. Qed.

(* Manually copying `GHC.Enum.eftInt`'s local function `go` *)
Program Fixpoint eftInt_aux (y x : Int) (pf : (x <= y)%Z) {measure (Z.to_nat (y - x))} : list Int :=
  x :: match Z.eq_dec x y with
       | left  _   => nil
       | right neq => eftInt_aux (eftInt_aux_pf pf neq)
       end%Z.
Next Obligation. apply Z2Nat.inj_lt; omega. Defined.
Arguments eftInt_aux _ _ _ : clear implicits.

(* Manually copying `GHC.Enum.eftInt` *)
Definition eftInt (x0 y : Int) :=
  match Z_gt_dec x0 y with
  | left  _   => nil
  | right Ngt => eftInt_aux y x0 (Znot_gt_le x0 y Ngt)
  end.

Instance instance__Enum_Int__184__ : (Enum Int) := {
  succ := (fun arg_185__ =>
    (match arg_185__ with
      | x => (if (x == maxBound)
             then GHC.Err.default
             else (x + #1))
    end)) ;
  pred := (fun arg_186__ =>
    (match arg_186__ with
      | x => (if (x == minBound)
             then GHC.Err.default
             else (x - #1))
    end)) ;
  toEnum := (fun arg_187__ => (match arg_187__ with | x => x end)) ;
  fromEnum := (fun arg_188__ => (match arg_188__ with | x => x end)) ;
  enumFrom := (fun x => eftInt x maxInt) ;
  enumFromTo := eftInt ;
}.


Definition boundedEnumFrom {a} `{(Bounded a)}
  (fromEnum : a -> Int)
  (toEnum   : Int -> a)
: (a -> (list a)) :=
  (fun arg_9__ =>
    (match arg_9__ with
      | n => ((map toEnum) (enumFromTo (fromEnum n) (fromEnum ((asTypeOf maxBound
                                                                         n)))))
    end)).

Instance instance__Bounded_bool__169__ : (Bounded bool) := {
  minBound := false ;
  maxBound := true }.

Definition toEnumBool : Int -> bool :=  (fun arg_173__ =>
    (match arg_173__ with
      | n => (if (n == #0)
             then false
             else true)
    end)).
Definition fromEnumBool : bool -> Int :=
(fun arg_174__ =>
    (match arg_174__ with
      | false => #0
      | true => #1
    end)).
Instance instance__Enum_bool__170__ : (Enum bool) := {
  succ := (fun arg_171__ =>
    (match arg_171__ with
      | false => true
      | true => true
    end)) ;
  pred := (fun arg_172__ =>
    (match arg_172__ with
      | true => false
      | false => false
    end)) ;
  toEnum := toEnumBool ;
  fromEnum := fromEnumBool ;
  enumFrom := boundedEnumFrom fromEnumBool toEnumBool;
  enumFromTo := (fix enumFromTo arg_4__ arg_5__ :=
                   (match arg_4__ , arg_5__ with
                    | x , y => ((map toEnumBool) (eftInt (fromEnumBool x) (fromEnumBool y)))
                    end))
}.

Instance instance__Bounded_comparison__175__ : (Bounded comparison) := {
  minBound := Lt ;
  maxBound := Gt }.

Definition fromEnum_comparison : comparison -> Int:=
 (fun arg_180__ =>
    (match arg_180__ with
      | Lt => #0
      | Eq => #1
      | Gt => #2
    end)).
Definition toEnum_comparison : Int -> comparison :=
  fun n =>
    (if (n == #0)
     then Lt
     else (if (n == #1)
           then Eq
           else (if (n == #2)
                 then Gt
                 else Gt
    ))).

Instance instance__Enum_comparison__176__ : (Enum comparison) := {
  succ := (fun arg_177__ =>
    (match arg_177__ with
      | Lt => Eq
      | Eq => Gt
      | Gt => Gt
    end)) ;
  pred := (fun arg_178__ =>
    (match arg_178__ with
      | Gt => Eq
      | Eq => Lt
      | Lt => Lt
    end)) ;
  toEnum := toEnum_comparison ;
  fromEnum := fromEnum_comparison ;
  enumFrom := boundedEnumFrom fromEnum_comparison toEnum_comparison;
enumFromTo := (fix enumFromTo_comparison arg_4__ arg_5__ :=
                 (match arg_4__ , arg_5__ with
                  | x , y => ((map toEnum_comparison)
                               (enumFromTo (fromEnum_comparison x)
                                           (fromEnum_comparison y)))
                  end))
 }.


Instance instance__Bounded_Char__181__ : (Bounded Char) := {
  minBound := 0%N;
  maxBound := &#"255" ;
}.

Definition toEnumChar (i : Integer) : Char :=
  if (Nless maxBound (Z.to_N i)) then maxBound
  else if Nless (Z.to_N i) minBound then minBound
       else Z.to_N i.

Definition fromEnumChar (c : Char) : Integer :=
  Z.of_N c.

Instance instance__Enum_N : (Enum N) := {
  succ := N.succ ;
  pred := fun x => if N.eqb x 0%N then GHC.Err.default else N.pred x;
  toEnum := Z.to_N ;
  fromEnum := Z.of_N ;
  enumFrom := fun _ => nil; (* we do not support infinite lists *)
  enumFromTo := fun x y => map N.of_nat (seq (N.to_nat x) (N.to_nat y));
}.
