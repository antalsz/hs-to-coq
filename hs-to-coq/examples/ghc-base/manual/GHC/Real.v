(* Preamble *)
Require Import GHC.Base.
Require Import GHC.Num.
Require Import GHC.List.
Require Import GHC.Enum.

Generalizable All Variables.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* This file is very different from the standard library so that it
   can take advantage of Coq's existing formalization of
   rational numbers. *)

(* Rational numbers *)

Require Import ZArith.
Require Import QArith.
Module Q := Coq.QArith.QArith_base.
Definition Rational := Q.Q.

Definition Qabs (q : Rational) : Rational :=
  match ((Q.Qnum q) ?= 0)%Z with
    | Lt => Q.Qinv q
    | _ => q
  end.

Definition Qsignum (q : Rational) : Rational :=
  Q.Qmake (Z.sgn (Q.Qnum q)) (Q.Qden q).

Instance Num_Q__ : Num Rational := {
  op_zp__   := Q.Qplus;
  op_zm__   := Q.Qminus;
  op_zt__   := Q.Qmult;
  abs         := Qabs;
  fromInteger := fun x => Q.Qmake x 1;
  negate      := Q.Qinv;
  signum      := Qsignum; }.

Instance Num_positive__ : Num positive := {}.
Admitted.

Definition numerator := Q.Qnum.
Definition denominator := Q.Qden.


Class Real a `{(Num a)} `{(Ord a)} := {
  toRational : (a -> Rational) }.

Class Integral a `{(Real a)} `{(Enum a)} := {
  div : (a -> (a -> a)) ;
  divMod : (a -> (a -> (a * a))) ;
  mod_ : (a -> (a -> a)) ;
  quot : (a -> (a -> a)) ;
  quotRem : (a -> (a -> (a * a))) ;
  rem : (a -> (a -> a)) ;
  toInteger : (a -> Z) }.

Class Fractional a `{((Num a))} := {
  op_zs__ : (a -> (a -> a)) ;
  fromRational : (Rational -> a) ;
  recip : (a -> a) }.

Infix "/" := (op_zs__) (left associativity, at level 40).

Notation "'_/_'" := (op_zs__).

Class RealFrac a `{(Real a)} `{(Fractional a)} := {
  ceiling : (forall {b}, (forall `{((Integral b))}, (a -> b))) ;
  floor : (forall {b}, (forall `{((Integral b))}, (a -> b))) ;
  properFraction : (forall {b}, (forall `{((Integral b))}, (a -> (b * a)))) ;
  round : (forall {b}, (forall `{((Integral b))}, (a -> b))) ;
  truncate : (forall {b}, (forall `{((Integral b))}, (a -> b))) }.

Definition realToFrac {a} {b} `{(Real a)} `{(Fractional b)} : (a -> b) :=
  (fromRational ∘ toRational).

Definition ratioPrec : Int := #7.

Definition ratioPrec1 : Int := (ratioPrec + #1)%Z.

Definition fromIntegral {a} {b} `{(Integral a)} `{(Num b)} : (a -> b) :=
  (fromInteger ∘ toInteger).

Instance instance__Real_Int__72__ : (Real Int) := {
  toRational := (fun x => Q.Qmake x #1)
}.

Definition quotRemZ : Z -> Z -> (Z * Z).
Admitted.
Definition divModZ : (Z -> (Z -> (Z * Z))).
Admitted.

Instance instance__Integral_Int__74__ : (Integral Int) := {
  toInteger := id ;
  quot := Z.quot ;
  rem := Z.rem ;
  div := Z.rem ;
  mod_ := Z.modulo ;
  quotRem := quotRemZ ;
  divMod := divModZ }.


(*

Definition numericEnumFromThen {a} `{((Fractional a))} : (a -> (a -> (list
                                                         a))) := (fix numericEnumFromThen arg_28__ arg_29__
                                                                        := (match arg_28__ , arg_29__ with
                                                                             | n , m => (seq_nop (seq_nop n m) ((n ::
                                                                                             ((numericEnumFromThen m)
                                                                                             (((m + m) - n))))))
                                                                           end)).

Definition numericEnumFromThenTo {a} `{(Ord a)} `{(Fractional a)}
  : (a -> (a -> (a -> (list a)))) := (fun arg_35__
                                          arg_36__
                                          arg_37__ =>
                                       (match arg_35__ , arg_36__ , arg_37__ with
                                         | e1 , e2 , e3 => (let mid := (((e2 - e1)) / #2)
                                                           in (let predicate :=
                                                                (if (e2 >= e1)
                                                                then ((fun arg_33__ => (arg_33__ <= (e3 + mid))))
                                                                else ((fun arg_34__ => (arg_34__ >= (e3 + mid)))))
                                                              in ((takeWhile predicate) (((numericEnumFromThen e1)
                                                                                        e2)))))
                                       end)).

Definition numericEnumFrom {a} `{((Fractional a))} : (a -> (list a)) :=
  (fix numericEnumFrom arg_27__ := (match arg_27__ with
                                     | n => (seq n ((n :: (numericEnumFrom ((n + #1))))))
                                   end)).

Definition numericEnumFromTo {a} `{(Ord a)} `{(Fractional a)}
  : (a -> (a -> (list a))) := (fun arg_31__
                                   arg_32__ =>
                                (match arg_31__ , arg_32__ with
                                  | n , m => ((takeWhile ((fun arg_30__ => (arg_30__ <= ((m + #1) / #2)))))
                                             ((numericEnumFrom n)))
                                end)).
*)

(*
Definition numerator {a} : ((Ratio a) -> a) := (fun arg_25__ =>
                                                 (match arg_25__ with
                                                   | (x Mk_Ratio _) => x
                                                 end)).
*)



(*
Definition notANumber : Rational := (Q.Qmake #0 #0).
Definition infinity : Rational := (Q.Qmake #1 #0).

Definition integralEnumFromTo {a} `{(Integral a)} : (a -> (a -> (list a))) :=
  (fun arg_67__
       arg_68__ =>
    (match arg_67__ , arg_68__ with
      | n , m => ((map fromInteger) (enumFromTo (toInteger n) (toInteger m)))
    end)).

Definition integralEnumFromThenTo {a} `{(Integral a)} : (a -> (a -> (a -> (list
                                                        a)))) := (fun arg_69__
                                                                      arg_70__
                                                                      arg_71__ =>
                                                                   (match arg_69__ , arg_70__ , arg_71__ with
                                                                     | n1 , n2 , m => ((map fromInteger) (enumFromThenTo
                                                                                                         (toInteger n1)
                                                                                                         (toInteger n2)
                                                                                                         (toInteger m)))
                                                                   end)).

Definition integralEnumFromThen {a} `{(Integral a)} `{(Bounded a)}
  : (a -> (a -> (list a))) := (fun arg_65__
                                   arg_66__ =>
                                (match arg_65__ , arg_66__ with
                                  | n1 , n2 => (let i_n1 := (toInteger n1)
                                               in (let i_n2 := (toInteger n2)
                                                  in (if (i_n2 >= i_n1)
                                                     then ((map fromInteger) (enumFromThenTo i_n1 i_n2 (toInteger
                                                                                             ((asTypeOf maxBound n1)))))
                                                     else ((map fromInteger) (enumFromThenTo i_n1 i_n2 (toInteger
                                                                                             ((asTypeOf minBound
                                                                                                        n1))))))))
                                end)).

Definition integralEnumFrom {a} `{(Integral a)} `{(Bounded a)} : (a -> (list
                                                                 a)) := (fun arg_64__ =>
                                                                          (match arg_64__ with
                                                                            | n => ((map fromInteger) (enumFromTo
                                                                                                      (toInteger n)
                                                                                                      (toInteger
                                                                                                      ((asTypeOf
                                                                                                      maxBound n)))))
                                                                          end)).



(*
Definition gcd {a} `{((Integral a))} : (a -> (a -> a)) := (fun arg_58__
                                                               arg_59__ =>
                                                            (match arg_58__ , arg_59__ with
                                                              | x , y => (let gcd' :=
                                                                           (fix gcd' arg_56__ arg_57__
                                                                                  := (match arg_56__ , arg_57__ with
                                                                                       | a , num_55__ => (if (num_55__
                                                                                                             == #0)
                                                                                                         then a
                                                                                                         else _(*MissingValue*))
                                                                                       | a , b => ((gcd' b) ((rem a b)))
                                                                                     end))
                                                                         in ((gcd' ((abs x))) ((abs y))))
                                                            end)).

Definition lcm {a} `{((Integral a))} : (a -> (a -> a)) := (fun arg_62__
                                                               arg_63__ =>
                                                            (match arg_62__ , arg_63__ with
                                                              | _ , num_60__ => (if (num_60__ == #0)
                                                                                then #0
                                                                                else _(*MissingValue*))
                                                              | num_61__ , _ => (if (num_61__ == #0)
                                                                                then #0
                                                                                else _(*MissingValue*))
                                                              | x , y => (abs ((((quot x (((gcd x) y)))) * y)))
                                                            end)).
*)

(*
Definition reduce {a} `{((Integral a))} : (a -> (a -> (Ratio a))) :=
  (fun arg_21__
       arg_22__ =>
    (match arg_21__ , arg_22__ with
      | _ , num_20__ => (if (num_20__ == #0)
                        then ratioZeroDenominatorError
                        else _(*MissingValue*))
      | x , y => (let d := ((gcd x) y)
                 in (Mk_Ratio ((quot x d)) ((quot y d))))
    end)).
*)
(*
Definition op_zv__ {a} `{((Integral a))} : (a -> (a -> (Ratio a))) :=
  (fun arg_23__
       arg_24__ =>
    (match arg_23__ , arg_24__ with
      | x , y => ((reduce ((x * (signum y)))) ((abs y)))
    end)).


Infix "%" := (op_zv__) (left associativity, at level 40).

Notation "'_%_'" := (op_zv__).
*)


Definition even {a} `{((Integral a))} : (a -> bool) := (fun arg_41__ =>
                                                         (match arg_41__ with
                                                           | n => ((rem n #2) == #0)
                                                         end)).

Definition odd {a} `{((Integral a))} : (a -> bool) := (negb ∘ even).

Definition op_zc__ {a} {b} `{(Num a)} `{(Integral b)} : (a -> (b -> a)) :=
  (fun arg_47__
       arg_48__ =>
    (match arg_47__ , arg_48__ with
      | x0 , y0 => (let f :=
                     (fix f arg_42__ arg_43__ := (match arg_42__ , arg_43__ with
                                                   | x , y => (if (even y)
                                                              then ((f ((x * x))) ((quot y #2)))
                                                              else (if (y == #1)
                                                                   then x
                                                                   else (((g ((x * x))) ((quot ((y - #1)) #2))) x)))
                                                 end))
                   in (let g :=
                        (fix g arg_44__ arg_45__ arg_46__ := (match arg_44__ , arg_45__ , arg_46__ with
                                                               | x , y , z => (if (even y)
                                                                              then (((g ((x * x))) ((quot y #2))) z)
                                                                              else (if (y == #1)
                                                                                   then (x * z)
                                                                                   else (((g ((x * x))) ((quot ((y -
                                                                                                               #1))
                                                                                                               #2))) ((x
                                                                                                                     *
                                                                                                                     z)))))
                                                             end))
                      in (if (y0 < #0)
                         then (errorWithoutStackTrace &"Negative exponent")
                         else (if (y0 == #0)
                              then #1
                              else ((f x0) y0)))))
    end)).

Infix "^" := (op_zc__) (right associativity, at level 30).

Notation "'_^_'" := (op_zc__).

Definition op_zczc__ {a} {b} `{(Fractional a)} `{(Integral b)}
  : (a -> (b -> a)) := (fun arg_49__
                            arg_50__ =>
                         (match arg_49__ , arg_50__ with
                           | x , n => (if (n >= #0)
                                      then (x ^ n)
                                      else (recip ((x ^ ((negate n))))))
                         end)).

Infix "^^" := (op_zczc__) (right associativity, at level 30).

Notation "'_^^_'" := (op_zczc__).

Definition op_zczvzc__ {a} `{(Integral a)} : (Rational -> (a -> Rational)) :=
  (fun arg_51__
       arg_52__ =>
    (match arg_51__ , arg_52__ with
      | (n Mk_Ratio d) , e => (if (e < #0)
                              then (errorWithoutStackTrace &"Negative exponent")
                              else (if (e == #0)
                                   then (Mk_Ratio #1 #1)
                                   else (Mk_Ratio ((n ^ e)) ((d ^ e)))))
    end)).

Infix "^%^" := (op_zczvzc__) (at level 99).

Notation "'_^%^_'" := (op_zczvzc__).

Definition op_zczczvzczc__ {a} `{(Integral a)}
  : (Rational -> (a -> Rational)) := (fun arg_53__
                                          arg_54__ =>
                                       (match arg_53__ , arg_54__ with
                                         | (n Mk_Ratio d) , e => (if (e > #0)
                                                                 then (Mk_Ratio ((n ^ e)) ((d ^ e)))
                                                                 else (if (e == #0)
                                                                      then (Mk_Ratio #1 #1)
                                                                      else (if (n > #0)
                                                                           then (Mk_Ratio ((d ^ ((negate e)))) ((n ^
                                                                                          ((negate e)))))
                                                                           else (if (n == #0)
                                                                                then ratioZeroDenominatorError
                                                                                else (let nn := (d ^ ((negate e)))
                                                                                     in (let dd :=
                                                                                          (((negate n)) ^ ((negate e)))
                                                                                        in (if (even e)
                                                                                           then ((Mk_Ratio nn dd))
                                                                                           else ((Mk_Ratio (negate nn)
                                                                                                           dd)))))))))
                                       end)).

Infix "^^%^^" := (op_zczczvzczc__) (at level 99).

Notation "'_^^%^^_'" := (op_zczczvzczc__).

Definition divZeroError {a} : a := (_raise#_ divZeroException).

Definition denominator {a} : ((Ratio a) -> a) := (fun arg_26__ =>
                                                   (match arg_26__ with
                                                     | (_ Mk_Ratio y) => y
                                                   end)).

(* Converted type class instance declarations: *)


Instance instance__Real_N__88__ : (Real N) := {
  toRational := (fun arg_89__ =>
    (match arg_89__ with
      | x => ((toInteger x) % #1)
    end)) }.

Instance instance__Integral_N__90__ : (Integral N) := {
  quot := (fun arg_91__
               arg_92__ =>
    (match arg_91__ , arg_92__ with
      | (W# x#) , ((W# y#) as y) => (if (y /= #0)
                                    then (_W#_ ((_x#_ quotWord# _y#_)))
                                    else divZeroError)
    end)) ;
  rem := (fun arg_93__
              arg_94__ =>
    (match arg_93__ , arg_94__ with
      | (W# x#) , ((W# y#) as y) => (if (y /= #0)
                                    then (_W#_ ((_x#_ remWord# _y#_)))
                                    else divZeroError)
    end)) ;
  div := (fun arg_95__
              arg_96__ =>
    (match arg_95__ , arg_96__ with
      | (W# x#) , ((W# y#) as y) => (if (y /= #0)
                                    then (_W#_ ((_x#_ quotWord# _y#_)))
                                    else divZeroError)
    end)) ;
  mod_ := (fun arg_97__
               arg_98__ =>
    (match arg_97__ , arg_98__ with
      | (W# x#) , ((W# y#) as y) => (if (y /= #0)
                                    then (_W#_ ((_x#_ remWord# _y#_)))
                                    else divZeroError)
    end)) ;
  quotRem := (fun arg_99__
                  arg_100__ =>
    (match arg_99__ , arg_100__ with
      | (W# x#) , ((W# y#) as y) => (if (y /= #0)
                                    then (match (_x#_ quotRemWord# _y#_) with
                                           | (pair q r) => (pair (_W#_ q) (_W#_ r))
                                         end)
                                    else divZeroError)
    end)) ;
  divMod := (fun arg_101__
                 arg_102__ =>
    (match arg_101__ , arg_102__ with
      | (W# x#) , ((W# y#) as y) => (if (y /= #0)
                                    then (pair (_W#_ ((_x#_ quotWord# _y#_))) (_W#_ ((_x#_ remWord# _y#_))))
                                    else divZeroError)
    end)) ;
  toInteger := (fun arg_103__ =>
    (match arg_103__ with
      | (W# x#) => (wordToInteger _x#_)
    end)) }.

Instance instance__Real_Z__104__ : (Real Z) := {
  toRational := (fun arg_105__ =>
    (match arg_105__ with
      | x => (Mk_Ratio x #1)
    end)) }.

Instance instance__Integral_Z__106__ : (Integral Z) := {
  toInteger := (fun arg_107__ => (match arg_107__ with | n => n end)) ;
  quot := (fun arg_109__
               arg_110__ =>
    (match arg_109__ , arg_110__ with
      | _ , num_108__ => (if (num_108__ == #0)
                         then divZeroError
                         else _(*MissingValue*))
      | n , d => (quotInteger n d)
    end)) ;
  rem := (fun arg_112__
              arg_113__ =>
    (match arg_112__ , arg_113__ with
      | _ , num_111__ => (if (num_111__ == #0)
                         then divZeroError
                         else _(*MissingValue*))
      | n , d => (remInteger n d)
    end)) ;
  div := (fun arg_115__
              arg_116__ =>
    (match arg_115__ , arg_116__ with
      | _ , num_114__ => (if (num_114__ == #0)
                         then divZeroError
                         else _(*MissingValue*))
      | n , d => (divInteger n d)
    end)) ;
  mod_ := (fun arg_118__
               arg_119__ =>
    (match arg_118__ , arg_119__ with
      | _ , num_117__ => (if (num_117__ == #0)
                         then divZeroError
                         else _(*MissingValue*))
      | n , d => (modInteger n d)
    end)) ;
  divMod := (fun arg_121__
                 arg_122__ =>
    (match arg_121__ , arg_122__ with
      | _ , num_120__ => (if (num_120__ == #0)
                         then divZeroError
                         else _(*MissingValue*))
      | n , d => (match (divModInteger n d) with
                   | (pair x y) => (pair x y)
                 end)
    end)) ;
  quotRem := (fun arg_124__
                  arg_125__ =>
    (match arg_124__ , arg_125__ with
      | _ , num_123__ => (if (num_123__ == #0)
                         then divZeroError
                         else _(*MissingValue*))
      | n , d => (match (quotRemInteger n d) with
                   | (pair q r) => (pair q r)
                 end)
    end)) }.

Instance instance__forall_____Integral_a______Ord___Ratio_a_____126__
  : (forall `{((Integral a))}, (Ord ((Ratio a)))) := {
  op_zlze__ := (fix op_zlze__ arg_127__ arg_128__ := (match arg_127__
                                                          , arg_128__ with
                                                       | (x Mk_Ratio y) , (x' Mk_Ratio y') => (((x * y') <= x') * y)
                                                     end)) ;
  op_zl__ := (fix op_zl__ arg_129__ arg_130__ := (match arg_129__ , arg_130__ with
                                                   | (x Mk_Ratio y) , (x' Mk_Ratio y') => (((x * y') < x') * y)
                                                 end)) }.

Instance instance__forall_____Integral_a______Num___Ratio_a_____131__
  : (forall `{((Integral a))}, (Num ((Ratio a)))) := {
  op_zp__ := (fix op_zp__ arg_132__ arg_133__ := (match arg_132__ , arg_133__ with
                                                   | (x Mk_Ratio y) , (x' Mk_Ratio y') => ((reduce ((((x * y') + x') *
                                                                                                   y))) ((y * y')))
                                                 end)) ;
  op_zm__ := (fix op_zm__ arg_134__ arg_135__ := (match arg_134__ , arg_135__ with
                                                   | (x Mk_Ratio y) , (x' Mk_Ratio y') => ((reduce ((((x * y') - x') *
                                                                                                   y))) ((y * y')))
                                                 end)) ;
  op_zt__ := (fix op_zt__ arg_136__ arg_137__ := (match arg_136__ , arg_137__ with
                                                   | (x Mk_Ratio y) , (x' Mk_Ratio y') => ((reduce ((x * x'))) ((y *
                                                                                                               y')))
                                                 end)) ;
  negate := (fix negate arg_138__ := (match arg_138__ with
                                       | (x Mk_Ratio y) => (Mk_Ratio ((negate x)) y)
                                     end)) ;
  abs := (fix abs arg_139__ := (match arg_139__ with
                                 | (x Mk_Ratio y) => (Mk_Ratio (abs x) y)
                               end)) ;
  signum := (fix signum arg_140__ := (match arg_140__ with
                                       | (x Mk_Ratio _) => (Mk_Ratio (signum x) #1)
                                     end)) ;
  fromInteger := (fix fromInteger arg_141__ := (match arg_141__ with
                                                 | x => (Mk_Ratio (fromInteger x) #1)
                                               end)) }.

Instance instance__forall_____Integral_a______Fractional___Ratio_a_____142__
  : (forall `{((Integral a))}, (Fractional ((Ratio a)))) := {
  op_zs__ := (fun arg_143__
                  arg_144__ =>
    (match arg_143__ , arg_144__ with
      | (x Mk_Ratio y) , (x' Mk_Ratio y') => (((x * y')) % ((y * x')))
    end)) ;
  recip := (fun arg_146__ =>
    (match arg_146__ with
      | (num_145__ Mk_Ratio _) => (if (num_145__ == #0)
                                  then ratioZeroDenominatorError
                                  else _(*MissingValue*))
      | (x Mk_Ratio y) => (if (x < #0)
                          then (Mk_Ratio (negate y) (negate x))
                          else (Mk_Ratio y x))
    end)) ;
  fromRational := (fun arg_147__ =>
    (match arg_147__ with
      | (x Mk_Ratio y) => ((fromInteger x) % (fromInteger y))
    end)) }.

Instance instance__forall_____Integral_a______Real___Ratio_a_____148__
  : (forall `{((Integral a))}, (Real ((Ratio a)))) := {
  toRational := (fun arg_149__ =>
    (match arg_149__ with
      | (x Mk_Ratio y) => (Mk_Ratio (toInteger x) (toInteger y))
    end)) }.

Instance instance__forall_____Integral_a______RealFrac___Ratio_a_____150__
  : (forall `{((Integral a))}, (RealFrac ((Ratio a)))) := {
  properFraction := (fun arg_151__ =>
    (match arg_151__ with
      | (x Mk_Ratio y) => (match ((quotRem x) y) with
                            | (pair q r) => (pair (fromInteger ((toInteger q))) (Mk_Ratio r y))
                          end)
    end)) ;
  ceiling := (fun arg_18__ =>
    (match arg_18__ with
      | x => (match (properFraction x) with
               | (pair n r) => (if (r > #0)
                               then (n + #1)
                               else n)
             end)
    end)) ;
  floor := (fun arg_19__ =>
    (match arg_19__ with
      | x => (match (properFraction x) with
               | (pair n r) => (if (r < #0)
                               then (n - #1)
                               else n)
             end)
    end)) ;
  round := (fun arg_17__ =>
    (match arg_17__ with
      | x => (match (properFraction x) with
               | (pair n r) => (let m := (if (r < #0) then (n - #1) else (n + #1))
                               in (match (signum (((abs r) - (fromRational (Q.Qmake 1 2))))) with
                                    | num_14__ => (if (num_14__ == #1)
                                                  then n
                                                  else _(*MissingValue*))
                                    | num_15__ => (if (num_15__ == #0)
                                                  then (if (even n)
                                                       then n
                                                       else m)
                                                  else _(*MissingValue*))
                                    | num_16__ => (if (num_16__ == #1)
                                                  then m
                                                  else _(*MissingValue*))
                                    | _ => (errorWithoutStackTrace &"round default defn: Bad value")
                                  end))
             end)
    end)) ;
  truncate := (fun arg_13__ =>
    (match arg_13__ with
      | x => (match (properFraction x) with
               | (pair m _) => m
             end)
    end)) }.

Instance instance__forall_____Show_a______Show___Ratio_a_____152__
  : (forall `{((Show a))}, (Show ((Ratio a)))) := {
  showsPrec := (fix showsPrec arg_153__ arg_154__ := (match arg_153__
                                                          , arg_154__ with
                                                       | p , (x Mk_Ratio y) => ((((showParen ((p > ratioPrec))) $
                                                                               ((showsPrec ratioPrec1) x)) ∘ (showString
                                                                               &" % ")) ∘ ((showsPrec ratioPrec1) y))
                                                     end)) }.

Instance instance__forall_____Integral_a______Enum___Ratio_a_____155__
  : (forall `{((Integral a))}, (Enum ((Ratio a)))) := {
  succ := (fun arg_156__ => (match arg_156__ with | x => (x + #1) end)) ;
  pred := (fun arg_157__ => (match arg_157__ with | x => (x - #1) end)) ;
  toEnum := (fun arg_158__ =>
    (match arg_158__ with
      | n => (Mk_Ratio (fromIntegral n) #1)
    end)) ;
  fromEnum := (fromInteger ∘ truncate) ;
  enumFrom := numericEnumFrom ;
  enumFromThen := numericEnumFromThen ;
  enumFromTo := numericEnumFromTo ;
  enumFromThenTo := numericEnumFromThenTo }.
*)

(* Unbound variables:
     $ * + - /= :: < <= == > >= Bounded Enum I# Int N Num Ord Q.Qmake Show ShowS W# Z
     _W#_ _raise#_ _x#_ _y#_ abs andb asTypeOf bool divInt divInteger divModInt
     divModInteger divZeroException enumFromThenTo enumFromTo errorWithoutStackTrace
     fromInteger g list map maxBound minBound modInt modInteger negate negb
     overflowException pair quotInt quotInteger quotRemInt quotRemInteger
     quotRemWord# quotWord# ratioZeroDenomException remInt remInteger remWord# seq
     showChar showParen showString signum smallInteger takeWhile wordToInteger ∘
*)
