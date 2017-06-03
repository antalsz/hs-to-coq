Require Export Coq.Lists.List.

Notation "'_(,)_'" := (fun x y => (x,y)).
Notation "'_(,,)_'" := (fun x y z => (x, y, z)).
Notation "'_++_'" := (fun x y => x ++ y).
Notation "'_::_'" := (fun x y => x :: y).

(* Integers *)
Require Export ZArith.
Definition Integer  := Z.

(* Rational numbers *)
Require QArith.
Module Q := Coq.QArith.QArith_base.
Definition Rational := Q.Q.

(* SSreflect library *)
Require Export mathcomp.ssreflect.ssreflect.

(****************************************************)

Definition Synonym {A : Type} (_uniq : Type) (x : A) : A := x.
Arguments Synonym {A}%type _uniq%type x%type.

(****************************************************)

Axiom primUserError : forall {A}, A.
Axiom primIOError   : forall {A}, A.

(*********** built in classes ***********************)

Class Eq a := {
  op_zsze__ : (a -> (a -> bool)) ;
  op_zeze__ : (a -> (a -> bool)) }.

Infix "/=" := (op_zsze__) (no associativity, at level 70).

Notation "'_/=_'" := (op_zsze__).

Infix "==" := (op_zeze__) (no associativity, at level 70).

Notation "'_==_'" := (op_zeze__).

Inductive Ordering :=
| LT : Ordering
| EQ : Ordering
| GT : Ordering.


Class Ord a `{((Eq a))} := {
  op_zl__ : (a -> (a -> bool)) ;
  op_zlze__ : (a -> (a -> bool)) ;
  op_zg__ : (a -> (a -> bool)) ;
  op_zgze__ : (a -> (a -> bool)) ;
  compare : (a -> (a -> Ordering)) ;
  max : (a -> (a -> a)) ;
  min : (a -> (a -> a)) }.

Infix "<" := (op_zl__) (no associativity, at level 70).

Notation "'_<_'" := (op_zl__).

Infix "<=" := (op_zlze__) (no associativity, at level 70).

Notation "'_<=_'" := (op_zlze__).

Infix ">" := (op_zg__) (no associativity, at level 70).

Notation "'_>_'" := (op_zg__).

Infix ">=" := (op_zgze__) (no associativity, at level 70).

Notation "'_>=_'" := (op_zgze__).


(*********** numbers ********************************)

(* Just make this Z??? *)
Axiom Int : Type.
Axiom lte_Int : Int -> Int -> bool.


Class Num a := {
  op_zp__   : a -> a -> a ;
  op_zm__   : a -> a -> a ;
  op_zt__   : a -> a -> a ;
  abs         : a -> a ;
  fromInteger : Z -> a ;
  negate      : a -> a ;
  signum      : a -> a
}.

Infix    "+"     := op_zp__ (at level 50, left associativity).
Notation "'_+_'" := op_zp__.

Infix    "-"     := op_zm__ (at level 50, left associativity).
Notation "'_-_'" := op_zm__.

Infix    "*"     := op_zt__ (at level 40, left associativity).
Notation "'_*_'" := op_zt__.

Notation "'#' n" := (fromInteger n) (at level 1, format "'#' n").

Instance Num_Int__ : Num Int. Admitted.

Instance Num_Z__ : Num Integer := {
  op_zp__   := Z.add %Z;
  op_zm__   := Z.sub %Z;
  op_zt__   := Z.mul %Z;
  abs         := Z.abs %Z;
  fromInteger := fun x => x;
  negate      := Z.opp %Z;
  signum      := Z.sgn %Z; }.

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


(* ********************************************************* *)
(* Some Haskell functions we cannot translate                *)


(* Pattern guards, ugh. *)
Fixpoint take {a:Type} (n:Int) (xs:list a) : list a :=
  match xs with
  | nil => nil
  | y :: ys => if lte_Int n #0 then nil else (y :: take (n - #1) ys)
  end.

Fixpoint drop {a:Type} (n:Int) (xs:list a) : list a :=
  match xs with
  | nil => nil
  | y :: ys => if lte_Int n #0 then (y :: ys) else drop (n - #1) ys
  end.

(* The inner nil case is impossible. So it is left out of the Haskell version. *)
Fixpoint scanr {a b:Type} (f : a -> b -> b) (q0 : b) (xs : list a) : list b :=
  match xs with
  | nil => q0 :: nil
  | y :: ys => match scanr f q0 ys with
              | q :: qs =>  f y q :: (q :: qs)
              | nil => nil
              end
end.

(* The inner nil case is impossible. So it is left out of the Haskell version. *)
Fixpoint scanr1 {a :Type} (f : a -> a -> a) (q0 : a) (xs : list a) : list a :=
  match xs with
  | nil => q0 :: nil
  | y :: nil => y :: nil
  | y :: ys => match scanr1 f q0 ys with
              | q :: qs =>  f y q :: (q :: qs)
              | nil => nil
              end
end.

(*
foldl k z0 xs =
  foldr (\(v::a) (fn::b->b) -> oneShot (\(z::b) -> fn (k z v))) (id :: b -> b) xs z0
*)

Fixpoint foldr {a}{b} (f: a -> b -> b) (z:b) (xs: list a) : b :=
  match xs with
  | nil => z
  | y :: ys => f y (foldr f z ys)
  end.

Definition foldl {a}{b} k z0 xs :=
  foldr (fun (v:a) (fn:b->b) => (fun (z:b) => fn (k z v))) (id : b -> b) xs z0.

Definition foldl' {a}{b} k z0 xs :=
  foldr (fun(v:a) (fn:b->b) => (fun(z:b) => fn (k z v))) (id : b -> b) xs z0.

(********************************************************************)

(* Characters and Strings *)

Axiom Char     : Type.
Definition String := list Char.

Require Coq.Strings.String.
Require Coq.Strings.Ascii.

Bind Scope string_scope with String.string.
Bind Scope char_scope   with Ascii.ascii.

Axiom hs_char__ : Ascii.ascii -> Char.
Notation "'&#' c" := (hs_char__ c) (at level 1, format "'&#' c").

Fixpoint hs_string__ (s : String.string) : String :=
  match s with
  | String.EmptyString => nil
  | String.String c s  => &#c :: hs_string__ s
  end.
Notation "'&' s" := (hs_string__ s) (at level 1, format "'&' s").

(********************************************************************)

Axiom error : forall {A : Type}, String -> A.
Axiom errorWithoutStackTrace : forall {A : Type}, String -> A.

(********************************************************************)

(* I've been assured that this is OK *)
Inductive IO (a : Type) : Type :=.
Inductive IORef (a : Type) : Type :=.
Inductive IOError : Type :=.

Definition FilePath := String.

Axiom primIntToChar      : Int -> Char.
Axiom primCharToInt      : Char -> Int.
Axiom primUnicodeMaxChar : Char.

Axiom primPutChar   : Char -> IO unit.
Axiom primReadFile  : String -> IO String.
Axiom primWriteFile : String -> String -> IO unit.
Axiom primGetContents : IO String.
Axiom primGetChar     : IO Char.
Axiom primCatch       : forall {a}, IO a -> (IOError -> IO a) -> IO a.
Axiom primAppendFile  : FilePath -> String -> IO unit.


Definition oneShot {a} (x:a) := x.