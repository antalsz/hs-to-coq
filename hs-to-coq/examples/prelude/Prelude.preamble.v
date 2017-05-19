Definition Synonym {A : Type} (_uniq : Type) (x : A) : A := x.
Arguments Synonym {A}%type _uniq%type x%type.

(*********** numbers ********************************)

Axiom Int : Type.
Axiom lte_Int : Int -> Int -> bool.

(* Integers *)
Require Import ZArith.
Definition Integer  := Z.

(* Rational numbers *)
Require QArith.
Module Q := Coq.QArith.QArith_base.
Definition Rational := Q.Q.


Class Num a := {
  __op_zp__   : a -> a -> a ;
  __op_zm__   : a -> a -> a ;
  __op_zt__   : a -> a -> a ;
  abs         : a -> a ;
  fromInteger : Z -> a ;
  negate      : a -> a ;
  signum      : a -> a
}.

Infix    "+"     := __op_zp__ (at level 50, left associativity).
Notation "'_+_'" := __op_zp__.

Infix    "-"     := __op_zm__ (at level 50, left associativity).
Notation "'_-_'" := __op_zm__.

Infix    "*"     := __op_zt__ (at level 40, left associativity).
Notation "'_*_'" := __op_zt__.

Notation "'#' n" := (fromInteger n) (at level 1, format "'#' n").

Instance __Num_Int__ : Num Int. Admitted.
Instance __Num_Z__ : Num Integer. Admitted.
Instance __Num_Q__ : Num Rational. Admitted.



(* List notation *)
Require Import Coq.Lists.List.


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

(* SSreflect library *)
Require Import mathcomp.ssreflect.ssreflect.

(*********************************************************************)

Notation "'_(,)_'" := (fun x y => (x,y)).
Notation "'_(,,)_'" := (fun x y z => (x, y, z)).

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


Notation "'_++_'" := (fun x y => x ++ y).
Notation "'_::_'" := (fun x y => x :: y).

(********************************************************************)

Axiom error : forall {A : Type}, String -> A.

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
Axiom primUserError : forall {A}, A.
Axiom primIOError   : forall {A}, A.
Axiom primGetContents : IO String.
Axiom primGetChar     : IO Char.
Axiom primCatch       : forall {a}, IO a -> (IOError -> IO a) -> IO a.
Axiom primAppendFile  : FilePath -> String -> IO unit.

Class Monad m := {
  op_zgzg__ : (forall {a} {b}, ((m a) -> ((m b) -> (m b)))) ;
  op_zgzgze__ : (forall {a} {b}, ((m a) -> (((a -> (m b))) -> (m b)))) ;
  fail : (forall {a}, (String -> (m a))) ;
  return_ : (forall {a}, (a -> (m a))) }.

Infix ">>" := (op_zgzg__) (left associativity, at level 86).

Notation "'_>>_'" := (op_zgzg__).

Infix ">>=" := (op_zgzgze__) (left associativity, at level 86).

Notation "'_>>=_'" := (op_zgzgze__).

Instance Monad__IO__ : Monad IO. Admitted.

(****************************************************************)

Axiom showSigned : Z -> String.

(*
     !! * ++ :: Char EQ GT IO Int LT None Rational Some String Z _(,)_ _(,,)_ _::_
     _Char.isSpace_ bool error list mandatory nil option optional pair primAppendFile
     primCatch primCharToInt primGetChar primGetContents primIOError primIntToChar
     primPutChar primReadFile primUnicodeMaxChar primUserError primWriteFile readDec
     readFloat readSigned showFloat showInt showLitChar showSigned tt unit xs xs'
*)

Generalizable All Variables.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
