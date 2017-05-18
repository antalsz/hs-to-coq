(* Preamble *)
Definition Synonym {A : Type} (_uniq : Type) (x : A) : A := x.
Arguments Synonym {A}%type _uniq%type x%type.

Require Import ZArith.

Axiom Int      : Type.
Axiom Rational : Type.


(* List notation *)
Require Import Coq.Lists.List.

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

(********************************************************************)

Axiom error : forall {A : Type}, String -> A.

(********************************************************************)

(* I've been assured that this is OK *)
Inductive IO (a : Type) : Type :=.
Inductive IORef (a : Type) : Type :=.

Axiom primIntToChar      : Int -> Char.
Axiom primCharToInt      : Char -> Int.
Axiom primUnicodeMaxChar : Char.

Axiom primWriteFile : String -> String -> IO unit.
Axiom primUserError : forall {A}, A.
(*
Definition primError          := error.

Definition primIOError        := error.
Definition primUserError      := error.
Definition primCatch          := error.
Definition primPutChar        := error.
Definition primGetChar        := error.
Definition primGetContents    := error.
*)

(*
     !! * ++ :: Char EQ GT IO Int LT None Rational Some String Z _(,)_ _(,,)_ _::_
     _Char.isSpace_ bool error list mandatory nil option optional pair primAppendFile
     primCatch primCharToInt primGetChar primGetContents primIOError primIntToChar
     primPutChar primReadFile primUnicodeMaxChar primUserError primWriteFile readDec
     readFloat readSigned showFloat showInt showLitChar showSigned tt unit xs xs'
*)
