Definition Synonym {A : Type} (_uniq : Type) (x : A) : A := x.
Arguments Synonym {A}%type _uniq%type x%type.

Require Import ZArith.

Axiom Char     : Type.
Axiom Int      : Type.
Axiom Rational : Type.

Definition String     := list Char.
Definition FilePath   := String.
Definition FastString := String.

(* Temporary *)
Record Array  k v := ListToArray  { arrayToList  : list (k * v) }.
Record Map    k v := ListToMap    { mapToList    : list (k * v) }.
Record IntMap   v := ListToIntMap { intMapToList : list (Int * v) }.

Axiom error : forall {A : Type}, String -> A.

(* I've been assured that this is OK *)
Inductive IORef (a : Type) : Type :=.

(* List notation *)
Require Import Coq.Lists.List.

(* Temporary – but will probably need to be handled specially *)
Axiom DynFlags : Type.

(* Temporary – this probably needs to map directly to a Coq type *)
Axiom ByteString : Type.

Generalizable All Variables.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(********************************************************************************)

(* Haskell Prelude stuff *)

Class Functor (f : Type -> Type) := {
  fmap : forall {a b}, (a -> b) -> f a -> f b;
  __op_zlzd__ : forall {a b}, a -> f b -> f a
}.

Infix "<$"        := __op_zlzd__ (at level 99).
Notation "'_<$_'" := __op_zlzd__.

Class Applicative (f : Type -> Type) `{Functor f} := {
  pure          : forall {a},   a -> f a;
  __op_zlztzg__ : forall {a b}, f (a -> b) -> f a -> f b;
  __op_ztzg__   : forall {a b}, f a -> f b -> f b;
  __op_zlzt__   : forall {a b}, f a -> f b -> f a
}.

Infix "<*>" := __op_zlztzg__ (at level 99).
Infix "*>"  := __op_ztzg__   (at level 99).
Infix "<*"  := __op_zlzt__   (at level 99).

Notation "'_<*>_'" := __op_zlztzg__.
Notation "'_*>_'"  := __op_ztzg__.
Notation "'_<*_'"  := __op_zlzt__.

Class Monad (m : Type -> Type) `{Applicative m} := {
  __op_zgzgze__ : forall {a b}, m a -> (a -> m b) -> m b;
  __op_zgzg__   : forall {a b}, m a -> m b -> m b;
  return_       : forall {a},   a -> m a;
  fail          : forall {a},   String -> m a
}.

Infix ">>=" := __op_zgzgze__ (at level 99).
Infix ">>"  := __op_zgzg__   (at level 99).

Notation "'_>>=_'" := __op_zgzgze__.
Notation "'_>>_'"  := __op_zgzg__.

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

(* Fancy notation *)

Notation "'#' n" := (fromInteger n) (at level 1, format "'#' n").

Require Coq.Strings.String.
Require Coq.Strings.Ascii.

Bind Scope string_scope with String.string.
Bind Scope char_scope   with Ascii.ascii.

Axiom __hs_char__ : Ascii.ascii -> Char.
Notation "'&#' c" := (__hs_char__ c) (at level 1, format "'&#' c").

Fixpoint __hs_string__ (s : String.string) : String :=
  match s with
  | String.EmptyString => nil
  | String.String c s  => &#c :: __hs_string__ s
  end.
Notation "'&' s" := (__hs_string__ s) (at level 1, format "'&' s").
