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

(* I've been assured that this is OK *)
Inductive IORef (a : Type) : Type :=.

(* Temporary – but will probably need to be handled specially *)
Axiom DynFlags : Type.

(* Temporary – this probably needs to map directly to a Coq type *)
Axiom ByteString : Type.

(* Temporary – I need to handle strings better *)
Require Coq.Strings.String.
Open Scope string_scope.
Axiom error : forall {A : Type}, String.string -> A.

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
