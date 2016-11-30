Definition Synonym {A : Type} (_uniq : Type) (x : A) : A := x.

Require Import ZArith.

Axiom Char     : Type.
Axiom Int      : Type.
Axiom Rational : Type.
Axiom Map      : Type -> Type -> Type.
Axiom IntMap   : Type -> Type.

Definition String     := list Char.
Definition FilePath   := String.
Definition FastString := String.

Record Array k v := ListToArray { arrayToList : list (k * v) }.

Inductive IORef (a : Type) : Type :=.
