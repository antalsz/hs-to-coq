(* Preamble *)
Require Import GHC.Base.

(* Set arguments *)
Set Implicit Arguments.
Generalizable All Variables.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Notation "a :~: b" := (a = b) (no associativity, at level 70).

Class EqTy {k} (a:k) (b:k) := { witness : a :~: b }.
Notation "a ~~ b" := (EqTy a b) (no associativity, at level 70).

Definition sym   := eq_sym.
Definition trans := eq_trans.
Definition castWith {a}{b} : (a :~: b) -> a -> b.
intros. subst. auto. Defined.

Definition gcastWith {k}{a:k}{b}{r} : (a :~: b) -> (forall `{a ~~ b}, r) -> r.
intros. subst. apply X. apply (Build_EqTy eq_refl).
Defined.

Definition apply {k1}{k2}{f : k1 -> k2}{g}{a}{b} : (f :~: g) -> (a :~: b) -> (f a :~: g b).
intros. subst. auto. Defined.

Instance Eq_EqTy {A} {a b : A} : `{Eq_ (a :~: b)} := fun _ k => k
	(Eq___Dict_Build _ (fun x y => true) (fun x y => false)).


(* inner and outer are not sound in Coq *)

Class TestEquality {k1} (f : k1 -> Type) :=
  { testEquality {a}{b} : f a -> f b -> option (a :~: b) }.

Instance TestEquality_EqTy {k}{a:k} : `{ TestEquality (fun x => a :~: x) } :=
  { testEquality := fun a b x y => match x,  y with eq_refl, eq_refl => Some eq_refl end }.

(* Coq cannot implement the == type family (for types) *)

Module Notations.
Notation "a 'Data.Type.Equality.:~:' b" := (a = b) (no associativity, at level 70).
Notation "'_Data.Type.Equality.:~:_'" := (fun a b => a = b) (no associativity, at level 70).
Notation "a 'Data.Type.Equality.~~' b" := (EqTy a b) (no associativity, at level 70).
Notation "'_Data.Type.Equality.~~_'" := (fun a b => EqTy a b) (no associativity, at level 70).
End Notations.
