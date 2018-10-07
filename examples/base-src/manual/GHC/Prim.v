Require Import GHC.Types.

Definition arrow  := (fun (x y :Type) => x -> y).

Definition seq {A} {B} (a : A) (b:B) := b.

(* Coq has no levity polymorphism, so map everything to Type *)
Definition TYPE (_ : RuntimeRep) := Type.


(* Unpeel class: A directed form of Coercible, where a is the newtype type,
   and b the base type *)
Class Unpeel a b :=
  { unpeel : a -> b
  ; repeel : b -> a }.

Instance Unpeel_refl a : Unpeel a a := Build_Unpeel _ _ (fun x => x) (fun x => x).

Instance Unpeel_arrow
  a b c d
  `{Unpeel b a}
  `{Unpeel c d}
  : Unpeel (b -> c) (a -> d) :=
  { unpeel f x := unpeel (f (repeel x))
  ; repeel f x := repeel (f (unpeel x))
  }.

Instance Unpeel_pair
  a b c d
  `{Unpeel a b}
  `{Unpeel c d}
  : Unpeel (a * c) (b * d) :=
  { unpeel '(x,y) := (unpeel x, unpeel y)
  ; repeel '(x,y) := (repeel x, repeel y)
  }.


Require Coq.Lists.List.
Instance Unpeel_list a b
   `{Unpeel a b} : Unpeel (list a) (list b) :=
  { unpeel x := Coq.Lists.List.map unpeel x
  ; repeel x := Coq.Lists.List.map repeel x
  }.

Class Coercible a b := { coerce : a -> b }.

Instance Coercible_Unpeel
  a b c
  {U1 : Unpeel a c}
  {U2 : Unpeel b c}
  : Coercible a b :=
  { coerce x := @repeel b c U2 (@unpeel a c U1 x) }.
