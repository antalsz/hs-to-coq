Definition arrow  := (fun (x y :Type) => x -> y).

Definition seq {A} {B} (a : A) (b:B) := b.

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

Class Coercible a b := { coerce : a -> b }.

Instance Coercible_Unpeel
  a b c
  {U1 : Unpeel a c}
  {U2 : Unpeel b c}
  : Coercible a b :=
  { coerce x := @repeel b c U2 (@unpeel a c U1 x) }.
