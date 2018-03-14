(**
Definitions for deferred recursion
*)

(** The fixpoint axiom *)


Require Export GHC.Err.

Axiom deferredFix: forall {a r} `{Default r}, ((a -> r) -> (a -> r)) -> a -> r.

(** Variants for differing arities *)

Definition deferredFix1 {a r} `{Default r} : ((a -> r) -> (a -> r)) -> a -> r
  := deferredFix.

Definition curry : forall {a b r}, (((a * b) -> r) -> a -> b -> r)
  := fun _ _ _ f x y => f (x, y).

Definition uncurry : forall {a b r}, ((a -> b -> r) -> (a * b) -> r)
  := fun _ _ _ f '(x, y) => f x y.

Definition deferredFix2 {a b r} `{Default r} : ((a -> b -> r) -> (a -> b-> r)) -> a -> b -> r
  := fun f => curry (deferredFix (fun g => uncurry (f (curry g)))).

Definition deferredFix3 {a b c r} `{Default r} : ((a -> b -> c -> r) -> (a -> b -> c -> r)) -> a -> b -> c -> r
  := fun f => curry (deferredFix2 (fun g => uncurry (f (curry g)))).

Definition deferredFix4 {a b c d r} `{Default r} : ((a -> b -> c -> d -> r) -> (a -> b -> c -> d-> r)) -> a -> b -> c -> d -> r
  := fun f => curry (deferredFix3 (fun g => uncurry (f (curry g)))).


(** The fixpoint unrolling axiom *)


Definition recurses_on {a b} (P : a -> Prop) (R : a -> a -> Prop) (f : (a -> b) -> (a -> b)) :=
  forall g h x, P x -> (forall y, P y ->  R y x -> g y = h y) -> f g x = f h x.

Axiom deferredFix_eq_on: forall {a b} `{Default b} (f : (a -> b) -> (a -> b)) (P : a -> Prop) (R : a -> a -> Prop),
   well_founded R -> recurses_on P R f ->
   forall x, P x -> deferredFix f x = f (deferredFix f) x.
