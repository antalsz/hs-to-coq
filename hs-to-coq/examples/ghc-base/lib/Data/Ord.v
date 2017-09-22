(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Set Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Let us be a bit explicit by having multiple axoims around *)
(* This one is for untranslatable expressions: *)
Local Axiom missingValue : forall {a}, a.
(* This one is for pattern match failures: *)
Local Axiom patternFailure : forall {a}, a.

(* Preamble *)

Require Import GHC.Base.
Require Import GHC.Num.

(* Converted data type declarations: *)
Inductive Down a : Type := Mk_Down : a -> Down a.

Instance instance_Down_Eq {a} `(Eq_ a) : Eq_ (Down a) := {
  op_zsze__ := (fun x y =>
                match x, y with
                | Mk_Down x0, Mk_Down y0 => x0 == y0
                end);
  op_zeze__ := (fun x y =>
                match x, y with
                | Mk_Down x0, Mk_Down y0 => x0 /= y0
                end);
}.

(*
 ( Eq
   , Show -- ^ @since 4.7.0.0
   , Read -- ^ @since 4.7.0.0
   , Num -- ^ @since 4.11.0.0
   , Monoid -- ^ @since 4.11.0.0
*)

(* Converted imports: *)

Require GHC.Base.
Require GHC.Show.
Require GHC.Read.
Require GHC.Prim.

(* Converted declarations: *)

(* Translating `instance (forall `{GHC.Prim.Ord a}, GHC.Prim.Ord (Down a))'
   failed: OOPS! Cannot construct types for this class def: Nothing unsupported *)

Definition comparing {a} {b} `{(GHC.Prim.Ord a)}
    : (b -> a) -> (b -> (b -> comparison)) :=
  fun arg_0__ arg_1__ arg_2__ =>
    match arg_0__ , arg_1__ , arg_2__ with
      | p , x , y => GHC.Prim.compare (p x) (p y)
    end.

Instance instance__forall___GHC_Prim_Ord_a___GHC_Prim_Ord__Down_a__
  : !(forall `{GHC.Prim.Ord a}, GHC.Prim.Ord (Down a)) := {}.
Proof.
Admitted.

(* Unbound variables:
     Down GHC.Prim.Ord GHC.Prim.compare comparison
*)
