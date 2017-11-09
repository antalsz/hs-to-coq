Require Import GHC.Base.
Require Import GHC.Num.

(* Converted data type declarations: *)
Inductive Down a : Type := Mk_Down : a -> Down a.
Arguments Mk_Down {_}.

Instance instance_Down_Eq {a} `(Eq_ a) : Eq_ (Down a) := fun _ k => k {|
  op_zeze____ := (fun x y =>
                match x, y with
                | Mk_Down x0, Mk_Down y0 => x0 == y0
                end);
  op_zsze____ := (fun x y =>
                match x, y with
                | Mk_Down x0, Mk_Down y0 => x0 /= y0
                end)
|}.

Definition compare_Down `{Ord a} (xs : Down a) (ys : Down a) : comparison :=
  match xs, ys with
  | Mk_Down x , Mk_Down y => compare y x
  end.

Instance instance_forall___GHC_Base_Ord_a___GHC_Base_Ord__Down_a_
   `{GHC.Base.Ord a}: !GHC.Base.Ord (Down a) := ord_default compare_Down.

(*
 ( Eq
   , Show -- ^ @since 4.7.0.0
   , Read -- ^ @since 4.7.0.0
   , Num -- ^ @since 4.11.0.0
   , Monoid -- ^ @since 4.11.0.0
*)
