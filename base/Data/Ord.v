(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Coq.Program.Tactics.
Require Coq.Program.Wf.

(* Preamble *)

Require Import GHC.Base.
Require Import GHC.Num.

(* Converted imports: *)

Require GHC.Base.
Require GHC.Prim.
Import GHC.Base.Notations.

(* Converted type declarations: *)

Inductive Down a : Type := Mk_Down : a -> Down a.

Arguments Mk_Down {_} _.
(* Midamble *)

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

(* Converted value declarations: *)

Local Definition Ord__Down_compare {inst_a} `{GHC.Base.Ord inst_a}
   : (Down inst_a) -> (Down inst_a) -> comparison :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | Mk_Down x, Mk_Down y => GHC.Base.compare y x
    end.

Local Definition Ord__Down_op_zg__ {inst_a} `{GHC.Base.Ord inst_a}
   : (Down inst_a) -> (Down inst_a) -> bool :=
  fun x y => _GHC.Base.==_ (Ord__Down_compare x y) Gt.

Local Definition Ord__Down_op_zgze__ {inst_a} `{GHC.Base.Ord inst_a}
   : (Down inst_a) -> (Down inst_a) -> bool :=
  fun x y => _GHC.Base./=_ (Ord__Down_compare x y) Lt.

Local Definition Ord__Down_op_zl__ {inst_a} `{GHC.Base.Ord inst_a}
   : (Down inst_a) -> (Down inst_a) -> bool :=
  fun x y => _GHC.Base.==_ (Ord__Down_compare x y) Lt.

Local Definition Ord__Down_op_zlze__ {inst_a} `{GHC.Base.Ord inst_a}
   : (Down inst_a) -> (Down inst_a) -> bool :=
  fun x y => _GHC.Base./=_ (Ord__Down_compare x y) Gt.

Local Definition Ord__Down_max {inst_a} `{GHC.Base.Ord inst_a}
   : (Down inst_a) -> (Down inst_a) -> (Down inst_a) :=
  fun x y => if Ord__Down_op_zlze__ x y : bool then y else x.

Local Definition Ord__Down_min {inst_a} `{GHC.Base.Ord inst_a}
   : (Down inst_a) -> (Down inst_a) -> (Down inst_a) :=
  fun x y => if Ord__Down_op_zlze__ x y : bool then x else y.

Program Instance Ord__Down {a} `{GHC.Base.Ord a} : GHC.Base.Ord (Down a) :=
  fun _ k =>
    k {| GHC.Base.op_zl____ := Ord__Down_op_zl__ ;
         GHC.Base.op_zlze____ := Ord__Down_op_zlze__ ;
         GHC.Base.op_zg____ := Ord__Down_op_zg__ ;
         GHC.Base.op_zgze____ := Ord__Down_op_zgze__ ;
         GHC.Base.compare__ := Ord__Down_compare ;
         GHC.Base.max__ := Ord__Down_max ;
         GHC.Base.min__ := Ord__Down_min |}.
Admit Obligations.

(* Translating `instance forall {a}, forall `{GHC.Read.Read a}, GHC.Read.Read
   (Data.Ord.Down a)' failed: OOPS! Cannot find information for class Qualified
   "GHC.Read" "Read" unsupported *)

(* Translating `instance forall {a}, forall `{GHC.Show.Show a}, GHC.Show.Show
   (Data.Ord.Down a)' failed: OOPS! Cannot find information for class Qualified
   "GHC.Show" "Show" unsupported *)

Local Definition Eq___Down_op_zeze__ {inst_a} `{GHC.Base.Eq_ inst_a}
   : Down inst_a -> Down inst_a -> bool :=
  GHC.Prim.coerce _GHC.Base.==_.

Local Definition Eq___Down_op_zsze__ {inst_a} `{GHC.Base.Eq_ inst_a}
   : Down inst_a -> Down inst_a -> bool :=
  GHC.Prim.coerce _GHC.Base./=_.

Program Instance Eq___Down {a} `{GHC.Base.Eq_ a} : GHC.Base.Eq_ (Down a) :=
  fun _ k =>
    k {| GHC.Base.op_zeze____ := Eq___Down_op_zeze__ ;
         GHC.Base.op_zsze____ := Eq___Down_op_zsze__ |}.
Admit Obligations.

Definition comparing {a} {b} `{(GHC.Base.Ord a)}
   : (b -> a) -> b -> b -> comparison :=
  fun p x y => GHC.Base.compare (p x) (p y).

(* Unbound variables:
     Gt Lt bool comparison GHC.Base.Eq_ GHC.Base.Ord GHC.Base.compare
     GHC.Base.op_zeze__ GHC.Base.op_zsze__ GHC.Prim.coerce
*)
