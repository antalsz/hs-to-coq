(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Coq.Program.Wf.

(* Preamble *)

Require Import GHC.Base.
Require Import GHC.Num.

(* Converted imports: *)

Require GHC.Base.

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

Local Definition instance_forall___GHC_Base_Ord_a___GHC_Base_Ord__Down_a__compare {inst_a}
                                                                                  `{GHC.Base.Ord inst_a} : (Down
                                                                                                           inst_a) -> (Down
                                                                                                           inst_a) -> comparison :=
  fun arg_5__ arg_6__ =>
    match arg_5__ , arg_6__ with
      | Mk_Down x , Mk_Down y => GHC.Base.compare y x
    end.

Local Definition instance_forall___GHC_Base_Ord_a___GHC_Base_Ord__Down_a__op_zg__ {inst_a}
                                                                                  `{GHC.Base.Ord inst_a} : (Down
                                                                                                           inst_a) -> (Down
                                                                                                           inst_a) -> bool :=
  fun x y =>
    op_zeze__ (instance_forall___GHC_Base_Ord_a___GHC_Base_Ord__Down_a__compare x y)
              Gt.

Local Definition instance_forall___GHC_Base_Ord_a___GHC_Base_Ord__Down_a__op_zgze__ {inst_a}
                                                                                    `{GHC.Base.Ord inst_a} : (Down
                                                                                                             inst_a) -> (Down
                                                                                                             inst_a) -> bool :=
  fun x y =>
    op_zsze__ (instance_forall___GHC_Base_Ord_a___GHC_Base_Ord__Down_a__compare x y)
              Lt.

Local Definition instance_forall___GHC_Base_Ord_a___GHC_Base_Ord__Down_a__op_zl__ {inst_a}
                                                                                  `{GHC.Base.Ord inst_a} : (Down
                                                                                                           inst_a) -> (Down
                                                                                                           inst_a) -> bool :=
  fun x y =>
    op_zeze__ (instance_forall___GHC_Base_Ord_a___GHC_Base_Ord__Down_a__compare x y)
              Lt.

Local Definition instance_forall___GHC_Base_Ord_a___GHC_Base_Ord__Down_a__op_zlze__ {inst_a}
                                                                                    `{GHC.Base.Ord inst_a} : (Down
                                                                                                             inst_a) -> (Down
                                                                                                             inst_a) -> bool :=
  fun x y =>
    op_zsze__ (instance_forall___GHC_Base_Ord_a___GHC_Base_Ord__Down_a__compare x y)
              Gt.

Local Definition instance_forall___GHC_Base_Ord_a___GHC_Base_Ord__Down_a__max {inst_a}
                                                                              `{GHC.Base.Ord inst_a} : (Down
                                                                                                       inst_a) -> (Down
                                                                                                       inst_a) -> (Down
                                                                                                       inst_a) :=
  fun x y =>
    if instance_forall___GHC_Base_Ord_a___GHC_Base_Ord__Down_a__op_zlze__ x y : bool
    then y
    else x.

Local Definition instance_forall___GHC_Base_Ord_a___GHC_Base_Ord__Down_a__min {inst_a}
                                                                              `{GHC.Base.Ord inst_a} : (Down
                                                                                                       inst_a) -> (Down
                                                                                                       inst_a) -> (Down
                                                                                                       inst_a) :=
  fun x y =>
    if instance_forall___GHC_Base_Ord_a___GHC_Base_Ord__Down_a__op_zlze__ x y : bool
    then x
    else y.

Instance instance_forall___GHC_Base_Ord_a___GHC_Base_Ord__Down_a_ {a}
                                                                  `{GHC.Base.Ord a} : GHC.Base.Ord (Down a) := fun _
                                                                                                                   k =>
    k (GHC.Base.Ord__Dict_Build (Down a)
                                instance_forall___GHC_Base_Ord_a___GHC_Base_Ord__Down_a__op_zl__
                                instance_forall___GHC_Base_Ord_a___GHC_Base_Ord__Down_a__op_zlze__
                                instance_forall___GHC_Base_Ord_a___GHC_Base_Ord__Down_a__op_zg__
                                instance_forall___GHC_Base_Ord_a___GHC_Base_Ord__Down_a__op_zgze__
                                instance_forall___GHC_Base_Ord_a___GHC_Base_Ord__Down_a__compare
                                instance_forall___GHC_Base_Ord_a___GHC_Base_Ord__Down_a__max
                                instance_forall___GHC_Base_Ord_a___GHC_Base_Ord__Down_a__min).

(* Translating `instance forall {a}, forall `{GHC.Read.Read a}, GHC.Read.Read
   (Down a)' failed: OOPS! Cannot find information for class "GHC.Read.Read"
   unsupported *)

(* Translating `instance forall {a}, forall `{GHC.Show.Show a}, GHC.Show.Show
   (Down a)' failed: OOPS! Cannot find information for class "GHC.Show.Show"
   unsupported *)

(* Translating `instance forall {a}, forall `{GHC.Base.Eq_ a}, GHC.Base.Eq_
   (Down a)' failed: type applications unsupported *)

Definition comparing {a} {b} `{(GHC.Base.Ord a)}
    : (b -> a) -> b -> b -> comparison :=
  fun arg_0__ arg_1__ arg_2__ =>
    match arg_0__ , arg_1__ , arg_2__ with
      | p , x , y => GHC.Base.compare (p x) (p y)
    end.

(* Unbound variables:
     GHC.Base.Ord GHC.Base.Ord__Dict_Build GHC.Base.compare Gt Lt bool comparison
     op_zeze__ op_zsze__
*)
