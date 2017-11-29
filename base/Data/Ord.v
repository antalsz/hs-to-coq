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

Local Definition instance_forall___GHC_Base_Ord_a___GHC_Base_Ord__Data_Ord_Down_a__compare {inst_a}
                                                                                           `{GHC.Base.Ord inst_a}
    : (Down inst_a) -> (Down inst_a) -> comparison :=
  fun arg_3__ arg_4__ =>
    match arg_3__ , arg_4__ with
      | Mk_Down x , Mk_Down y => GHC.Base.compare y x
    end.

Local Definition instance_forall___GHC_Base_Ord_a___GHC_Base_Ord__Data_Ord_Down_a__op_zg__ {inst_a}
                                                                                           `{GHC.Base.Ord inst_a}
    : (Down inst_a) -> (Down inst_a) -> bool :=
  fun x y =>
    GHC.Base.op_zeze__
    (instance_forall___GHC_Base_Ord_a___GHC_Base_Ord__Data_Ord_Down_a__compare x y)
    Gt.

Local Definition instance_forall___GHC_Base_Ord_a___GHC_Base_Ord__Data_Ord_Down_a__op_zgze__ {inst_a}
                                                                                             `{GHC.Base.Ord inst_a}
    : (Down inst_a) -> (Down inst_a) -> bool :=
  fun x y =>
    GHC.Base.op_zsze__
    (instance_forall___GHC_Base_Ord_a___GHC_Base_Ord__Data_Ord_Down_a__compare x y)
    Lt.

Local Definition instance_forall___GHC_Base_Ord_a___GHC_Base_Ord__Data_Ord_Down_a__op_zl__ {inst_a}
                                                                                           `{GHC.Base.Ord inst_a}
    : (Down inst_a) -> (Down inst_a) -> bool :=
  fun x y =>
    GHC.Base.op_zeze__
    (instance_forall___GHC_Base_Ord_a___GHC_Base_Ord__Data_Ord_Down_a__compare x y)
    Lt.

Local Definition instance_forall___GHC_Base_Ord_a___GHC_Base_Ord__Data_Ord_Down_a__op_zlze__ {inst_a}
                                                                                             `{GHC.Base.Ord inst_a}
    : (Down inst_a) -> (Down inst_a) -> bool :=
  fun x y =>
    GHC.Base.op_zsze__
    (instance_forall___GHC_Base_Ord_a___GHC_Base_Ord__Data_Ord_Down_a__compare x y)
    Gt.

Local Definition instance_forall___GHC_Base_Ord_a___GHC_Base_Ord__Data_Ord_Down_a__max {inst_a}
                                                                                       `{GHC.Base.Ord inst_a} : (Down
                                                                                                                inst_a) -> (Down
                                                                                                                inst_a) -> (Down
                                                                                                                inst_a) :=
  fun x y =>
    if instance_forall___GHC_Base_Ord_a___GHC_Base_Ord__Data_Ord_Down_a__op_zlze__ x
                                                                                   y : bool
    then y
    else x.

Local Definition instance_forall___GHC_Base_Ord_a___GHC_Base_Ord__Data_Ord_Down_a__min {inst_a}
                                                                                       `{GHC.Base.Ord inst_a} : (Down
                                                                                                                inst_a) -> (Down
                                                                                                                inst_a) -> (Down
                                                                                                                inst_a) :=
  fun x y =>
    if instance_forall___GHC_Base_Ord_a___GHC_Base_Ord__Data_Ord_Down_a__op_zlze__ x
                                                                                   y : bool
    then x
    else y.

Program Instance instance_forall___GHC_Base_Ord_a___GHC_Base_Ord__Data_Ord_Down_a_ {a}
                                                                                   `{GHC.Base.Ord a} : GHC.Base.Ord
                                                                                                       (Down a) := fun _
                                                                                                                       k =>
    k
    {|GHC.Base.op_zl____ := instance_forall___GHC_Base_Ord_a___GHC_Base_Ord__Data_Ord_Down_a__op_zl__ ;
    GHC.Base.op_zlze____ := instance_forall___GHC_Base_Ord_a___GHC_Base_Ord__Data_Ord_Down_a__op_zlze__ ;
    GHC.Base.op_zg____ := instance_forall___GHC_Base_Ord_a___GHC_Base_Ord__Data_Ord_Down_a__op_zg__ ;
    GHC.Base.op_zgze____ := instance_forall___GHC_Base_Ord_a___GHC_Base_Ord__Data_Ord_Down_a__op_zgze__ ;
    GHC.Base.compare__ := instance_forall___GHC_Base_Ord_a___GHC_Base_Ord__Data_Ord_Down_a__compare ;
    GHC.Base.max__ := instance_forall___GHC_Base_Ord_a___GHC_Base_Ord__Data_Ord_Down_a__max ;
    GHC.Base.min__ := instance_forall___GHC_Base_Ord_a___GHC_Base_Ord__Data_Ord_Down_a__min |}.

(* Translating `instance forall {a}, forall `{GHC.Read.Read a}, GHC.Read.Read
   (Data.Ord.Down a)' failed: OOPS! Cannot find information for class Qualified
   "GHC.Read" "Read" unsupported *)

(* Translating `instance forall {a}, forall `{GHC.Show.Show a}, GHC.Show.Show
   (Data.Ord.Down a)' failed: OOPS! Cannot find information for class Qualified
   "GHC.Show" "Show" unsupported *)

Local Definition instance_forall___GHC_Base_Eq__a___GHC_Base_Eq___Data_Ord_Down_a__op_zeze__ {inst_a}
                                                                                             `{GHC.Base.Eq_ inst_a}
    : Down inst_a -> Down inst_a -> bool :=
  GHC.Prim.coerce GHC.Base.op_zeze__.

Local Definition instance_forall___GHC_Base_Eq__a___GHC_Base_Eq___Data_Ord_Down_a__op_zsze__ {inst_a}
                                                                                             `{GHC.Base.Eq_ inst_a}
    : Down inst_a -> Down inst_a -> bool :=
  GHC.Prim.coerce GHC.Base.op_zsze__.

Program Instance instance_forall___GHC_Base_Eq__a___GHC_Base_Eq___Data_Ord_Down_a_ {a}
                                                                                   `{GHC.Base.Eq_ a} : GHC.Base.Eq_
                                                                                                       (Down a) := fun _
                                                                                                                       k =>
    k
    {|GHC.Base.op_zeze____ := instance_forall___GHC_Base_Eq__a___GHC_Base_Eq___Data_Ord_Down_a__op_zeze__ ;
    GHC.Base.op_zsze____ := instance_forall___GHC_Base_Eq__a___GHC_Base_Eq___Data_Ord_Down_a__op_zsze__ |}.

Definition comparing {a} {b} `{(GHC.Base.Ord a)}
    : (b -> a) -> b -> b -> comparison :=
  fun p x y => GHC.Base.compare (p x) (p y).

(* Unbound variables:
     Gt Lt bool comparison GHC.Base.Eq_ GHC.Base.Ord GHC.Base.compare
     GHC.Base.op_zeze__ GHC.Base.op_zsze__ GHC.Prim.coerce
*)
