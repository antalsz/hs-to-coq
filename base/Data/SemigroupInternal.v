(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Coq.Program.Tactics.
Require Coq.Program.Wf.

(* Preamble *)

(* A hack to make a few kind-polymorpic definitions go through *)
Class unit_class.
Instance unit_class_instance : unit_class := {}.
Implicit Type inst_k: unit_class.

(* Converted imports: *)

Require Coq.Program.Basics.
Require GHC.Base.
Require GHC.Err.
Require GHC.Num.
Require GHC.Prim.
Require GHC.Real.
Import GHC.Base.Notations.
Import GHC.Num.Notations.

(* Converted type declarations: *)

Inductive Sum a : Type := | Mk_Sum (getSum : a) : Sum a.

Inductive Product a : Type := | Mk_Product (getProduct : a) : Product a.

Inductive Endo a : Type := | Mk_Endo (appEndo : a -> a) : Endo a.

Inductive Dual a : Type := | Mk_Dual (getDual : a) : Dual a.

Inductive Any : Type := | Mk_Any (getAny : bool) : Any.

Inductive Alt (f : Type -> Type) a : Type := | Mk_Alt (getAlt : f a) : Alt f a.

Inductive All : Type := | Mk_All (getAll : bool) : All.

Arguments Mk_Sum {_} _.

Arguments Mk_Product {_} _.

Arguments Mk_Endo {_} _.

Arguments Mk_Dual {_} _.

Arguments Mk_Alt {_} {_} _.

Instance Default__Any : GHC.Err.Default Any :=
  GHC.Err.Build_Default _ (Mk_Any GHC.Err.default).

Instance Default__All : GHC.Err.Default All :=
  GHC.Err.Build_Default _ (Mk_All GHC.Err.default).

Definition getSum {a} (arg_0__ : Sum a) :=
  let 'Mk_Sum getSum := arg_0__ in
  getSum.

Definition getProduct {a} (arg_0__ : Product a) :=
  let 'Mk_Product getProduct := arg_0__ in
  getProduct.

Definition appEndo {a} (arg_0__ : Endo a) :=
  let 'Mk_Endo appEndo := arg_0__ in
  appEndo.

Definition getDual {a} (arg_0__ : Dual a) :=
  let 'Mk_Dual getDual := arg_0__ in
  getDual.

Definition getAny (arg_0__ : Any) :=
  let 'Mk_Any getAny := arg_0__ in
  getAny.

Definition getAlt {f : Type -> Type} {a} (arg_0__ : Alt f a) :=
  let 'Mk_Alt getAlt := arg_0__ in
  getAlt.

Definition getAll (arg_0__ : All) :=
  let 'Mk_All getAll := arg_0__ in
  getAll.

(* Midamble *)

Instance Unpeel_Alt (f:Type->Type) a : GHC.Prim.Unpeel (Alt f a) (f a) :=
    GHC.Prim.Build_Unpeel _ _ getAlt Mk_Alt.

(*
Local Definition instance_forall___GHC_Base_Eq___f_a____GHC_Base_Eq___Alt_f_a__op_zeze__
                                                                                         {inst_f} {inst_a}
                                                                                         `{GHC.Base.Eq_ (inst_f inst_a)}
    : Alt inst_f inst_a -> Alt inst_f inst_a -> bool :=
  GHC.Prim.coerce GHC.Base.op_zeze__.

Local Definition instance_forall___GHC_Base_Eq___f_a____GHC_Base_Eq___Alt_f_a__op_zsze__
                                                                                         {inst_f} {inst_a}
                                                                                         `{GHC.Base.Eq_ (inst_f inst_a)}
    : Alt inst_f inst_a -> Alt inst_f inst_a -> bool :=
  GHC.Prim.coerce GHC.Base.op_zsze__.

Instance instance_forall___GHC_Base_Eq___f_a____GHC_Base_Eq___Alt_f_a_  {f}
                                                                       {a} `{GHC.Base.Eq_ (f a)} : GHC.Base.Eq_ (Alt f
                                                                                                                a) :=
  fun _ k =>
    k (GHC.Base.Eq___Dict_Build (Alt f a)
                                instance_forall___GHC_Base_Eq___f_a____GHC_Base_Eq___Alt_f_a__op_zeze__
                                instance_forall___GHC_Base_Eq___f_a____GHC_Base_Eq___Alt_f_a__op_zsze__).


Local Definition instance_forall___GHC_Base_Ord__f_a____GHC_Base_Ord__Alt_f_a__compare
                                                                                       {inst_f} {inst_a} `{GHC.Base.Ord
                                                                                       (inst_f inst_a)} : Alt inst_f
                                                                                                          inst_a -> Alt
                                                                                                          inst_f
                                                                                                          inst_a -> comparison :=
  GHC.Prim.coerce GHC.Base.compare.

Local Definition instance_forall___GHC_Base_Ord__f_a____GHC_Base_Ord__Alt_f_a__max                                                                                   {inst_f} {inst_a} `{GHC.Base.Ord
                                                                                   (inst_f inst_a)} : Alt inst_f
                                                                                                      inst_a -> Alt
                                                                                                      inst_f
                                                                                                      inst_a -> Alt
                                                                                                      inst_f inst_a :=
  GHC.Prim.coerce GHC.Base.max.

Local Definition instance_forall___GHC_Base_Ord__f_a____GHC_Base_Ord__Alt_f_a__min                                                                                    {inst_f} {inst_a} `{GHC.Base.Ord
                                                                                   (inst_f inst_a)} : Alt inst_f
                                                                                                      inst_a -> Alt
                                                                                                      inst_f
                                                                                                      inst_a -> Alt
                                                                                                      inst_f inst_a :=
  GHC.Prim.coerce GHC.Base.min.

Local Definition instance_forall___GHC_Base_Ord__f_a____GHC_Base_Ord__Alt_f_a__op_zg__
                                                                                       {inst_f} {inst_a} `{GHC.Base.Ord
                                                                                       (inst_f inst_a)} : Alt inst_f
                                                                                                          inst_a -> Alt
                                                                                                          inst_f
                                                                                                          inst_a -> bool :=
  GHC.Prim.coerce GHC.Base.op_zg__.

Local Definition instance_forall___GHC_Base_Ord__f_a____GHC_Base_Ord__Alt_f_a__op_zgze__
                                                                                         {inst_f} {inst_a}
                                                                                         `{GHC.Base.Ord (inst_f inst_a)}
    : Alt inst_f inst_a -> Alt inst_f inst_a -> bool :=
  GHC.Prim.coerce GHC.Base.op_zgze__.

Local Definition instance_forall___GHC_Base_Ord__f_a____GHC_Base_Ord__Alt_f_a__op_zl__
                                                                                       {inst_f} {inst_a} `{GHC.Base.Ord
                                                                                       (inst_f inst_a)} : Alt inst_f
                                                                                                          inst_a -> Alt
                                                                                                          inst_f
                                                                                                          inst_a -> bool :=
  GHC.Prim.coerce GHC.Base.op_zl__.

Local Definition instance_forall___GHC_Base_Ord__f_a____GHC_Base_Ord__Alt_f_a__op_zlze__
                                                                                         {inst_f} {inst_a}
                                                                                         `{GHC.Base.Ord (inst_f inst_a)}
    : Alt inst_f inst_a -> Alt inst_f inst_a -> bool :=
  GHC.Prim.coerce GHC.Base.op_zlze__.

Instance instance_forall___GHC_Base_Ord__f_a____GHC_Base_Ord__Alt_f_a_  {f}
                                                                       {a} `{GHC.Base.Ord (f a)} : GHC.Base.Ord (Alt f
                                                                                                                a) :=
  fun _ k =>
    k (GHC.Base.Ord__Dict_Build (Alt f a)
                                instance_forall___GHC_Base_Ord__f_a____GHC_Base_Ord__Alt_f_a__op_zl__
                                instance_forall___GHC_Base_Ord__f_a____GHC_Base_Ord__Alt_f_a__op_zlze__
                                instance_forall___GHC_Base_Ord__f_a____GHC_Base_Ord__Alt_f_a__op_zg__
                                instance_forall___GHC_Base_Ord__f_a____GHC_Base_Ord__Alt_f_a__op_zgze__
                                instance_forall___GHC_Base_Ord__f_a____GHC_Base_Ord__Alt_f_a__compare
                                instance_forall___GHC_Base_Ord__f_a____GHC_Base_Ord__Alt_f_a__max
                                instance_forall___GHC_Base_Ord__f_a____GHC_Base_Ord__Alt_f_a__min).
*)

(* Converted value declarations: *)

Instance Unpeel_Dual a : GHC.Prim.Unpeel (Dual a) a :=
  GHC.Prim.Build_Unpeel _ _ getDual Mk_Dual.

Local Definition Eq___Dual_op_zeze__ {inst_a} `{GHC.Base.Eq_ inst_a}
   : Dual inst_a -> Dual inst_a -> bool :=
  GHC.Prim.coerce _GHC.Base.==_.

Local Definition Eq___Dual_op_zsze__ {inst_a} `{GHC.Base.Eq_ inst_a}
   : Dual inst_a -> Dual inst_a -> bool :=
  GHC.Prim.coerce _GHC.Base./=_.

Program Instance Eq___Dual {a} `{GHC.Base.Eq_ a} : GHC.Base.Eq_ (Dual a) :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zeze____ := Eq___Dual_op_zeze__ ;
           GHC.Base.op_zsze____ := Eq___Dual_op_zsze__ |}.

Local Definition Ord__Dual_op_zl__ {inst_a} `{GHC.Base.Ord inst_a}
   : Dual inst_a -> Dual inst_a -> bool :=
  GHC.Prim.coerce _GHC.Base.<_.

Local Definition Ord__Dual_op_zlze__ {inst_a} `{GHC.Base.Ord inst_a}
   : Dual inst_a -> Dual inst_a -> bool :=
  GHC.Prim.coerce _GHC.Base.<=_.

Local Definition Ord__Dual_op_zg__ {inst_a} `{GHC.Base.Ord inst_a}
   : Dual inst_a -> Dual inst_a -> bool :=
  GHC.Prim.coerce _GHC.Base.>_.

Local Definition Ord__Dual_op_zgze__ {inst_a} `{GHC.Base.Ord inst_a}
   : Dual inst_a -> Dual inst_a -> bool :=
  GHC.Prim.coerce _GHC.Base.>=_.

Local Definition Ord__Dual_compare {inst_a} `{GHC.Base.Ord inst_a}
   : Dual inst_a -> Dual inst_a -> comparison :=
  GHC.Prim.coerce GHC.Base.compare.

Local Definition Ord__Dual_max {inst_a} `{GHC.Base.Ord inst_a}
   : Dual inst_a -> Dual inst_a -> Dual inst_a :=
  GHC.Prim.coerce GHC.Base.max.

Local Definition Ord__Dual_min {inst_a} `{GHC.Base.Ord inst_a}
   : Dual inst_a -> Dual inst_a -> Dual inst_a :=
  GHC.Prim.coerce GHC.Base.min.

Program Instance Ord__Dual {a} `{GHC.Base.Ord a} : GHC.Base.Ord (Dual a) :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zl____ := Ord__Dual_op_zl__ ;
           GHC.Base.op_zlze____ := Ord__Dual_op_zlze__ ;
           GHC.Base.op_zg____ := Ord__Dual_op_zg__ ;
           GHC.Base.op_zgze____ := Ord__Dual_op_zgze__ ;
           GHC.Base.compare__ := Ord__Dual_compare ;
           GHC.Base.max__ := Ord__Dual_max ;
           GHC.Base.min__ := Ord__Dual_min |}.

(* Skipping all instances of class `GHC.Read.Read', including
   `Data.SemigroupInternal.Read__Dual' *)

(* Skipping all instances of class `GHC.Show.Show', including
   `Data.SemigroupInternal.Show__Dual' *)

(* Skipping all instances of class `GHC.Enum.Bounded', including
   `Data.SemigroupInternal.Bounded__Dual' *)

(* Skipping all instances of class `GHC.Generics.Generic', including
   `Data.SemigroupInternal.Generic__Dual' *)

(* Skipping all instances of class `GHC.Generics.Generic1', including
   `Data.SemigroupInternal.Generic1__TYPE__Dual__LiftedRep' *)

(* Skipping all instances of class `GHC.Generics.Generic', including
   `Data.SemigroupInternal.Generic__Endo' *)

Instance Unpeel_All : GHC.Prim.Unpeel All bool :=
  GHC.Prim.Build_Unpeel _ _ getAll Mk_All.

Local Definition Eq___All_op_zeze__ : All -> All -> bool :=
  GHC.Prim.coerce _GHC.Base.==_.

Local Definition Eq___All_op_zsze__ : All -> All -> bool :=
  GHC.Prim.coerce _GHC.Base./=_.

Program Instance Eq___All : GHC.Base.Eq_ All :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zeze____ := Eq___All_op_zeze__ ;
           GHC.Base.op_zsze____ := Eq___All_op_zsze__ |}.

Local Definition Ord__All_op_zl__ : All -> All -> bool :=
  GHC.Prim.coerce _GHC.Base.<_.

Local Definition Ord__All_op_zlze__ : All -> All -> bool :=
  GHC.Prim.coerce _GHC.Base.<=_.

Local Definition Ord__All_op_zg__ : All -> All -> bool :=
  GHC.Prim.coerce _GHC.Base.>_.

Local Definition Ord__All_op_zgze__ : All -> All -> bool :=
  GHC.Prim.coerce _GHC.Base.>=_.

Local Definition Ord__All_compare : All -> All -> comparison :=
  GHC.Prim.coerce GHC.Base.compare.

Local Definition Ord__All_max : All -> All -> All :=
  GHC.Prim.coerce GHC.Base.max.

Local Definition Ord__All_min : All -> All -> All :=
  GHC.Prim.coerce GHC.Base.min.

Program Instance Ord__All : GHC.Base.Ord All :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zl____ := Ord__All_op_zl__ ;
           GHC.Base.op_zlze____ := Ord__All_op_zlze__ ;
           GHC.Base.op_zg____ := Ord__All_op_zg__ ;
           GHC.Base.op_zgze____ := Ord__All_op_zgze__ ;
           GHC.Base.compare__ := Ord__All_compare ;
           GHC.Base.max__ := Ord__All_max ;
           GHC.Base.min__ := Ord__All_min |}.

(* Skipping all instances of class `GHC.Read.Read', including
   `Data.SemigroupInternal.Read__All' *)

(* Skipping all instances of class `GHC.Show.Show', including
   `Data.SemigroupInternal.Show__All' *)

(* Skipping all instances of class `GHC.Enum.Bounded', including
   `Data.SemigroupInternal.Bounded__All' *)

(* Skipping all instances of class `GHC.Generics.Generic', including
   `Data.SemigroupInternal.Generic__All' *)

Instance Unpeel_Any : GHC.Prim.Unpeel Any bool :=
  GHC.Prim.Build_Unpeel _ _ getAny Mk_Any.

Local Definition Eq___Any_op_zeze__ : Any -> Any -> bool :=
  GHC.Prim.coerce _GHC.Base.==_.

Local Definition Eq___Any_op_zsze__ : Any -> Any -> bool :=
  GHC.Prim.coerce _GHC.Base./=_.

Program Instance Eq___Any : GHC.Base.Eq_ Any :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zeze____ := Eq___Any_op_zeze__ ;
           GHC.Base.op_zsze____ := Eq___Any_op_zsze__ |}.

Local Definition Ord__Any_op_zl__ : Any -> Any -> bool :=
  GHC.Prim.coerce _GHC.Base.<_.

Local Definition Ord__Any_op_zlze__ : Any -> Any -> bool :=
  GHC.Prim.coerce _GHC.Base.<=_.

Local Definition Ord__Any_op_zg__ : Any -> Any -> bool :=
  GHC.Prim.coerce _GHC.Base.>_.

Local Definition Ord__Any_op_zgze__ : Any -> Any -> bool :=
  GHC.Prim.coerce _GHC.Base.>=_.

Local Definition Ord__Any_compare : Any -> Any -> comparison :=
  GHC.Prim.coerce GHC.Base.compare.

Local Definition Ord__Any_max : Any -> Any -> Any :=
  GHC.Prim.coerce GHC.Base.max.

Local Definition Ord__Any_min : Any -> Any -> Any :=
  GHC.Prim.coerce GHC.Base.min.

Program Instance Ord__Any : GHC.Base.Ord Any :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zl____ := Ord__Any_op_zl__ ;
           GHC.Base.op_zlze____ := Ord__Any_op_zlze__ ;
           GHC.Base.op_zg____ := Ord__Any_op_zg__ ;
           GHC.Base.op_zgze____ := Ord__Any_op_zgze__ ;
           GHC.Base.compare__ := Ord__Any_compare ;
           GHC.Base.max__ := Ord__Any_max ;
           GHC.Base.min__ := Ord__Any_min |}.

(* Skipping all instances of class `GHC.Read.Read', including
   `Data.SemigroupInternal.Read__Any' *)

(* Skipping all instances of class `GHC.Show.Show', including
   `Data.SemigroupInternal.Show__Any' *)

(* Skipping all instances of class `GHC.Enum.Bounded', including
   `Data.SemigroupInternal.Bounded__Any' *)

(* Skipping all instances of class `GHC.Generics.Generic', including
   `Data.SemigroupInternal.Generic__Any' *)

Instance Unpeel_Sum a : GHC.Prim.Unpeel (Sum a) a :=
  GHC.Prim.Build_Unpeel _ _ getSum Mk_Sum.

Local Definition Eq___Sum_op_zeze__ {inst_a} `{GHC.Base.Eq_ inst_a}
   : Sum inst_a -> Sum inst_a -> bool :=
  GHC.Prim.coerce _GHC.Base.==_.

Local Definition Eq___Sum_op_zsze__ {inst_a} `{GHC.Base.Eq_ inst_a}
   : Sum inst_a -> Sum inst_a -> bool :=
  GHC.Prim.coerce _GHC.Base./=_.

Program Instance Eq___Sum {a} `{GHC.Base.Eq_ a} : GHC.Base.Eq_ (Sum a) :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zeze____ := Eq___Sum_op_zeze__ ;
           GHC.Base.op_zsze____ := Eq___Sum_op_zsze__ |}.

Local Definition Ord__Sum_op_zl__ {inst_a} `{GHC.Base.Ord inst_a}
   : Sum inst_a -> Sum inst_a -> bool :=
  GHC.Prim.coerce _GHC.Base.<_.

Local Definition Ord__Sum_op_zlze__ {inst_a} `{GHC.Base.Ord inst_a}
   : Sum inst_a -> Sum inst_a -> bool :=
  GHC.Prim.coerce _GHC.Base.<=_.

Local Definition Ord__Sum_op_zg__ {inst_a} `{GHC.Base.Ord inst_a}
   : Sum inst_a -> Sum inst_a -> bool :=
  GHC.Prim.coerce _GHC.Base.>_.

Local Definition Ord__Sum_op_zgze__ {inst_a} `{GHC.Base.Ord inst_a}
   : Sum inst_a -> Sum inst_a -> bool :=
  GHC.Prim.coerce _GHC.Base.>=_.

Local Definition Ord__Sum_compare {inst_a} `{GHC.Base.Ord inst_a}
   : Sum inst_a -> Sum inst_a -> comparison :=
  GHC.Prim.coerce GHC.Base.compare.

Local Definition Ord__Sum_max {inst_a} `{GHC.Base.Ord inst_a}
   : Sum inst_a -> Sum inst_a -> Sum inst_a :=
  GHC.Prim.coerce GHC.Base.max.

Local Definition Ord__Sum_min {inst_a} `{GHC.Base.Ord inst_a}
   : Sum inst_a -> Sum inst_a -> Sum inst_a :=
  GHC.Prim.coerce GHC.Base.min.

Program Instance Ord__Sum {a} `{GHC.Base.Ord a} : GHC.Base.Ord (Sum a) :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zl____ := Ord__Sum_op_zl__ ;
           GHC.Base.op_zlze____ := Ord__Sum_op_zlze__ ;
           GHC.Base.op_zg____ := Ord__Sum_op_zg__ ;
           GHC.Base.op_zgze____ := Ord__Sum_op_zgze__ ;
           GHC.Base.compare__ := Ord__Sum_compare ;
           GHC.Base.max__ := Ord__Sum_max ;
           GHC.Base.min__ := Ord__Sum_min |}.

(* Skipping all instances of class `GHC.Read.Read', including
   `Data.SemigroupInternal.Read__Sum' *)

(* Skipping all instances of class `GHC.Show.Show', including
   `Data.SemigroupInternal.Show__Sum' *)

(* Skipping all instances of class `GHC.Enum.Bounded', including
   `Data.SemigroupInternal.Bounded__Sum' *)

(* Skipping all instances of class `GHC.Generics.Generic', including
   `Data.SemigroupInternal.Generic__Sum' *)

(* Skipping all instances of class `GHC.Generics.Generic1', including
   `Data.SemigroupInternal.Generic1__TYPE__Sum__LiftedRep' *)

(* Skipping all instances of class `GHC.Num.Num', including
   `Data.SemigroupInternal.Num__Sum' *)

Instance Unpeel_Product a : GHC.Prim.Unpeel (Product a) a :=
  GHC.Prim.Build_Unpeel _ _ getProduct Mk_Product.

Local Definition Eq___Product_op_zeze__ {inst_a} `{GHC.Base.Eq_ inst_a}
   : Product inst_a -> Product inst_a -> bool :=
  GHC.Prim.coerce _GHC.Base.==_.

Local Definition Eq___Product_op_zsze__ {inst_a} `{GHC.Base.Eq_ inst_a}
   : Product inst_a -> Product inst_a -> bool :=
  GHC.Prim.coerce _GHC.Base./=_.

Program Instance Eq___Product {a} `{GHC.Base.Eq_ a}
   : GHC.Base.Eq_ (Product a) :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zeze____ := Eq___Product_op_zeze__ ;
           GHC.Base.op_zsze____ := Eq___Product_op_zsze__ |}.

Local Definition Ord__Product_op_zl__ {inst_a} `{GHC.Base.Ord inst_a}
   : Product inst_a -> Product inst_a -> bool :=
  GHC.Prim.coerce _GHC.Base.<_.

Local Definition Ord__Product_op_zlze__ {inst_a} `{GHC.Base.Ord inst_a}
   : Product inst_a -> Product inst_a -> bool :=
  GHC.Prim.coerce _GHC.Base.<=_.

Local Definition Ord__Product_op_zg__ {inst_a} `{GHC.Base.Ord inst_a}
   : Product inst_a -> Product inst_a -> bool :=
  GHC.Prim.coerce _GHC.Base.>_.

Local Definition Ord__Product_op_zgze__ {inst_a} `{GHC.Base.Ord inst_a}
   : Product inst_a -> Product inst_a -> bool :=
  GHC.Prim.coerce _GHC.Base.>=_.

Local Definition Ord__Product_compare {inst_a} `{GHC.Base.Ord inst_a}
   : Product inst_a -> Product inst_a -> comparison :=
  GHC.Prim.coerce GHC.Base.compare.

Local Definition Ord__Product_max {inst_a} `{GHC.Base.Ord inst_a}
   : Product inst_a -> Product inst_a -> Product inst_a :=
  GHC.Prim.coerce GHC.Base.max.

Local Definition Ord__Product_min {inst_a} `{GHC.Base.Ord inst_a}
   : Product inst_a -> Product inst_a -> Product inst_a :=
  GHC.Prim.coerce GHC.Base.min.

Program Instance Ord__Product {a} `{GHC.Base.Ord a}
   : GHC.Base.Ord (Product a) :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zl____ := Ord__Product_op_zl__ ;
           GHC.Base.op_zlze____ := Ord__Product_op_zlze__ ;
           GHC.Base.op_zg____ := Ord__Product_op_zg__ ;
           GHC.Base.op_zgze____ := Ord__Product_op_zgze__ ;
           GHC.Base.compare__ := Ord__Product_compare ;
           GHC.Base.max__ := Ord__Product_max ;
           GHC.Base.min__ := Ord__Product_min |}.

(* Skipping all instances of class `GHC.Read.Read', including
   `Data.SemigroupInternal.Read__Product' *)

(* Skipping all instances of class `GHC.Show.Show', including
   `Data.SemigroupInternal.Show__Product' *)

(* Skipping all instances of class `GHC.Enum.Bounded', including
   `Data.SemigroupInternal.Bounded__Product' *)

(* Skipping all instances of class `GHC.Generics.Generic', including
   `Data.SemigroupInternal.Generic__Product' *)

(* Skipping all instances of class `GHC.Generics.Generic1', including
   `Data.SemigroupInternal.Generic1__TYPE__Product__LiftedRep' *)

(* Skipping all instances of class `GHC.Num.Num', including
   `Data.SemigroupInternal.Num__Product' *)

(* Skipping all instances of class `GHC.Generics.Generic', including
   `Data.SemigroupInternal.Generic__Alt' *)

(* Skipping all instances of class `GHC.Generics.Generic1', including
   `Data.SemigroupInternal.Generic1__Alt__5' *)

(* Skipping all instances of class `GHC.Read.Read', including
   `Data.SemigroupInternal.Read__Alt' *)

(* Skipping all instances of class `GHC.Show.Show', including
   `Data.SemigroupInternal.Show__Alt' *)

Local Definition Eq___Alt_op_zeze__ {inst_f} {inst_a} `{GHC.Base.Eq_ (inst_f
                                                                      inst_a)}
   : (Alt inst_f inst_a : GHC.Prim.TYPE GHC.Types.LiftedRep) ->
     (Alt inst_f inst_a : GHC.Prim.TYPE GHC.Types.LiftedRep) -> bool :=
  GHC.Prim.coerce _GHC.Base.==_.

Local Definition Eq___Alt_op_zsze__ {inst_f} {inst_a} `{GHC.Base.Eq_ (inst_f
                                                                      inst_a)}
   : (Alt inst_f inst_a : GHC.Prim.TYPE GHC.Types.LiftedRep) ->
     (Alt inst_f inst_a : GHC.Prim.TYPE GHC.Types.LiftedRep) -> bool :=
  GHC.Prim.coerce _GHC.Base./=_.

Program Instance Eq___Alt {f} {a} `{GHC.Base.Eq_ (f a)}
   : GHC.Base.Eq_ (Alt f a : GHC.Prim.TYPE GHC.Types.LiftedRep) :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zeze____ := Eq___Alt_op_zeze__ ;
           GHC.Base.op_zsze____ := Eq___Alt_op_zsze__ |}.

Local Definition Ord__Alt_op_zl__ {inst_f} {inst_a} `{GHC.Base.Ord (inst_f
                                                                    inst_a)}
   : (Alt inst_f inst_a : GHC.Prim.TYPE GHC.Types.LiftedRep) ->
     (Alt inst_f inst_a : GHC.Prim.TYPE GHC.Types.LiftedRep) -> bool :=
  GHC.Prim.coerce _GHC.Base.<_.

Local Definition Ord__Alt_op_zlze__ {inst_f} {inst_a} `{GHC.Base.Ord (inst_f
                                                                      inst_a)}
   : (Alt inst_f inst_a : GHC.Prim.TYPE GHC.Types.LiftedRep) ->
     (Alt inst_f inst_a : GHC.Prim.TYPE GHC.Types.LiftedRep) -> bool :=
  GHC.Prim.coerce _GHC.Base.<=_.

Local Definition Ord__Alt_op_zg__ {inst_f} {inst_a} `{GHC.Base.Ord (inst_f
                                                                    inst_a)}
   : (Alt inst_f inst_a : GHC.Prim.TYPE GHC.Types.LiftedRep) ->
     (Alt inst_f inst_a : GHC.Prim.TYPE GHC.Types.LiftedRep) -> bool :=
  GHC.Prim.coerce _GHC.Base.>_.

Local Definition Ord__Alt_op_zgze__ {inst_f} {inst_a} `{GHC.Base.Ord (inst_f
                                                                      inst_a)}
   : (Alt inst_f inst_a : GHC.Prim.TYPE GHC.Types.LiftedRep) ->
     (Alt inst_f inst_a : GHC.Prim.TYPE GHC.Types.LiftedRep) -> bool :=
  GHC.Prim.coerce _GHC.Base.>=_.

Local Definition Ord__Alt_compare {inst_f} {inst_a} `{GHC.Base.Ord (inst_f
                                                                    inst_a)}
   : (Alt inst_f inst_a : GHC.Prim.TYPE GHC.Types.LiftedRep) ->
     (Alt inst_f inst_a : GHC.Prim.TYPE GHC.Types.LiftedRep) -> comparison :=
  GHC.Prim.coerce GHC.Base.compare.

Local Definition Ord__Alt_max {inst_f} {inst_a} `{GHC.Base.Ord (inst_f inst_a)}
   : (Alt inst_f inst_a : GHC.Prim.TYPE GHC.Types.LiftedRep) ->
     (Alt inst_f inst_a : GHC.Prim.TYPE GHC.Types.LiftedRep) ->
     (Alt inst_f inst_a : GHC.Prim.TYPE GHC.Types.LiftedRep) :=
  GHC.Prim.coerce GHC.Base.max.

Local Definition Ord__Alt_min {inst_f} {inst_a} `{GHC.Base.Ord (inst_f inst_a)}
   : (Alt inst_f inst_a : GHC.Prim.TYPE GHC.Types.LiftedRep) ->
     (Alt inst_f inst_a : GHC.Prim.TYPE GHC.Types.LiftedRep) ->
     (Alt inst_f inst_a : GHC.Prim.TYPE GHC.Types.LiftedRep) :=
  GHC.Prim.coerce GHC.Base.min.

Program Instance Ord__Alt {f} {a} `{GHC.Base.Ord (f a)}
   : GHC.Base.Ord (Alt f a : GHC.Prim.TYPE GHC.Types.LiftedRep) :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zl____ := Ord__Alt_op_zl__ ;
           GHC.Base.op_zlze____ := Ord__Alt_op_zlze__ ;
           GHC.Base.op_zg____ := Ord__Alt_op_zg__ ;
           GHC.Base.op_zgze____ := Ord__Alt_op_zgze__ ;
           GHC.Base.compare__ := Ord__Alt_compare ;
           GHC.Base.max__ := Ord__Alt_max ;
           GHC.Base.min__ := Ord__Alt_min |}.

(* Skipping all instances of class `GHC.Num.Num', including
   `Data.SemigroupInternal.Num__Alt' *)

(* Skipping all instances of class `GHC.Enum.Enum', including
   `Data.SemigroupInternal.Enum__Alt' *)

Local Definition Monad__Alt_op_zgzg__ {inst_f} `{GHC.Base.Monad inst_f}
   : forall {a} {b},
     (Alt inst_f : GHC.Prim.TYPE GHC.Types.LiftedRep ->
      GHC.Prim.TYPE GHC.Types.LiftedRep) a ->
     (Alt inst_f : GHC.Prim.TYPE GHC.Types.LiftedRep ->
      GHC.Prim.TYPE GHC.Types.LiftedRep) b ->
     (Alt inst_f : GHC.Prim.TYPE GHC.Types.LiftedRep ->
      GHC.Prim.TYPE GHC.Types.LiftedRep) b :=
  fun {a} {b} => GHC.Prim.coerce _GHC.Base.>>_.

Local Definition Monad__Alt_op_zgzgze__ {inst_f} `{GHC.Base.Monad inst_f}
   : forall {a} {b},
     (Alt inst_f : GHC.Prim.TYPE GHC.Types.LiftedRep ->
      GHC.Prim.TYPE GHC.Types.LiftedRep) a ->
     (a ->
      (Alt inst_f : GHC.Prim.TYPE GHC.Types.LiftedRep ->
       GHC.Prim.TYPE GHC.Types.LiftedRep) b) ->
     (Alt inst_f : GHC.Prim.TYPE GHC.Types.LiftedRep ->
      GHC.Prim.TYPE GHC.Types.LiftedRep) b :=
  fun {a} {b} => GHC.Prim.coerce _GHC.Base.>>=_.

Local Definition Monad__Alt_return_ {inst_f} `{GHC.Base.Monad inst_f}
   : forall {a},
     a ->
     (Alt inst_f : GHC.Prim.TYPE GHC.Types.LiftedRep ->
      GHC.Prim.TYPE GHC.Types.LiftedRep) a :=
  fun {a} => GHC.Prim.coerce GHC.Base.return_.

Local Definition Applicative__Alt_liftA2 {inst_f} `{GHC.Base.Applicative inst_f}
   : forall {a} {b} {c},
     (a -> b -> c) ->
     (Alt inst_f : GHC.Prim.TYPE GHC.Types.LiftedRep ->
      GHC.Prim.TYPE GHC.Types.LiftedRep) a ->
     (Alt inst_f : GHC.Prim.TYPE GHC.Types.LiftedRep ->
      GHC.Prim.TYPE GHC.Types.LiftedRep) b ->
     (Alt inst_f : GHC.Prim.TYPE GHC.Types.LiftedRep ->
      GHC.Prim.TYPE GHC.Types.LiftedRep) c :=
  fun {a} {b} {c} => GHC.Prim.coerce GHC.Base.liftA2.

Local Definition Applicative__Alt_op_zlztzg__ {inst_f} `{GHC.Base.Applicative
  inst_f}
   : forall {a} {b},
     (Alt inst_f : GHC.Prim.TYPE GHC.Types.LiftedRep ->
      GHC.Prim.TYPE GHC.Types.LiftedRep) (a -> b) ->
     (Alt inst_f : GHC.Prim.TYPE GHC.Types.LiftedRep ->
      GHC.Prim.TYPE GHC.Types.LiftedRep) a ->
     (Alt inst_f : GHC.Prim.TYPE GHC.Types.LiftedRep ->
      GHC.Prim.TYPE GHC.Types.LiftedRep) b :=
  fun {a} {b} => GHC.Prim.coerce _GHC.Base.<*>_.

Local Definition Applicative__Alt_op_ztzg__ {inst_f} `{GHC.Base.Applicative
  inst_f}
   : forall {a} {b},
     (Alt inst_f : GHC.Prim.TYPE GHC.Types.LiftedRep ->
      GHC.Prim.TYPE GHC.Types.LiftedRep) a ->
     (Alt inst_f : GHC.Prim.TYPE GHC.Types.LiftedRep ->
      GHC.Prim.TYPE GHC.Types.LiftedRep) b ->
     (Alt inst_f : GHC.Prim.TYPE GHC.Types.LiftedRep ->
      GHC.Prim.TYPE GHC.Types.LiftedRep) b :=
  fun {a} {b} => GHC.Prim.coerce _GHC.Base.*>_.

Local Definition Applicative__Alt_pure {inst_f} `{GHC.Base.Applicative inst_f}
   : forall {a},
     a ->
     (Alt inst_f : GHC.Prim.TYPE GHC.Types.LiftedRep ->
      GHC.Prim.TYPE GHC.Types.LiftedRep) a :=
  fun {a} => GHC.Prim.coerce GHC.Base.pure.

Local Definition Functor__Alt_fmap {inst_f} `{GHC.Base.Functor inst_f}
   : forall {a} {b},
     (a -> b) ->
     (Alt inst_f : GHC.Prim.TYPE GHC.Types.LiftedRep ->
      GHC.Prim.TYPE GHC.Types.LiftedRep) a ->
     (Alt inst_f : GHC.Prim.TYPE GHC.Types.LiftedRep ->
      GHC.Prim.TYPE GHC.Types.LiftedRep) b :=
  fun {a} {b} => GHC.Prim.coerce GHC.Base.fmap.

Local Definition Functor__Alt_op_zlzd__ {inst_f} `{GHC.Base.Functor inst_f}
   : forall {a} {b},
     a ->
     (Alt inst_f : GHC.Prim.TYPE GHC.Types.LiftedRep ->
      GHC.Prim.TYPE GHC.Types.LiftedRep) b ->
     (Alt inst_f : GHC.Prim.TYPE GHC.Types.LiftedRep ->
      GHC.Prim.TYPE GHC.Types.LiftedRep) a :=
  fun {a} {b} => GHC.Prim.coerce _GHC.Base.<$_.

Program Instance Functor__Alt {f} `{GHC.Base.Functor f}
   : GHC.Base.Functor (Alt f : GHC.Prim.TYPE GHC.Types.LiftedRep ->
                       GHC.Prim.TYPE GHC.Types.LiftedRep) :=
  fun _ k__ =>
    k__ {| GHC.Base.fmap__ := fun {a} {b} => Functor__Alt_fmap ;
           GHC.Base.op_zlzd____ := fun {a} {b} => Functor__Alt_op_zlzd__ |}.

Program Instance Applicative__Alt {f} `{GHC.Base.Applicative f}
   : GHC.Base.Applicative (Alt f : GHC.Prim.TYPE GHC.Types.LiftedRep ->
                           GHC.Prim.TYPE GHC.Types.LiftedRep) :=
  fun _ k__ =>
    k__ {| GHC.Base.liftA2__ := fun {a} {b} {c} => Applicative__Alt_liftA2 ;
           GHC.Base.op_zlztzg____ := fun {a} {b} => Applicative__Alt_op_zlztzg__ ;
           GHC.Base.op_ztzg____ := fun {a} {b} => Applicative__Alt_op_ztzg__ ;
           GHC.Base.pure__ := fun {a} => Applicative__Alt_pure |}.

Program Instance Monad__Alt {f} `{GHC.Base.Monad f}
   : GHC.Base.Monad (Alt f : GHC.Prim.TYPE GHC.Types.LiftedRep ->
                     GHC.Prim.TYPE GHC.Types.LiftedRep) :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zgzg____ := fun {a} {b} => Monad__Alt_op_zgzg__ ;
           GHC.Base.op_zgzgze____ := fun {a} {b} => Monad__Alt_op_zgzgze__ ;
           GHC.Base.return___ := fun {a} => Monad__Alt_return_ |}.

(* Skipping all instances of class `GHC.Base.MonadPlus', including
   `Data.SemigroupInternal.MonadPlus__Alt' *)

(* Skipping all instances of class `GHC.Base.Alternative', including
   `Data.SemigroupInternal.Alternative__Alt' *)

Local Definition Semigroup__Dual_op_zlzlzgzg__ {inst_a} `{GHC.Base.Semigroup
  inst_a}
   : (Dual inst_a) -> (Dual inst_a) -> (Dual inst_a) :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | Mk_Dual a, Mk_Dual b => Mk_Dual (b GHC.Base.<<>> a)
    end.

Program Instance Semigroup__Dual {a} `{GHC.Base.Semigroup a}
   : GHC.Base.Semigroup (Dual a) :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zlzlzgzg____ := Semigroup__Dual_op_zlzlzgzg__ |}.

Local Definition Monoid__Dual_mappend {inst_a} `{GHC.Base.Monoid inst_a}
   : (Dual inst_a) -> (Dual inst_a) -> (Dual inst_a) :=
  _GHC.Base.<<>>_.

Local Definition Monoid__Dual_mempty {inst_a} `{GHC.Base.Monoid inst_a}
   : (Dual inst_a) :=
  Mk_Dual GHC.Base.mempty.

Local Definition Monoid__Dual_mconcat {inst_a} `{GHC.Base.Monoid inst_a}
   : list (Dual inst_a) -> (Dual inst_a) :=
  GHC.Base.foldr Monoid__Dual_mappend Monoid__Dual_mempty.

Program Instance Monoid__Dual {a} `{GHC.Base.Monoid a}
   : GHC.Base.Monoid (Dual a) :=
  fun _ k__ =>
    k__ {| GHC.Base.mappend__ := Monoid__Dual_mappend ;
           GHC.Base.mconcat__ := Monoid__Dual_mconcat ;
           GHC.Base.mempty__ := Monoid__Dual_mempty |}.

Local Definition Functor__Dual_fmap
   : forall {a} {b}, (a -> b) -> Dual a -> Dual b :=
  fun {a} {b} => GHC.Prim.coerce.

Local Definition Functor__Dual_op_zlzd__
   : forall {a} {b}, a -> Dual b -> Dual a :=
  fun {a} {b} => Functor__Dual_fmap GHC.Base.∘ GHC.Base.const.

Program Instance Functor__Dual : GHC.Base.Functor Dual :=
  fun _ k__ =>
    k__ {| GHC.Base.fmap__ := fun {a} {b} => Functor__Dual_fmap ;
           GHC.Base.op_zlzd____ := fun {a} {b} => Functor__Dual_op_zlzd__ |}.

Local Definition Applicative__Dual_op_zlztzg__
   : forall {a} {b}, Dual (a -> b) -> Dual a -> Dual b :=
  fun {a} {b} => GHC.Prim.coerce.

Local Definition Applicative__Dual_liftA2
   : forall {a} {b} {c}, (a -> b -> c) -> Dual a -> Dual b -> Dual c :=
  fun {a} {b} {c} => fun f x => Applicative__Dual_op_zlztzg__ (GHC.Base.fmap f x).

Local Definition Applicative__Dual_op_ztzg__
   : forall {a} {b}, Dual a -> Dual b -> Dual b :=
  fun {a} {b} =>
    fun a1 a2 => Applicative__Dual_op_zlztzg__ (GHC.Base.id GHC.Base.<$ a1) a2.

Local Definition Applicative__Dual_pure : forall {a}, a -> Dual a :=
  fun {a} => Mk_Dual.

Program Instance Applicative__Dual : GHC.Base.Applicative Dual :=
  fun _ k__ =>
    k__ {| GHC.Base.liftA2__ := fun {a} {b} {c} => Applicative__Dual_liftA2 ;
           GHC.Base.op_zlztzg____ := fun {a} {b} => Applicative__Dual_op_zlztzg__ ;
           GHC.Base.op_ztzg____ := fun {a} {b} => Applicative__Dual_op_ztzg__ ;
           GHC.Base.pure__ := fun {a} => Applicative__Dual_pure |}.

Local Definition Monad__Dual_op_zgzgze__
   : forall {a} {b}, Dual a -> (a -> Dual b) -> Dual b :=
  fun {a} {b} => fun m k => k (getDual m).

Local Definition Monad__Dual_op_zgzg__
   : forall {a} {b}, Dual a -> Dual b -> Dual b :=
  fun {a} {b} => fun m k => Monad__Dual_op_zgzgze__ m (fun arg_0__ => k).

Local Definition Monad__Dual_return_ : forall {a}, a -> Dual a :=
  fun {a} => GHC.Base.pure.

Program Instance Monad__Dual : GHC.Base.Monad Dual :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zgzg____ := fun {a} {b} => Monad__Dual_op_zgzg__ ;
           GHC.Base.op_zgzgze____ := fun {a} {b} => Monad__Dual_op_zgzgze__ ;
           GHC.Base.return___ := fun {a} => Monad__Dual_return_ |}.

Instance Unpeel_Endo a : GHC.Prim.Unpeel (Endo a) (a -> a) :=
  GHC.Prim.Build_Unpeel _ _ appEndo Mk_Endo.

Local Definition Semigroup__Endo_op_zlzlzgzg__ {inst_a}
   : Endo inst_a -> Endo inst_a -> Endo inst_a :=
  GHC.Prim.coerce Coq.Program.Basics.compose.

Program Instance Semigroup__Endo {a} : GHC.Base.Semigroup (Endo a) :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zlzlzgzg____ := Semigroup__Endo_op_zlzlzgzg__ |}.

Local Definition Monoid__Endo_mappend {inst_a}
   : (Endo inst_a) -> (Endo inst_a) -> (Endo inst_a) :=
  _GHC.Base.<<>>_.

Local Definition Monoid__Endo_mempty {inst_a} : (Endo inst_a) :=
  Mk_Endo GHC.Base.id.

Local Definition Monoid__Endo_mconcat {inst_a}
   : list (Endo inst_a) -> (Endo inst_a) :=
  GHC.Base.foldr Monoid__Endo_mappend Monoid__Endo_mempty.

Program Instance Monoid__Endo {a} : GHC.Base.Monoid (Endo a) :=
  fun _ k__ =>
    k__ {| GHC.Base.mappend__ := Monoid__Endo_mappend ;
           GHC.Base.mconcat__ := Monoid__Endo_mconcat ;
           GHC.Base.mempty__ := Monoid__Endo_mempty |}.

Local Definition Semigroup__All_op_zlzlzgzg__ : All -> All -> All :=
  GHC.Prim.coerce andb.

Program Instance Semigroup__All : GHC.Base.Semigroup All :=
  fun _ k__ => k__ {| GHC.Base.op_zlzlzgzg____ := Semigroup__All_op_zlzlzgzg__ |}.

Local Definition Monoid__All_mappend : All -> All -> All :=
  _GHC.Base.<<>>_.

Local Definition Monoid__All_mempty : All :=
  Mk_All true.

Local Definition Monoid__All_mconcat : list All -> All :=
  GHC.Base.foldr Monoid__All_mappend Monoid__All_mempty.

Program Instance Monoid__All : GHC.Base.Monoid All :=
  fun _ k__ =>
    k__ {| GHC.Base.mappend__ := Monoid__All_mappend ;
           GHC.Base.mconcat__ := Monoid__All_mconcat ;
           GHC.Base.mempty__ := Monoid__All_mempty |}.

Local Definition Semigroup__Any_op_zlzlzgzg__ : Any -> Any -> Any :=
  GHC.Prim.coerce orb.

Program Instance Semigroup__Any : GHC.Base.Semigroup Any :=
  fun _ k__ => k__ {| GHC.Base.op_zlzlzgzg____ := Semigroup__Any_op_zlzlzgzg__ |}.

Local Definition Monoid__Any_mappend : Any -> Any -> Any :=
  _GHC.Base.<<>>_.

Local Definition Monoid__Any_mempty : Any :=
  Mk_Any false.

Local Definition Monoid__Any_mconcat : list Any -> Any :=
  GHC.Base.foldr Monoid__Any_mappend Monoid__Any_mempty.

Program Instance Monoid__Any : GHC.Base.Monoid Any :=
  fun _ k__ =>
    k__ {| GHC.Base.mappend__ := Monoid__Any_mappend ;
           GHC.Base.mconcat__ := Monoid__Any_mconcat ;
           GHC.Base.mempty__ := Monoid__Any_mempty |}.

Local Definition Semigroup__Sum_op_zlzlzgzg__ {inst_a} `{GHC.Num.Num inst_a}
   : Sum inst_a -> Sum inst_a -> Sum inst_a :=
  GHC.Prim.coerce _GHC.Num.+_.

Program Instance Semigroup__Sum {a} `{GHC.Num.Num a}
   : GHC.Base.Semigroup (Sum a) :=
  fun _ k__ => k__ {| GHC.Base.op_zlzlzgzg____ := Semigroup__Sum_op_zlzlzgzg__ |}.

Local Definition Monoid__Sum_mappend {inst_a} `{GHC.Num.Num inst_a}
   : (Sum inst_a) -> (Sum inst_a) -> (Sum inst_a) :=
  _GHC.Base.<<>>_.

Local Definition Monoid__Sum_mempty {inst_a} `{GHC.Num.Num inst_a}
   : (Sum inst_a) :=
  Mk_Sum #0.

Local Definition Monoid__Sum_mconcat {inst_a} `{GHC.Num.Num inst_a}
   : list (Sum inst_a) -> (Sum inst_a) :=
  GHC.Base.foldr Monoid__Sum_mappend Monoid__Sum_mempty.

Program Instance Monoid__Sum {a} `{GHC.Num.Num a} : GHC.Base.Monoid (Sum a) :=
  fun _ k__ =>
    k__ {| GHC.Base.mappend__ := Monoid__Sum_mappend ;
           GHC.Base.mconcat__ := Monoid__Sum_mconcat ;
           GHC.Base.mempty__ := Monoid__Sum_mempty |}.

Local Definition Functor__Sum_fmap
   : forall {a} {b}, (a -> b) -> Sum a -> Sum b :=
  fun {a} {b} => GHC.Prim.coerce.

Local Definition Functor__Sum_op_zlzd__ : forall {a} {b}, a -> Sum b -> Sum a :=
  fun {a} {b} => Functor__Sum_fmap GHC.Base.∘ GHC.Base.const.

Program Instance Functor__Sum : GHC.Base.Functor Sum :=
  fun _ k__ =>
    k__ {| GHC.Base.fmap__ := fun {a} {b} => Functor__Sum_fmap ;
           GHC.Base.op_zlzd____ := fun {a} {b} => Functor__Sum_op_zlzd__ |}.

Local Definition Applicative__Sum_op_zlztzg__
   : forall {a} {b}, Sum (a -> b) -> Sum a -> Sum b :=
  fun {a} {b} => GHC.Prim.coerce.

Local Definition Applicative__Sum_liftA2
   : forall {a} {b} {c}, (a -> b -> c) -> Sum a -> Sum b -> Sum c :=
  fun {a} {b} {c} => fun f x => Applicative__Sum_op_zlztzg__ (GHC.Base.fmap f x).

Local Definition Applicative__Sum_op_ztzg__
   : forall {a} {b}, Sum a -> Sum b -> Sum b :=
  fun {a} {b} =>
    fun a1 a2 => Applicative__Sum_op_zlztzg__ (GHC.Base.id GHC.Base.<$ a1) a2.

Local Definition Applicative__Sum_pure : forall {a}, a -> Sum a :=
  fun {a} => Mk_Sum.

Program Instance Applicative__Sum : GHC.Base.Applicative Sum :=
  fun _ k__ =>
    k__ {| GHC.Base.liftA2__ := fun {a} {b} {c} => Applicative__Sum_liftA2 ;
           GHC.Base.op_zlztzg____ := fun {a} {b} => Applicative__Sum_op_zlztzg__ ;
           GHC.Base.op_ztzg____ := fun {a} {b} => Applicative__Sum_op_ztzg__ ;
           GHC.Base.pure__ := fun {a} => Applicative__Sum_pure |}.

Local Definition Monad__Sum_op_zgzgze__
   : forall {a} {b}, Sum a -> (a -> Sum b) -> Sum b :=
  fun {a} {b} => fun m k => k (getSum m).

Local Definition Monad__Sum_op_zgzg__
   : forall {a} {b}, Sum a -> Sum b -> Sum b :=
  fun {a} {b} => fun m k => Monad__Sum_op_zgzgze__ m (fun arg_0__ => k).

Local Definition Monad__Sum_return_ : forall {a}, a -> Sum a :=
  fun {a} => GHC.Base.pure.

Program Instance Monad__Sum : GHC.Base.Monad Sum :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zgzg____ := fun {a} {b} => Monad__Sum_op_zgzg__ ;
           GHC.Base.op_zgzgze____ := fun {a} {b} => Monad__Sum_op_zgzgze__ ;
           GHC.Base.return___ := fun {a} => Monad__Sum_return_ |}.

Local Definition Semigroup__Product_op_zlzlzgzg__ {inst_a} `{GHC.Num.Num inst_a}
   : Product inst_a -> Product inst_a -> Product inst_a :=
  GHC.Prim.coerce _GHC.Num.*_.

Program Instance Semigroup__Product {a} `{GHC.Num.Num a}
   : GHC.Base.Semigroup (Product a) :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zlzlzgzg____ := Semigroup__Product_op_zlzlzgzg__ |}.

Local Definition Monoid__Product_mappend {inst_a} `{GHC.Num.Num inst_a}
   : (Product inst_a) -> (Product inst_a) -> (Product inst_a) :=
  _GHC.Base.<<>>_.

Local Definition Monoid__Product_mempty {inst_a} `{GHC.Num.Num inst_a}
   : (Product inst_a) :=
  Mk_Product #1.

Local Definition Monoid__Product_mconcat {inst_a} `{GHC.Num.Num inst_a}
   : list (Product inst_a) -> (Product inst_a) :=
  GHC.Base.foldr Monoid__Product_mappend Monoid__Product_mempty.

Program Instance Monoid__Product {a} `{GHC.Num.Num a}
   : GHC.Base.Monoid (Product a) :=
  fun _ k__ =>
    k__ {| GHC.Base.mappend__ := Monoid__Product_mappend ;
           GHC.Base.mconcat__ := Monoid__Product_mconcat ;
           GHC.Base.mempty__ := Monoid__Product_mempty |}.

Local Definition Functor__Product_fmap
   : forall {a} {b}, (a -> b) -> Product a -> Product b :=
  fun {a} {b} => GHC.Prim.coerce.

Local Definition Functor__Product_op_zlzd__
   : forall {a} {b}, a -> Product b -> Product a :=
  fun {a} {b} => Functor__Product_fmap GHC.Base.∘ GHC.Base.const.

Program Instance Functor__Product : GHC.Base.Functor Product :=
  fun _ k__ =>
    k__ {| GHC.Base.fmap__ := fun {a} {b} => Functor__Product_fmap ;
           GHC.Base.op_zlzd____ := fun {a} {b} => Functor__Product_op_zlzd__ |}.

Local Definition Applicative__Product_op_zlztzg__
   : forall {a} {b}, Product (a -> b) -> Product a -> Product b :=
  fun {a} {b} => GHC.Prim.coerce.

Local Definition Applicative__Product_liftA2
   : forall {a} {b} {c}, (a -> b -> c) -> Product a -> Product b -> Product c :=
  fun {a} {b} {c} =>
    fun f x => Applicative__Product_op_zlztzg__ (GHC.Base.fmap f x).

Local Definition Applicative__Product_op_ztzg__
   : forall {a} {b}, Product a -> Product b -> Product b :=
  fun {a} {b} =>
    fun a1 a2 => Applicative__Product_op_zlztzg__ (GHC.Base.id GHC.Base.<$ a1) a2.

Local Definition Applicative__Product_pure : forall {a}, a -> Product a :=
  fun {a} => Mk_Product.

Program Instance Applicative__Product : GHC.Base.Applicative Product :=
  fun _ k__ =>
    k__ {| GHC.Base.liftA2__ := fun {a} {b} {c} => Applicative__Product_liftA2 ;
           GHC.Base.op_zlztzg____ := fun {a} {b} => Applicative__Product_op_zlztzg__ ;
           GHC.Base.op_ztzg____ := fun {a} {b} => Applicative__Product_op_ztzg__ ;
           GHC.Base.pure__ := fun {a} => Applicative__Product_pure |}.

Local Definition Monad__Product_op_zgzgze__
   : forall {a} {b}, Product a -> (a -> Product b) -> Product b :=
  fun {a} {b} => fun m k => k (getProduct m).

Local Definition Monad__Product_op_zgzg__
   : forall {a} {b}, Product a -> Product b -> Product b :=
  fun {a} {b} => fun m k => Monad__Product_op_zgzgze__ m (fun arg_0__ => k).

Local Definition Monad__Product_return_ : forall {a}, a -> Product a :=
  fun {a} => GHC.Base.pure.

Program Instance Monad__Product : GHC.Base.Monad Product :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zgzg____ := fun {a} {b} => Monad__Product_op_zgzg__ ;
           GHC.Base.op_zgzgze____ := fun {a} {b} => Monad__Product_op_zgzgze__ ;
           GHC.Base.return___ := fun {a} => Monad__Product_return_ |}.

(* Skipping instance `Data.SemigroupInternal.Semigroup__Alt' of class
   `GHC.Base.Semigroup' *)

(* Skipping instance `Data.SemigroupInternal.Monoid__Alt' of class
   `GHC.Base.Monoid' *)

(* Skipping definition `Data.SemigroupInternal.stimesIdempotent' *)

Definition stimesIdempotentMonoid {b} {a} `{GHC.Real.Integral b}
  `{GHC.Base.Monoid a}
   : b -> a -> a :=
  fun n x =>
    match GHC.Base.compare n #0 with
    | Lt =>
        GHC.Err.errorWithoutStackTrace (GHC.Base.hs_string__
                                        "stimesIdempotentMonoid: negative multiplier")
    | Eq => GHC.Base.mempty
    | Gt => x
    end.

(* Skipping definition `Data.SemigroupInternal.stimesMonoid' *)

(* Skipping definition `Data.SemigroupInternal.stimesDefault' *)

(* Skipping definition `Data.SemigroupInternal.stimesMaybe' *)

(* Skipping definition `Data.SemigroupInternal.stimesList' *)

(* External variables:
     Eq Gt Lt Type andb bool comparison false list orb true
     Coq.Program.Basics.compose GHC.Base.Applicative GHC.Base.Eq_ GHC.Base.Functor
     GHC.Base.Monad GHC.Base.Monoid GHC.Base.Ord GHC.Base.Semigroup GHC.Base.compare
     GHC.Base.compare__ GHC.Base.const GHC.Base.fmap GHC.Base.fmap__ GHC.Base.foldr
     GHC.Base.id GHC.Base.liftA2 GHC.Base.liftA2__ GHC.Base.mappend__ GHC.Base.max
     GHC.Base.max__ GHC.Base.mconcat__ GHC.Base.mempty GHC.Base.mempty__ GHC.Base.min
     GHC.Base.min__ GHC.Base.op_z2218U__ GHC.Base.op_zeze__ GHC.Base.op_zeze____
     GHC.Base.op_zg__ GHC.Base.op_zg____ GHC.Base.op_zgze__ GHC.Base.op_zgze____
     GHC.Base.op_zgzg__ GHC.Base.op_zgzg____ GHC.Base.op_zgzgze__
     GHC.Base.op_zgzgze____ GHC.Base.op_zl__ GHC.Base.op_zl____ GHC.Base.op_zlzd__
     GHC.Base.op_zlzd____ GHC.Base.op_zlze__ GHC.Base.op_zlze____
     GHC.Base.op_zlzlzgzg__ GHC.Base.op_zlzlzgzg____ GHC.Base.op_zlztzg__
     GHC.Base.op_zlztzg____ GHC.Base.op_zsze__ GHC.Base.op_zsze____
     GHC.Base.op_ztzg__ GHC.Base.op_ztzg____ GHC.Base.pure GHC.Base.pure__
     GHC.Base.return_ GHC.Base.return___ GHC.Err.Build_Default GHC.Err.Default
     GHC.Err.default GHC.Err.errorWithoutStackTrace GHC.Num.Num GHC.Num.fromInteger
     GHC.Num.op_zp__ GHC.Num.op_zt__ GHC.Prim.Build_Unpeel GHC.Prim.TYPE
     GHC.Prim.Unpeel GHC.Prim.coerce GHC.Real.Integral GHC.Types.LiftedRep
*)
