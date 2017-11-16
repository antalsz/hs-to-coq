(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Coq.Program.Wf.

(* Preamble *)

Require Import GHC.Base.
(* Converted imports: *)

Require GHC.Base.

(* Converted type declarations: *)

Inductive Void : Type :=.
(* Converted value declarations: *)

Local Definition instance_GHC_Base_Eq__Void_op_zeze__ : Void -> Void -> bool :=
  fun arg_29__ arg_30__ => true.

Local Definition instance_GHC_Base_Eq__Void_op_zsze__ : Void -> Void -> bool :=
  fun x y => negb (instance_GHC_Base_Eq__Void_op_zeze__ x y).

Instance instance_GHC_Base_Eq__Void : GHC.Base.Eq_ Void := fun _ k =>
    k (GHC.Base.Eq___Dict_Build Void instance_GHC_Base_Eq__Void_op_zeze__
                                instance_GHC_Base_Eq__Void_op_zsze__).

Local Definition instance_GHC_Base_Ord_Void_compare
    : Void -> Void -> comparison :=
  fun arg_27__ arg_28__ => Eq.

Local Definition instance_GHC_Base_Ord_Void_op_zg__ : Void -> Void -> bool :=
  fun x y => op_zeze__ (instance_GHC_Base_Ord_Void_compare x y) Gt.

Local Definition instance_GHC_Base_Ord_Void_op_zgze__ : Void -> Void -> bool :=
  fun x y => op_zsze__ (instance_GHC_Base_Ord_Void_compare x y) Lt.

Local Definition instance_GHC_Base_Ord_Void_op_zl__ : Void -> Void -> bool :=
  fun x y => op_zeze__ (instance_GHC_Base_Ord_Void_compare x y) Lt.

Local Definition instance_GHC_Base_Ord_Void_op_zlze__ : Void -> Void -> bool :=
  fun x y => op_zsze__ (instance_GHC_Base_Ord_Void_compare x y) Gt.

Local Definition instance_GHC_Base_Ord_Void_max : Void -> Void -> Void :=
  fun x y => if instance_GHC_Base_Ord_Void_op_zlze__ x y : bool then y else x.

Local Definition instance_GHC_Base_Ord_Void_min : Void -> Void -> Void :=
  fun x y => if instance_GHC_Base_Ord_Void_op_zlze__ x y : bool then x else y.

Instance instance_GHC_Base_Ord_Void : GHC.Base.Ord Void := fun _ k =>
    k (GHC.Base.Ord__Dict_Build Void instance_GHC_Base_Ord_Void_op_zl__
                                instance_GHC_Base_Ord_Void_op_zlze__ instance_GHC_Base_Ord_Void_op_zg__
                                instance_GHC_Base_Ord_Void_op_zgze__ instance_GHC_Base_Ord_Void_compare
                                instance_GHC_Base_Ord_Void_max instance_GHC_Base_Ord_Void_min).

(* Skipping instance instance_GHC_Read_Read_Void *)

(* Skipping instance instance_GHC_Show_Show_Void *)

(* Skipping instance instance_GHC_Arr_Ix_Void *)

(* Skipping instance instance_GHC_Exception_Exception_Void *)

(* Translating `instance GHC.Generics.Generic Void' failed: OOPS! Cannot find
   information for class "GHC.Generics.Generic" unsupported *)

(* Skipping instance instance_Data_Data_Data_Void *)

Definition absurd {a} : Void -> a :=
  fun arg_0__ => match arg_0__ with | a => match a with end end.

Definition vacuous {f} {a} `{GHC.Base.Functor f} : f Void -> f a :=
  GHC.Base.fmap absurd.

(* Unbound variables:
     Eq GHC.Base.Eq_ GHC.Base.Eq___Dict_Build GHC.Base.Functor GHC.Base.Ord
     GHC.Base.Ord__Dict_Build GHC.Base.fmap Gt Lt bool comparison negb op_zeze__
     op_zsze__ true
*)
