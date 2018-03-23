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
(* Converted imports: *)

Require GHC.Base.
Import GHC.Base.Notations.

(* Converted type declarations: *)

Inductive Void : Type :=.
(* Converted value declarations: *)

Local Definition Eq___Void_op_zeze__ : Void -> Void -> bool :=
  fun arg_0__ arg_1__ => true.

Local Definition Eq___Void_op_zsze__ : Void -> Void -> bool :=
  fun x y => negb (Eq___Void_op_zeze__ x y).

Program Instance Eq___Void : GHC.Base.Eq_ Void :=
  fun _ k =>
    k {| GHC.Base.op_zeze____ := Eq___Void_op_zeze__ ;
         GHC.Base.op_zsze____ := Eq___Void_op_zsze__ |}.

Local Definition Ord__Void_compare : Void -> Void -> comparison :=
  fun arg_0__ arg_1__ => Eq.

Local Definition Ord__Void_op_zg__ : Void -> Void -> bool :=
  fun x y => _GHC.Base.==_ (Ord__Void_compare x y) Gt.

Local Definition Ord__Void_op_zgze__ : Void -> Void -> bool :=
  fun x y => _GHC.Base./=_ (Ord__Void_compare x y) Lt.

Local Definition Ord__Void_op_zl__ : Void -> Void -> bool :=
  fun x y => _GHC.Base.==_ (Ord__Void_compare x y) Lt.

Local Definition Ord__Void_op_zlze__ : Void -> Void -> bool :=
  fun x y => _GHC.Base./=_ (Ord__Void_compare x y) Gt.

Local Definition Ord__Void_max : Void -> Void -> Void :=
  fun x y => if Ord__Void_op_zlze__ x y : bool then y else x.

Local Definition Ord__Void_min : Void -> Void -> Void :=
  fun x y => if Ord__Void_op_zlze__ x y : bool then x else y.

Program Instance Ord__Void : GHC.Base.Ord Void :=
  fun _ k =>
    k {| GHC.Base.op_zl____ := Ord__Void_op_zl__ ;
         GHC.Base.op_zlze____ := Ord__Void_op_zlze__ ;
         GHC.Base.op_zg____ := Ord__Void_op_zg__ ;
         GHC.Base.op_zgze____ := Ord__Void_op_zgze__ ;
         GHC.Base.compare__ := Ord__Void_compare ;
         GHC.Base.max__ := Ord__Void_max ;
         GHC.Base.min__ := Ord__Void_min |}.

(* Translating `instance Read__Void' failed: OOPS! Cannot find information for
   class Qualified "GHC.Read" "Read" unsupported *)

(* Translating `instance Show__Void' failed: OOPS! Cannot find information for
   class Qualified "GHC.Show" "Show" unsupported *)

(* Translating `instance Ix__Void' failed: OOPS! Cannot find information for
   class Qualified "GHC.Arr" "Ix" unsupported *)

(* Translating `instance Exception__Void' failed: OOPS! Cannot find information
   for class Qualified "GHC.Exception" "Exception" unsupported *)

(* Translating `instance Generic__Void' failed: OOPS! Cannot find information
   for class Qualified "GHC.Generics" "Generic" unsupported *)

(* Translating `instance Data__Void' failed: OOPS! Cannot find information for
   class Qualified "Data.Data" "Data" unsupported *)

Definition absurd {a} : Void -> a :=
  fun a => match a with end.

Definition vacuous {f} {a} `{GHC.Base.Functor f} : f Void -> f a :=
  GHC.Base.fmap absurd.

(* Unbound variables:
     Eq Gt Lt bool comparison negb true GHC.Base.Eq_ GHC.Base.Functor GHC.Base.Ord
     GHC.Base.fmap GHC.Base.op_zeze__ GHC.Base.op_zsze__
*)
