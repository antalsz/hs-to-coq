(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Coq.Program.Tactics.
Require Coq.Program.Wf.

(* Converted imports: *)

Require GHC.Base.
Import GHC.Base.Notations.

(* Converted type declarations: *)

Inductive Void : Type :=.

(* Converted value declarations: *)

Local Definition Eq___Void_op_zeze__ : Void -> Void -> bool :=
  fun arg_0__ arg_1__ => match arg_0__, arg_1__ with | _, z => true end.

Local Definition Eq___Void_op_zsze__ : Void -> Void -> bool :=
  fun x y => negb (Eq___Void_op_zeze__ x y).

Program Instance Eq___Void : GHC.Base.Eq_ Void :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zeze____ := Eq___Void_op_zeze__ ;
           GHC.Base.op_zsze____ := Eq___Void_op_zsze__ |}.

(* Skipping all instances of class `Data.Data.Data', including
   `Data.Void.Data__Void' *)

(* Skipping all instances of class `GHC.Generics.Generic', including
   `Data.Void.Generic__Void' *)

Local Definition Ord__Void_compare : Void -> Void -> comparison :=
  fun arg_0__ arg_1__ => match arg_0__, arg_1__ with | _, z => Eq end.

Local Definition Ord__Void_op_zl__ : Void -> Void -> bool :=
  fun x y => Ord__Void_compare x y GHC.Base.== Lt.

Local Definition Ord__Void_op_zlze__ : Void -> Void -> bool :=
  fun x y => Ord__Void_compare x y GHC.Base./= Gt.

Local Definition Ord__Void_op_zg__ : Void -> Void -> bool :=
  fun x y => Ord__Void_compare x y GHC.Base.== Gt.

Local Definition Ord__Void_op_zgze__ : Void -> Void -> bool :=
  fun x y => Ord__Void_compare x y GHC.Base./= Lt.

Local Definition Ord__Void_max : Void -> Void -> Void :=
  fun x y => if Ord__Void_op_zlze__ x y : bool then y else x.

Local Definition Ord__Void_min : Void -> Void -> Void :=
  fun x y => if Ord__Void_op_zlze__ x y : bool then x else y.

Program Instance Ord__Void : GHC.Base.Ord Void :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zl____ := Ord__Void_op_zl__ ;
           GHC.Base.op_zlze____ := Ord__Void_op_zlze__ ;
           GHC.Base.op_zg____ := Ord__Void_op_zg__ ;
           GHC.Base.op_zgze____ := Ord__Void_op_zgze__ ;
           GHC.Base.compare__ := Ord__Void_compare ;
           GHC.Base.max__ := Ord__Void_max ;
           GHC.Base.min__ := Ord__Void_min |}.

(* Skipping all instances of class `GHC.Read.Read', including
   `Data.Void.Read__Void' *)

(* Skipping all instances of class `GHC.Show.Show', including
   `Data.Void.Show__Void' *)

(* Skipping all instances of class `GHC.Arr.Ix', including
   `Data.Void.Ix__Void' *)

(* Skipping all instances of class `GHC.Exception.Exception', including
   `Data.Void.Exception__Void' *)

Local Definition Semigroup__Void_op_zlzlzgzg__ : Void -> Void -> Void :=
  fun arg_0__ arg_1__ => match arg_0__, arg_1__ with | a, _ => a end.

Program Instance Semigroup__Void : GHC.Base.Semigroup Void :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zlzlzgzg____ := Semigroup__Void_op_zlzlzgzg__ |}.

Definition absurd {a} : Void -> a :=
  fun a => match a with end.

Definition vacuous {f} {a} `{GHC.Base.Functor f} : f Void -> f a :=
  GHC.Base.fmap absurd.

(* External variables:
     Eq Gt Lt bool comparison negb true GHC.Base.Eq_ GHC.Base.Functor GHC.Base.Ord
     GHC.Base.Semigroup GHC.Base.compare__ GHC.Base.fmap GHC.Base.max__
     GHC.Base.min__ GHC.Base.op_zeze__ GHC.Base.op_zeze____ GHC.Base.op_zg____
     GHC.Base.op_zgze____ GHC.Base.op_zl____ GHC.Base.op_zlze____
     GHC.Base.op_zlzlzgzg____ GHC.Base.op_zsze__ GHC.Base.op_zsze____
*)
