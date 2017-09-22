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
Require Import GHC.Enum.
Require Import GHC.Num.

(* Converted imports: *)

Require GHC.Base.
Require GHC.Enum.
Require GHC.Num.
Require GHC.Read.
Require GHC.Show.
Require GHC.Generics.
Require GHC.BaseGen.

(* Converted declarations: *)

(* Translating `instance (forall `{GHC.BaseGen.Monoid a}, GHC.BaseGen.Monoid
   (Dual a))' failed: OOPS! Cannot construct types for this class def: Nothing
   unsupported *)

(* Skipping instance instance_GHC_Base_Functor_Dual *)

(* Skipping instance instance_GHC_Base_Applicative_Dual *)

(* Skipping instance instance_GHC_BaseGen_Monad_Dual *)

(* Translating `instance GHC.BaseGen.Monoid (Endo a)' failed: OOPS! Cannot
   construct types for this class def: Nothing unsupported *)

(* Translating `instance GHC.BaseGen.Monoid All' failed: OOPS! Cannot construct
   types for this class def: Nothing unsupported *)

(* Translating `instance GHC.BaseGen.Monoid Any' failed: OOPS! Cannot construct
   types for this class def: Nothing unsupported *)

(* Translating `instance (forall `{GHC.Num.Num a}, GHC.BaseGen.Monoid (Sum a))'
   failed: OOPS! Cannot construct types for this class def: Nothing unsupported *)

(* Skipping instance instance_GHC_Base_Functor_Sum *)

(* Skipping instance instance_GHC_Base_Applicative_Sum *)

(* Skipping instance instance_GHC_BaseGen_Monad_Sum *)

(* Translating `instance (forall `{GHC.Num.Num a}, GHC.BaseGen.Monoid (Product
   a))' failed: OOPS! Cannot construct types for this class def: Nothing
   unsupported *)

(* Skipping instance instance_GHC_Base_Functor_Product *)

(* Skipping instance instance_GHC_Base_Applicative_Product *)

(* Skipping instance instance_GHC_BaseGen_Monad_Product *)

(* Translating `instance GHC.BaseGen.Monoid (First a)' failed: OOPS! Cannot
   construct types for this class def: Nothing unsupported *)

(* Translating `instance GHC.BaseGen.Monoid (Last a)' failed: OOPS! Cannot
   construct types for this class def: Nothing unsupported *)

(* Translating `instance (forall `{GHC.BaseGen.Alternative f},
   GHC.BaseGen.Monoid (Alt f a))' failed: OOPS! Cannot construct types for this
   class def: Nothing unsupported *)

Inductive All : Type := Mk_All : bool -> All.

Definition getAll (arg_7__ : All) :=
  match arg_7__ with
    | (Mk_All getAll) => getAll
  end.

Instance instance_GHC_BaseGen_Monoid_All : !GHC.BaseGen.Monoid All := {}.
Proof.
Admitted.

Inductive Alt (f : Type -> Type) a : Type := Mk_Alt : (f a) -> (Alt f a).

Inductive Any : Type := Mk_Any : bool -> Any.

Definition getAny (arg_6__ : Any) :=
  match arg_6__ with
    | (Mk_Any getAny) => getAny
  end.

Instance instance_GHC_BaseGen_Monoid_Any : !GHC.BaseGen.Monoid Any := {}.
Proof.
Admitted.

Inductive Dual a : Type := Mk_Dual : a -> (Dual a).

Definition getDual {a} (arg_5__ : Dual a) :=
  match arg_5__ with
    | (Mk_Dual getDual) => getDual
  end.

Instance instance__forall___GHC_BaseGen_Alternative_f___GHC_BaseGen_Monoid__Alt_f_a__
  : !(forall `{GHC.BaseGen.Alternative f}, GHC.BaseGen.Monoid (Alt f a)) := {}.
Proof.
Admitted.

Instance instance__forall___GHC_BaseGen_Monoid_a___GHC_BaseGen_Monoid__Dual_a__
  : !(forall `{GHC.BaseGen.Monoid a}, GHC.BaseGen.Monoid (Dual a)) := {}.
Proof.
Admitted.

Inductive Endo a : Type := Mk_Endo : (a -> a) -> (Endo a).

Definition appEndo {a} (arg_4__ : Endo a) :=
  match arg_4__ with
    | (Mk_Endo appEndo) => appEndo
  end.

Instance instance_GHC_BaseGen_Monoid__Endo_a_ : !GHC.BaseGen.Monoid (Endo a) :=
  {}.
Proof.
Admitted.

Inductive First a : Type := Mk_First : (option a) -> (First a).

Definition getFirst {a} (arg_3__ : First a) :=
  match arg_3__ with
    | (Mk_First getFirst) => getFirst
  end.

Instance instance_GHC_BaseGen_Monoid__First_a_ : !GHC.BaseGen.Monoid (First
                                                                     a) := {}.
Proof.
Admitted.

Inductive Last a : Type := Mk_Last : (option a) -> (Last a).

Definition getLast {a} (arg_2__ : Last a) :=
  match arg_2__ with
    | (Mk_Last getLast) => getLast
  end.

Instance instance_GHC_BaseGen_Monoid__Last_a_ : !GHC.BaseGen.Monoid (Last a) :=
  {}.
Proof.
Admitted.

Inductive Product a : Type := Mk_Product : a -> (Product a).

Definition getProduct {a} (arg_1__ : Product a) :=
  match arg_1__ with
    | (Mk_Product getProduct) => getProduct
  end.

Instance instance__forall___GHC_Num_Num_a___GHC_BaseGen_Monoid__Product_a__
  : !(forall `{GHC.Num.Num a}, GHC.BaseGen.Monoid (Product a)) := {}.
Proof.
Admitted.

Inductive Sum a : Type := Mk_Sum : a -> (Sum a).

Definition getSum {a} (arg_0__ : Sum a) :=
  match arg_0__ with
    | (Mk_Sum getSum) => getSum
  end.

Instance instance__forall___GHC_Num_Num_a___GHC_BaseGen_Monoid__Sum_a__
  : !(forall `{GHC.Num.Num a}, GHC.BaseGen.Monoid (Sum a)) := {}.
Proof.
Admitted.

(* Unbound variables:
     GHC.BaseGen.Alternative GHC.BaseGen.Monoid GHC.Num.Num Type bool f option
*)
