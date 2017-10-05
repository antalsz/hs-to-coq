(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Set Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Preamble *)

Require Import GHC.Base.
Require Import GHC.Enum.
Require Import GHC.Num.


(* Converted declarations: *)

(* Translating `instance forall `{GHC.Base.Monoid a}, GHC.Base.Monoid (Dual a)'
   failed: OOPS! Cannot construct types for this class def: Nothing unsupported *)

(* Translating `instance GHC.Base.Functor Dual' failed: OOPS! Cannot construct
   types for this class def: Nothing unsupported *)

(* Translating `instance GHC.Base.Applicative Dual' failed: OOPS! Cannot
   construct types for this class def: Nothing unsupported *)

(* Translating `instance GHC.Base.Monad Dual' failed: OOPS! Cannot construct
   types for this class def: Nothing unsupported *)

(* Translating `instance GHC.Base.Monoid (Endo a)' failed: OOPS! Cannot
   construct types for this class def: Nothing unsupported *)

(* Translating `instance GHC.Base.Monoid All' failed: OOPS! Cannot construct
   types for this class def: Nothing unsupported *)

(* Translating `instance GHC.Base.Monoid Any' failed: OOPS! Cannot construct
   types for this class def: Nothing unsupported *)

(* Translating `instance forall `{GHC.Num.Num a}, GHC.Base.Monoid (Sum a)'
   failed: OOPS! Cannot construct types for this class def: Nothing unsupported *)

(* Translating `instance GHC.Base.Functor Sum' failed: OOPS! Cannot construct
   types for this class def: Nothing unsupported *)

(* Translating `instance GHC.Base.Applicative Sum' failed: OOPS! Cannot
   construct types for this class def: Nothing unsupported *)

(* Translating `instance GHC.Base.Monad Sum' failed: OOPS! Cannot construct
   types for this class def: Nothing unsupported *)

(* Translating `instance forall `{GHC.Num.Num a}, GHC.Base.Monoid (Product a)'
   failed: OOPS! Cannot construct types for this class def: Nothing unsupported *)

(* Translating `instance GHC.Base.Functor Product' failed: OOPS! Cannot
   construct types for this class def: Nothing unsupported *)

(* Translating `instance GHC.Base.Applicative Product' failed: OOPS! Cannot
   construct types for this class def: Nothing unsupported *)

(* Translating `instance GHC.Base.Monad Product' failed: OOPS! Cannot construct
   types for this class def: Nothing unsupported *)

(* Translating `instance GHC.Base.Monoid (First a)' failed: OOPS! Cannot
   construct types for this class def: Nothing unsupported *)

(* Translating `instance GHC.Base.Monoid (Last a)' failed: OOPS! Cannot
   construct types for this class def: Nothing unsupported *)

(* Translating `instance forall `{GHC.Base.Alternative f}, GHC.Base.Monoid (Alt
   f a)' failed: OOPS! Cannot construct types for this class def: Nothing
   unsupported *)

Inductive All : Type := Mk_All : bool -> All.

Definition getAll (arg_7__ : All) :=
  match arg_7__ with
    | (Mk_All getAll) => getAll
  end.

Definition mappend_All : All -> All -> All :=
  fun x y => match x,y with
          | Mk_All b1, Mk_All b2 => Mk_All (b1 && b2)
          end.
Definition mempty_All : All := Mk_All true.

Instance instance_GHC_Base_Monoid_All : !GHC.Base.Monoid All := {
   mappend := mappend_All;
   mempty  := mempty_All;
   mconcat := foldr mappend_All mempty_All;
}.

Inductive Alt (f : Type -> Type) a : Type := Mk_Alt : f a -> Alt f a.

Inductive Any : Type := Mk_Any : bool -> Any.

Definition getAny (arg_6__ : Any) :=
  match arg_6__ with
    | (Mk_Any getAny) => getAny
  end.

Instance instance_GHC_Base_Monoid_Any : !GHC.Base.Monoid Any := {}.
Proof.
Admitted.

Inductive Dual a : Type := Mk_Dual : a -> Dual a.

Definition getDual {a} (arg_5__ : Dual a) :=
  match arg_5__ with
    | (Mk_Dual getDual) => getDual
  end.

Instance instance_forall___GHC_Base_Alternative_f___GHC_Base_Monoid__Alt_f_a_
  : !forall `{GHC.Base.Alternative f}, GHC.Base.Monoid (Alt f a) := {}.
Proof.
Admitted.

Instance instance_GHC_Base_Functor_Dual : !GHC.Base.Functor Dual := {}.
Proof.
Admitted.

Instance instance_GHC_Base_Applicative_Dual : !GHC.Base.Applicative Dual := {}.
Proof.
Admitted.


Instance instance_GHC_Base_Monad_Dual : !GHC.Base.Monad Dual := {}.
Proof.
Admitted.


Instance instance_forall___GHC_Base_Monoid_a___GHC_Base_Monoid__Dual_a_
  : !forall `{GHC.Base.Monoid a}, GHC.Base.Monoid (Dual a) := {}.
Proof.
Admitted.

Inductive Endo a : Type := Mk_Endo : (a -> a) -> Endo a.

Definition appEndo {a} (arg_4__ : Endo a) :=
  match arg_4__ with
    | (Mk_Endo appEndo) => appEndo
  end.

Instance instance_GHC_Base_Monoid__Endo_a_ : !GHC.Base.Monoid (Endo a) := {}.
Proof.
Admitted.

Inductive First a : Type := Mk_First : option a -> First a.

Definition getFirst {a} (arg_3__ : First a) :=
  match arg_3__ with
    | (Mk_First getFirst) => getFirst
  end.

Instance instance_GHC_Base_Monoid__First_a_ : !GHC.Base.Monoid (First a) := {}.
Proof.
Admitted.

Inductive Last a : Type := Mk_Last : option a -> Last a.

Definition getLast {a} (arg_2__ : Last a) :=
  match arg_2__ with
    | (Mk_Last getLast) => getLast
  end.

Instance instance_GHC_Base_Monoid__Last_a_ : !GHC.Base.Monoid (Last a) := {}.
Proof.
Admitted.

Inductive Product a : Type := Mk_Product : a -> Product a.

Definition getProduct {a} (arg_1__ : Product a) :=
  match arg_1__ with
    | (Mk_Product getProduct) => getProduct
  end.



Instance instance_GHC_Base_Functor_Product : !GHC.Base.Functor Product := {}.
Proof.
Admitted.

Instance instance_GHC_Base_Applicative_Product : !GHC.Base.Applicative
                                                 Product := {}.
Proof.
Admitted.

Instance instance_GHC_Base_Monad_Product : !GHC.Base.Monad Product := {}.
Proof.
Admitted.

Instance instance_forall___GHC_Num_Num_a___GHC_Base_Monoid__Product_a_
  : !forall `{GHC.Num.Num a}, GHC.Base.Monoid (Product a) := {}.
Proof.
Admitted.

Inductive Sum a : Type := Mk_Sum : a -> Sum a.

Definition getSum {a} (arg_0__ : Sum a) :=
  match arg_0__ with
    | (Mk_Sum getSum) => getSum
  end.


Instance instance_forall___GHC_Num_Num_a___GHC_Base_Monoid__Sum_a_
  : !forall `{GHC.Num.Num a}, GHC.Base.Monoid (Sum a) := {}.
Proof.
Admitted.


Instance instance_GHC_Base_Functor_Sum : !GHC.Base.Functor Sum := {}.
Proof.
Admitted.

Instance instance_GHC_Base_Applicative_Sum : !GHC.Base.Applicative Sum := {}.
Proof.
Admitted.

Instance instance_GHC_Base_Monad_Sum : !GHC.Base.Monad Sum := {}.
Proof.
Admitted.


(* Unbound variables:
     GHC.Base.Alternative GHC.Base.Applicative GHC.Base.Functor GHC.Base.Monad
     GHC.Base.Monoid GHC.Num.Num Type bool f option
*)
