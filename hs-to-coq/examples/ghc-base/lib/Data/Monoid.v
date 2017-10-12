(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Preamble *)

Require Import GHC.Base.

(* WE do these by hand because they are defined in GHC using Data.Coerce. *)

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


Inductive Any : Type := Mk_Any : bool -> Any.
Definition getAny (arg_7__ : Any) :=
  match arg_7__ with
    | (Mk_Any getAny) => getAny
  end.

Definition mappend_Any : Any -> Any -> Any :=
  fun x y => match x,y with
          | Mk_Any b1, Mk_Any b2 => Mk_Any (b1 || b2)
          end.
Definition mempty_Any : Any := Mk_Any false.

Instance instance_GHC_Base_Monoid_Any : !GHC.Base.Monoid Any := {
   mappend := mappend_Any;
   mempty  := mempty_Any;
   mconcat := foldr mappend_Any mempty_Any;
}.


Inductive First a : Type := Mk_First : option a -> First a.
Arguments Mk_First {_}.

Definition getFirst {a} (arg_3__ : First a) :=
  match arg_3__ with
    | (Mk_First getFirst) => getFirst
  end.

Definition mempty_First {a} : First a := Mk_First None.
Definition mappend_First {a} (x: First a) (y :First a) : First a :=
  match x , y with
    | Mk_First None, _ => y
    | _ , _ => x
  end.
Instance instance_GHC_Base_Monoid__First_a_ : !GHC.Base.Monoid (First a) :=
 { mappend := mappend_First;
   mempty  := mempty_First;
   mconcat := foldr mappend_First mempty_First }.

Inductive Last a : Type := Mk_Last : option a -> Last a.
Arguments Mk_Last {_}.

Definition getLast {a} (arg_2__ : Last a) :=
  match arg_2__ with
    | (Mk_Last getLast) => getLast
  end.
Definition mempty_Last {a} : Last a := Mk_Last None.
Definition mappend_Last {a} (x: Last a) (y :Last a) : Last a :=
  match x , y with
    | _ , Mk_Last None => y
    | _ , _ => x
  end.
Instance instance_GHC_Base_Monoid__Last_a_ : !GHC.Base.Monoid (Last a) :=
 { mappend := mappend_Last;
   mempty  := mempty_Last;
   mconcat := foldr mappend_Last mempty_Last }.



Inductive Product a : Type := Mk_Product : a -> Product a.
Arguments Mk_Product {_}.

Definition getProduct {a} (arg_1__ : Product a) :=
  match arg_1__ with
    | (Mk_Product getProduct) => getProduct
  end.

Definition mempty_Product {a} `{Num a} : Product a := Mk_Product #1.
Definition mappend_Product {a} `{Num a} (x: Product a) (y :Product a)  : Product a :=
  match x , y with
    | Mk_Product i , Mk_Product j => Mk_Product (i * j)
  end.
Instance instance_GHC_Base_Monoid__Product_a_ {a} `{Num a}: !GHC.Base.Monoid (Product a) :=
 { mappend := mappend_Product;
   mempty  := mempty_Product;
   mconcat := foldr mappend_Product mempty_Product }.

Instance instance_GHC_Base_Functor__Product_ : !GHC.Base.Functor Product := {}.
Proof.
- intros a b x pb. apply Mk_Product. exact x.
- intros a b f pa. destruct pa. apply Mk_Product. apply f. exact a0.
Defined.


Inductive Sum a : Type := Mk_Sum : a -> Sum a.
Arguments Mk_Sum {_}.

Definition getSum {a} (arg_1__ : Sum a) :=
  match arg_1__ with
    | (Mk_Sum getSum) => getSum
  end.

Definition mempty_Sum {a} `{Num a} : Sum a := Mk_Sum #0.
Definition mappend_Sum {a} `{Num a} (x: Sum a) (y :Sum a)  : Sum a :=
  match x , y with
    | Mk_Sum i , Mk_Sum j => Mk_Sum (i + j)
  end.
Instance instance_GHC_Base_Monoid__Sum_a_ {a} `{Num a}: !GHC.Base.Monoid (Sum a) :=
 { mappend := mappend_Sum;
   mempty  := mempty_Sum;
   mconcat := foldr mappend_Sum mempty_Sum }.

Instance instance_GHC_Base_Functor__Sum_ : !GHC.Base.Functor Sum := {}.
Proof.
- intros a b x pb. apply Mk_Sum. exact x.
- intros a b f pa. destruct pa. apply Mk_Sum. apply f. exact a0.
Defined.

(* No imports to convert. *)

(* Converted declarations: *)

(* Translating `instance forall {a}, forall `{GHC.Base.Monoid a},
   GHC.Base.Monoid (Dual a)' failed: OOPS! Cannot find information for class
   "GHC.Base.Monoid" unsupported *)

(* Skipping instance instance_GHC_Base_Functor_Dual *)

(* Skipping instance instance_GHC_Base_Applicative_Dual *)

(* Skipping instance instance_GHC_Base_Monad_Dual *)

(* Translating `instance forall {a}, GHC.Base.Monoid (Endo a)' failed: OOPS!
   Cannot find information for class "GHC.Base.Monoid" unsupported *)

(* Translating `instance GHC.Base.Monoid All' failed: OOPS! Cannot find
   information for class "GHC.Base.Monoid" unsupported *)

(* Translating `instance GHC.Base.Monoid Any' failed: OOPS! Cannot find
   information for class "GHC.Base.Monoid" unsupported *)

(* Translating `instance forall {a}, forall `{GHC.Num.Num a}, GHC.Base.Monoid
   (Sum a)' failed: OOPS! Cannot find information for class "GHC.Base.Monoid"
   unsupported *)

(* Skipping instance instance_GHC_Base_Functor_Sum *)

(* Skipping instance instance_GHC_Base_Applicative_Sum *)

(* Skipping instance instance_GHC_Base_Monad_Sum *)

(* Translating `instance forall {a}, forall `{GHC.Num.Num a}, GHC.Base.Monoid
   (Product a)' failed: OOPS! Cannot find information for class "GHC.Base.Monoid"
   unsupported *)

(* Skipping instance instance_GHC_Base_Functor_Product *)

(* Skipping instance instance_GHC_Base_Applicative_Product *)

(* Skipping instance instance_GHC_Base_Monad_Product *)

(* Translating `instance forall {a}, GHC.Base.Monoid (First a)' failed: OOPS!
   Cannot find information for class "GHC.Base.Monoid" unsupported *)

(* Translating `instance forall {a}, GHC.Base.Monoid (Last a)' failed: OOPS!
   Cannot find information for class "GHC.Base.Monoid" unsupported *)

(* Skipping instance
   instance_forall___GHC_Base_Alternative_f___GHC_Base_Monoid__Alt_f_a_ *)

(* Translating `instance forall {f}, forall `{GHC.Base.Functor f},
   GHC.Base.Functor (Alt f)' failed: type applications unsupported *)

(* Translating `instance forall {f}, forall `{GHC.Base.Alternative f},
   GHC.Base.Alternative (Alt f)' failed: type applications unsupported *)

(* Translating `instance forall {f}, forall `{GHC.Base.Applicative f},
   GHC.Base.Applicative (Alt f)' failed: type applications unsupported *)

(* Translating `instance forall {f}, forall `{GHC.Base.MonadPlus f},
   GHC.Base.MonadPlus (Alt f)' failed: type applications unsupported *)

(* Translating `instance forall {f}, forall `{GHC.Base.Monad f}, GHC.Base.Monad
   (Alt f)' failed: type applications unsupported *)

(* Translating `instance forall {k} {f} {a}, forall `{GHC.Enum.Enum (f a)},
   GHC.Enum.Enum (Alt f a)' failed: type applications unsupported *)

(* Translating `instance forall {k} {f} {a}, forall `{GHC.Num.Num (f a)},
   GHC.Num.Num (Alt f a)' failed: type applications unsupported *)

(* Translating `instance forall {k} {f} {a}, forall `{GHC.Base.Ord (f a)},
   GHC.Base.Ord (Alt f a)' failed: type applications unsupported *)

(* Translating `instance forall {k} {f} {a}, forall `{GHC.Base.Eq_ (f a)},
   GHC.Base.Eq_ (Alt f a)' failed: type applications unsupported *)

(* Skipping instance
   instance_forall___GHC_Show_Show__f_a____GHC_Show_Show__Alt_f_a_ *)

(* Skipping instance
   instance_forall___GHC_Read_Read__f_a____GHC_Read_Read__Alt_f_a_ *)

(* Translating `instance forall {f}, GHC.Generics.Generic1 (Alt f)' failed:
   OOPS! Cannot find information for class "GHC.Generics.Generic1" unsupported *)

(* Translating `instance forall {k} {f} {a}, GHC.Generics.Generic (Alt f a)'
   failed: OOPS! Cannot find information for class "GHC.Generics.Generic"
   unsupported *)

(* Translating `instance GHC.Base.Monad Last' failed: type applications
   unsupported *)

(* Translating `instance GHC.Base.Applicative Last' failed: type applications
   unsupported *)

(* Translating `instance GHC.Base.Functor Last' failed: type applications
   unsupported *)

(* Translating `instance GHC.Generics.Generic1 Last' failed: OOPS! Cannot find
   information for class "GHC.Generics.Generic1" unsupported *)

(* Translating `instance forall {a}, GHC.Generics.Generic (Last a)' failed:
   OOPS! Cannot find information for class "GHC.Generics.Generic" unsupported *)

(* Skipping instance
   instance_forall___GHC_Show_Show_a___GHC_Show_Show__Last_a_ *)

(* Skipping instance
   instance_forall___GHC_Read_Read_a___GHC_Read_Read__Last_a_ *)

(* Translating `instance forall {a}, forall `{GHC.Base.Ord a}, GHC.Base.Ord
   (Last a)' failed: type applications unsupported *)

(* Translating `instance forall {a}, forall `{GHC.Base.Eq_ a}, GHC.Base.Eq_
   (Last a)' failed: type applications unsupported *)

(* Translating `instance GHC.Base.Monad First' failed: type applications
   unsupported *)

(* Translating `instance GHC.Base.Applicative First' failed: type applications
   unsupported *)

(* Translating `instance GHC.Base.Functor First' failed: type applications
   unsupported *)

(* Translating `instance GHC.Generics.Generic1 First' failed: OOPS! Cannot find
   information for class "GHC.Generics.Generic1" unsupported *)

(* Translating `instance forall {a}, GHC.Generics.Generic (First a)' failed:
   OOPS! Cannot find information for class "GHC.Generics.Generic" unsupported *)

(* Skipping instance
   instance_forall___GHC_Show_Show_a___GHC_Show_Show__First_a_ *)

(* Skipping instance
   instance_forall___GHC_Read_Read_a___GHC_Read_Read__First_a_ *)

(* Translating `instance forall {a}, forall `{GHC.Base.Ord a}, GHC.Base.Ord
   (First a)' failed: type applications unsupported *)

(* Translating `instance forall {a}, forall `{GHC.Base.Eq_ a}, GHC.Base.Eq_
   (First a)' failed: type applications unsupported *)

(* Translating `instance forall {a}, forall `{GHC.Num.Num a}, GHC.Num.Num
   (Product a)' failed: type applications unsupported *)

(* Translating `instance GHC.Generics.Generic1 Product' failed: OOPS! Cannot
   find information for class "GHC.Generics.Generic1" unsupported *)

(* Translating `instance forall {a}, GHC.Generics.Generic (Product a)' failed:
   OOPS! Cannot find information for class "GHC.Generics.Generic" unsupported *)

(* Translating `instance forall {a}, forall `{GHC.Enum.Bounded a},
   GHC.Enum.Bounded (Product a)' failed: type applications unsupported *)

(* Skipping instance
   instance_forall___GHC_Show_Show_a___GHC_Show_Show__Product_a_ *)

(* Skipping instance
   instance_forall___GHC_Read_Read_a___GHC_Read_Read__Product_a_ *)

(* Translating `instance forall {a}, forall `{GHC.Base.Ord a}, GHC.Base.Ord
   (Product a)' failed: type applications unsupported *)

(* Translating `instance forall {a}, forall `{GHC.Base.Eq_ a}, GHC.Base.Eq_
   (Product a)' failed: type applications unsupported *)

(* Translating `instance forall {a}, forall `{GHC.Num.Num a}, GHC.Num.Num (Sum
   a)' failed: type applications unsupported *)

(* Translating `instance GHC.Generics.Generic1 Sum' failed: OOPS! Cannot find
   information for class "GHC.Generics.Generic1" unsupported *)

(* Translating `instance forall {a}, GHC.Generics.Generic (Sum a)' failed: OOPS!
   Cannot find information for class "GHC.Generics.Generic" unsupported *)

(* Translating `instance forall {a}, forall `{GHC.Enum.Bounded a},
   GHC.Enum.Bounded (Sum a)' failed: type applications unsupported *)

(* Skipping instance
   instance_forall___GHC_Show_Show_a___GHC_Show_Show__Sum_a_ *)

(* Skipping instance
   instance_forall___GHC_Read_Read_a___GHC_Read_Read__Sum_a_ *)

(* Translating `instance forall {a}, forall `{GHC.Base.Ord a}, GHC.Base.Ord (Sum
   a)' failed: type applications unsupported *)

(* Translating `instance forall {a}, forall `{GHC.Base.Eq_ a}, GHC.Base.Eq_ (Sum
   a)' failed: type applications unsupported *)

(* Translating `instance GHC.Generics.Generic Any' failed: OOPS! Cannot find
   information for class "GHC.Generics.Generic" unsupported *)

(* Translating `instance GHC.Enum.Bounded Any' failed: type applications
   unsupported *)

(* Skipping instance instance_GHC_Show_Show_Any *)

(* Skipping instance instance_GHC_Read_Read_Any *)

(* Translating `instance GHC.Base.Ord Any' failed: type applications
   unsupported *)

(* Translating `instance GHC.Base.Eq_ Any' failed: type applications
   unsupported *)

(* Translating `instance GHC.Generics.Generic All' failed: OOPS! Cannot find
   information for class "GHC.Generics.Generic" unsupported *)

(* Translating `instance GHC.Enum.Bounded All' failed: type applications
   unsupported *)

(* Skipping instance instance_GHC_Show_Show_All *)

(* Skipping instance instance_GHC_Read_Read_All *)

(* Translating `instance GHC.Base.Ord All' failed: type applications
   unsupported *)

(* Translating `instance GHC.Base.Eq_ All' failed: type applications
   unsupported *)

(* Translating `instance forall {a}, GHC.Generics.Generic (Endo a)' failed:
   OOPS! Cannot find information for class "GHC.Generics.Generic" unsupported *)

(* Translating `instance GHC.Generics.Generic1 Dual' failed: OOPS! Cannot find
   information for class "GHC.Generics.Generic1" unsupported *)

(* Translating `instance forall {a}, GHC.Generics.Generic (Dual a)' failed:
   OOPS! Cannot find information for class "GHC.Generics.Generic" unsupported *)

(* Translating `instance forall {a}, forall `{GHC.Enum.Bounded a},
   GHC.Enum.Bounded (Dual a)' failed: type applications unsupported *)

(* Skipping instance
   instance_forall___GHC_Show_Show_a___GHC_Show_Show__Dual_a_ *)

(* Skipping instance
   instance_forall___GHC_Read_Read_a___GHC_Read_Read__Dual_a_ *)

(* Translating `instance forall {a}, forall `{GHC.Base.Ord a}, GHC.Base.Ord
   (Dual a)' failed: type applications unsupported *)

(* Translating `instance forall {a}, forall `{GHC.Base.Eq_ a}, GHC.Base.Eq_
   (Dual a)' failed: type applications unsupported *)

Inductive Alt (f : Type -> Type) a : Type := Mk_Alt : f a -> Alt f a.

Inductive Dual a : Type := Mk_Dual : a -> Dual a.

Arguments Mk_Dual {_} _.

Definition getDual {a} (arg_1__ : Dual a) :=
  match arg_1__ with
    | Mk_Dual getDual => getDual
  end.

Inductive Endo a : Type := Mk_Endo : (a -> a) -> Endo a.

Arguments Mk_Endo {_} _.

Definition appEndo {a} (arg_0__ : Endo a) :=
  match arg_0__ with
    | Mk_Endo appEndo => appEndo
  end.

(* Unbound variables:
     Type
*)
