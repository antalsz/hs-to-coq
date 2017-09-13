(* Default settings (from HsToCoq.Coq.Preamble) *)

Set Implicit Arguments.
Set Maximal Implicit Insertion.
Generalizable All Variables.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Axiom patternFailure : forall {a}, a.

(* Preamble *)
Require Import GHC.Base.
Require Import GHC.Enum.
Require Import GHC.Num.

(* Successfully converted the following code: *)
(* Skipping instance instance_Functor_Dual *)
(* Skipping instance instance_Applicative_Dual *)
(* Skipping instance instance_Monad_Dual *)
(* Skipping instance instance_Monoid__Endo_a_ *)
(* Skipping instance instance__forall___Num_a___Monoid__Sum_a__ *)
(* Skipping instance instance_Functor_Sum *)
(* Skipping instance instance_Applicative_Sum *)
(* Skipping instance instance_Monad_Sum *)
(* Skipping instance instance__forall___Num_a___Monoid__Product_a__ *)
(* Skipping instance instance_Functor_Product *)
(* Skipping instance instance_Applicative_Product *)
(* Skipping instance instance_Monad_Product *)
(* Skipping instance instance_Monoid__First_a_ *)
(* Skipping instance instance_Monoid__Last_a_ *)
(* Skipping instance instance__forall___Alternative_f___Monoid__Alt_f_a__ *)
Inductive All : Type := Mk_All : bool -> All.
Definition getAll (arg_7__ : All) :=
  match arg_7__ with
    | (Mk_All getAll) => getAll
  end.
Local Definition instance_Monoid_All_mempty : All :=
  Mk_All true.
Local Definition instance_Monoid_All_mappend : All -> (All -> All) :=
  fun arg_38__ arg_39__ =>
    match arg_38__ , arg_39__ with
      | (Mk_All x) , (Mk_All y) => Mk_All (andb x y)
    end.
Local Definition instance_Monoid_All_mconcat : (list All) -> All :=
  foldr instance_Monoid_All_mappend instance_Monoid_All_mempty.
Instance instance_Monoid_All : !Monoid All := {
  mappend := instance_Monoid_All_mappend ;
  mconcat := instance_Monoid_All_mconcat ;
  mempty := instance_Monoid_All_mempty }.
Inductive Alt (f : Type -> Type) a : Type := Mk_Alt : (f a) -> (Alt f a).
Inductive Any : Type := Mk_Any : bool -> Any.
Definition getAny (arg_6__ : Any) :=
  match arg_6__ with
    | (Mk_Any getAny) => getAny
  end.
Local Definition instance_Monoid_Any_mempty : Any :=
  Mk_Any false.
Local Definition instance_Monoid_Any_mappend : Any -> (Any -> Any) :=
  fun arg_33__ arg_34__ =>
    match arg_33__ , arg_34__ with
      | (Mk_Any x) , (Mk_Any y) => Mk_Any (orb x y)
    end.
Local Definition instance_Monoid_Any_mconcat : (list Any) -> Any :=
  foldr instance_Monoid_Any_mappend instance_Monoid_Any_mempty.
Instance instance_Monoid_Any : !Monoid Any := {
  mappend := instance_Monoid_Any_mappend ;
  mconcat := instance_Monoid_Any_mconcat ;
  mempty := instance_Monoid_Any_mempty }.
Inductive Dual a : Type := Mk_Dual : a -> (Dual a).
Definition getDual {a} (arg_5__ : Dual a) :=
  match arg_5__ with
    | (Mk_Dual getDual) => getDual
  end.
Local Definition instance__forall___Monoid_a___Monoid__Dual_a___mempty `{Monoid
                                                                       a} : (Dual a) :=
  Mk_Dual mempty.
Local Definition instance__forall___Monoid_a___Monoid__Dual_a___mappend `{Monoid
                                                                        a} : (Dual a) -> ((Dual a) -> (Dual a)) :=
  fun arg_52__ arg_53__ =>
    match arg_52__ , arg_53__ with
      | (Mk_Dual x) , (Mk_Dual y) => Mk_Dual (mappend y x)
    end.
Local Definition instance__forall___Monoid_a___Monoid__Dual_a___mconcat `{Monoid
                                                                        a} : (list (Dual a)) -> (Dual a) :=
  foldr instance__forall___Monoid_a___Monoid__Dual_a___mappend
        instance__forall___Monoid_a___Monoid__Dual_a___mempty.
Instance instance__forall___Monoid_a___Monoid__Dual_a__ : !(forall `{Monoid a},
                                                            Monoid (Dual a)) := {
  mappend := instance__forall___Monoid_a___Monoid__Dual_a___mappend ;
  mconcat := instance__forall___Monoid_a___Monoid__Dual_a___mconcat ;
  mempty := instance__forall___Monoid_a___Monoid__Dual_a___mempty }.
Inductive Endo a : Type := Mk_Endo : (a -> a) -> (Endo a).
Definition appEndo {a} (arg_4__ : Endo a) :=
  match arg_4__ with
    | (Mk_Endo appEndo) => appEndo
  end.
Inductive First a : Type := Mk_First : (option a) -> (First a).
Definition getFirst {a} (arg_3__ : First a) :=
  match arg_3__ with
    | (Mk_First getFirst) => getFirst
  end.
Inductive Last a : Type := Mk_Last : (option a) -> (Last a).
Definition getLast {a} (arg_2__ : Last a) :=
  match arg_2__ with
    | (Mk_Last getLast) => getLast
  end.
Inductive Product a : Type := Mk_Product : a -> (Product a).
Definition getProduct {a} (arg_1__ : Product a) :=
  match arg_1__ with
    | (Mk_Product getProduct) => getProduct
  end.
Inductive Sum a : Type := Mk_Sum : a -> (Sum a).
Definition getSum {a} (arg_0__ : Sum a) :=
  match arg_0__ with
    | (Mk_Sum getSum) => getSum
  end.

(* Unbound variables:
     Monoid Type andb bool false foldr list mappend mempty option orb true
*)
