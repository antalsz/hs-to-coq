(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Preamble *)

Require Import GHC.Base.
Open Scope type_scope.

(* Converted imports: *)

Require GHC.Base.

(* Converted declarations: *)

(* Translating `instance Data.Foldable.Foldable Pair' failed: OOPS! Cannot find
   information for class "Data.Foldable.Foldable" unsupported *)

(* Translating `instance Data.Traversable.Traversable Pair' failed: OOPS! Cannot
   find information for class "Data.Traversable.Traversable" unsupported *)

(* Translating `instance forall {a}, forall `{GHC.Base.Monoid a},
   GHC.Base.Monoid (Pair a)' failed: OOPS! Cannot find information for class
   "GHC.Base.Monoid" unsupported *)

(* Translating `instance forall {a}, forall `{Outputable.Outputable a},
   Outputable.Outputable (Pair a)' failed: OOPS! Cannot find information for class
   "Outputable.Outputable" unsupported *)

Inductive Pair a : Type := Mk_Pair : a -> a -> Pair a.

Arguments Mk_Pair {_} _ _.

Definition pFst {a} (arg_0__ : Pair a) :=
  match arg_0__ with
    | Mk_Pair pFst _ => pFst
  end.

Definition pSnd {a} (arg_1__ : Pair a) :=
  match arg_1__ with
    | Mk_Pair _ pSnd => pSnd
  end.

Definition unPair {a} : Pair a -> a * a :=
  fun arg_16__ => match arg_16__ with | Mk_Pair x y => pair x y end.

Definition toPair {a} : a * a -> Pair a :=
  fun arg_13__ => match arg_13__ with | pair x y => Mk_Pair x y end.

Definition swap {a} : Pair a -> Pair a :=
  fun arg_10__ => match arg_10__ with | Mk_Pair x y => Mk_Pair y x end.

Definition pLiftSnd {a} : (a -> a) -> Pair a -> Pair a :=
  fun arg_2__ arg_3__ =>
    match arg_2__ , arg_3__ with
      | f , Mk_Pair a b => Mk_Pair a (f b)
    end.

Definition pLiftFst {a} : (a -> a) -> Pair a -> Pair a :=
  fun arg_6__ arg_7__ =>
    match arg_6__ , arg_7__ with
      | f , Mk_Pair a b => Mk_Pair (f a) b
    end.

Local Definition instance_GHC_Base_Applicative_Pair_pure : forall {a},
                                                             a -> Pair a :=
  fun {a} => fun arg_19__ => match arg_19__ with | x => Mk_Pair x x end.

Local Definition instance_GHC_Base_Applicative_Pair_op_zlztzg__ : forall {a}
                                                                         {b},
                                                                    Pair (a -> b) -> Pair a -> Pair b :=
  fun {a} {b} =>
    fun arg_22__ arg_23__ =>
      match arg_22__ , arg_23__ with
        | Mk_Pair f g , Mk_Pair x y => Mk_Pair (f x) (g y)
      end.

Local Definition instance_GHC_Base_Functor_Pair_fmap : forall {a} {b},
                                                         (a -> b) -> Pair a -> Pair b :=
  fun {a} {b} =>
    fun arg_26__ arg_27__ =>
      match arg_26__ , arg_27__ with
        | f , Mk_Pair x y => Mk_Pair (f x) (f y)
      end.

Local Definition instance_GHC_Base_Functor_Pair_op_zlzd__ : forall {a} {b},
                                                              b -> Pair a -> Pair b :=
  fun {a} {b} => fun x => instance_GHC_Base_Functor_Pair_fmap (GHC.Base.const x).

Instance instance_GHC_Base_Functor_Pair : GHC.Base.Functor Pair := {
  fmap := fun {a} {b} => instance_GHC_Base_Functor_Pair_fmap ;
  op_zlzd__ := fun {a} {b} => instance_GHC_Base_Functor_Pair_op_zlzd__ }.

Local Definition instance_GHC_Base_Applicative_Pair_op_ztzg__ : forall {a} {b},
                                                                  Pair a -> Pair b -> Pair b :=
  fun {a} {b} =>
    fun x y =>
      instance_GHC_Base_Applicative_Pair_op_zlztzg__ (GHC.Base.fmap (GHC.Base.const
                                                                    GHC.Base.id) x) y.

Instance instance_GHC_Base_Applicative_Pair : GHC.Base.Applicative Pair := {
  op_zlztzg__ := fun {a} {b} => instance_GHC_Base_Applicative_Pair_op_zlztzg__ ;
  op_ztzg__ := fun {a} {b} => instance_GHC_Base_Applicative_Pair_op_ztzg__ ;
  pure := fun {a} => instance_GHC_Base_Applicative_Pair_pure }.

(* Unbound variables:
     * GHC.Base.Applicative GHC.Base.Functor GHC.Base.const GHC.Base.fmap GHC.Base.id
     pair
*)
