(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Set Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Preamble *)


(* Converted imports: *)

Require GHC.Base.
Require GHC.Show.
Require GHC.Read.
Require Data.Type.Equality.
Require Coq.Lists.List.
Require GHC.Base.

(* Converted declarations: *)
(*
Inductive Either a b : Type := inl : a -> Either a b
                            |  inr : b -> Either a b.

Arguments inl {_} {_} _.

Arguments inr {_} {_} _.
*)
Definition rights {a} {b} : list (sum a b) -> list b :=
  fun arg_4__ =>
    match arg_4__ with
      | x => let cont_5__ arg_6__ :=
               match arg_6__ with
                 | (inr a) => cons a nil
                 | _ => nil
               end in
             Coq.Lists.List.flat_map cont_5__ x
    end.

Definition lefts {a} {b} : list (sum a b) -> list a :=
  fun arg_9__ =>
    match arg_9__ with
      | x => let cont_10__ arg_11__ :=
               match arg_11__ with
                 | (inl a) => cons a nil
                 | _ => nil
               end in
             Coq.Lists.List.flat_map cont_10__ x
    end.

Definition isRight {a} {b} : sum a b -> bool :=
  fun arg_0__ =>
    match arg_0__ with
      | (inl _) => false
      | (inr _) => true
    end.

Definition isLeft {a} {b} : sum a b -> bool :=
  fun arg_2__ =>
    match arg_2__ with
      | (inl _) => true
      | (inr _) => false
    end.

Definition either {a} {c} {b} : (a -> c) -> (b -> c) -> sum a b -> c :=
  fun arg_14__ arg_15__ arg_16__ =>
    match arg_14__ , arg_15__ , arg_16__ with
      | f , _ , (inl x) => f x
      | _ , g , (inr y) => g y
    end.

Definition partitionsums {a} {b} : list (sum a b) -> list a * list b :=
  let right :=
    fun arg_20__ arg_21__ =>
      match arg_20__ , arg_21__ with
        | a , (pair l r) => pair l (cons a r)
      end in
  let left :=
    fun arg_24__ arg_25__ =>
      match arg_24__ , arg_25__ with
        | a , (pair l r) => pair (cons a l) r
      end in
  GHC.Base.foldr (either left right) (pair nil nil).



Local Definition instance_GHC_Base_Functor__sum_a__fmap {e} : forall {a} {b},
                                                                  (a -> b) -> (sum e) a -> (sum e) b :=
  fun {a} {b} =>
    fun arg_39__ arg_40__ =>
      match arg_39__ , arg_40__ with
        | _ , (inl x) => inl x
        | f , (inr y) => inr (f y)
      end.

Local Definition instance_GHC_Base_Functor__sum_a__op_zlzd__ {e} : forall {a}
                                                                            {b},
                                                                       b -> (sum e) a -> (sum e) b :=
  fun {a} {b} =>
    fun x => instance_GHC_Base_Functor__sum_a__fmap (GHC.Base.const x).

Instance instance_GHC_Base_Functor__sum_a_  {e} : !GHC.Base.Functor (sum
                                                                        e) := {
  fmap := fun {a} {b} => instance_GHC_Base_Functor__sum_a__fmap ;
  op_zlzd__ := fun {a} {b} => instance_GHC_Base_Functor__sum_a__op_zlzd__ }.

(* Unbound variables:
     * Coq.Lists.List.flat_map GHC.Base.fmap GHC.Base.Applicative
     GHC.Base.Functor GHC.Base.Monad GHC.Base.const GHC.Base.fmap
     GHC.Base.foldr GHC.Base.id GHC.Base.op_ztzg__ GHC.Base.pure bool
     cons e false list nil pair true
*)


Local Definition instance_GHC_Base_Applicative__sum_e__pure {e} : forall {a},
                                                                      a -> (sum e) a :=
  fun {a} => inr.

Local Definition instance_GHC_Base_Applicative__sum_e__op_zlztzg__ {e}
    : forall {a} {b}, (sum e) (a -> b) -> (sum e) a -> (sum e) b :=
  fun {a} {b} =>
    fun arg_34__ arg_35__ =>
      match arg_34__ , arg_35__ with
        | (inl e) , _ => inl e
        | (inr f) , r => GHC.Base.fmap f r
      end.

Local Definition instance_GHC_Base_Applicative__sum_e__op_ztzg__ {e}
    : forall {a} {b}, (sum e) a -> (sum e) b -> (sum e) b :=
  fun {a} {b} =>
    fun x y =>
      instance_GHC_Base_Applicative__sum_e__op_zlztzg__ (GHC.Base.fmap
                                                              (GHC.Base.const GHC.Base.id) x) y.

Local Definition instance_GHC_Base_Applicative__sum_e__op_zlzt__ {e}
    : forall {a} {b}, (sum e) a -> (sum e) b -> (sum e) a :=
  fun {a} {b} =>
    fun x y =>
      instance_GHC_Base_Applicative__sum_e__op_zlztzg__ (GHC.Base.fmap
                                                              GHC.Base.const x) y.

Instance instance_GHC_Base_Applicative__sum_e_ {e} : !GHC.Base.Applicative
                                                       (sum e) := {
  op_zlzt__ := fun {a} {b} =>
    instance_GHC_Base_Applicative__sum_e__op_zlzt__ ;
  op_zlztzg__ := fun {a} {b} =>
    instance_GHC_Base_Applicative__sum_e__op_zlztzg__ ;
  op_ztzg__ := fun {a} {b} =>
    instance_GHC_Base_Applicative__sum_e__op_ztzg__ ;
  pure := fun {a} => instance_GHC_Base_Applicative__sum_e__pure }.



Local Definition instance_GHC_Base_Monad__sum_e__return_ {e} : forall {a},
                                                                   a -> (sum e) a :=
  fun {a} => GHC.Base.pure.

Local Definition instance_GHC_Base_Monad__sum_e__op_zgzgze__ {e} : forall {a}
                                                                            {b},
                                                                       (sum e) a -> (a -> (sum e) b) -> (sum e)
                                                                       b :=
  fun {a} {b} =>
    fun arg_29__ arg_30__ =>
      match arg_29__ , arg_30__ with
        | (inl l) , _ => inl l
        | (inr r) , k => k r
      end.

Local Definition instance_GHC_Base_Monad__sum_e__op_zgzg__ {e} : forall {a}
                                                                          {b},
                                                                     (sum e) a -> (sum e) b -> (sum e) b :=
  fun {a} {b} => GHC.Base.op_ztzg__.

Instance instance_GHC_Base_Monad__sum_e_ {e} : !GHC.Base.Monad (sum
                                                                    e) := {
  op_zgzg__ := fun {a} {b} => instance_GHC_Base_Monad__sum_e__op_zgzg__ ;
  op_zgzgze__ := fun {a} {b} =>
    instance_GHC_Base_Monad__sum_e__op_zgzgze__ ;
  return_ := fun {a} => instance_GHC_Base_Monad__sum_e__return_ }.
