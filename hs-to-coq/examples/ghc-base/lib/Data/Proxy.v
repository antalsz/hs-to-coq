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

Inductive Proxy (t : Type) : Type := Mk_Proxy : Proxy t.

Inductive KProxy (t : Type) : Type := Mk_KProxy : KProxy t.

Arguments Mk_Proxy {_}.

Arguments Mk_KProxy {_}.
(* Converted value declarations: *)

Local Definition instance_GHC_Base_Eq___Proxy_s__op_zeze__ {inst_s} : (Proxy
                                                                      inst_s) -> (Proxy inst_s) -> bool :=
  fun arg_12__ arg_13__ => true.

Local Definition instance_GHC_Base_Eq___Proxy_s__op_zsze__ {inst_s} : (Proxy
                                                                      inst_s) -> (Proxy inst_s) -> bool :=
  fun x y => negb (instance_GHC_Base_Eq___Proxy_s__op_zeze__ x y).

Instance instance_GHC_Base_Eq___Proxy_s_ {s} : GHC.Base.Eq_ (Proxy s) := fun _
                                                                             k =>
    k (GHC.Base.Eq___Dict_Build (Proxy s) instance_GHC_Base_Eq___Proxy_s__op_zeze__
                                instance_GHC_Base_Eq___Proxy_s__op_zsze__).

Local Definition instance_GHC_Base_Ord__Proxy_s__compare {inst_s} : (Proxy
                                                                    inst_s) -> (Proxy inst_s) -> comparison :=
  fun arg_10__ arg_11__ => Eq.

Local Definition instance_GHC_Base_Ord__Proxy_s__op_zg__ {inst_s} : (Proxy
                                                                    inst_s) -> (Proxy inst_s) -> bool :=
  fun x y => op_zeze__ (instance_GHC_Base_Ord__Proxy_s__compare x y) Gt.

Local Definition instance_GHC_Base_Ord__Proxy_s__op_zgze__ {inst_s} : (Proxy
                                                                      inst_s) -> (Proxy inst_s) -> bool :=
  fun x y => op_zsze__ (instance_GHC_Base_Ord__Proxy_s__compare x y) Lt.

Local Definition instance_GHC_Base_Ord__Proxy_s__op_zl__ {inst_s} : (Proxy
                                                                    inst_s) -> (Proxy inst_s) -> bool :=
  fun x y => op_zeze__ (instance_GHC_Base_Ord__Proxy_s__compare x y) Lt.

Local Definition instance_GHC_Base_Ord__Proxy_s__op_zlze__ {inst_s} : (Proxy
                                                                      inst_s) -> (Proxy inst_s) -> bool :=
  fun x y => op_zsze__ (instance_GHC_Base_Ord__Proxy_s__compare x y) Gt.

Local Definition instance_GHC_Base_Ord__Proxy_s__max {inst_s} : (Proxy
                                                                inst_s) -> (Proxy inst_s) -> (Proxy inst_s) :=
  fun x y =>
    if instance_GHC_Base_Ord__Proxy_s__op_zlze__ x y : bool
    then y
    else x.

Local Definition instance_GHC_Base_Ord__Proxy_s__min {inst_s} : (Proxy
                                                                inst_s) -> (Proxy inst_s) -> (Proxy inst_s) :=
  fun x y =>
    if instance_GHC_Base_Ord__Proxy_s__op_zlze__ x y : bool
    then x
    else y.

Instance instance_GHC_Base_Ord__Proxy_s_ {s} : GHC.Base.Ord (Proxy s) := fun _
                                                                             k =>
    k (GHC.Base.Ord__Dict_Build (Proxy s) instance_GHC_Base_Ord__Proxy_s__op_zl__
                                instance_GHC_Base_Ord__Proxy_s__op_zlze__
                                instance_GHC_Base_Ord__Proxy_s__op_zg__
                                instance_GHC_Base_Ord__Proxy_s__op_zgze__
                                instance_GHC_Base_Ord__Proxy_s__compare instance_GHC_Base_Ord__Proxy_s__max
                                instance_GHC_Base_Ord__Proxy_s__min).

(* Translating `instance forall {s}, GHC.Show.Show (Proxy s)' failed: OOPS!
   Cannot find information for class "GHC.Show.Show" unsupported *)

(* Translating `instance forall {s}, GHC.Read.Read (Proxy s)' failed: OOPS!
   Cannot find information for class "GHC.Read.Read" unsupported *)

(* Translating `instance forall {s}, GHC.Enum.Enum (Proxy s)' failed: OOPS!
   Cannot find information for class "GHC.Enum.Enum" unsupported *)

(* Translating `instance forall {s}, GHC.Arr.Ix (Proxy s)' failed: OOPS! Cannot
   find information for class "GHC.Arr.Ix" unsupported *)

(* Translating `instance forall {s}, GHC.Enum.Bounded (Proxy s)' failed: OOPS!
   Cannot find information for class "GHC.Enum.Bounded" unsupported *)

Local Definition instance_GHC_Base_Monoid__Proxy_s__mappend {inst_s} : (Proxy
                                                                       inst_s) -> (Proxy inst_s) -> (Proxy inst_s) :=
  fun arg_7__ arg_8__ => Mk_Proxy.

Local Definition instance_GHC_Base_Monoid__Proxy_s__mconcat {inst_s} : list
                                                                       (Proxy inst_s) -> (Proxy inst_s) :=
  fun arg_9__ => Mk_Proxy.

Local Definition instance_GHC_Base_Monoid__Proxy_s__mempty {inst_s} : (Proxy
                                                                      inst_s) :=
  Mk_Proxy.

Instance instance_GHC_Base_Monoid__Proxy_s_ {s} : GHC.Base.Monoid (Proxy s) :=
  fun _ k =>
    k (GHC.Base.Monoid__Dict_Build (Proxy s)
                                   instance_GHC_Base_Monoid__Proxy_s__mappend
                                   instance_GHC_Base_Monoid__Proxy_s__mconcat
                                   instance_GHC_Base_Monoid__Proxy_s__mempty).

Local Definition instance_GHC_Base_Functor_Proxy_fmap : forall {a} {b},
                                                          (a -> b) -> Proxy a -> Proxy b :=
  fun {a} {b} => fun arg_5__ arg_6__ => Mk_Proxy.

Local Definition instance_GHC_Base_Functor_Proxy_op_zlzd__ : forall {a} {b},
                                                               a -> Proxy b -> Proxy a :=
  fun {a} {b} => fun x => instance_GHC_Base_Functor_Proxy_fmap (GHC.Base.const x).

Instance instance_GHC_Base_Functor_Proxy : GHC.Base.Functor Proxy := fun _ k =>
    k (GHC.Base.Functor__Dict_Build Proxy (fun {a} {b} =>
                                      instance_GHC_Base_Functor_Proxy_op_zlzd__) (fun {a} {b} =>
                                      instance_GHC_Base_Functor_Proxy_fmap)).

Local Definition instance_GHC_Base_Applicative_Proxy_op_zlztzg__ : forall {a}
                                                                          {b},
                                                                     Proxy (a -> b) -> Proxy a -> Proxy b :=
  fun {a} {b} => fun arg_3__ arg_4__ => Mk_Proxy.

Local Definition instance_GHC_Base_Applicative_Proxy_op_ztzg__ : forall {a} {b},
                                                                   Proxy a -> Proxy b -> Proxy b :=
  fun {a} {b} =>
    fun x y =>
      instance_GHC_Base_Applicative_Proxy_op_zlztzg__ (GHC.Base.fmap (GHC.Base.const
                                                                     GHC.Base.id) x) y.

Local Definition instance_GHC_Base_Applicative_Proxy_pure : forall {a},
                                                              a -> Proxy a :=
  fun {a} => fun arg_2__ => Mk_Proxy.

Instance instance_GHC_Base_Applicative_Proxy : GHC.Base.Applicative Proxy :=
  fun _ k =>
    k (GHC.Base.Applicative__Dict_Build Proxy (fun {a} {b} =>
                                          instance_GHC_Base_Applicative_Proxy_op_ztzg__) (fun {a} {b} =>
                                          instance_GHC_Base_Applicative_Proxy_op_zlztzg__) (fun {a} =>
                                          instance_GHC_Base_Applicative_Proxy_pure)).

(* Translating `instance GHC.Base.Alternative Proxy' failed: OOPS! Cannot find
   information for class "GHC.Base.Alternative" unsupported *)

Local Definition instance_GHC_Base_Monad_Proxy_op_zgzg__ : forall {a} {b},
                                                             Proxy a -> Proxy b -> Proxy b :=
  fun {a} {b} => GHC.Base.op_ztzg__.

Local Definition instance_GHC_Base_Monad_Proxy_op_zgzgze__ : forall {a} {b},
                                                               Proxy a -> (a -> Proxy b) -> Proxy b :=
  fun {a} {b} => fun arg_0__ arg_1__ => Mk_Proxy.

Local Definition instance_GHC_Base_Monad_Proxy_return_ : forall {a},
                                                           a -> Proxy a :=
  fun {a} => GHC.Base.pure.

Instance instance_GHC_Base_Monad_Proxy : GHC.Base.Monad Proxy := fun _ k =>
    k (GHC.Base.Monad__Dict_Build Proxy (fun {a} {b} =>
                                    instance_GHC_Base_Monad_Proxy_op_zgzg__) (fun {a} {b} =>
                                    instance_GHC_Base_Monad_Proxy_op_zgzgze__) (fun {a} =>
                                    instance_GHC_Base_Monad_Proxy_return_)).

(* Translating `instance GHC.Base.MonadPlus Proxy' failed: OOPS! Cannot find
   information for class "GHC.Base.MonadPlus" unsupported *)

Definition asProxyTypeOf {a} : a -> Proxy a -> a :=
  GHC.Base.const.

(* Unbound variables:
     Eq GHC.Base.Applicative GHC.Base.Applicative__Dict_Build GHC.Base.Eq_
     GHC.Base.Eq___Dict_Build GHC.Base.Functor GHC.Base.Functor__Dict_Build
     GHC.Base.Monad GHC.Base.Monad__Dict_Build GHC.Base.Monoid
     GHC.Base.Monoid__Dict_Build GHC.Base.Ord GHC.Base.Ord__Dict_Build GHC.Base.const
     GHC.Base.fmap GHC.Base.id GHC.Base.op_ztzg__ GHC.Base.pure Gt Lt Type bool
     comparison list negb op_zeze__ op_zsze__ true
*)
