(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Set Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Preamble *)

(*
skipped instances

instance_GHC_Base_Alternative_Proxy
instance_GHC_Base_MonadPlus_Proxy
instance_GHC_Arr_Ix__Proxy_s_
instance_GHC_Read_Read__Proxy_s_
Instance instance_GHC_Show_Show__Proxy_s_

instance_GHC_Enum_Enum__Proxy_s_

manually crafted instances
- monoid/bounded

*)

(* Converted imports: *)

Require GHC.Base.
Require GHC.Enum.

(* Converted declarations: *)

(* Translating `instance GHC.Base.Eq_ (Proxy s)' failed: OOPS! Cannot construct
   types for this class def: Nothing unsupported *)

(* Translating `instance GHC.Base.Ord (Proxy s)' failed: OOPS! Cannot construct
   types for this class def: Nothing unsupported *)

(* Translating `instance GHC.Show.Show (Proxy s)' failed: OOPS! Cannot construct
   types for this class def: Nothing unsupported *)

(* Translating `instance GHC.Read.Read (Proxy s)' failed: OOPS! Cannot construct
   types for this class def: Nothing unsupported *)

(* Translating `instance GHC.Enum.Enum (Proxy s)' failed: OOPS! Cannot construct
   types for this class def: Nothing unsupported *)

(* Translating `instance GHC.Arr.Ix (Proxy s)' failed: OOPS! Cannot construct
   types for this class def: Nothing unsupported *)

(* Translating `instance GHC.Enum.Bounded (Proxy s)' failed: OOPS! Cannot
   construct types for this class def: Nothing unsupported *)

(* Translating `instance GHC.Base.Monoid (Proxy s)' failed: OOPS! Cannot
   construct types for this class def: Nothing unsupported *)

(* Translating `instance GHC.Base.Alternative Proxy' failed: OOPS! Cannot
   construct types for this class def: Nothing unsupported *)

Inductive KProxy (t : Type) : Type := Mk_KProxy : KProxy t.

Arguments Mk_KProxy {_}.

Inductive Proxy (t : Type) : Type := Mk_Proxy : Proxy t.

Arguments Mk_Proxy {_}.

Definition asProxyTypeOf {a} : a -> Proxy a -> a :=
  GHC.Base.const.

Local Definition instance_GHC_Base_Functor_Proxy_fmap : forall {a} {b},
                                                             (a -> b) -> Proxy a -> Proxy b :=
  fun {a} {b} => fun arg_5__ arg_6__ => Mk_Proxy.

Local Definition instance_GHC_Base_Functor_Proxy_op_zlzd__ : forall {a} {b},
                                                                  b -> Proxy a -> Proxy b :=
  fun {a} {b} =>
    fun x => instance_GHC_Base_Functor_Proxy_fmap (GHC.Base.const x).

Instance instance_GHC_Base_Functor_Proxy : !GHC.Base.Functor Proxy := {
  fmap := fun {a} {b} => instance_GHC_Base_Functor_Proxy_fmap ;
  op_zlzd__ := fun {a} {b} => instance_GHC_Base_Functor_Proxy_op_zlzd__ }.


Local Definition instance_GHC_Base_Applicative_Proxy_pure : forall {a},
                                                                 a -> Proxy a :=
  fun {a} => fun arg_2__ => Mk_Proxy.

Local Definition instance_GHC_Base_Applicative_Proxy_op_zlztzg__ : forall {a}
                                                                             {b},
                                                                        Proxy (a -> b) -> Proxy a -> Proxy b :=
  fun {a} {b} => fun arg_3__ arg_4__ => Mk_Proxy.

Local Definition instance_GHC_Base_Applicative_Proxy_op_ztzg__ : forall {a}
                                                                           {b},
                                                                      Proxy a -> Proxy b -> Proxy b :=
  fun {a} {b} =>
    fun x y =>
      instance_GHC_Base_Applicative_Proxy_op_zlztzg__ (GHC.Base.fmap
                                                         (GHC.Base.const GHC.Base.id) x) y.

Local Definition instance_GHC_Base_Applicative_Proxy_op_zlzt__ : forall {a}
                                                                           {b},
                                                                      Proxy a -> Proxy b -> Proxy a :=
  fun {a} {b} =>
    fun x y =>
      instance_GHC_Base_Applicative_Proxy_op_zlztzg__ (GHC.Base.fmap
                                                         GHC.Base.const x) y.

Instance instance_GHC_Base_Applicative_Proxy : !GHC.Base.Applicative
                                                  Proxy := {
  op_zlzt__ := fun {a} {b} => instance_GHC_Base_Applicative_Proxy_op_zlzt__ ;
  op_zlztzg__ := fun {a} {b} =>
    instance_GHC_Base_Applicative_Proxy_op_zlztzg__ ;
  op_ztzg__ := fun {a} {b} => instance_GHC_Base_Applicative_Proxy_op_ztzg__ ;
  pure := fun {a} => instance_GHC_Base_Applicative_Proxy_pure }.


Local Definition instance_GHC_Base_Monad_Proxy_return_ : forall {a},
                                                              a -> Proxy a :=
  fun {a} => GHC.Base.pure.

Local Definition instance_GHC_Base_Monad_Proxy_op_zgzgze__ : forall {a} {b},
                                                                  Proxy a -> (a -> Proxy b) -> Proxy b :=
  fun {a} {b} => fun arg_0__ arg_1__ => Mk_Proxy.

Local Definition instance_GHC_Base_Monad_Proxy_op_zgzg__ : forall {a} {b},
                                                                Proxy a -> Proxy b -> Proxy b :=
  fun {a} {b} => GHC.Base.op_ztzg__.

Instance instance_GHC_Base_Monad_Proxy : !GHC.Base.Monad Proxy := {
  op_zgzg__ := fun {a} {b} => instance_GHC_Base_Monad_Proxy_op_zgzg__ ;
  op_zgzgze__ := fun {a} {b} => instance_GHC_Base_Monad_Proxy_op_zgzgze__ ;
  return_ := fun {a} => instance_GHC_Base_Monad_Proxy_return_ }.

Instance instance_GHC_Base_Monoid__Proxy_s_ : !GHC.Base.Monoid (Proxy
                                                                     s) := {}.
Proof.
  split. intros. apply Mk_Proxy. apply Mk_Proxy.
Defined.

Instance instance_GHC_Enum_Bounded__Proxy_s_ : !GHC.Enum.Bounded (Proxy s) :=
  {}.
Proof.
  split. apply Mk_Proxy.
Defined.

Instance instance_GHC_Base_Eq___Proxy_s_ : !GHC.Base.Eq_ (Proxy s) := {}.
Proof.
  - intros. exact false.
  - intros. exact true.
Defined.

Definition compare_Proxy {s} : Proxy s -> Proxy s -> comparison := fun _ _ => Eq.

Instance instance_GHC_Prim_Ord__Proxy_s_ {s} : !GHC.Base.Ord (Proxy s) :=
  Base.ord_default compare_Proxy.
