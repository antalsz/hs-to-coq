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

Local Definition instance_GHC_Base_Functor_Proxy_op_zlzd__ :
   forall {b} {a}, b -> Proxy a -> Proxy b :=
  fun {b} {a} => fun x => instance_GHC_Base_Functor_Proxy_fmap (GHC.Base.const x).

Instance instance_GHC_Base_Functor_Proxy : GHC.Base.Functor Proxy := fun _ k => k {|
  GHC.Base.fmap__ := @instance_GHC_Base_Functor_Proxy_fmap ;
  GHC.Base.op_zlzd____ := @instance_GHC_Base_Functor_Proxy_op_zlzd__  |}.


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

Instance instance_GHC_Base_Applicative_Proxy :
  GHC.Base.Applicative Proxy := fun _ k => k {|
  GHC.Base.op_zlztzg____ := @instance_GHC_Base_Applicative_Proxy_op_zlztzg__ ;
  GHC.Base.op_ztzg____ := @instance_GHC_Base_Applicative_Proxy_op_ztzg__ ;
  GHC.Base.pure__ := @instance_GHC_Base_Applicative_Proxy_pure |}.


Local Definition instance_GHC_Base_Monad_Proxy_return_ : forall {a},
                                                              a -> Proxy a :=
  fun {a} => GHC.Base.pure.

Local Definition instance_GHC_Base_Monad_Proxy_op_zgzgze__ : forall {a} {b},
                                                                  Proxy a -> (a -> Proxy b) -> Proxy b :=
  fun {a} {b} => fun arg_0__ arg_1__ => Mk_Proxy.

Local Definition instance_GHC_Base_Monad_Proxy_op_zgzg__ : forall {a} {b},
                                                                Proxy a -> Proxy b -> Proxy b :=
  fun {a} {b} => GHC.Base.op_ztzg__.

Instance instance_GHC_Base_Monad_Proxy : GHC.Base.Monad Proxy := fun _ k => k {|
  GHC.Base.op_zgzg____ := @instance_GHC_Base_Monad_Proxy_op_zgzg__ ;
  GHC.Base.op_zgzgze____ := @instance_GHC_Base_Monad_Proxy_op_zgzgze__ ;
  GHC.Base.return___ := @instance_GHC_Base_Monad_Proxy_return_ |}.

Instance instance_GHC_Base_Monoid__Proxy_s_ {s} : GHC.Base.Monoid (Proxy s) :=
  fun _ k => k {|
    GHC.Base.mempty__ := Mk_Proxy ;
    GHC.Base.mappend__ := fun _ _ => Mk_Proxy ;
    GHC.Base.mconcat__ := fun _ => Mk_Proxy|}.

Instance instance_GHC_Base_Bounded__Proxy_s_ {s} : GHC.Enum.Bounded (Proxy s) :=
  { maxBound := Mk_Proxy;
    minBound := Mk_Proxy }.

Instance instance_GHC_Base_Eq__Proxy_s_ {s} : GHC.Base.Eq_ (Proxy s) := fun _ k => k
  {| GHC.Base.op_zeze____ := fun _ _ => true;
     GHC.Base.op_zsze____ := fun _ _ => false |}.

Definition compare_Proxy {s} : Proxy s -> Proxy s -> comparison := fun _ _ => Eq.

Instance instance_GHC_Prim_Ord__Proxy_s_ {s} : GHC.Base.Ord (Proxy s) :=
  Base.ord_default compare_Proxy.
