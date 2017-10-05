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
Require GHC.Enum.
Require GHC.Arr.
Require GHC.BaseGen.
Require GHC.Prim.

(* Converted declarations: *)

(* Translating `instance GHC.Prim.Eq_ (Proxy s)' failed: OOPS! Cannot construct
   types for this class def: Nothing unsupported *)

(* Translating `instance GHC.Prim.Ord (Proxy s)' failed: OOPS! Cannot construct
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

(* Translating `instance GHC.BaseGen.Monoid (Proxy s)' failed: OOPS! Cannot
   construct types for this class def: Nothing unsupported *)

(* Translating `instance GHC.BaseGen.Alternative Proxy' failed: OOPS! Cannot
   construct types for this class def: Nothing unsupported *)

Inductive KProxy (t : Type) : Type := Mk_KProxy : KProxy t.

Arguments Mk_KProxy {_}.

Inductive Proxy (t : Type) : Type := Mk_Proxy : Proxy t.

Arguments Mk_Proxy {_}.

Definition asProxyTypeOf {a} : a -> Proxy a -> a :=
  GHC.BaseGen.const.

Local Definition instance_GHC_BaseGen_Functor_Proxy_fmap : forall {a} {b},
                                                             (a -> b) -> Proxy a -> Proxy b :=
  fun {a} {b} => fun arg_5__ arg_6__ => Mk_Proxy.

Local Definition instance_GHC_BaseGen_Functor_Proxy_op_zlzd__ : forall {a} {b},
                                                                  b -> Proxy a -> Proxy b :=
  fun {a} {b} =>
    fun x => instance_GHC_BaseGen_Functor_Proxy_fmap (GHC.BaseGen.const x).

Instance instance_GHC_BaseGen_Functor_Proxy : !GHC.BaseGen.Functor Proxy := {
  fmap := fun {a} {b} => instance_GHC_BaseGen_Functor_Proxy_fmap ;
  op_zlzd__ := fun {a} {b} => instance_GHC_BaseGen_Functor_Proxy_op_zlzd__ }.


Local Definition instance_GHC_BaseGen_Applicative_Proxy_pure : forall {a},
                                                                 a -> Proxy a :=
  fun {a} => fun arg_2__ => Mk_Proxy.

Local Definition instance_GHC_BaseGen_Applicative_Proxy_op_zlztzg__ : forall {a}
                                                                             {b},
                                                                        Proxy (a -> b) -> Proxy a -> Proxy b :=
  fun {a} {b} => fun arg_3__ arg_4__ => Mk_Proxy.

Local Definition instance_GHC_BaseGen_Applicative_Proxy_op_ztzg__ : forall {a}
                                                                           {b},
                                                                      Proxy a -> Proxy b -> Proxy b :=
  fun {a} {b} =>
    fun x y =>
      instance_GHC_BaseGen_Applicative_Proxy_op_zlztzg__ (GHC.BaseGen.fmap
                                                         (GHC.BaseGen.const GHC.BaseGen.id) x) y.

Local Definition instance_GHC_BaseGen_Applicative_Proxy_op_zlzt__ : forall {a}
                                                                           {b},
                                                                      Proxy a -> Proxy b -> Proxy a :=
  fun {a} {b} =>
    fun x y =>
      instance_GHC_BaseGen_Applicative_Proxy_op_zlztzg__ (GHC.BaseGen.fmap
                                                         GHC.BaseGen.const x) y.

Instance instance_GHC_BaseGen_Applicative_Proxy : !GHC.BaseGen.Applicative
                                                  Proxy := {
  op_zlzt__ := fun {a} {b} => instance_GHC_BaseGen_Applicative_Proxy_op_zlzt__ ;
  op_zlztzg__ := fun {a} {b} =>
    instance_GHC_BaseGen_Applicative_Proxy_op_zlztzg__ ;
  op_ztzg__ := fun {a} {b} => instance_GHC_BaseGen_Applicative_Proxy_op_ztzg__ ;
  pure := fun {a} => instance_GHC_BaseGen_Applicative_Proxy_pure }.


Local Definition instance_GHC_BaseGen_Monad_Proxy_return_ : forall {a},
                                                              a -> Proxy a :=
  fun {a} => GHC.BaseGen.pure.

Local Definition instance_GHC_BaseGen_Monad_Proxy_op_zgzgze__ : forall {a} {b},
                                                                  Proxy a -> (a -> Proxy b) -> Proxy b :=
  fun {a} {b} => fun arg_0__ arg_1__ => Mk_Proxy.

Local Definition instance_GHC_BaseGen_Monad_Proxy_op_zgzg__ : forall {a} {b},
                                                                Proxy a -> Proxy b -> Proxy b :=
  fun {a} {b} => GHC.BaseGen.op_ztzg__.

Instance instance_GHC_BaseGen_Monad_Proxy : !GHC.BaseGen.Monad Proxy := {
  op_zgzg__ := fun {a} {b} => instance_GHC_BaseGen_Monad_Proxy_op_zgzg__ ;
  op_zgzgze__ := fun {a} {b} => instance_GHC_BaseGen_Monad_Proxy_op_zgzgze__ ;
  return_ := fun {a} => instance_GHC_BaseGen_Monad_Proxy_return_ }.

Instance instance_GHC_BaseGen_Alternative_Proxy : !GHC.BaseGen.Alternative
                                                  Proxy := {}.
Proof.
Admitted.

Instance instance_GHC_Base_MonadPlus_Proxy : !GHC.BaseGen.MonadPlus Proxy := {}.


Instance instance_GHC_BaseGen_Monoid__Proxy_s_ : !GHC.BaseGen.Monoid (Proxy
                                                                     s) := {}.
Proof.
Admitted.

Instance instance_GHC_Enum_Bounded__Proxy_s_ : !GHC.Enum.Bounded (Proxy s) :=
  {}.
Proof.
Admitted.

(*
Instance instance_GHC_Arr_Ix__Proxy_s_ : !GHC.Arr.Ix (Proxy s) := {}.
Proof.
Admitted. *)

Instance instance_GHC_Enum_Enum__Proxy_s_ : !GHC.Enum.Enum (Proxy s) := {}.
Proof.
Admitted.

(*
Instance instance_GHC_Read_Read__Proxy_s_ : !GHC.Read.Read (Proxy s) := {}.
Proof.
Admitted.

Instance instance_GHC_Show_Show__Proxy_s_ : !GHC.Show.Show (Proxy s) := {}.
Proof.
Admitted. *)

Instance instance_GHC_Prim_Eq___Proxy_s_ : !GHC.Prim.Eq_ (Proxy s) := {}.
Proof.
Admitted.


Instance instance_GHC_Prim_Ord__Proxy_s_ : !GHC.Prim.Ord (Proxy s) := {}.
Proof.
Admitted.


(* Unbound variables:
     GHC.Arr.Ix GHC.Base.MonadPlus GHC.BaseGen.Alternative GHC.BaseGen.Applicative
     GHC.BaseGen.Functor GHC.BaseGen.Monad GHC.BaseGen.Monoid GHC.BaseGen.const
     GHC.BaseGen.fmap GHC.BaseGen.id GHC.BaseGen.op_ztzg__ GHC.BaseGen.pure
     GHC.Enum.Bounded GHC.Enum.Enum GHC.Prim.Eq_ GHC.Prim.Ord GHC.Read.Read
     GHC.Show.Show Type s
*)
