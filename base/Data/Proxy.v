(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Coq.Program.Tactics.
Require Coq.Program.Wf.

(* Preamble *)

Require Import GHC.Base.

(* Converted imports: *)

Require GHC.Base.
Import GHC.Base.Notations.

(* Converted type declarations: *)

Inductive Proxy (t : Type) : Type := Mk_Proxy : Proxy t.

Inductive KProxy (t : Type) : Type := Mk_KProxy : KProxy t.

Arguments Mk_Proxy {_}.

Arguments Mk_KProxy {_}.
(* Converted value declarations: *)

Local Definition instance_GHC_Base_Eq___Data_Proxy_Proxy_s__op_zeze__ {inst_s}
    : (Proxy inst_s) -> (Proxy inst_s) -> bool :=
  fun arg_12__ arg_13__ => true.

Local Definition instance_GHC_Base_Eq___Data_Proxy_Proxy_s__op_zsze__ {inst_s}
    : (Proxy inst_s) -> (Proxy inst_s) -> bool :=
  fun x y => negb (instance_GHC_Base_Eq___Data_Proxy_Proxy_s__op_zeze__ x y).

Program Instance instance_GHC_Base_Eq___Data_Proxy_Proxy_s_ {s} : GHC.Base.Eq_
                                                                  (Proxy s) := fun _ k =>
    k
    {|GHC.Base.op_zeze____ := instance_GHC_Base_Eq___Data_Proxy_Proxy_s__op_zeze__ ;
    GHC.Base.op_zsze____ := instance_GHC_Base_Eq___Data_Proxy_Proxy_s__op_zsze__ |}.

Local Definition instance_GHC_Base_Ord__Data_Proxy_Proxy_s__compare {inst_s}
    : (Proxy inst_s) -> (Proxy inst_s) -> comparison :=
  fun arg_10__ arg_11__ => Eq.

Local Definition instance_GHC_Base_Ord__Data_Proxy_Proxy_s__op_zg__ {inst_s}
    : (Proxy inst_s) -> (Proxy inst_s) -> bool :=
  fun x y =>
    _GHC.Base.==_ (instance_GHC_Base_Ord__Data_Proxy_Proxy_s__compare x y) Gt.

Local Definition instance_GHC_Base_Ord__Data_Proxy_Proxy_s__op_zgze__ {inst_s}
    : (Proxy inst_s) -> (Proxy inst_s) -> bool :=
  fun x y =>
    _GHC.Base./=_ (instance_GHC_Base_Ord__Data_Proxy_Proxy_s__compare x y) Lt.

Local Definition instance_GHC_Base_Ord__Data_Proxy_Proxy_s__op_zl__ {inst_s}
    : (Proxy inst_s) -> (Proxy inst_s) -> bool :=
  fun x y =>
    _GHC.Base.==_ (instance_GHC_Base_Ord__Data_Proxy_Proxy_s__compare x y) Lt.

Local Definition instance_GHC_Base_Ord__Data_Proxy_Proxy_s__op_zlze__ {inst_s}
    : (Proxy inst_s) -> (Proxy inst_s) -> bool :=
  fun x y =>
    _GHC.Base./=_ (instance_GHC_Base_Ord__Data_Proxy_Proxy_s__compare x y) Gt.

Local Definition instance_GHC_Base_Ord__Data_Proxy_Proxy_s__max {inst_s}
    : (Proxy inst_s) -> (Proxy inst_s) -> (Proxy inst_s) :=
  fun x y =>
    if instance_GHC_Base_Ord__Data_Proxy_Proxy_s__op_zlze__ x y : bool
    then y
    else x.

Local Definition instance_GHC_Base_Ord__Data_Proxy_Proxy_s__min {inst_s}
    : (Proxy inst_s) -> (Proxy inst_s) -> (Proxy inst_s) :=
  fun x y =>
    if instance_GHC_Base_Ord__Data_Proxy_Proxy_s__op_zlze__ x y : bool
    then x
    else y.

Program Instance instance_GHC_Base_Ord__Data_Proxy_Proxy_s_ {s} : GHC.Base.Ord
                                                                  (Proxy s) := fun _ k =>
    k {|GHC.Base.op_zl____ := instance_GHC_Base_Ord__Data_Proxy_Proxy_s__op_zl__ ;
      GHC.Base.op_zlze____ := instance_GHC_Base_Ord__Data_Proxy_Proxy_s__op_zlze__ ;
      GHC.Base.op_zg____ := instance_GHC_Base_Ord__Data_Proxy_Proxy_s__op_zg__ ;
      GHC.Base.op_zgze____ := instance_GHC_Base_Ord__Data_Proxy_Proxy_s__op_zgze__ ;
      GHC.Base.compare__ := instance_GHC_Base_Ord__Data_Proxy_Proxy_s__compare ;
      GHC.Base.max__ := instance_GHC_Base_Ord__Data_Proxy_Proxy_s__max ;
      GHC.Base.min__ := instance_GHC_Base_Ord__Data_Proxy_Proxy_s__min |}.

(* Translating `instance forall {s}, GHC.Show.Show (Data.Proxy.Proxy s)' failed:
   OOPS! Cannot find information for class Qualified "GHC.Show" "Show"
   unsupported *)

(* Translating `instance forall {s}, GHC.Read.Read (Data.Proxy.Proxy s)' failed:
   OOPS! Cannot find information for class Qualified "GHC.Read" "Read"
   unsupported *)

(* Translating `instance forall {s}, GHC.Enum.Enum (Data.Proxy.Proxy s)' failed:
   OOPS! Cannot find information for class Qualified "GHC.Enum" "Enum"
   unsupported *)

(* Translating `instance forall {s}, GHC.Arr.Ix (Data.Proxy.Proxy s)' failed:
   OOPS! Cannot find information for class Qualified "GHC.Arr" "Ix" unsupported *)

(* Translating `instance forall {s}, GHC.Enum.Bounded (Data.Proxy.Proxy s)'
   failed: OOPS! Cannot find information for class Qualified "GHC.Enum" "Bounded"
   unsupported *)

Local Definition instance_GHC_Base_Monoid__Data_Proxy_Proxy_s__mappend {inst_s}
    : (Proxy inst_s) -> (Proxy inst_s) -> (Proxy inst_s) :=
  fun arg_7__ arg_8__ => Mk_Proxy.

Local Definition instance_GHC_Base_Monoid__Data_Proxy_Proxy_s__mconcat {inst_s}
    : list (Proxy inst_s) -> (Proxy inst_s) :=
  fun arg_9__ => Mk_Proxy.

Local Definition instance_GHC_Base_Monoid__Data_Proxy_Proxy_s__mempty {inst_s}
    : (Proxy inst_s) :=
  Mk_Proxy.

Program Instance instance_GHC_Base_Monoid__Data_Proxy_Proxy_s_ {s}
  : GHC.Base.Monoid (Proxy s) := fun _ k =>
    k
    {|GHC.Base.mappend__ := instance_GHC_Base_Monoid__Data_Proxy_Proxy_s__mappend ;
    GHC.Base.mconcat__ := instance_GHC_Base_Monoid__Data_Proxy_Proxy_s__mconcat ;
    GHC.Base.mempty__ := instance_GHC_Base_Monoid__Data_Proxy_Proxy_s__mempty |}.

Local Definition instance_GHC_Base_Functor_Data_Proxy_Proxy_fmap : forall {a}
                                                                          {b},
                                                                     (a -> b) -> Proxy a -> Proxy b :=
  fun {a} {b} => fun arg_5__ arg_6__ => Mk_Proxy.

Local Definition instance_GHC_Base_Functor_Data_Proxy_Proxy_op_zlzd__
    : forall {a} {b}, a -> Proxy b -> Proxy a :=
  fun {a} {b} =>
    fun x => instance_GHC_Base_Functor_Data_Proxy_Proxy_fmap (GHC.Base.const x).

Program Instance instance_GHC_Base_Functor_Data_Proxy_Proxy : GHC.Base.Functor
                                                              Proxy := fun _ k =>
    k {|GHC.Base.op_zlzd____ := fun {a} {b} =>
        instance_GHC_Base_Functor_Data_Proxy_Proxy_op_zlzd__ ;
      GHC.Base.fmap__ := fun {a} {b} =>
        instance_GHC_Base_Functor_Data_Proxy_Proxy_fmap |}.

Local Definition instance_GHC_Base_Applicative_Data_Proxy_Proxy_op_zlztzg__
    : forall {a} {b}, Proxy (a -> b) -> Proxy a -> Proxy b :=
  fun {a} {b} => fun arg_3__ arg_4__ => Mk_Proxy.

Local Definition instance_GHC_Base_Applicative_Data_Proxy_Proxy_op_ztzg__
    : forall {a} {b}, Proxy a -> Proxy b -> Proxy b :=
  fun {a} {b} =>
    fun x y =>
      instance_GHC_Base_Applicative_Data_Proxy_Proxy_op_zlztzg__ (GHC.Base.fmap
                                                                 (GHC.Base.const GHC.Base.id) x) y.

Local Definition instance_GHC_Base_Applicative_Data_Proxy_Proxy_pure
    : forall {a}, a -> Proxy a :=
  fun {a} => fun arg_2__ => Mk_Proxy.

Program Instance instance_GHC_Base_Applicative_Data_Proxy_Proxy
  : GHC.Base.Applicative Proxy := fun _ k =>
    k {|GHC.Base.op_ztzg____ := fun {a} {b} =>
        instance_GHC_Base_Applicative_Data_Proxy_Proxy_op_ztzg__ ;
      GHC.Base.op_zlztzg____ := fun {a} {b} =>
        instance_GHC_Base_Applicative_Data_Proxy_Proxy_op_zlztzg__ ;
      GHC.Base.pure__ := fun {a} =>
        instance_GHC_Base_Applicative_Data_Proxy_Proxy_pure |}.

(* Translating `instance GHC.Base.Alternative Data.Proxy.Proxy' failed: OOPS!
   Cannot find information for class Qualified "GHC.Base" "Alternative"
   unsupported *)

Local Definition instance_GHC_Base_Monad_Data_Proxy_Proxy_op_zgzg__ : forall {a}
                                                                             {b},
                                                                        Proxy a -> Proxy b -> Proxy b :=
  fun {a} {b} => _GHC.Base.*>_.

Local Definition instance_GHC_Base_Monad_Data_Proxy_Proxy_op_zgzgze__
    : forall {a} {b}, Proxy a -> (a -> Proxy b) -> Proxy b :=
  fun {a} {b} => fun arg_0__ arg_1__ => Mk_Proxy.

Local Definition instance_GHC_Base_Monad_Data_Proxy_Proxy_return_ : forall {a},
                                                                      a -> Proxy a :=
  fun {a} => GHC.Base.pure.

Program Instance instance_GHC_Base_Monad_Data_Proxy_Proxy : GHC.Base.Monad
                                                            Proxy := fun _ k =>
    k {|GHC.Base.op_zgzg____ := fun {a} {b} =>
        instance_GHC_Base_Monad_Data_Proxy_Proxy_op_zgzg__ ;
      GHC.Base.op_zgzgze____ := fun {a} {b} =>
        instance_GHC_Base_Monad_Data_Proxy_Proxy_op_zgzgze__ ;
      GHC.Base.return___ := fun {a} =>
        instance_GHC_Base_Monad_Data_Proxy_Proxy_return_ |}.

(* Translating `instance GHC.Base.MonadPlus Data.Proxy.Proxy' failed: OOPS!
   Cannot find information for class Qualified "GHC.Base" "MonadPlus"
   unsupported *)

Definition asProxyTypeOf {a} : a -> Proxy a -> a :=
  GHC.Base.const.

(* Unbound variables:
     Eq Gt Lt Type bool comparison list negb true GHC.Base.Applicative GHC.Base.Eq_
     GHC.Base.Functor GHC.Base.Monad GHC.Base.Monoid GHC.Base.Ord GHC.Base.const
     GHC.Base.fmap GHC.Base.id GHC.Base.op_zeze__ GHC.Base.op_zsze__
     GHC.Base.op_ztzg__ GHC.Base.pure
*)
