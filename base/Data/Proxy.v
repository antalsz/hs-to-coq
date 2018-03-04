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

Local Definition Eq___Proxy_op_zeze__ {inst_s}
   : (Proxy inst_s) -> (Proxy inst_s) -> bool :=
  fun arg_0__ arg_1__ => true.

Local Definition Eq___Proxy_op_zsze__ {inst_s}
   : (Proxy inst_s) -> (Proxy inst_s) -> bool :=
  fun x y => negb (Eq___Proxy_op_zeze__ x y).

Program Instance Eq___Proxy {s} : GHC.Base.Eq_ (Proxy s) :=
  fun _ k =>
    k {| GHC.Base.op_zeze____ := Eq___Proxy_op_zeze__ ;
         GHC.Base.op_zsze____ := Eq___Proxy_op_zsze__ |}.

Local Definition Ord__Proxy_compare {inst_s}
   : (Proxy inst_s) -> (Proxy inst_s) -> comparison :=
  fun arg_0__ arg_1__ => Eq.

Local Definition Ord__Proxy_op_zg__ {inst_s}
   : (Proxy inst_s) -> (Proxy inst_s) -> bool :=
  fun x y => _GHC.Base.==_ (Ord__Proxy_compare x y) Gt.

Local Definition Ord__Proxy_op_zgze__ {inst_s}
   : (Proxy inst_s) -> (Proxy inst_s) -> bool :=
  fun x y => _GHC.Base./=_ (Ord__Proxy_compare x y) Lt.

Local Definition Ord__Proxy_op_zl__ {inst_s}
   : (Proxy inst_s) -> (Proxy inst_s) -> bool :=
  fun x y => _GHC.Base.==_ (Ord__Proxy_compare x y) Lt.

Local Definition Ord__Proxy_op_zlze__ {inst_s}
   : (Proxy inst_s) -> (Proxy inst_s) -> bool :=
  fun x y => _GHC.Base./=_ (Ord__Proxy_compare x y) Gt.

Local Definition Ord__Proxy_max {inst_s}
   : (Proxy inst_s) -> (Proxy inst_s) -> (Proxy inst_s) :=
  fun x y => if Ord__Proxy_op_zlze__ x y : bool then y else x.

Local Definition Ord__Proxy_min {inst_s}
   : (Proxy inst_s) -> (Proxy inst_s) -> (Proxy inst_s) :=
  fun x y => if Ord__Proxy_op_zlze__ x y : bool then x else y.

Program Instance Ord__Proxy {s} : GHC.Base.Ord (Proxy s) :=
  fun _ k =>
    k {| GHC.Base.op_zl____ := Ord__Proxy_op_zl__ ;
         GHC.Base.op_zlze____ := Ord__Proxy_op_zlze__ ;
         GHC.Base.op_zg____ := Ord__Proxy_op_zg__ ;
         GHC.Base.op_zgze____ := Ord__Proxy_op_zgze__ ;
         GHC.Base.compare__ := Ord__Proxy_compare ;
         GHC.Base.max__ := Ord__Proxy_max ;
         GHC.Base.min__ := Ord__Proxy_min |}.

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

Local Definition Monoid__Proxy_mappend {inst_s}
   : (Proxy inst_s) -> (Proxy inst_s) -> (Proxy inst_s) :=
  fun arg_0__ arg_1__ => Mk_Proxy.

Local Definition Monoid__Proxy_mconcat {inst_s}
   : list (Proxy inst_s) -> (Proxy inst_s) :=
  fun arg_0__ => Mk_Proxy.

Local Definition Monoid__Proxy_mempty {inst_s} : (Proxy inst_s) :=
  Mk_Proxy.

Program Instance Monoid__Proxy {s} : GHC.Base.Monoid (Proxy s) :=
  fun _ k =>
    k {| GHC.Base.mappend__ := Monoid__Proxy_mappend ;
         GHC.Base.mconcat__ := Monoid__Proxy_mconcat ;
         GHC.Base.mempty__ := Monoid__Proxy_mempty |}.

Local Definition Functor__Proxy_fmap
   : forall {a} {b}, (a -> b) -> Proxy a -> Proxy b :=
  fun {a} {b} => fun arg_0__ arg_1__ => Mk_Proxy.

Local Definition Functor__Proxy_op_zlzd__
   : forall {a} {b}, a -> Proxy b -> Proxy a :=
  fun {a} {b} => fun x => Functor__Proxy_fmap (GHC.Base.const x).

Program Instance Functor__Proxy : GHC.Base.Functor Proxy :=
  fun _ k =>
    k {| GHC.Base.op_zlzd____ := fun {a} {b} => Functor__Proxy_op_zlzd__ ;
         GHC.Base.fmap__ := fun {a} {b} => Functor__Proxy_fmap |}.

Local Definition Applicative__Proxy_op_zlztzg__
   : forall {a} {b}, Proxy (a -> b) -> Proxy a -> Proxy b :=
  fun {a} {b} => fun arg_0__ arg_1__ => Mk_Proxy.

Local Definition Applicative__Proxy_op_ztzg__
   : forall {a} {b}, Proxy a -> Proxy b -> Proxy b :=
  fun {a} {b} =>
    fun x y =>
      Applicative__Proxy_op_zlztzg__ (GHC.Base.fmap (GHC.Base.const GHC.Base.id) x) y.

Local Definition Applicative__Proxy_pure : forall {a}, a -> Proxy a :=
  fun {a} => fun arg_0__ => Mk_Proxy.

Program Instance Applicative__Proxy : GHC.Base.Applicative Proxy :=
  fun _ k =>
    k {| GHC.Base.op_ztzg____ := fun {a} {b} => Applicative__Proxy_op_ztzg__ ;
         GHC.Base.op_zlztzg____ := fun {a} {b} => Applicative__Proxy_op_zlztzg__ ;
         GHC.Base.pure__ := fun {a} => Applicative__Proxy_pure |}.

(* Translating `instance GHC.Base.Alternative Data.Proxy.Proxy' failed: OOPS!
   Cannot find information for class Qualified "GHC.Base" "Alternative"
   unsupported *)

Local Definition Monad__Proxy_op_zgzg__
   : forall {a} {b}, Proxy a -> Proxy b -> Proxy b :=
  fun {a} {b} => _GHC.Base.*>_.

Local Definition Monad__Proxy_op_zgzgze__
   : forall {a} {b}, Proxy a -> (a -> Proxy b) -> Proxy b :=
  fun {a} {b} => fun arg_0__ arg_1__ => Mk_Proxy.

Local Definition Monad__Proxy_return_ : forall {a}, a -> Proxy a :=
  fun {a} => GHC.Base.pure.

Program Instance Monad__Proxy : GHC.Base.Monad Proxy :=
  fun _ k =>
    k {| GHC.Base.op_zgzg____ := fun {a} {b} => Monad__Proxy_op_zgzg__ ;
         GHC.Base.op_zgzgze____ := fun {a} {b} => Monad__Proxy_op_zgzgze__ ;
         GHC.Base.return___ := fun {a} => Monad__Proxy_return_ |}.

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
