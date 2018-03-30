(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Coq.Program.Tactics.
Require Coq.Program.Wf.

(* Converted imports: *)

Require Control.Arrow.
Require Control.Category.
Require Data.Functor.
Require GHC.Base.
Require GHC.Prim.
Import Control.Category.Notations.
Import Data.Functor.Notations.
Import GHC.Base.Notations.

(* Converted type declarations: *)

Inductive WrappedMonad (m : Type -> Type) a : Type
  := WrapMonad : m a -> WrappedMonad m a.

Inductive WrappedArrow (a : Type -> Type -> Type) b c : Type
  := WrapArrow : a b c -> WrappedArrow a b c.

Arguments WrapMonad {_} {_} _.

Arguments WrapArrow {_} {_} {_} _.

Definition unwrapMonad {m : Type -> Type} {a} (arg_0__ : WrappedMonad m a) :=
  let 'WrapMonad unwrapMonad := arg_0__ in
  unwrapMonad.

Definition unwrapArrow {a : Type -> Type -> Type} {b} {c} (arg_1__
    : WrappedArrow a b c) :=
  let 'WrapArrow unwrapArrow := arg_1__ in
  unwrapArrow.
(* Converted value declarations: *)

Instance Unpeel_WrappedMonad {m} {a}
   : GHC.Prim.Unpeel (WrappedMonad m a) (m a) :=
  GHC.Prim.Build_Unpeel _ _ unwrapMonad WrapMonad.

Instance Unpeel_WrappedArrow {a} {b} {c}
   : GHC.Prim.Unpeel (WrappedArrow a b c) (a b c) :=
  GHC.Prim.Build_Unpeel _ _ unwrapArrow WrapArrow.

(* Skipping instance Applicative__ZipList *)

(* Translating `instance Alternative__ZipList' failed: OOPS! Cannot find
   information for class Qualified "GHC.Base" "Alternative" unsupported *)

Local Definition Functor__WrappedArrow_fmap {inst_a} {inst_b}
  `{Control.Arrow.Arrow inst_a}
   : forall {a} {b},
     (a -> b) -> (WrappedArrow inst_a inst_b) a -> (WrappedArrow inst_a inst_b) b :=
  fun {a} {b} =>
    fun arg_0__ arg_1__ =>
      match arg_0__, arg_1__ with
      | f, WrapArrow a => WrapArrow (a Control.Category.>>> Control.Arrow.arr f)
      end.

Local Definition Functor__WrappedArrow_op_zlzd__ {inst_a} {inst_b}
  `{Control.Arrow.Arrow inst_a}
   : forall {a} {b},
     a -> (WrappedArrow inst_a inst_b) b -> (WrappedArrow inst_a inst_b) a :=
  fun {a} {b} => fun x => Functor__WrappedArrow_fmap (GHC.Base.const x).

Program Instance Functor__WrappedArrow {a} {b} `{Control.Arrow.Arrow a}
   : GHC.Base.Functor (WrappedArrow a b) :=
  fun _ k =>
    k {| GHC.Base.op_zlzd____ := fun {a} {b} => Functor__WrappedArrow_op_zlzd__ ;
         GHC.Base.fmap__ := fun {a} {b} => Functor__WrappedArrow_fmap |}.

(* Translating `instance Applicative__WrappedArrow' failed: Cannot find sig for
   Qualified "GHC.Base" "liftA2" unsupported *)

(* Translating `instance Alternative__WrappedArrow' failed: OOPS! Cannot find
   information for class Qualified "GHC.Base" "Alternative" unsupported *)

Local Definition Functor__WrappedMonad_fmap {inst_m} `{GHC.Base.Monad inst_m}
   : forall {a} {b},
     (a -> b) -> (WrappedMonad inst_m) a -> (WrappedMonad inst_m) b :=
  fun {a} {b} =>
    fun arg_0__ arg_1__ =>
      match arg_0__, arg_1__ with
      | f, WrapMonad v => WrapMonad (GHC.Base.liftM f v)
      end.

Local Definition Functor__WrappedMonad_op_zlzd__ {inst_m} `{GHC.Base.Monad
  inst_m}
   : forall {a} {b}, a -> (WrappedMonad inst_m) b -> (WrappedMonad inst_m) a :=
  fun {a} {b} => fun x => Functor__WrappedMonad_fmap (GHC.Base.const x).

Program Instance Functor__WrappedMonad {m} `{GHC.Base.Monad m}
   : GHC.Base.Functor (WrappedMonad m) :=
  fun _ k =>
    k {| GHC.Base.op_zlzd____ := fun {a} {b} => Functor__WrappedMonad_op_zlzd__ ;
         GHC.Base.fmap__ := fun {a} {b} => Functor__WrappedMonad_fmap |}.

(* Translating `instance Applicative__WrappedMonad' failed: Cannot find sig for
   Qualified "GHC.Base" "liftA2" unsupported *)

(* Translating `instance Alternative__WrappedMonad' failed: OOPS! Cannot find
   information for class Qualified "GHC.Base" "Alternative" unsupported *)

(* Translating `instance Generic1__TYPE__ZipList__LiftedRep' failed: OOPS!
   Cannot find information for class Qualified "GHC.Generics" "Generic1"
   unsupported *)

(* Translating `instance Generic__ZipList' failed: OOPS! Cannot find information
   for class Qualified "GHC.Generics" "Generic" unsupported *)

(* Skipping instance Foldable__ZipList *)

(* Skipping instance Functor__ZipList *)

(* Translating `instance Read__ZipList' failed: OOPS! Cannot find information
   for class Qualified "GHC.Read" "Read" unsupported *)

(* Skipping instance Ord__ZipList *)

(* Skipping instance Eq___ZipList *)

(* Translating `instance Show__ZipList' failed: OOPS! Cannot find information
   for class Qualified "GHC.Show" "Show" unsupported *)

(* Translating `instance Generic1__TYPE__WrappedArrow__LiftedRep' failed: OOPS!
   Cannot find information for class Qualified "GHC.Generics" "Generic1"
   unsupported *)

(* Translating `instance Generic__WrappedArrow' failed: OOPS! Cannot find
   information for class Qualified "GHC.Generics" "Generic" unsupported *)

Local Definition Monad__WrappedMonad_op_zgzg__ {inst_m} `{GHC.Base.Monad inst_m}
   : forall {a} {b},
     WrappedMonad inst_m a -> WrappedMonad inst_m b -> WrappedMonad inst_m b :=
  fun {a} {b} => GHC.Prim.coerce _GHC.Base.>>_.

Local Definition Monad__WrappedMonad_op_zgzgze__ {inst_m} `{GHC.Base.Monad
  inst_m}
   : forall {a} {b},
     WrappedMonad inst_m a ->
     (a -> WrappedMonad inst_m b) -> WrappedMonad inst_m b :=
  fun {a} {b} => GHC.Prim.coerce _GHC.Base.>>=_.

Local Definition Monad__WrappedMonad_return_ {inst_m} `{GHC.Base.Monad inst_m}
   : forall {a}, a -> WrappedMonad inst_m a :=
  fun {a} => GHC.Prim.coerce GHC.Base.return_.

Program Instance Monad__WrappedMonad {m} `{GHC.Base.Monad m}
   : GHC.Base.Monad (WrappedMonad m) :=
  fun _ k =>
    k {| GHC.Base.op_zgzg____ := fun {a} {b} => Monad__WrappedMonad_op_zgzg__ ;
         GHC.Base.op_zgzgze____ := fun {a} {b} => Monad__WrappedMonad_op_zgzgze__ ;
         GHC.Base.return___ := fun {a} => Monad__WrappedMonad_return_ |}.

(* Translating `instance Generic1__TYPE__WrappedMonad__LiftedRep' failed: OOPS!
   Cannot find information for class Qualified "GHC.Generics" "Generic1"
   unsupported *)

(* Translating `instance Generic__WrappedMonad' failed: OOPS! Cannot find
   information for class Qualified "GHC.Generics" "Generic" unsupported *)

Definition optional {f} {a} `{GHC.Base.Alternative f} : f a -> f (option a) :=
  fun v => (Some Data.Functor.<$> v) GHC.Base.<|> GHC.Base.pure None.

(* Unbound variables:
     None Some Type option Control.Arrow.Arrow Control.Arrow.arr
     Control.Category.op_zgzgzg__ Data.Functor.op_zlzdzg__ GHC.Base.Alternative
     GHC.Base.Functor GHC.Base.Monad GHC.Base.const GHC.Base.liftM GHC.Base.op_zgzg__
     GHC.Base.op_zgzgze__ GHC.Base.op_zlzbzg__ GHC.Base.pure GHC.Base.return_
     GHC.Prim.Build_Unpeel GHC.Prim.Unpeel GHC.Prim.coerce
*)
