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
Require Data.Tuple.
Require GHC.Base.
Require GHC.Prim.
Import Control.Arrow.Notations.
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

Local Definition Applicative__WrappedMonad_op_zlztzg__ {inst_m} `{GHC.Base.Monad
  inst_m}
   : forall {a} {b},
     (WrappedMonad inst_m) (a -> b) ->
     (WrappedMonad inst_m) a -> (WrappedMonad inst_m) b :=
  fun {a} {b} =>
    fun arg_0__ arg_1__ =>
      match arg_0__, arg_1__ with
      | WrapMonad f, WrapMonad v => WrapMonad (GHC.Base.ap f v)
      end.

Local Definition Applicative__WrappedMonad_op_ztzg__ {inst_m} `{GHC.Base.Monad
  inst_m}
   : forall {a} {b},
     (WrappedMonad inst_m) a -> (WrappedMonad inst_m) b -> (WrappedMonad inst_m) b :=
  fun {a} {b} =>
    fun x y =>
      Applicative__WrappedMonad_op_zlztzg__ (GHC.Base.fmap (GHC.Base.const
                                                            GHC.Base.id) x) y.

Local Definition Applicative__WrappedMonad_pure {inst_m} `{GHC.Base.Monad
  inst_m}
   : forall {a}, a -> (WrappedMonad inst_m) a :=
  fun {a} => WrapMonad GHC.Base.∘ GHC.Base.pure.

Program Instance Applicative__WrappedMonad {m} `{GHC.Base.Monad m}
   : GHC.Base.Applicative (WrappedMonad m) :=
  fun _ k =>
    k {| GHC.Base.op_ztzg____ := fun {a} {b} =>
           Applicative__WrappedMonad_op_ztzg__ ;
         GHC.Base.op_zlztzg____ := fun {a} {b} => Applicative__WrappedMonad_op_zlztzg__ ;
         GHC.Base.pure__ := fun {a} => Applicative__WrappedMonad_pure |}.

(* Translating `instance Alternative__WrappedMonad' failed: OOPS! Cannot find
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

Local Definition Applicative__WrappedArrow_op_zlztzg__ {inst_a} {inst_b}
  `{Control.Arrow.Arrow inst_a}
   : forall {a} {b},
     (WrappedArrow inst_a inst_b) (a -> b) ->
     (WrappedArrow inst_a inst_b) a -> (WrappedArrow inst_a inst_b) b :=
  fun {a} {b} =>
    fun arg_0__ arg_1__ =>
      match arg_0__, arg_1__ with
      | WrapArrow f, WrapArrow v =>
          WrapArrow ((f Control.Arrow.&&& v) Control.Category.>>>
                     Control.Arrow.arr (Data.Tuple.uncurry GHC.Base.id))
      end.

Local Definition Applicative__WrappedArrow_op_ztzg__ {inst_a} {inst_b}
  `{Control.Arrow.Arrow inst_a}
   : forall {a} {b},
     (WrappedArrow inst_a inst_b) a ->
     (WrappedArrow inst_a inst_b) b -> (WrappedArrow inst_a inst_b) b :=
  fun {a} {b} =>
    fun x y =>
      Applicative__WrappedArrow_op_zlztzg__ (GHC.Base.fmap (GHC.Base.const
                                                            GHC.Base.id) x) y.

Local Definition Applicative__WrappedArrow_pure {inst_a} {inst_b}
  `{Control.Arrow.Arrow inst_a}
   : forall {a}, a -> (WrappedArrow inst_a inst_b) a :=
  fun {a} => fun x => WrapArrow (Control.Arrow.arr (GHC.Base.const x)).

Program Instance Applicative__WrappedArrow {a} {b} `{Control.Arrow.Arrow a}
   : GHC.Base.Applicative (WrappedArrow a b) :=
  fun _ k =>
    k {| GHC.Base.op_ztzg____ := fun {a} {b} =>
           Applicative__WrappedArrow_op_ztzg__ ;
         GHC.Base.op_zlztzg____ := fun {a} {b} => Applicative__WrappedArrow_op_zlztzg__ ;
         GHC.Base.pure__ := fun {a} => Applicative__WrappedArrow_pure |}.

(* Translating `instance Alternative__WrappedArrow' failed: OOPS! Cannot find
   information for class Qualified "GHC.Base" "Alternative" unsupported *)

(* Skipping instance Applicative__ZipList *)

(* Translating `instance Generic1__ZipList' failed: OOPS! Cannot find
   information for class Qualified "GHC.Generics" "Generic1" unsupported *)

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

(* Translating `instance Generic1__WrappedArrow' failed: OOPS! Cannot find
   information for class Qualified "GHC.Generics" "Generic1" unsupported *)

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

(* Translating `instance Generic1__WrappedMonad' failed: OOPS! Cannot find
   information for class Qualified "GHC.Generics" "Generic1" unsupported *)

(* Translating `instance Generic__WrappedMonad' failed: OOPS! Cannot find
   information for class Qualified "GHC.Generics" "Generic" unsupported *)

Definition optional {f} {a} `{GHC.Base.Alternative f} : f a -> f (option a) :=
  fun v => (Some Data.Functor.<$> v) GHC.Base.<|> GHC.Base.pure None.

(* Unbound variables:
     None Some Type option Control.Arrow.Arrow Control.Arrow.arr
     Control.Arrow.op_zazaza__ Control.Category.op_zgzgzg__ Data.Functor.op_zlzdzg__
     Data.Tuple.uncurry GHC.Base.Alternative GHC.Base.Applicative GHC.Base.Functor
     GHC.Base.Monad GHC.Base.ap GHC.Base.const GHC.Base.fmap GHC.Base.id
     GHC.Base.liftM GHC.Base.op_z2218U__ GHC.Base.op_zgzg__ GHC.Base.op_zgzgze__
     GHC.Base.op_zlzbzg__ GHC.Base.pure GHC.Base.return_ GHC.Prim.Build_Unpeel
     GHC.Prim.Unpeel GHC.Prim.coerce
*)
