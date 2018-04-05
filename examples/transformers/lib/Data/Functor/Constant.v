(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Coq.Program.Tactics.
Require Coq.Program.Wf.

(* Converted imports: *)

Require Coq.Program.Basics.
Require Data.Foldable.
Require Data.SemigroupInternal.
Require Data.Traversable.
Require GHC.Base.
Require GHC.Num.
Import GHC.Base.Notations.
Import GHC.Num.Notations.

(* Converted type declarations: *)

Inductive Constant (a : Type) (b : Type) : Type
  := Mk_Constant : a -> Constant a b.

Arguments Mk_Constant {_} {_} _.

Definition getConstant {a : Type} {b : Type} (arg_0__ : Constant a b) :=
  let 'Mk_Constant getConstant := arg_0__ in
  getConstant.
(* Midamble *)

Require Import GHC.Prim.
Require GHC.Err.

Instance Default_Constant {a}{b} `{GHC.Err.Default a} : GHC.Err.Default (Constant a b) := Err.Build_Default _ (Mk_Constant Err.default).

Instance Unpeel_Constant {a}{b} : Unpeel (Constant a b) a :=
  Build_Unpeel _ _ getConstant Mk_Constant.

(* Converted value declarations: *)

(* Translating `instance Read__Constant' failed: OOPS! Cannot find information
   for class Qualified "GHC.Read" "Read" unsupported *)

(* Translating `instance Show__Constant' failed: OOPS! Cannot find information
   for class Qualified "GHC.Show" "Show" unsupported *)

(* Translating `instance Eq2__Constant' failed: OOPS! Cannot find information
   for class Qualified "Data.Functor.Classes" "Eq2" unsupported *)

(* Translating `instance Ord2__Constant' failed: OOPS! Cannot find information
   for class Qualified "Data.Functor.Classes" "Ord2" unsupported *)

(* Translating `instance Read2__Constant' failed: OOPS! Cannot find information
   for class Qualified "Data.Functor.Classes" "Read2" unsupported *)

(* Translating `instance Show2__Constant' failed: OOPS! Cannot find information
   for class Qualified "Data.Functor.Classes" "Show2" unsupported *)

(* Skipping instance Eq1__Constant *)

(* Skipping instance Ord1__Constant *)

(* Translating `instance Read1__Constant' failed: OOPS! Cannot find information
   for class Qualified "Data.Functor.Classes" "Read1" unsupported *)

(* Translating `instance Show1__Constant' failed: OOPS! Cannot find information
   for class Qualified "Data.Functor.Classes" "Show1" unsupported *)

Local Definition Functor__Constant_fmap {inst_a}
   : forall {a} {b}, (a -> b) -> (Constant inst_a) a -> (Constant inst_a) b :=
  fun {a} {b} =>
    fun arg_0__ arg_1__ =>
      match arg_0__, arg_1__ with
      | _, Mk_Constant x => Mk_Constant x
      end.

Local Definition Functor__Constant_op_zlzd__ {inst_a}
   : forall {a} {b}, a -> (Constant inst_a) b -> (Constant inst_a) a :=
  fun {a} {b} => fun x => Functor__Constant_fmap (GHC.Base.const x).

Program Instance Functor__Constant {a} : GHC.Base.Functor (Constant a) :=
  fun _ k =>
    k {| GHC.Base.op_zlzd____ := fun {a} {b} => Functor__Constant_op_zlzd__ ;
         GHC.Base.fmap__ := fun {a} {b} => Functor__Constant_fmap |}.

Local Definition Foldable__Constant_foldMap {inst_a}
   : forall {m} {a},
     forall `{GHC.Base.Monoid m}, (a -> m) -> (Constant inst_a) a -> m :=
  fun {m} {a} `{GHC.Base.Monoid m} =>
    fun arg_0__ arg_1__ =>
      match arg_0__, arg_1__ with
      | _, Mk_Constant _ => GHC.Base.mempty
      end.

Local Definition Foldable__Constant_foldl {inst_a}
   : forall {b} {a}, (b -> a -> b) -> b -> (Constant inst_a) a -> b :=
  fun {b} {a} =>
    fun arg_19__ arg_20__ arg_21__ =>
      match arg_19__, arg_20__, arg_21__ with
      | f, z, t =>
          Data.SemigroupInternal.appEndo (Data.SemigroupInternal.getDual
                                          (Foldable__Constant_foldMap (Coq.Program.Basics.compose
                                                                       Data.SemigroupInternal.Mk_Dual
                                                                       (Coq.Program.Basics.compose
                                                                        Data.SemigroupInternal.Mk_Endo (GHC.Base.flip
                                                                         f))) t)) z
      end.

Local Definition Foldable__Constant_foldr' {inst_a}
   : forall {a} {b}, (a -> b -> b) -> b -> (Constant inst_a) a -> b :=
  fun {a} {b} =>
    fun arg_9__ arg_10__ arg_11__ =>
      match arg_9__, arg_10__, arg_11__ with
      | f, z0, xs =>
          let f' :=
            fun arg_12__ arg_13__ arg_14__ =>
              match arg_12__, arg_13__, arg_14__ with
              | k, x, z => k GHC.Base.$! f x z
              end in
          Foldable__Constant_foldl f' GHC.Base.id xs z0
      end.

Local Definition Foldable__Constant_foldr {inst_a}
   : forall {a} {b}, (a -> b -> b) -> b -> (Constant inst_a) a -> b :=
  fun {a} {b} =>
    fun arg_4__ arg_5__ arg_6__ =>
      match arg_4__, arg_5__, arg_6__ with
      | f, z, t =>
          Data.SemigroupInternal.appEndo (Foldable__Constant_foldMap
                                          (Coq.Program.Basics.compose Data.SemigroupInternal.Mk_Endo f) t) z
      end.

Local Definition Foldable__Constant_foldl' {inst_a}
   : forall {b} {a}, (b -> a -> b) -> b -> (Constant inst_a) a -> b :=
  fun {b} {a} =>
    fun arg_24__ arg_25__ arg_26__ =>
      match arg_24__, arg_25__, arg_26__ with
      | f, z0, xs =>
          let f' :=
            fun arg_27__ arg_28__ arg_29__ =>
              match arg_27__, arg_28__, arg_29__ with
              | x, k, z => k GHC.Base.$! f z x
              end in
          Foldable__Constant_foldr f' GHC.Base.id xs z0
      end.

Local Definition Foldable__Constant_toList {inst_a}
   : forall {a}, (Constant inst_a) a -> list a :=
  fun {a} =>
    fun arg_54__ =>
      let 't := arg_54__ in
      GHC.Base.build (fun _ arg_55__ arg_56__ =>
                        match arg_55__, arg_56__ with
                        | c, n => Foldable__Constant_foldr c n t
                        end).

Local Definition Foldable__Constant_product {inst_a}
   : forall {a}, forall `{GHC.Num.Num a}, (Constant inst_a) a -> a :=
  fun {a} `{GHC.Num.Num a} =>
    Coq.Program.Basics.compose Data.SemigroupInternal.getProduct
                               (Foldable__Constant_foldMap Data.SemigroupInternal.Mk_Product).

Local Definition Foldable__Constant_sum {inst_a}
   : forall {a}, forall `{GHC.Num.Num a}, (Constant inst_a) a -> a :=
  fun {a} `{GHC.Num.Num a} =>
    Coq.Program.Basics.compose Data.SemigroupInternal.getSum
                               (Foldable__Constant_foldMap Data.SemigroupInternal.Mk_Sum).

Local Definition Foldable__Constant_fold {inst_a}
   : forall {m}, forall `{GHC.Base.Monoid m}, (Constant inst_a) m -> m :=
  fun {m} `{GHC.Base.Monoid m} => Foldable__Constant_foldMap GHC.Base.id.

Local Definition Foldable__Constant_elem {inst_a}
   : forall {a}, forall `{GHC.Base.Eq_ a}, a -> (Constant inst_a) a -> bool :=
  fun {a} `{GHC.Base.Eq_ a} =>
    Coq.Program.Basics.compose (fun arg_69__ =>
                                  let 'p := arg_69__ in
                                  Coq.Program.Basics.compose Data.SemigroupInternal.getAny
                                                             (Foldable__Constant_foldMap (Coq.Program.Basics.compose
                                                                                          Data.SemigroupInternal.Mk_Any
                                                                                          p))) _GHC.Base.==_.

Local Definition Foldable__Constant_length {inst_a}
   : forall {a}, (Constant inst_a) a -> GHC.Num.Int :=
  fun {a} => fun arg_0__ => let 'Mk_Constant _ := arg_0__ in #0.

Local Definition Foldable__Constant_null {inst_a}
   : forall {a}, (Constant inst_a) a -> bool :=
  fun {a} => fun arg_0__ => let 'Mk_Constant _ := arg_0__ in true.

Program Instance Foldable__Constant {a} : Data.Foldable.Foldable (Constant a) :=
  fun _ k =>
    k {| Data.Foldable.elem__ := fun {a} `{GHC.Base.Eq_ a} =>
           Foldable__Constant_elem ;
         Data.Foldable.fold__ := fun {m} `{GHC.Base.Monoid m} =>
           Foldable__Constant_fold ;
         Data.Foldable.foldMap__ := fun {m} {a} `{GHC.Base.Monoid m} =>
           Foldable__Constant_foldMap ;
         Data.Foldable.foldl__ := fun {b} {a} => Foldable__Constant_foldl ;
         Data.Foldable.foldl'__ := fun {b} {a} => Foldable__Constant_foldl' ;
         Data.Foldable.foldr__ := fun {a} {b} => Foldable__Constant_foldr ;
         Data.Foldable.foldr'__ := fun {a} {b} => Foldable__Constant_foldr' ;
         Data.Foldable.length__ := fun {a} => Foldable__Constant_length ;
         Data.Foldable.null__ := fun {a} => Foldable__Constant_null ;
         Data.Foldable.product__ := fun {a} `{GHC.Num.Num a} =>
           Foldable__Constant_product ;
         Data.Foldable.sum__ := fun {a} `{GHC.Num.Num a} => Foldable__Constant_sum ;
         Data.Foldable.toList__ := fun {a} => Foldable__Constant_toList |}.

Local Definition Traversable__Constant_traverse {inst_a}
   : forall {f} {a} {b},
     forall `{GHC.Base.Applicative f},
     (a -> f b) -> (Constant inst_a) a -> f ((Constant inst_a) b) :=
  fun {f} {a} {b} `{GHC.Base.Applicative f} =>
    fun arg_0__ arg_1__ =>
      match arg_0__, arg_1__ with
      | _, Mk_Constant x => GHC.Base.pure (Mk_Constant x)
      end.

Local Definition Traversable__Constant_sequenceA {inst_a}
   : forall {f} {a},
     forall `{GHC.Base.Applicative f},
     (Constant inst_a) (f a) -> f ((Constant inst_a) a) :=
  fun {f} {a} `{GHC.Base.Applicative f} =>
    Traversable__Constant_traverse GHC.Base.id.

Local Definition Traversable__Constant_sequence {inst_a}
   : forall {m} {a},
     forall `{GHC.Base.Monad m},
     (Constant inst_a) (m a) -> m ((Constant inst_a) a) :=
  fun {m} {a} `{GHC.Base.Monad m} => Traversable__Constant_sequenceA.

Local Definition Traversable__Constant_mapM {inst_a}
   : forall {m} {a} {b},
     forall `{GHC.Base.Monad m},
     (a -> m b) -> (Constant inst_a) a -> m ((Constant inst_a) b) :=
  fun {m} {a} {b} `{GHC.Base.Monad m} => Traversable__Constant_traverse.

Program Instance Traversable__Constant {a}
   : Data.Traversable.Traversable (Constant a) :=
  fun _ k =>
    k {| Data.Traversable.mapM__ := fun {m} {a} {b} `{GHC.Base.Monad m} =>
           Traversable__Constant_mapM ;
         Data.Traversable.sequence__ := fun {m} {a} `{GHC.Base.Monad m} =>
           Traversable__Constant_sequence ;
         Data.Traversable.sequenceA__ := fun {f} {a} `{GHC.Base.Applicative f} =>
           Traversable__Constant_sequenceA ;
         Data.Traversable.traverse__ := fun {f} {a} {b} `{GHC.Base.Applicative f} =>
           Traversable__Constant_traverse |}.

Local Definition Semigroup__Constant_op_zlzlzgzg__ {inst_a} {inst_b}
  `{(GHC.Base.Semigroup inst_a)}
   : (Constant inst_a inst_b) ->
     (Constant inst_a inst_b) -> (Constant inst_a inst_b) :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | Mk_Constant x, Mk_Constant y => Mk_Constant (x GHC.Base.<<>> y)
    end.

Program Instance Semigroup__Constant {a} {b} `{(GHC.Base.Semigroup a)}
   : GHC.Base.Semigroup (Constant a b) :=
  fun _ k =>
    k {| GHC.Base.op_zlzlzgzg____ := Semigroup__Constant_op_zlzlzgzg__ |}.

Local Definition Applicative__Constant_op_zlztzg__ {inst_a} `{(GHC.Base.Monoid
   inst_a)}
   : forall {a} {b},
     (Constant inst_a) (a -> b) -> (Constant inst_a) a -> (Constant inst_a) b :=
  fun {a} {b} =>
    fun arg_0__ arg_1__ =>
      match arg_0__, arg_1__ with
      | Mk_Constant x, Mk_Constant y => Mk_Constant (GHC.Base.mappend x y)
      end.

Local Definition Applicative__Constant_op_ztzg__ {inst_a} `{(GHC.Base.Monoid
   inst_a)}
   : forall {a} {b},
     (Constant inst_a) a -> (Constant inst_a) b -> (Constant inst_a) b :=
  fun {a} {b} =>
    fun x y =>
      Applicative__Constant_op_zlztzg__ (GHC.Base.fmap (GHC.Base.const GHC.Base.id) x)
                                        y.

Local Definition Applicative__Constant_liftA2 {inst_a} `{(GHC.Base.Monoid
   inst_a)}
   : forall {a} {b} {c},
     (a -> b -> c) ->
     (Constant inst_a) a -> (Constant inst_a) b -> (Constant inst_a) c :=
  fun {a} {b} {c} =>
    fun f x => Applicative__Constant_op_zlztzg__ (GHC.Base.fmap f x).

Local Definition Applicative__Constant_pure {inst_a} `{(GHC.Base.Monoid inst_a)}
   : forall {a}, a -> (Constant inst_a) a :=
  fun {a} => fun arg_0__ => Mk_Constant GHC.Base.mempty.

Program Instance Applicative__Constant {a} `{(GHC.Base.Monoid a)}
   : GHC.Base.Applicative (Constant a) :=
  fun _ k =>
    k {| GHC.Base.op_ztzg____ := fun {a} {b} => Applicative__Constant_op_ztzg__ ;
         GHC.Base.op_zlztzg____ := fun {a} {b} => Applicative__Constant_op_zlztzg__ ;
         GHC.Base.liftA2__ := fun {a} {b} {c} => Applicative__Constant_liftA2 ;
         GHC.Base.pure__ := fun {a} => Applicative__Constant_pure |}.

Local Definition Monoid__Constant_mappend {inst_a} {inst_b} `{(GHC.Base.Monoid
   inst_a)}
   : (Constant inst_a inst_b) ->
     (Constant inst_a inst_b) -> (Constant inst_a inst_b) :=
  _GHC.Base.<<>>_.

Local Definition Monoid__Constant_mempty {inst_a} {inst_b} `{(GHC.Base.Monoid
   inst_a)}
   : (Constant inst_a inst_b) :=
  Mk_Constant GHC.Base.mempty.

Local Definition Monoid__Constant_mconcat {inst_a} {inst_b} `{(GHC.Base.Monoid
   inst_a)}
   : list (Constant inst_a inst_b) -> (Constant inst_a inst_b) :=
  GHC.Base.foldr Monoid__Constant_mappend Monoid__Constant_mempty.

Program Instance Monoid__Constant {a} {b} `{(GHC.Base.Monoid a)}
   : GHC.Base.Monoid (Constant a b) :=
  fun _ k =>
    k {| GHC.Base.mappend__ := Monoid__Constant_mappend ;
         GHC.Base.mconcat__ := Monoid__Constant_mconcat ;
         GHC.Base.mempty__ := Monoid__Constant_mempty |}.

(* Translating `instance Bifunctor__Constant' failed: missing Qualified
   "Data.Bifunctor" "bimap" in fromList [(Qualified "Data.Bifunctor"
   "first",Qualified "Data.Functor.Constant"
   "Bifunctor__Constant_first"),(Qualified "Data.Bifunctor" "second",Qualified
   "Data.Functor.Constant" "Bifunctor__Constant_second")] unsupported *)

(* Translating `instance Bifoldable__Constant' failed: OOPS! Cannot find
   information for class Qualified "Data.Bifoldable" "Bifoldable" unsupported *)

(* Translating `instance Bitraversable__Constant' failed: OOPS! Cannot find
   information for class Qualified "Data.Bitraversable" "Bitraversable"
   unsupported *)

(* Skipping instance Ord__Constant *)

(* Skipping instance Eq___Constant *)

(* External variables:
     Type bool list true Coq.Program.Basics.compose Data.Foldable.Foldable
     Data.Foldable.elem__ Data.Foldable.foldMap__ Data.Foldable.fold__
     Data.Foldable.foldl'__ Data.Foldable.foldl__ Data.Foldable.foldr'__
     Data.Foldable.foldr__ Data.Foldable.length__ Data.Foldable.null__
     Data.Foldable.product__ Data.Foldable.sum__ Data.Foldable.toList__
     Data.SemigroupInternal.Mk_Any Data.SemigroupInternal.Mk_Dual
     Data.SemigroupInternal.Mk_Endo Data.SemigroupInternal.Mk_Product
     Data.SemigroupInternal.Mk_Sum Data.SemigroupInternal.appEndo
     Data.SemigroupInternal.getAny Data.SemigroupInternal.getDual
     Data.SemigroupInternal.getProduct Data.SemigroupInternal.getSum
     Data.Traversable.Traversable Data.Traversable.mapM__
     Data.Traversable.sequenceA__ Data.Traversable.sequence__
     Data.Traversable.traverse__ GHC.Base.Applicative GHC.Base.Eq_ GHC.Base.Functor
     GHC.Base.Monad GHC.Base.Monoid GHC.Base.Semigroup GHC.Base.build GHC.Base.const
     GHC.Base.flip GHC.Base.fmap GHC.Base.fmap__ GHC.Base.foldr GHC.Base.id
     GHC.Base.liftA2__ GHC.Base.mappend GHC.Base.mappend__ GHC.Base.mconcat__
     GHC.Base.mempty GHC.Base.mempty__ GHC.Base.op_zdzn__ GHC.Base.op_zeze__
     GHC.Base.op_zlzd____ GHC.Base.op_zlzlzgzg__ GHC.Base.op_zlzlzgzg____
     GHC.Base.op_zlztzg____ GHC.Base.op_ztzg____ GHC.Base.pure GHC.Base.pure__
     GHC.Num.Int GHC.Num.Num GHC.Num.fromInteger
*)
