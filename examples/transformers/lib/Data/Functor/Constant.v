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
Require Data.Bifoldable.
Require Data.Bifunctor.
Require Data.Bitraversable.
Require Data.Foldable.
Require Data.Functor.
Require Data.Functor.Classes.
Require Data.SemigroupInternal.
Require Data.Traversable.
Require GHC.Base.
Require GHC.Num.
Require GHC.Prim.
Import Data.Functor.Notations.
Import GHC.Base.Notations.
Import GHC.Num.Notations.

(* Converted type declarations: *)

Inductive Constant (a : Type) (b : Type) : Type
  := Mk_Constant (getConstant : a) : Constant a b.

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

Local Definition Eq___Constant_op_zeze__ {inst_a} {inst_b} `{GHC.Base.Eq_
  inst_a}
   : (Constant inst_a inst_b : GHC.Prim.TYPE GHC.Types.LiftedRep) ->
     (Constant inst_a inst_b : GHC.Prim.TYPE GHC.Types.LiftedRep) -> bool :=
  GHC.Prim.coerce _GHC.Base.==_.

Local Definition Eq___Constant_op_zsze__ {inst_a} {inst_b} `{GHC.Base.Eq_
  inst_a}
   : (Constant inst_a inst_b : GHC.Prim.TYPE GHC.Types.LiftedRep) ->
     (Constant inst_a inst_b : GHC.Prim.TYPE GHC.Types.LiftedRep) -> bool :=
  GHC.Prim.coerce _GHC.Base./=_.

Program Instance Eq___Constant {a} {b} `{GHC.Base.Eq_ a}
   : GHC.Base.Eq_ (Constant a b : GHC.Prim.TYPE GHC.Types.LiftedRep) :=
  fun _ k =>
    k {| GHC.Base.op_zeze____ := Eq___Constant_op_zeze__ ;
         GHC.Base.op_zsze____ := Eq___Constant_op_zsze__ |}.

Local Definition Ord__Constant_op_zl__ {inst_a} {inst_b} `{GHC.Base.Ord inst_a}
   : (Constant inst_a inst_b : GHC.Prim.TYPE GHC.Types.LiftedRep) ->
     (Constant inst_a inst_b : GHC.Prim.TYPE GHC.Types.LiftedRep) -> bool :=
  GHC.Prim.coerce _GHC.Base.<_.

Local Definition Ord__Constant_op_zlze__ {inst_a} {inst_b} `{GHC.Base.Ord
  inst_a}
   : (Constant inst_a inst_b : GHC.Prim.TYPE GHC.Types.LiftedRep) ->
     (Constant inst_a inst_b : GHC.Prim.TYPE GHC.Types.LiftedRep) -> bool :=
  GHC.Prim.coerce _GHC.Base.<=_.

Local Definition Ord__Constant_op_zg__ {inst_a} {inst_b} `{GHC.Base.Ord inst_a}
   : (Constant inst_a inst_b : GHC.Prim.TYPE GHC.Types.LiftedRep) ->
     (Constant inst_a inst_b : GHC.Prim.TYPE GHC.Types.LiftedRep) -> bool :=
  GHC.Prim.coerce _GHC.Base.>_.

Local Definition Ord__Constant_op_zgze__ {inst_a} {inst_b} `{GHC.Base.Ord
  inst_a}
   : (Constant inst_a inst_b : GHC.Prim.TYPE GHC.Types.LiftedRep) ->
     (Constant inst_a inst_b : GHC.Prim.TYPE GHC.Types.LiftedRep) -> bool :=
  GHC.Prim.coerce _GHC.Base.>=_.

Local Definition Ord__Constant_compare {inst_a} {inst_b} `{GHC.Base.Ord inst_a}
   : (Constant inst_a inst_b : GHC.Prim.TYPE GHC.Types.LiftedRep) ->
     (Constant inst_a inst_b : GHC.Prim.TYPE GHC.Types.LiftedRep) -> comparison :=
  GHC.Prim.coerce GHC.Base.compare.

Local Definition Ord__Constant_max {inst_a} {inst_b} `{GHC.Base.Ord inst_a}
   : (Constant inst_a inst_b : GHC.Prim.TYPE GHC.Types.LiftedRep) ->
     (Constant inst_a inst_b : GHC.Prim.TYPE GHC.Types.LiftedRep) ->
     (Constant inst_a inst_b : GHC.Prim.TYPE GHC.Types.LiftedRep) :=
  GHC.Prim.coerce GHC.Base.max.

Local Definition Ord__Constant_min {inst_a} {inst_b} `{GHC.Base.Ord inst_a}
   : (Constant inst_a inst_b : GHC.Prim.TYPE GHC.Types.LiftedRep) ->
     (Constant inst_a inst_b : GHC.Prim.TYPE GHC.Types.LiftedRep) ->
     (Constant inst_a inst_b : GHC.Prim.TYPE GHC.Types.LiftedRep) :=
  GHC.Prim.coerce GHC.Base.min.

Program Instance Ord__Constant {a} {b} `{GHC.Base.Ord a}
   : GHC.Base.Ord (Constant a b : GHC.Prim.TYPE GHC.Types.LiftedRep) :=
  fun _ k =>
    k {| GHC.Base.op_zl____ := Ord__Constant_op_zl__ ;
         GHC.Base.op_zlze____ := Ord__Constant_op_zlze__ ;
         GHC.Base.op_zg____ := Ord__Constant_op_zg__ ;
         GHC.Base.op_zgze____ := Ord__Constant_op_zgze__ ;
         GHC.Base.compare__ := Ord__Constant_compare ;
         GHC.Base.max__ := Ord__Constant_max ;
         GHC.Base.min__ := Ord__Constant_min |}.

Local Definition Bitraversable__Constant_bitraverse
   : forall {f} {a} {c} {b} {d},
     forall `{GHC.Base.Applicative f},
     (a -> f c) -> (b -> f d) -> Constant a b -> f (Constant c d) :=
  fun {f} {a} {c} {b} {d} `{GHC.Base.Applicative f} =>
    fun arg_0__ arg_1__ arg_2__ =>
      match arg_0__, arg_1__, arg_2__ with
      | f, _, Mk_Constant a => Mk_Constant Data.Functor.<$> f a
      end.

Local Definition Bifoldable__Constant_bifoldMap
   : forall {m} {a} {b},
     forall `{GHC.Base.Monoid m}, (a -> m) -> (b -> m) -> Constant a b -> m :=
  fun {m} {a} {b} `{GHC.Base.Monoid m} =>
    fun arg_0__ arg_1__ arg_2__ =>
      match arg_0__, arg_1__, arg_2__ with
      | f, _, Mk_Constant a => f a
      end.

Local Definition Bifoldable__Constant_bifold
   : forall {m}, forall `{GHC.Base.Monoid m}, Constant m m -> m :=
  fun {m} `{GHC.Base.Monoid m} =>
    Bifoldable__Constant_bifoldMap GHC.Base.id GHC.Base.id.

Local Definition Bifoldable__Constant_bifoldl
   : forall {c} {a} {b},
     (c -> a -> c) -> (c -> b -> c) -> c -> Constant a b -> c :=
  fun {c} {a} {b} =>
    fun f g z t =>
      Data.SemigroupInternal.appEndo (Data.SemigroupInternal.getDual
                                      (Bifoldable__Constant_bifoldMap (Data.SemigroupInternal.Mk_Dual GHC.Base.∘
                                                                       (Data.SemigroupInternal.Mk_Endo GHC.Base.∘
                                                                        GHC.Base.flip f))
                                       (Data.SemigroupInternal.Mk_Dual GHC.Base.∘
                                        (Data.SemigroupInternal.Mk_Endo GHC.Base.∘ GHC.Base.flip g)) t)) z.

Local Definition Bifoldable__Constant_bifoldr
   : forall {a} {c} {b},
     (a -> c -> c) -> (b -> c -> c) -> c -> Constant a b -> c :=
  fun {a} {c} {b} =>
    fun f g z t =>
      Data.SemigroupInternal.appEndo (Bifoldable__Constant_bifoldMap
                                      (Coq.Program.Basics.compose Data.SemigroupInternal.Mk_Endo f)
                                      (Coq.Program.Basics.compose Data.SemigroupInternal.Mk_Endo g) t) z.

Program Instance Bifoldable__Constant : Data.Bifoldable.Bifoldable Constant :=
  fun _ k =>
    k {| Data.Bifoldable.bifold__ := fun {m} `{GHC.Base.Monoid m} =>
           Bifoldable__Constant_bifold ;
         Data.Bifoldable.bifoldMap__ := fun {m} {a} {b} `{GHC.Base.Monoid m} =>
           Bifoldable__Constant_bifoldMap ;
         Data.Bifoldable.bifoldl__ := fun {c} {a} {b} => Bifoldable__Constant_bifoldl ;
         Data.Bifoldable.bifoldr__ := fun {a} {c} {b} => Bifoldable__Constant_bifoldr |}.

Local Definition Bifunctor__Constant_first
   : forall {a} {b} {c}, (a -> b) -> Constant a c -> Constant b c :=
  fun {a} {b} {c} =>
    fun arg_0__ arg_1__ =>
      match arg_0__, arg_1__ with
      | f, Mk_Constant x => Mk_Constant (f x)
      end.

Local Definition Bifunctor__Constant_second
   : forall {b} {c} {a}, (b -> c) -> Constant a b -> Constant a c :=
  fun {b} {c} {a} =>
    fun arg_0__ arg_1__ =>
      match arg_0__, arg_1__ with
      | _, Mk_Constant x => Mk_Constant x
      end.

Local Definition Bifunctor__Constant_bimap
   : forall {a} {b} {c} {d},
     (a -> b) -> (c -> d) -> Constant a c -> Constant b d :=
  fun {a} {b} {c} {d} =>
    fun f g => Bifunctor__Constant_first f GHC.Base.∘ Bifunctor__Constant_second g.

Program Instance Bifunctor__Constant : Data.Bifunctor.Bifunctor Constant :=
  fun _ k =>
    k {| Data.Bifunctor.bimap__ := fun {a} {b} {c} {d} =>
           Bifunctor__Constant_bimap ;
         Data.Bifunctor.first__ := fun {a} {b} {c} => Bifunctor__Constant_first ;
         Data.Bifunctor.second__ := fun {b} {c} {a} => Bifunctor__Constant_second |}.

Program Instance Bitraversable__Constant
   : Data.Bitraversable.Bitraversable Constant :=
  fun _ k =>
    k {| Data.Bitraversable.bitraverse__ := fun {f}
         {a}
         {c}
         {b}
         {d}
         `{GHC.Base.Applicative f} =>
           Bitraversable__Constant_bitraverse |}.

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

Local Definition Applicative__Constant_op_zlztzg__ {inst_a} `{(GHC.Base.Monoid
   inst_a)}
   : forall {a} {b},
     (Constant inst_a) (a -> b) -> (Constant inst_a) a -> (Constant inst_a) b :=
  fun {a} {b} =>
    fun arg_0__ arg_1__ =>
      match arg_0__, arg_1__ with
      | Mk_Constant x, Mk_Constant y => Mk_Constant (GHC.Base.mappend x y)
      end.

Local Definition Functor__Constant_fmap {inst_a}
   : forall {a} {b}, (a -> b) -> (Constant inst_a) a -> (Constant inst_a) b :=
  fun {a} {b} =>
    fun arg_0__ arg_1__ =>
      match arg_0__, arg_1__ with
      | _, Mk_Constant x => Mk_Constant x
      end.

Local Definition Functor__Constant_op_zlzd__ {inst_a}
   : forall {a} {b}, a -> (Constant inst_a) b -> (Constant inst_a) a :=
  fun {a} {b} => Functor__Constant_fmap GHC.Base.∘ GHC.Base.const.

Program Instance Functor__Constant {a} : GHC.Base.Functor (Constant a) :=
  fun _ k =>
    k {| GHC.Base.fmap__ := fun {a} {b} => Functor__Constant_fmap ;
         GHC.Base.op_zlzd____ := fun {a} {b} => Functor__Constant_op_zlzd__ |}.

Local Definition Applicative__Constant_liftA2 {inst_a} `{(GHC.Base.Monoid
   inst_a)}
   : forall {a} {b} {c},
     (a -> b -> c) ->
     (Constant inst_a) a -> (Constant inst_a) b -> (Constant inst_a) c :=
  fun {a} {b} {c} =>
    fun f x => Applicative__Constant_op_zlztzg__ (GHC.Base.fmap f x).

Local Definition Applicative__Constant_op_ztzg__ {inst_a} `{(GHC.Base.Monoid
   inst_a)}
   : forall {a} {b},
     (Constant inst_a) a -> (Constant inst_a) b -> (Constant inst_a) b :=
  fun {a} {b} =>
    fun a1 a2 => Applicative__Constant_op_zlztzg__ (GHC.Base.id GHC.Base.<$ a1) a2.

Local Definition Applicative__Constant_pure {inst_a} `{(GHC.Base.Monoid inst_a)}
   : forall {a}, a -> (Constant inst_a) a :=
  fun {a} => fun arg_0__ => Mk_Constant GHC.Base.mempty.

Program Instance Applicative__Constant {a} `{(GHC.Base.Monoid a)}
   : GHC.Base.Applicative (Constant a) :=
  fun _ k =>
    k {| GHC.Base.liftA2__ := fun {a} {b} {c} => Applicative__Constant_liftA2 ;
         GHC.Base.op_zlztzg____ := fun {a} {b} => Applicative__Constant_op_zlztzg__ ;
         GHC.Base.op_ztzg____ := fun {a} {b} => Applicative__Constant_op_ztzg__ ;
         GHC.Base.pure__ := fun {a} => Applicative__Constant_pure |}.

Local Definition Traversable__Constant_traverse {inst_a}
   : forall {f} {a} {b},
     forall `{GHC.Base.Applicative f},
     (a -> f b) -> (Constant inst_a) a -> f ((Constant inst_a) b) :=
  fun {f} {a} {b} `{GHC.Base.Applicative f} =>
    fun arg_0__ arg_1__ =>
      match arg_0__, arg_1__ with
      | _, Mk_Constant x => GHC.Base.pure (Mk_Constant x)
      end.

Local Definition Traversable__Constant_mapM {inst_a}
   : forall {m} {a} {b},
     forall `{GHC.Base.Monad m},
     (a -> m b) -> (Constant inst_a) a -> m ((Constant inst_a) b) :=
  fun {m} {a} {b} `{GHC.Base.Monad m} => Traversable__Constant_traverse.

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

Local Definition Foldable__Constant_foldMap {inst_a}
   : forall {m} {a},
     forall `{GHC.Base.Monoid m}, (a -> m) -> (Constant inst_a) a -> m :=
  fun {m} {a} `{GHC.Base.Monoid m} =>
    fun arg_0__ arg_1__ =>
      match arg_0__, arg_1__ with
      | _, Mk_Constant _ => GHC.Base.mempty
      end.

Local Definition Foldable__Constant_fold {inst_a}
   : forall {m}, forall `{GHC.Base.Monoid m}, (Constant inst_a) m -> m :=
  fun {m} `{GHC.Base.Monoid m} => Foldable__Constant_foldMap GHC.Base.id.

Local Definition Foldable__Constant_foldl {inst_a}
   : forall {b} {a}, (b -> a -> b) -> b -> (Constant inst_a) a -> b :=
  fun {b} {a} =>
    fun f z t =>
      Data.SemigroupInternal.appEndo (Data.SemigroupInternal.getDual
                                      (Foldable__Constant_foldMap (Data.SemigroupInternal.Mk_Dual GHC.Base.∘
                                                                   (Data.SemigroupInternal.Mk_Endo GHC.Base.∘
                                                                    GHC.Base.flip f)) t)) z.

Local Definition Foldable__Constant_foldr {inst_a}
   : forall {a} {b}, (a -> b -> b) -> b -> (Constant inst_a) a -> b :=
  fun {a} {b} =>
    fun f z t =>
      Data.SemigroupInternal.appEndo (Foldable__Constant_foldMap
                                      (Coq.Program.Basics.compose Data.SemigroupInternal.Mk_Endo f) t) z.

Local Definition Foldable__Constant_foldl' {inst_a}
   : forall {b} {a}, (b -> a -> b) -> b -> (Constant inst_a) a -> b :=
  fun {b} {a} =>
    fun f z0 xs =>
      let f' := fun x k z => k (f z x) in
      Foldable__Constant_foldr f' GHC.Base.id xs z0.

Local Definition Foldable__Constant_foldr' {inst_a}
   : forall {a} {b}, (a -> b -> b) -> b -> (Constant inst_a) a -> b :=
  fun {a} {b} =>
    fun f z0 xs =>
      let f' := fun k x z => k (f x z) in
      Foldable__Constant_foldl f' GHC.Base.id xs z0.

Local Definition Foldable__Constant_length {inst_a}
   : forall {a}, (Constant inst_a) a -> GHC.Num.Int :=
  fun {a} => fun '(Mk_Constant _) => #0.

Local Definition Foldable__Constant_null {inst_a}
   : forall {a}, (Constant inst_a) a -> bool :=
  fun {a} => fun '(Mk_Constant _) => true.

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

Local Definition Foldable__Constant_toList {inst_a}
   : forall {a}, (Constant inst_a) a -> list a :=
  fun {a} =>
    fun t => GHC.Base.build' (fun _ => (fun c n => Foldable__Constant_foldr c n t)).

Program Instance Foldable__Constant {a} : Data.Foldable.Foldable (Constant a) :=
  fun _ k =>
    k {| Data.Foldable.fold__ := fun {m} `{GHC.Base.Monoid m} =>
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

(* Skipping all instances of class `Data.Functor.Classes.Show1', including
   `Data.Functor.Constant.Show1__Constant' *)

(* Skipping all instances of class `Data.Functor.Classes.Read1', including
   `Data.Functor.Constant.Read1__Constant' *)

Local Definition Ord2__Constant_liftCompare2
   : forall {a} {b} {c} {d},
     (a -> b -> comparison) ->
     (c -> d -> comparison) -> Constant a c -> Constant b d -> comparison :=
  fun {a} {b} {c} {d} =>
    fun arg_0__ arg_1__ arg_2__ arg_3__ =>
      match arg_0__, arg_1__, arg_2__, arg_3__ with
      | comp, _, Mk_Constant x, Mk_Constant y => comp x y
      end.

Local Definition Eq2__Constant_liftEq2
   : forall {a} {b} {c} {d},
     (a -> b -> bool) -> (c -> d -> bool) -> Constant a c -> Constant b d -> bool :=
  fun {a} {b} {c} {d} =>
    fun arg_0__ arg_1__ arg_2__ arg_3__ =>
      match arg_0__, arg_1__, arg_2__, arg_3__ with
      | eq, _, Mk_Constant x, Mk_Constant y => eq x y
      end.

Program Instance Eq2__Constant : Data.Functor.Classes.Eq2 Constant :=
  fun _ k =>
    k {| Data.Functor.Classes.liftEq2__ := fun {a} {b} {c} {d} =>
           Eq2__Constant_liftEq2 |}.

Program Instance Ord2__Constant : Data.Functor.Classes.Ord2 Constant :=
  fun _ k =>
    k {| Data.Functor.Classes.liftCompare2__ := fun {a} {b} {c} {d} =>
           Ord2__Constant_liftCompare2 |}.

Local Definition Ord1__Constant_liftCompare {inst_a} `{(GHC.Base.Ord inst_a)}
   : forall {a} {b},
     (a -> b -> comparison) ->
     (Constant inst_a) a -> (Constant inst_a) b -> comparison :=
  fun {a} {b} => Data.Functor.Classes.liftCompare2 GHC.Base.compare.

Local Definition Eq1__Constant_liftEq {inst_a} `{(GHC.Base.Eq_ inst_a)}
   : forall {a} {b},
     (a -> b -> bool) -> (Constant inst_a) a -> (Constant inst_a) b -> bool :=
  fun {a} {b} => Data.Functor.Classes.liftEq2 _GHC.Base.==_.

Program Instance Eq1__Constant {a} `{(GHC.Base.Eq_ a)}
   : Data.Functor.Classes.Eq1 (Constant a) :=
  fun _ k =>
    k {| Data.Functor.Classes.liftEq__ := fun {a} {b} => Eq1__Constant_liftEq |}.

Program Instance Ord1__Constant {a} `{(GHC.Base.Ord a)}
   : Data.Functor.Classes.Ord1 (Constant a) :=
  fun _ k =>
    k {| Data.Functor.Classes.liftCompare__ := fun {a} {b} =>
           Ord1__Constant_liftCompare |}.

(* Skipping all instances of class `Data.Functor.Classes.Show2', including
   `Data.Functor.Constant.Show2__Constant' *)

(* Skipping all instances of class `Data.Functor.Classes.Read2', including
   `Data.Functor.Constant.Read2__Constant' *)

(* Skipping all instances of class `GHC.Show.Show', including
   `Data.Functor.Constant.Show__Constant' *)

(* Skipping all instances of class `GHC.Read.Read', including
   `Data.Functor.Constant.Read__Constant' *)

(* External variables:
     Type bool comparison list true Coq.Program.Basics.compose
     Data.Bifoldable.Bifoldable Data.Bifoldable.bifoldMap__ Data.Bifoldable.bifold__
     Data.Bifoldable.bifoldl__ Data.Bifoldable.bifoldr__ Data.Bifunctor.Bifunctor
     Data.Bifunctor.bimap__ Data.Bifunctor.first__ Data.Bifunctor.second__
     Data.Bitraversable.Bitraversable Data.Bitraversable.bitraverse__
     Data.Foldable.Foldable Data.Foldable.foldMap__ Data.Foldable.fold__
     Data.Foldable.foldl'__ Data.Foldable.foldl__ Data.Foldable.foldr'__
     Data.Foldable.foldr__ Data.Foldable.length__ Data.Foldable.null__
     Data.Foldable.product__ Data.Foldable.sum__ Data.Foldable.toList__
     Data.Functor.op_zlzdzg__ Data.Functor.Classes.Eq1 Data.Functor.Classes.Eq2
     Data.Functor.Classes.Ord1 Data.Functor.Classes.Ord2
     Data.Functor.Classes.liftCompare2 Data.Functor.Classes.liftCompare2__
     Data.Functor.Classes.liftCompare__ Data.Functor.Classes.liftEq2
     Data.Functor.Classes.liftEq2__ Data.Functor.Classes.liftEq__
     Data.SemigroupInternal.Mk_Dual Data.SemigroupInternal.Mk_Endo
     Data.SemigroupInternal.Mk_Product Data.SemigroupInternal.Mk_Sum
     Data.SemigroupInternal.appEndo Data.SemigroupInternal.getDual
     Data.SemigroupInternal.getProduct Data.SemigroupInternal.getSum
     Data.Traversable.Traversable Data.Traversable.mapM__
     Data.Traversable.sequenceA__ Data.Traversable.sequence__
     Data.Traversable.traverse__ GHC.Base.Applicative GHC.Base.Eq_ GHC.Base.Functor
     GHC.Base.Monad GHC.Base.Monoid GHC.Base.Ord GHC.Base.Semigroup GHC.Base.build'
     GHC.Base.compare GHC.Base.compare__ GHC.Base.const GHC.Base.flip GHC.Base.fmap
     GHC.Base.fmap__ GHC.Base.foldr GHC.Base.id GHC.Base.liftA2__ GHC.Base.mappend
     GHC.Base.mappend__ GHC.Base.max GHC.Base.max__ GHC.Base.mconcat__
     GHC.Base.mempty GHC.Base.mempty__ GHC.Base.min GHC.Base.min__
     GHC.Base.op_z2218U__ GHC.Base.op_zeze__ GHC.Base.op_zeze____ GHC.Base.op_zg__
     GHC.Base.op_zg____ GHC.Base.op_zgze__ GHC.Base.op_zgze____ GHC.Base.op_zl__
     GHC.Base.op_zl____ GHC.Base.op_zlzd__ GHC.Base.op_zlzd____ GHC.Base.op_zlze__
     GHC.Base.op_zlze____ GHC.Base.op_zlzlzgzg__ GHC.Base.op_zlzlzgzg____
     GHC.Base.op_zlztzg____ GHC.Base.op_zsze__ GHC.Base.op_zsze____
     GHC.Base.op_ztzg____ GHC.Base.pure GHC.Base.pure__ GHC.Num.Int GHC.Num.Num
     GHC.Num.fromInteger GHC.Prim.TYPE GHC.Prim.coerce GHC.Types.LiftedRep
*)
