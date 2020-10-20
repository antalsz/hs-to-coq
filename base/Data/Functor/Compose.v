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
Require Data.Functor.
Require Data.Functor.Classes.
Require Data.SemigroupInternal.
Require Data.Traversable.
Require GHC.Base.
Require GHC.Num.
Import Data.Functor.Notations.
Import GHC.Base.Notations.
Import GHC.Num.Notations.

(* Converted type declarations: *)

Inductive Compose (f : Type -> Type) (g : Type -> Type) (a : Type) : Type
  := | Mk_Compose (getCompose : f (g a)) : Compose f g a.

Arguments Mk_Compose {_} {_} {_} _.

Definition getCompose {f : Type -> Type} {g : Type -> Type} {a : Type} (arg_0__
    : Compose f g a) :=
  let 'Mk_Compose getCompose := arg_0__ in
  getCompose.

(* Converted value declarations: *)

(* Skipping all instances of class `Data.Data.Data', including
   `Data.Functor.Compose.Data__Compose' *)

(* Skipping all instances of class `GHC.Generics.Generic', including
   `Data.Functor.Compose.Generic__Compose' *)

(* Skipping all instances of class `GHC.Generics.Generic1', including
   `Data.Functor.Compose.Generic1__Compose__5' *)

Local Definition Eq1__Compose_liftEq {inst_f} {inst_g}
  `{Data.Functor.Classes.Eq1 inst_f} `{Data.Functor.Classes.Eq1 inst_g}
   : forall {a} {b},
     (a -> b -> bool) ->
     (Compose inst_f inst_g) a -> (Compose inst_f inst_g) b -> bool :=
  fun {a} {b} =>
    fun arg_0__ arg_1__ arg_2__ =>
      match arg_0__, arg_1__, arg_2__ with
      | eq, Mk_Compose x, Mk_Compose y =>
          Data.Functor.Classes.liftEq (Data.Functor.Classes.liftEq eq) x y
      end.

Program Instance Eq1__Compose {f} {g} `{Data.Functor.Classes.Eq1 f}
  `{Data.Functor.Classes.Eq1 g}
   : Data.Functor.Classes.Eq1 (Compose f g) :=
  fun _ k__ =>
    k__ {| Data.Functor.Classes.liftEq__ := fun {a} {b} => Eq1__Compose_liftEq |}.

Local Definition Ord1__Compose_liftCompare {inst_f} {inst_g}
  `{Data.Functor.Classes.Ord1 inst_f} `{Data.Functor.Classes.Ord1 inst_g}
   : forall {a} {b},
     (a -> b -> comparison) ->
     (Compose inst_f inst_g) a -> (Compose inst_f inst_g) b -> comparison :=
  fun {a} {b} =>
    fun arg_0__ arg_1__ arg_2__ =>
      match arg_0__, arg_1__, arg_2__ with
      | comp, Mk_Compose x, Mk_Compose y =>
          Data.Functor.Classes.liftCompare (Data.Functor.Classes.liftCompare comp) x y
      end.

Program Instance Ord1__Compose {f} {g} `{Data.Functor.Classes.Ord1 f}
  `{Data.Functor.Classes.Ord1 g}
   : Data.Functor.Classes.Ord1 (Compose f g) :=
  fun _ k__ =>
    k__ {| Data.Functor.Classes.liftCompare__ := fun {a} {b} =>
             Ord1__Compose_liftCompare |}.

(* Skipping all instances of class `Data.Functor.Classes.Read1', including
   `Data.Functor.Compose.Read1__Compose' *)

(* Skipping all instances of class `Data.Functor.Classes.Show1', including
   `Data.Functor.Compose.Show1__Compose' *)

Local Definition Eq___Compose_op_zeze__ {inst_f} {inst_g} {inst_a}
  `{Data.Functor.Classes.Eq1 inst_f} `{Data.Functor.Classes.Eq1 inst_g}
  `{GHC.Base.Eq_ inst_a}
   : (Compose inst_f inst_g inst_a) -> (Compose inst_f inst_g inst_a) -> bool :=
  Data.Functor.Classes.eq1.

Local Definition Eq___Compose_op_zsze__ {inst_f} {inst_g} {inst_a}
  `{Data.Functor.Classes.Eq1 inst_f} `{Data.Functor.Classes.Eq1 inst_g}
  `{GHC.Base.Eq_ inst_a}
   : (Compose inst_f inst_g inst_a) -> (Compose inst_f inst_g inst_a) -> bool :=
  fun x y => negb (Eq___Compose_op_zeze__ x y).

Program Instance Eq___Compose {f} {g} {a} `{Data.Functor.Classes.Eq1 f}
  `{Data.Functor.Classes.Eq1 g} `{GHC.Base.Eq_ a}
   : GHC.Base.Eq_ (Compose f g a) :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zeze____ := Eq___Compose_op_zeze__ ;
           GHC.Base.op_zsze____ := Eq___Compose_op_zsze__ |}.

Local Definition Ord__Compose_compare {inst_f} {inst_g} {inst_a}
  `{Data.Functor.Classes.Ord1 inst_f} `{Data.Functor.Classes.Ord1 inst_g}
  `{GHC.Base.Ord inst_a}
   : (Compose inst_f inst_g inst_a) ->
     (Compose inst_f inst_g inst_a) -> comparison :=
  Data.Functor.Classes.compare1.

Local Definition Ord__Compose_op_zl__ {inst_f} {inst_g} {inst_a}
  `{Data.Functor.Classes.Ord1 inst_f} `{Data.Functor.Classes.Ord1 inst_g}
  `{GHC.Base.Ord inst_a}
   : (Compose inst_f inst_g inst_a) -> (Compose inst_f inst_g inst_a) -> bool :=
  fun x y => Ord__Compose_compare x y GHC.Base.== Lt.

Local Definition Ord__Compose_op_zlze__ {inst_f} {inst_g} {inst_a}
  `{Data.Functor.Classes.Ord1 inst_f} `{Data.Functor.Classes.Ord1 inst_g}
  `{GHC.Base.Ord inst_a}
   : (Compose inst_f inst_g inst_a) -> (Compose inst_f inst_g inst_a) -> bool :=
  fun x y => Ord__Compose_compare x y GHC.Base./= Gt.

Local Definition Ord__Compose_op_zg__ {inst_f} {inst_g} {inst_a}
  `{Data.Functor.Classes.Ord1 inst_f} `{Data.Functor.Classes.Ord1 inst_g}
  `{GHC.Base.Ord inst_a}
   : (Compose inst_f inst_g inst_a) -> (Compose inst_f inst_g inst_a) -> bool :=
  fun x y => Ord__Compose_compare x y GHC.Base.== Gt.

Local Definition Ord__Compose_op_zgze__ {inst_f} {inst_g} {inst_a}
  `{Data.Functor.Classes.Ord1 inst_f} `{Data.Functor.Classes.Ord1 inst_g}
  `{GHC.Base.Ord inst_a}
   : (Compose inst_f inst_g inst_a) -> (Compose inst_f inst_g inst_a) -> bool :=
  fun x y => Ord__Compose_compare x y GHC.Base./= Lt.

Local Definition Ord__Compose_max {inst_f} {inst_g} {inst_a}
  `{Data.Functor.Classes.Ord1 inst_f} `{Data.Functor.Classes.Ord1 inst_g}
  `{GHC.Base.Ord inst_a}
   : (Compose inst_f inst_g inst_a) ->
     (Compose inst_f inst_g inst_a) -> (Compose inst_f inst_g inst_a) :=
  fun x y => if Ord__Compose_op_zlze__ x y : bool then y else x.

Local Definition Ord__Compose_min {inst_f} {inst_g} {inst_a}
  `{Data.Functor.Classes.Ord1 inst_f} `{Data.Functor.Classes.Ord1 inst_g}
  `{GHC.Base.Ord inst_a}
   : (Compose inst_f inst_g inst_a) ->
     (Compose inst_f inst_g inst_a) -> (Compose inst_f inst_g inst_a) :=
  fun x y => if Ord__Compose_op_zlze__ x y : bool then x else y.

Program Instance Ord__Compose {f} {g} {a} `{Data.Functor.Classes.Ord1 f}
  `{Data.Functor.Classes.Ord1 g} `{GHC.Base.Ord a}
   : GHC.Base.Ord (Compose f g a) :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zl____ := Ord__Compose_op_zl__ ;
           GHC.Base.op_zlze____ := Ord__Compose_op_zlze__ ;
           GHC.Base.op_zg____ := Ord__Compose_op_zg__ ;
           GHC.Base.op_zgze____ := Ord__Compose_op_zgze__ ;
           GHC.Base.compare__ := Ord__Compose_compare ;
           GHC.Base.max__ := Ord__Compose_max ;
           GHC.Base.min__ := Ord__Compose_min |}.

(* Skipping all instances of class `GHC.Read.Read', including
   `Data.Functor.Compose.Read__Compose' *)

(* Skipping all instances of class `GHC.Show.Show', including
   `Data.Functor.Compose.Show__Compose' *)

Local Definition Functor__Compose_fmap {inst_f} {inst_g} `{GHC.Base.Functor
  inst_f} `{GHC.Base.Functor inst_g}
   : forall {a} {b},
     (a -> b) -> (Compose inst_f inst_g) a -> (Compose inst_f inst_g) b :=
  fun {a} {b} =>
    fun arg_0__ arg_1__ =>
      match arg_0__, arg_1__ with
      | f, Mk_Compose x => Mk_Compose (GHC.Base.fmap (GHC.Base.fmap f) x)
      end.

Local Definition Functor__Compose_op_zlzd__ {inst_f} {inst_g} `{GHC.Base.Functor
  inst_f} `{GHC.Base.Functor inst_g}
   : forall {a} {b},
     a -> (Compose inst_f inst_g) b -> (Compose inst_f inst_g) a :=
  fun {a} {b} => Functor__Compose_fmap GHC.Base.∘ GHC.Base.const.

Program Instance Functor__Compose {f} {g} `{GHC.Base.Functor f}
  `{GHC.Base.Functor g}
   : GHC.Base.Functor (Compose f g) :=
  fun _ k__ =>
    k__ {| GHC.Base.fmap__ := fun {a} {b} => Functor__Compose_fmap ;
           GHC.Base.op_zlzd____ := fun {a} {b} => Functor__Compose_op_zlzd__ |}.

Local Definition Foldable__Compose_foldMap {inst_f} {inst_g}
  `{Data.Foldable.Foldable inst_f} `{Data.Foldable.Foldable inst_g}
   : forall {m} {a},
     forall `{GHC.Base.Monoid m}, (a -> m) -> (Compose inst_f inst_g) a -> m :=
  fun {m} {a} `{GHC.Base.Monoid m} =>
    fun arg_0__ arg_1__ =>
      match arg_0__, arg_1__ with
      | f, Mk_Compose t => Data.Foldable.foldMap (Data.Foldable.foldMap f) t
      end.

Local Definition Foldable__Compose_fold {inst_f} {inst_g}
  `{Data.Foldable.Foldable inst_f} `{Data.Foldable.Foldable inst_g}
   : forall {m}, forall `{GHC.Base.Monoid m}, (Compose inst_f inst_g) m -> m :=
  fun {m} `{GHC.Base.Monoid m} => Foldable__Compose_foldMap GHC.Base.id.

Local Definition Foldable__Compose_foldl {inst_f} {inst_g}
  `{Data.Foldable.Foldable inst_f} `{Data.Foldable.Foldable inst_g}
   : forall {b} {a}, (b -> a -> b) -> b -> (Compose inst_f inst_g) a -> b :=
  fun {b} {a} =>
    fun f z t =>
      Data.SemigroupInternal.appEndo (Data.SemigroupInternal.getDual
                                      (Foldable__Compose_foldMap (Data.SemigroupInternal.Mk_Dual GHC.Base.∘
                                                                  (Data.SemigroupInternal.Mk_Endo GHC.Base.∘
                                                                   GHC.Base.flip f)) t)) z.

Local Definition Foldable__Compose_foldr {inst_f} {inst_g}
  `{Data.Foldable.Foldable inst_f} `{Data.Foldable.Foldable inst_g}
   : forall {a} {b}, (a -> b -> b) -> b -> (Compose inst_f inst_g) a -> b :=
  fun {a} {b} =>
    fun f z t =>
      Data.SemigroupInternal.appEndo (Foldable__Compose_foldMap
                                      (Coq.Program.Basics.compose Data.SemigroupInternal.Mk_Endo f) t) z.

Local Definition Foldable__Compose_foldl' {inst_f} {inst_g}
  `{Data.Foldable.Foldable inst_f} `{Data.Foldable.Foldable inst_g}
   : forall {b} {a}, (b -> a -> b) -> b -> (Compose inst_f inst_g) a -> b :=
  fun {b} {a} =>
    fun f z0 xs =>
      let f' := fun x k z => k (f z x) in
      Foldable__Compose_foldr f' GHC.Base.id xs z0.

Local Definition Foldable__Compose_foldr' {inst_f} {inst_g}
  `{Data.Foldable.Foldable inst_f} `{Data.Foldable.Foldable inst_g}
   : forall {a} {b}, (a -> b -> b) -> b -> (Compose inst_f inst_g) a -> b :=
  fun {a} {b} =>
    fun f z0 xs =>
      let f' := fun k x z => k (f x z) in
      Foldable__Compose_foldl f' GHC.Base.id xs z0.

Local Definition Foldable__Compose_length {inst_f} {inst_g}
  `{Data.Foldable.Foldable inst_f} `{Data.Foldable.Foldable inst_g}
   : forall {a}, (Compose inst_f inst_g) a -> GHC.Num.Int :=
  fun {a} =>
    Foldable__Compose_foldl' (fun arg_0__ arg_1__ =>
                                match arg_0__, arg_1__ with
                                | c, _ => c GHC.Num.+ #1
                                end) #0.

Local Definition Foldable__Compose_null {inst_f} {inst_g}
  `{Data.Foldable.Foldable inst_f} `{Data.Foldable.Foldable inst_g}
   : forall {a}, (Compose inst_f inst_g) a -> bool :=
  fun {a} => Foldable__Compose_foldr (fun arg_0__ arg_1__ => false) true.

Local Definition Foldable__Compose_product {inst_f} {inst_g}
  `{Data.Foldable.Foldable inst_f} `{Data.Foldable.Foldable inst_g}
   : forall {a}, forall `{GHC.Num.Num a}, (Compose inst_f inst_g) a -> a :=
  fun {a} `{GHC.Num.Num a} =>
    Coq.Program.Basics.compose Data.SemigroupInternal.getProduct
                               (Foldable__Compose_foldMap Data.SemigroupInternal.Mk_Product).

Local Definition Foldable__Compose_sum {inst_f} {inst_g}
  `{Data.Foldable.Foldable inst_f} `{Data.Foldable.Foldable inst_g}
   : forall {a}, forall `{GHC.Num.Num a}, (Compose inst_f inst_g) a -> a :=
  fun {a} `{GHC.Num.Num a} =>
    Coq.Program.Basics.compose Data.SemigroupInternal.getSum
                               (Foldable__Compose_foldMap Data.SemigroupInternal.Mk_Sum).

Local Definition Foldable__Compose_toList {inst_f} {inst_g}
  `{Data.Foldable.Foldable inst_f} `{Data.Foldable.Foldable inst_g}
   : forall {a}, (Compose inst_f inst_g) a -> list a :=
  fun {a} =>
    fun t => GHC.Base.build' (fun _ => (fun c n => Foldable__Compose_foldr c n t)).

Program Instance Foldable__Compose {f} {g} `{Data.Foldable.Foldable f}
  `{Data.Foldable.Foldable g}
   : Data.Foldable.Foldable (Compose f g) :=
  fun _ k__ =>
    k__ {| Data.Foldable.fold__ := fun {m} `{GHC.Base.Monoid m} =>
             Foldable__Compose_fold ;
           Data.Foldable.foldMap__ := fun {m} {a} `{GHC.Base.Monoid m} =>
             Foldable__Compose_foldMap ;
           Data.Foldable.foldl__ := fun {b} {a} => Foldable__Compose_foldl ;
           Data.Foldable.foldl'__ := fun {b} {a} => Foldable__Compose_foldl' ;
           Data.Foldable.foldr__ := fun {a} {b} => Foldable__Compose_foldr ;
           Data.Foldable.foldr'__ := fun {a} {b} => Foldable__Compose_foldr' ;
           Data.Foldable.length__ := fun {a} => Foldable__Compose_length ;
           Data.Foldable.null__ := fun {a} => Foldable__Compose_null ;
           Data.Foldable.product__ := fun {a} `{GHC.Num.Num a} =>
             Foldable__Compose_product ;
           Data.Foldable.sum__ := fun {a} `{GHC.Num.Num a} => Foldable__Compose_sum ;
           Data.Foldable.toList__ := fun {a} => Foldable__Compose_toList |}.

Local Definition Traversable__Compose_traverse {inst_f} {inst_g}
  `{Data.Traversable.Traversable inst_f} `{Data.Traversable.Traversable inst_g}
   : forall {f} {a} {b},
     forall `{GHC.Base.Applicative f},
     (a -> f b) -> (Compose inst_f inst_g) a -> f ((Compose inst_f inst_g) b) :=
  fun {f} {a} {b} `{GHC.Base.Applicative f} =>
    fun arg_0__ arg_1__ =>
      match arg_0__, arg_1__ with
      | f, Mk_Compose t =>
          Mk_Compose Data.Functor.<$>
          Data.Traversable.traverse (Data.Traversable.traverse f) t
      end.

Local Definition Traversable__Compose_mapM {inst_f} {inst_g}
  `{Data.Traversable.Traversable inst_f} `{Data.Traversable.Traversable inst_g}
   : forall {m} {a} {b},
     forall `{GHC.Base.Monad m},
     (a -> m b) -> (Compose inst_f inst_g) a -> m ((Compose inst_f inst_g) b) :=
  fun {m} {a} {b} `{GHC.Base.Monad m} => Traversable__Compose_traverse.

Local Definition Traversable__Compose_sequenceA {inst_f} {inst_g}
  `{Data.Traversable.Traversable inst_f} `{Data.Traversable.Traversable inst_g}
   : forall {f} {a},
     forall `{GHC.Base.Applicative f},
     (Compose inst_f inst_g) (f a) -> f ((Compose inst_f inst_g) a) :=
  fun {f} {a} `{GHC.Base.Applicative f} =>
    Traversable__Compose_traverse GHC.Base.id.

Local Definition Traversable__Compose_sequence {inst_f} {inst_g}
  `{Data.Traversable.Traversable inst_f} `{Data.Traversable.Traversable inst_g}
   : forall {m} {a},
     forall `{GHC.Base.Monad m},
     (Compose inst_f inst_g) (m a) -> m ((Compose inst_f inst_g) a) :=
  fun {m} {a} `{GHC.Base.Monad m} => Traversable__Compose_sequenceA.

Program Instance Traversable__Compose {f} {g} `{Data.Traversable.Traversable f}
  `{Data.Traversable.Traversable g}
   : Data.Traversable.Traversable (Compose f g) :=
  fun _ k__ =>
    k__ {| Data.Traversable.mapM__ := fun {m} {a} {b} `{GHC.Base.Monad m} =>
             Traversable__Compose_mapM ;
           Data.Traversable.sequence__ := fun {m} {a} `{GHC.Base.Monad m} =>
             Traversable__Compose_sequence ;
           Data.Traversable.sequenceA__ := fun {f} {a} `{GHC.Base.Applicative f} =>
             Traversable__Compose_sequenceA ;
           Data.Traversable.traverse__ := fun {f} {a} {b} `{GHC.Base.Applicative f} =>
             Traversable__Compose_traverse |}.

Local Definition Applicative__Compose_liftA2 {inst_f} {inst_g}
  `{GHC.Base.Applicative inst_f} `{GHC.Base.Applicative inst_g}
   : forall {a} {b} {c},
     (a -> b -> c) ->
     (Compose inst_f inst_g) a ->
     (Compose inst_f inst_g) b -> (Compose inst_f inst_g) c :=
  fun {a} {b} {c} =>
    fun arg_0__ arg_1__ arg_2__ =>
      match arg_0__, arg_1__, arg_2__ with
      | f, Mk_Compose x, Mk_Compose y =>
          Mk_Compose (GHC.Base.liftA2 (GHC.Base.liftA2 f) x y)
      end.

Local Definition Applicative__Compose_op_zlztzg__ {inst_f} {inst_g}
  `{GHC.Base.Applicative inst_f} `{GHC.Base.Applicative inst_g}
   : forall {a} {b},
     (Compose inst_f inst_g) (a -> b) ->
     (Compose inst_f inst_g) a -> (Compose inst_f inst_g) b :=
  fun {a} {b} =>
    fun arg_0__ arg_1__ =>
      match arg_0__, arg_1__ with
      | Mk_Compose f, Mk_Compose x => Mk_Compose (GHC.Base.liftA2 _GHC.Base.<*>_ f x)
      end.

Local Definition Applicative__Compose_op_ztzg__ {inst_f} {inst_g}
  `{GHC.Base.Applicative inst_f} `{GHC.Base.Applicative inst_g}
   : forall {a} {b},
     (Compose inst_f inst_g) a ->
     (Compose inst_f inst_g) b -> (Compose inst_f inst_g) b :=
  fun {a} {b} =>
    fun a1 a2 => Applicative__Compose_op_zlztzg__ (GHC.Base.id GHC.Base.<$ a1) a2.

Local Definition Applicative__Compose_pure {inst_f} {inst_g}
  `{GHC.Base.Applicative inst_f} `{GHC.Base.Applicative inst_g}
   : forall {a}, a -> (Compose inst_f inst_g) a :=
  fun {a} => fun x => Mk_Compose (GHC.Base.pure (GHC.Base.pure x)).

Program Instance Applicative__Compose {f} {g} `{GHC.Base.Applicative f}
  `{GHC.Base.Applicative g}
   : GHC.Base.Applicative (Compose f g) :=
  fun _ k__ =>
    k__ {| GHC.Base.liftA2__ := fun {a} {b} {c} => Applicative__Compose_liftA2 ;
           GHC.Base.op_zlztzg____ := fun {a} {b} => Applicative__Compose_op_zlztzg__ ;
           GHC.Base.op_ztzg____ := fun {a} {b} => Applicative__Compose_op_ztzg__ ;
           GHC.Base.pure__ := fun {a} => Applicative__Compose_pure |}.

(* Skipping all instances of class `GHC.Base.Alternative', including
   `Data.Functor.Compose.Alternative__Compose' *)

(* External variables:
     Gt Lt Type bool comparison false list negb true Coq.Program.Basics.compose
     Data.Foldable.Foldable Data.Foldable.foldMap Data.Foldable.foldMap__
     Data.Foldable.fold__ Data.Foldable.foldl'__ Data.Foldable.foldl__
     Data.Foldable.foldr'__ Data.Foldable.foldr__ Data.Foldable.length__
     Data.Foldable.null__ Data.Foldable.product__ Data.Foldable.sum__
     Data.Foldable.toList__ Data.Functor.op_zlzdzg__ Data.Functor.Classes.Eq1
     Data.Functor.Classes.Ord1 Data.Functor.Classes.compare1 Data.Functor.Classes.eq1
     Data.Functor.Classes.liftCompare Data.Functor.Classes.liftCompare__
     Data.Functor.Classes.liftEq Data.Functor.Classes.liftEq__
     Data.SemigroupInternal.Mk_Dual Data.SemigroupInternal.Mk_Endo
     Data.SemigroupInternal.Mk_Product Data.SemigroupInternal.Mk_Sum
     Data.SemigroupInternal.appEndo Data.SemigroupInternal.getDual
     Data.SemigroupInternal.getProduct Data.SemigroupInternal.getSum
     Data.Traversable.Traversable Data.Traversable.mapM__
     Data.Traversable.sequenceA__ Data.Traversable.sequence__
     Data.Traversable.traverse Data.Traversable.traverse__ GHC.Base.Applicative
     GHC.Base.Eq_ GHC.Base.Functor GHC.Base.Monad GHC.Base.Monoid GHC.Base.Ord
     GHC.Base.build' GHC.Base.compare__ GHC.Base.const GHC.Base.flip GHC.Base.fmap
     GHC.Base.fmap__ GHC.Base.id GHC.Base.liftA2 GHC.Base.liftA2__ GHC.Base.max__
     GHC.Base.min__ GHC.Base.op_z2218U__ GHC.Base.op_zeze__ GHC.Base.op_zeze____
     GHC.Base.op_zg____ GHC.Base.op_zgze____ GHC.Base.op_zl____ GHC.Base.op_zlzd__
     GHC.Base.op_zlzd____ GHC.Base.op_zlze____ GHC.Base.op_zlztzg__
     GHC.Base.op_zlztzg____ GHC.Base.op_zsze__ GHC.Base.op_zsze____
     GHC.Base.op_ztzg____ GHC.Base.pure GHC.Base.pure__ GHC.Num.Int GHC.Num.Num
     GHC.Num.fromInteger GHC.Num.op_zp__
*)
