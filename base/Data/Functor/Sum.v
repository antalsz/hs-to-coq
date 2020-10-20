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

Inductive Sum (f : Type -> Type) (g : Type -> Type) a : Type
  := | InL : (f a) -> Sum f g a
  |  InR : (g a) -> Sum f g a.

Arguments InL {_} {_} {_} _.

Arguments InR {_} {_} {_} _.

(* Converted value declarations: *)

(* Skipping all instances of class `Data.Data.Data', including
   `Data.Functor.Sum.Data__Sum' *)

(* Skipping all instances of class `GHC.Generics.Generic', including
   `Data.Functor.Sum.Generic__Sum' *)

(* Skipping all instances of class `GHC.Generics.Generic1', including
   `Data.Functor.Sum.Generic1__Sum__5' *)

Local Definition Eq1__Sum_liftEq {inst_f} {inst_g} `{Data.Functor.Classes.Eq1
  inst_f} `{Data.Functor.Classes.Eq1 inst_g}
   : forall {a} {b},
     (a -> b -> bool) -> (Sum inst_f inst_g) a -> (Sum inst_f inst_g) b -> bool :=
  fun {a} {b} =>
    fun arg_0__ arg_1__ arg_2__ =>
      match arg_0__, arg_1__, arg_2__ with
      | eq, InL x1, InL x2 => Data.Functor.Classes.liftEq eq x1 x2
      | _, InL _, InR _ => false
      | _, InR _, InL _ => false
      | eq, InR y1, InR y2 => Data.Functor.Classes.liftEq eq y1 y2
      end.

Program Instance Eq1__Sum {f} {g} `{Data.Functor.Classes.Eq1 f}
  `{Data.Functor.Classes.Eq1 g}
   : Data.Functor.Classes.Eq1 (Sum f g) :=
  fun _ k__ =>
    k__ {| Data.Functor.Classes.liftEq__ := fun {a} {b} => Eq1__Sum_liftEq |}.

Local Definition Ord1__Sum_liftCompare {inst_f} {inst_g}
  `{Data.Functor.Classes.Ord1 inst_f} `{Data.Functor.Classes.Ord1 inst_g}
   : forall {a} {b},
     (a -> b -> comparison) ->
     (Sum inst_f inst_g) a -> (Sum inst_f inst_g) b -> comparison :=
  fun {a} {b} =>
    fun arg_0__ arg_1__ arg_2__ =>
      match arg_0__, arg_1__, arg_2__ with
      | comp, InL x1, InL x2 => Data.Functor.Classes.liftCompare comp x1 x2
      | _, InL _, InR _ => Lt
      | _, InR _, InL _ => Gt
      | comp, InR y1, InR y2 => Data.Functor.Classes.liftCompare comp y1 y2
      end.

Program Instance Ord1__Sum {f} {g} `{Data.Functor.Classes.Ord1 f}
  `{Data.Functor.Classes.Ord1 g}
   : Data.Functor.Classes.Ord1 (Sum f g) :=
  fun _ k__ =>
    k__ {| Data.Functor.Classes.liftCompare__ := fun {a} {b} =>
             Ord1__Sum_liftCompare |}.

(* Skipping all instances of class `Data.Functor.Classes.Read1', including
   `Data.Functor.Sum.Read1__Sum' *)

(* Skipping all instances of class `Data.Functor.Classes.Show1', including
   `Data.Functor.Sum.Show1__Sum' *)

Local Definition Eq___Sum_op_zeze__ {inst_f} {inst_g} {inst_a}
  `{Data.Functor.Classes.Eq1 inst_f} `{Data.Functor.Classes.Eq1 inst_g}
  `{GHC.Base.Eq_ inst_a}
   : (Sum inst_f inst_g inst_a) -> (Sum inst_f inst_g inst_a) -> bool :=
  Data.Functor.Classes.eq1.

Local Definition Eq___Sum_op_zsze__ {inst_f} {inst_g} {inst_a}
  `{Data.Functor.Classes.Eq1 inst_f} `{Data.Functor.Classes.Eq1 inst_g}
  `{GHC.Base.Eq_ inst_a}
   : (Sum inst_f inst_g inst_a) -> (Sum inst_f inst_g inst_a) -> bool :=
  fun x y => negb (Eq___Sum_op_zeze__ x y).

Program Instance Eq___Sum {f} {g} {a} `{Data.Functor.Classes.Eq1 f}
  `{Data.Functor.Classes.Eq1 g} `{GHC.Base.Eq_ a}
   : GHC.Base.Eq_ (Sum f g a) :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zeze____ := Eq___Sum_op_zeze__ ;
           GHC.Base.op_zsze____ := Eq___Sum_op_zsze__ |}.

Local Definition Ord__Sum_compare {inst_f} {inst_g} {inst_a}
  `{Data.Functor.Classes.Ord1 inst_f} `{Data.Functor.Classes.Ord1 inst_g}
  `{GHC.Base.Ord inst_a}
   : (Sum inst_f inst_g inst_a) -> (Sum inst_f inst_g inst_a) -> comparison :=
  Data.Functor.Classes.compare1.

Local Definition Ord__Sum_op_zl__ {inst_f} {inst_g} {inst_a}
  `{Data.Functor.Classes.Ord1 inst_f} `{Data.Functor.Classes.Ord1 inst_g}
  `{GHC.Base.Ord inst_a}
   : (Sum inst_f inst_g inst_a) -> (Sum inst_f inst_g inst_a) -> bool :=
  fun x y => Ord__Sum_compare x y GHC.Base.== Lt.

Local Definition Ord__Sum_op_zlze__ {inst_f} {inst_g} {inst_a}
  `{Data.Functor.Classes.Ord1 inst_f} `{Data.Functor.Classes.Ord1 inst_g}
  `{GHC.Base.Ord inst_a}
   : (Sum inst_f inst_g inst_a) -> (Sum inst_f inst_g inst_a) -> bool :=
  fun x y => Ord__Sum_compare x y GHC.Base./= Gt.

Local Definition Ord__Sum_op_zg__ {inst_f} {inst_g} {inst_a}
  `{Data.Functor.Classes.Ord1 inst_f} `{Data.Functor.Classes.Ord1 inst_g}
  `{GHC.Base.Ord inst_a}
   : (Sum inst_f inst_g inst_a) -> (Sum inst_f inst_g inst_a) -> bool :=
  fun x y => Ord__Sum_compare x y GHC.Base.== Gt.

Local Definition Ord__Sum_op_zgze__ {inst_f} {inst_g} {inst_a}
  `{Data.Functor.Classes.Ord1 inst_f} `{Data.Functor.Classes.Ord1 inst_g}
  `{GHC.Base.Ord inst_a}
   : (Sum inst_f inst_g inst_a) -> (Sum inst_f inst_g inst_a) -> bool :=
  fun x y => Ord__Sum_compare x y GHC.Base./= Lt.

Local Definition Ord__Sum_max {inst_f} {inst_g} {inst_a}
  `{Data.Functor.Classes.Ord1 inst_f} `{Data.Functor.Classes.Ord1 inst_g}
  `{GHC.Base.Ord inst_a}
   : (Sum inst_f inst_g inst_a) ->
     (Sum inst_f inst_g inst_a) -> (Sum inst_f inst_g inst_a) :=
  fun x y => if Ord__Sum_op_zlze__ x y : bool then y else x.

Local Definition Ord__Sum_min {inst_f} {inst_g} {inst_a}
  `{Data.Functor.Classes.Ord1 inst_f} `{Data.Functor.Classes.Ord1 inst_g}
  `{GHC.Base.Ord inst_a}
   : (Sum inst_f inst_g inst_a) ->
     (Sum inst_f inst_g inst_a) -> (Sum inst_f inst_g inst_a) :=
  fun x y => if Ord__Sum_op_zlze__ x y : bool then x else y.

Program Instance Ord__Sum {f} {g} {a} `{Data.Functor.Classes.Ord1 f}
  `{Data.Functor.Classes.Ord1 g} `{GHC.Base.Ord a}
   : GHC.Base.Ord (Sum f g a) :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zl____ := Ord__Sum_op_zl__ ;
           GHC.Base.op_zlze____ := Ord__Sum_op_zlze__ ;
           GHC.Base.op_zg____ := Ord__Sum_op_zg__ ;
           GHC.Base.op_zgze____ := Ord__Sum_op_zgze__ ;
           GHC.Base.compare__ := Ord__Sum_compare ;
           GHC.Base.max__ := Ord__Sum_max ;
           GHC.Base.min__ := Ord__Sum_min |}.

(* Skipping all instances of class `GHC.Read.Read', including
   `Data.Functor.Sum.Read__Sum' *)

(* Skipping all instances of class `GHC.Show.Show', including
   `Data.Functor.Sum.Show__Sum' *)

Local Definition Functor__Sum_fmap {inst_f} {inst_g} `{GHC.Base.Functor inst_f}
  `{GHC.Base.Functor inst_g}
   : forall {a} {b}, (a -> b) -> (Sum inst_f inst_g) a -> (Sum inst_f inst_g) b :=
  fun {a} {b} =>
    fun arg_0__ arg_1__ =>
      match arg_0__, arg_1__ with
      | f, InL x => InL (GHC.Base.fmap f x)
      | f, InR y => InR (GHC.Base.fmap f y)
      end.

Local Definition Functor__Sum_op_zlzd__ {inst_f} {inst_g} `{GHC.Base.Functor
  inst_f} `{GHC.Base.Functor inst_g}
   : forall {a} {b}, a -> (Sum inst_f inst_g) b -> (Sum inst_f inst_g) a :=
  fun {a} {b} => Functor__Sum_fmap GHC.Base.∘ GHC.Base.const.

Program Instance Functor__Sum {f} {g} `{GHC.Base.Functor f} `{GHC.Base.Functor
  g}
   : GHC.Base.Functor (Sum f g) :=
  fun _ k__ =>
    k__ {| GHC.Base.fmap__ := fun {a} {b} => Functor__Sum_fmap ;
           GHC.Base.op_zlzd____ := fun {a} {b} => Functor__Sum_op_zlzd__ |}.

Local Definition Foldable__Sum_foldMap {inst_f} {inst_g}
  `{Data.Foldable.Foldable inst_f} `{Data.Foldable.Foldable inst_g}
   : forall {m} {a},
     forall `{GHC.Base.Monoid m}, (a -> m) -> (Sum inst_f inst_g) a -> m :=
  fun {m} {a} `{GHC.Base.Monoid m} =>
    fun arg_0__ arg_1__ =>
      match arg_0__, arg_1__ with
      | f, InL x => Data.Foldable.foldMap f x
      | f, InR y => Data.Foldable.foldMap f y
      end.

Local Definition Foldable__Sum_fold {inst_f} {inst_g} `{Data.Foldable.Foldable
  inst_f} `{Data.Foldable.Foldable inst_g}
   : forall {m}, forall `{GHC.Base.Monoid m}, (Sum inst_f inst_g) m -> m :=
  fun {m} `{GHC.Base.Monoid m} => Foldable__Sum_foldMap GHC.Base.id.

Local Definition Foldable__Sum_foldl {inst_f} {inst_g} `{Data.Foldable.Foldable
  inst_f} `{Data.Foldable.Foldable inst_g}
   : forall {b} {a}, (b -> a -> b) -> b -> (Sum inst_f inst_g) a -> b :=
  fun {b} {a} =>
    fun f z t =>
      Data.SemigroupInternal.appEndo (Data.SemigroupInternal.getDual
                                      (Foldable__Sum_foldMap (Data.SemigroupInternal.Mk_Dual GHC.Base.∘
                                                              (Data.SemigroupInternal.Mk_Endo GHC.Base.∘
                                                               GHC.Base.flip f)) t)) z.

Local Definition Foldable__Sum_foldr {inst_f} {inst_g} `{Data.Foldable.Foldable
  inst_f} `{Data.Foldable.Foldable inst_g}
   : forall {a} {b}, (a -> b -> b) -> b -> (Sum inst_f inst_g) a -> b :=
  fun {a} {b} =>
    fun f z t =>
      Data.SemigroupInternal.appEndo (Foldable__Sum_foldMap
                                      (Coq.Program.Basics.compose Data.SemigroupInternal.Mk_Endo f) t) z.

Local Definition Foldable__Sum_foldl' {inst_f} {inst_g} `{Data.Foldable.Foldable
  inst_f} `{Data.Foldable.Foldable inst_g}
   : forall {b} {a}, (b -> a -> b) -> b -> (Sum inst_f inst_g) a -> b :=
  fun {b} {a} =>
    fun f z0 xs =>
      let f' := fun x k z => k (f z x) in Foldable__Sum_foldr f' GHC.Base.id xs z0.

Local Definition Foldable__Sum_foldr' {inst_f} {inst_g} `{Data.Foldable.Foldable
  inst_f} `{Data.Foldable.Foldable inst_g}
   : forall {a} {b}, (a -> b -> b) -> b -> (Sum inst_f inst_g) a -> b :=
  fun {a} {b} =>
    fun f z0 xs =>
      let f' := fun k x z => k (f x z) in Foldable__Sum_foldl f' GHC.Base.id xs z0.

Local Definition Foldable__Sum_length {inst_f} {inst_g} `{Data.Foldable.Foldable
  inst_f} `{Data.Foldable.Foldable inst_g}
   : forall {a}, (Sum inst_f inst_g) a -> GHC.Num.Int :=
  fun {a} =>
    Foldable__Sum_foldl' (fun arg_0__ arg_1__ =>
                            match arg_0__, arg_1__ with
                            | c, _ => c GHC.Num.+ #1
                            end) #0.

Local Definition Foldable__Sum_null {inst_f} {inst_g} `{Data.Foldable.Foldable
  inst_f} `{Data.Foldable.Foldable inst_g}
   : forall {a}, (Sum inst_f inst_g) a -> bool :=
  fun {a} => Foldable__Sum_foldr (fun arg_0__ arg_1__ => false) true.

Local Definition Foldable__Sum_product {inst_f} {inst_g}
  `{Data.Foldable.Foldable inst_f} `{Data.Foldable.Foldable inst_g}
   : forall {a}, forall `{GHC.Num.Num a}, (Sum inst_f inst_g) a -> a :=
  fun {a} `{GHC.Num.Num a} =>
    Coq.Program.Basics.compose Data.SemigroupInternal.getProduct
                               (Foldable__Sum_foldMap Data.SemigroupInternal.Mk_Product).

Local Definition Foldable__Sum_sum {inst_f} {inst_g} `{Data.Foldable.Foldable
  inst_f} `{Data.Foldable.Foldable inst_g}
   : forall {a}, forall `{GHC.Num.Num a}, (Sum inst_f inst_g) a -> a :=
  fun {a} `{GHC.Num.Num a} =>
    Coq.Program.Basics.compose Data.SemigroupInternal.getSum (Foldable__Sum_foldMap
                                Data.SemigroupInternal.Mk_Sum).

Local Definition Foldable__Sum_toList {inst_f} {inst_g} `{Data.Foldable.Foldable
  inst_f} `{Data.Foldable.Foldable inst_g}
   : forall {a}, (Sum inst_f inst_g) a -> list a :=
  fun {a} =>
    fun t => GHC.Base.build' (fun _ => (fun c n => Foldable__Sum_foldr c n t)).

Program Instance Foldable__Sum {f} {g} `{Data.Foldable.Foldable f}
  `{Data.Foldable.Foldable g}
   : Data.Foldable.Foldable (Sum f g) :=
  fun _ k__ =>
    k__ {| Data.Foldable.fold__ := fun {m} `{GHC.Base.Monoid m} =>
             Foldable__Sum_fold ;
           Data.Foldable.foldMap__ := fun {m} {a} `{GHC.Base.Monoid m} =>
             Foldable__Sum_foldMap ;
           Data.Foldable.foldl__ := fun {b} {a} => Foldable__Sum_foldl ;
           Data.Foldable.foldl'__ := fun {b} {a} => Foldable__Sum_foldl' ;
           Data.Foldable.foldr__ := fun {a} {b} => Foldable__Sum_foldr ;
           Data.Foldable.foldr'__ := fun {a} {b} => Foldable__Sum_foldr' ;
           Data.Foldable.length__ := fun {a} => Foldable__Sum_length ;
           Data.Foldable.null__ := fun {a} => Foldable__Sum_null ;
           Data.Foldable.product__ := fun {a} `{GHC.Num.Num a} => Foldable__Sum_product ;
           Data.Foldable.sum__ := fun {a} `{GHC.Num.Num a} => Foldable__Sum_sum ;
           Data.Foldable.toList__ := fun {a} => Foldable__Sum_toList |}.

Local Definition Traversable__Sum_traverse {inst_f} {inst_g}
  `{Data.Traversable.Traversable inst_f} `{Data.Traversable.Traversable inst_g}
   : forall {f} {a} {b},
     forall `{GHC.Base.Applicative f},
     (a -> f b) -> (Sum inst_f inst_g) a -> f ((Sum inst_f inst_g) b) :=
  fun {f} {a} {b} `{GHC.Base.Applicative f} =>
    fun arg_0__ arg_1__ =>
      match arg_0__, arg_1__ with
      | f, InL x => InL Data.Functor.<$> Data.Traversable.traverse f x
      | f, InR y => InR Data.Functor.<$> Data.Traversable.traverse f y
      end.

Local Definition Traversable__Sum_mapM {inst_f} {inst_g}
  `{Data.Traversable.Traversable inst_f} `{Data.Traversable.Traversable inst_g}
   : forall {m} {a} {b},
     forall `{GHC.Base.Monad m},
     (a -> m b) -> (Sum inst_f inst_g) a -> m ((Sum inst_f inst_g) b) :=
  fun {m} {a} {b} `{GHC.Base.Monad m} => Traversable__Sum_traverse.

Local Definition Traversable__Sum_sequenceA {inst_f} {inst_g}
  `{Data.Traversable.Traversable inst_f} `{Data.Traversable.Traversable inst_g}
   : forall {f} {a},
     forall `{GHC.Base.Applicative f},
     (Sum inst_f inst_g) (f a) -> f ((Sum inst_f inst_g) a) :=
  fun {f} {a} `{GHC.Base.Applicative f} => Traversable__Sum_traverse GHC.Base.id.

Local Definition Traversable__Sum_sequence {inst_f} {inst_g}
  `{Data.Traversable.Traversable inst_f} `{Data.Traversable.Traversable inst_g}
   : forall {m} {a},
     forall `{GHC.Base.Monad m},
     (Sum inst_f inst_g) (m a) -> m ((Sum inst_f inst_g) a) :=
  fun {m} {a} `{GHC.Base.Monad m} => Traversable__Sum_sequenceA.

Program Instance Traversable__Sum {f} {g} `{Data.Traversable.Traversable f}
  `{Data.Traversable.Traversable g}
   : Data.Traversable.Traversable (Sum f g) :=
  fun _ k__ =>
    k__ {| Data.Traversable.mapM__ := fun {m} {a} {b} `{GHC.Base.Monad m} =>
             Traversable__Sum_mapM ;
           Data.Traversable.sequence__ := fun {m} {a} `{GHC.Base.Monad m} =>
             Traversable__Sum_sequence ;
           Data.Traversable.sequenceA__ := fun {f} {a} `{GHC.Base.Applicative f} =>
             Traversable__Sum_sequenceA ;
           Data.Traversable.traverse__ := fun {f} {a} {b} `{GHC.Base.Applicative f} =>
             Traversable__Sum_traverse |}.

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
     GHC.Base.fmap__ GHC.Base.id GHC.Base.max__ GHC.Base.min__ GHC.Base.op_z2218U__
     GHC.Base.op_zeze__ GHC.Base.op_zeze____ GHC.Base.op_zg____ GHC.Base.op_zgze____
     GHC.Base.op_zl____ GHC.Base.op_zlzd____ GHC.Base.op_zlze____ GHC.Base.op_zsze__
     GHC.Base.op_zsze____ GHC.Num.Int GHC.Num.Num GHC.Num.fromInteger GHC.Num.op_zp__
*)
