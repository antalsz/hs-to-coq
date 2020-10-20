(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Coq.Program.Tactics.
Require Coq.Program.Wf.

(* Converted imports: *)

Require Control.Monad.Zip.
Require Coq.Program.Basics.
Require Data.Foldable.
Require Data.Functor.Classes.
Require Data.SemigroupInternal.
Require Data.Traversable.
Require Data.Tuple.
Require GHC.Base.
Require GHC.Num.
Require GHC.Tuple.
Import GHC.Base.Notations.
Import GHC.Num.Notations.

(* Converted type declarations: *)

Inductive Product (f : Type -> Type) (g : Type -> Type) a : Type
  := | Pair : (f a) -> (g a) -> Product f g a.

Arguments Pair {_} {_} {_} _ _.

(* Converted value declarations: *)

(* Skipping all instances of class `Data.Data.Data', including
   `Data.Functor.Product.Data__Product' *)

(* Skipping all instances of class `GHC.Generics.Generic', including
   `Data.Functor.Product.Generic__Product' *)

(* Skipping all instances of class `GHC.Generics.Generic1', including
   `Data.Functor.Product.Generic1__Product__5' *)

Local Definition Eq1__Product_liftEq {inst_f} {inst_g}
  `{Data.Functor.Classes.Eq1 inst_f} `{Data.Functor.Classes.Eq1 inst_g}
   : forall {a} {b},
     (a -> b -> bool) ->
     (Product inst_f inst_g) a -> (Product inst_f inst_g) b -> bool :=
  fun {a} {b} =>
    fun arg_0__ arg_1__ arg_2__ =>
      match arg_0__, arg_1__, arg_2__ with
      | eq, Pair x1 y1, Pair x2 y2 =>
          andb (Data.Functor.Classes.liftEq eq x1 x2) (Data.Functor.Classes.liftEq eq y1
                y2)
      end.

Program Instance Eq1__Product {f} {g} `{Data.Functor.Classes.Eq1 f}
  `{Data.Functor.Classes.Eq1 g}
   : Data.Functor.Classes.Eq1 (Product f g) :=
  fun _ k__ =>
    k__ {| Data.Functor.Classes.liftEq__ := fun {a} {b} => Eq1__Product_liftEq |}.

Local Definition Ord1__Product_liftCompare {inst_f} {inst_g}
  `{Data.Functor.Classes.Ord1 inst_f} `{Data.Functor.Classes.Ord1 inst_g}
   : forall {a} {b},
     (a -> b -> comparison) ->
     (Product inst_f inst_g) a -> (Product inst_f inst_g) b -> comparison :=
  fun {a} {b} =>
    fun arg_0__ arg_1__ arg_2__ =>
      match arg_0__, arg_1__, arg_2__ with
      | comp, Pair x1 y1, Pair x2 y2 =>
          GHC.Base.mappend (Data.Functor.Classes.liftCompare comp x1 x2)
                           (Data.Functor.Classes.liftCompare comp y1 y2)
      end.

Program Instance Ord1__Product {f} {g} `{Data.Functor.Classes.Ord1 f}
  `{Data.Functor.Classes.Ord1 g}
   : Data.Functor.Classes.Ord1 (Product f g) :=
  fun _ k__ =>
    k__ {| Data.Functor.Classes.liftCompare__ := fun {a} {b} =>
             Ord1__Product_liftCompare |}.

(* Skipping all instances of class `Data.Functor.Classes.Read1', including
   `Data.Functor.Product.Read1__Product' *)

(* Skipping all instances of class `Data.Functor.Classes.Show1', including
   `Data.Functor.Product.Show1__Product' *)

Local Definition Eq___Product_op_zeze__ {inst_f} {inst_g} {inst_a}
  `{Data.Functor.Classes.Eq1 inst_f} `{Data.Functor.Classes.Eq1 inst_g}
  `{GHC.Base.Eq_ inst_a}
   : (Product inst_f inst_g inst_a) -> (Product inst_f inst_g inst_a) -> bool :=
  Data.Functor.Classes.eq1.

Local Definition Eq___Product_op_zsze__ {inst_f} {inst_g} {inst_a}
  `{Data.Functor.Classes.Eq1 inst_f} `{Data.Functor.Classes.Eq1 inst_g}
  `{GHC.Base.Eq_ inst_a}
   : (Product inst_f inst_g inst_a) -> (Product inst_f inst_g inst_a) -> bool :=
  fun x y => negb (Eq___Product_op_zeze__ x y).

Program Instance Eq___Product {f} {g} {a} `{Data.Functor.Classes.Eq1 f}
  `{Data.Functor.Classes.Eq1 g} `{GHC.Base.Eq_ a}
   : GHC.Base.Eq_ (Product f g a) :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zeze____ := Eq___Product_op_zeze__ ;
           GHC.Base.op_zsze____ := Eq___Product_op_zsze__ |}.

Local Definition Ord__Product_compare {inst_f} {inst_g} {inst_a}
  `{Data.Functor.Classes.Ord1 inst_f} `{Data.Functor.Classes.Ord1 inst_g}
  `{GHC.Base.Ord inst_a}
   : (Product inst_f inst_g inst_a) ->
     (Product inst_f inst_g inst_a) -> comparison :=
  Data.Functor.Classes.compare1.

Local Definition Ord__Product_op_zl__ {inst_f} {inst_g} {inst_a}
  `{Data.Functor.Classes.Ord1 inst_f} `{Data.Functor.Classes.Ord1 inst_g}
  `{GHC.Base.Ord inst_a}
   : (Product inst_f inst_g inst_a) -> (Product inst_f inst_g inst_a) -> bool :=
  fun x y => Ord__Product_compare x y GHC.Base.== Lt.

Local Definition Ord__Product_op_zlze__ {inst_f} {inst_g} {inst_a}
  `{Data.Functor.Classes.Ord1 inst_f} `{Data.Functor.Classes.Ord1 inst_g}
  `{GHC.Base.Ord inst_a}
   : (Product inst_f inst_g inst_a) -> (Product inst_f inst_g inst_a) -> bool :=
  fun x y => Ord__Product_compare x y GHC.Base./= Gt.

Local Definition Ord__Product_op_zg__ {inst_f} {inst_g} {inst_a}
  `{Data.Functor.Classes.Ord1 inst_f} `{Data.Functor.Classes.Ord1 inst_g}
  `{GHC.Base.Ord inst_a}
   : (Product inst_f inst_g inst_a) -> (Product inst_f inst_g inst_a) -> bool :=
  fun x y => Ord__Product_compare x y GHC.Base.== Gt.

Local Definition Ord__Product_op_zgze__ {inst_f} {inst_g} {inst_a}
  `{Data.Functor.Classes.Ord1 inst_f} `{Data.Functor.Classes.Ord1 inst_g}
  `{GHC.Base.Ord inst_a}
   : (Product inst_f inst_g inst_a) -> (Product inst_f inst_g inst_a) -> bool :=
  fun x y => Ord__Product_compare x y GHC.Base./= Lt.

Local Definition Ord__Product_max {inst_f} {inst_g} {inst_a}
  `{Data.Functor.Classes.Ord1 inst_f} `{Data.Functor.Classes.Ord1 inst_g}
  `{GHC.Base.Ord inst_a}
   : (Product inst_f inst_g inst_a) ->
     (Product inst_f inst_g inst_a) -> (Product inst_f inst_g inst_a) :=
  fun x y => if Ord__Product_op_zlze__ x y : bool then y else x.

Local Definition Ord__Product_min {inst_f} {inst_g} {inst_a}
  `{Data.Functor.Classes.Ord1 inst_f} `{Data.Functor.Classes.Ord1 inst_g}
  `{GHC.Base.Ord inst_a}
   : (Product inst_f inst_g inst_a) ->
     (Product inst_f inst_g inst_a) -> (Product inst_f inst_g inst_a) :=
  fun x y => if Ord__Product_op_zlze__ x y : bool then x else y.

Program Instance Ord__Product {f} {g} {a} `{Data.Functor.Classes.Ord1 f}
  `{Data.Functor.Classes.Ord1 g} `{GHC.Base.Ord a}
   : GHC.Base.Ord (Product f g a) :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zl____ := Ord__Product_op_zl__ ;
           GHC.Base.op_zlze____ := Ord__Product_op_zlze__ ;
           GHC.Base.op_zg____ := Ord__Product_op_zg__ ;
           GHC.Base.op_zgze____ := Ord__Product_op_zgze__ ;
           GHC.Base.compare__ := Ord__Product_compare ;
           GHC.Base.max__ := Ord__Product_max ;
           GHC.Base.min__ := Ord__Product_min |}.

(* Skipping all instances of class `GHC.Read.Read', including
   `Data.Functor.Product.Read__Product' *)

(* Skipping all instances of class `GHC.Show.Show', including
   `Data.Functor.Product.Show__Product' *)

Local Definition Functor__Product_fmap {inst_f} {inst_g} `{GHC.Base.Functor
  inst_f} `{GHC.Base.Functor inst_g}
   : forall {a} {b},
     (a -> b) -> (Product inst_f inst_g) a -> (Product inst_f inst_g) b :=
  fun {a} {b} =>
    fun arg_0__ arg_1__ =>
      match arg_0__, arg_1__ with
      | f, Pair x y => Pair (GHC.Base.fmap f x) (GHC.Base.fmap f y)
      end.

Local Definition Functor__Product_op_zlzd__ {inst_f} {inst_g} `{GHC.Base.Functor
  inst_f} `{GHC.Base.Functor inst_g}
   : forall {a} {b},
     a -> (Product inst_f inst_g) b -> (Product inst_f inst_g) a :=
  fun {a} {b} => Functor__Product_fmap GHC.Base.∘ GHC.Base.const.

Program Instance Functor__Product {f} {g} `{GHC.Base.Functor f}
  `{GHC.Base.Functor g}
   : GHC.Base.Functor (Product f g) :=
  fun _ k__ =>
    k__ {| GHC.Base.fmap__ := fun {a} {b} => Functor__Product_fmap ;
           GHC.Base.op_zlzd____ := fun {a} {b} => Functor__Product_op_zlzd__ |}.

Local Definition Foldable__Product_foldMap {inst_f} {inst_g}
  `{Data.Foldable.Foldable inst_f} `{Data.Foldable.Foldable inst_g}
   : forall {m} {a},
     forall `{GHC.Base.Monoid m}, (a -> m) -> (Product inst_f inst_g) a -> m :=
  fun {m} {a} `{GHC.Base.Monoid m} =>
    fun arg_0__ arg_1__ =>
      match arg_0__, arg_1__ with
      | f, Pair x y =>
          GHC.Base.mappend (Data.Foldable.foldMap f x) (Data.Foldable.foldMap f y)
      end.

Local Definition Foldable__Product_fold {inst_f} {inst_g}
  `{Data.Foldable.Foldable inst_f} `{Data.Foldable.Foldable inst_g}
   : forall {m}, forall `{GHC.Base.Monoid m}, (Product inst_f inst_g) m -> m :=
  fun {m} `{GHC.Base.Monoid m} => Foldable__Product_foldMap GHC.Base.id.

Local Definition Foldable__Product_foldl {inst_f} {inst_g}
  `{Data.Foldable.Foldable inst_f} `{Data.Foldable.Foldable inst_g}
   : forall {b} {a}, (b -> a -> b) -> b -> (Product inst_f inst_g) a -> b :=
  fun {b} {a} =>
    fun f z t =>
      Data.SemigroupInternal.appEndo (Data.SemigroupInternal.getDual
                                      (Foldable__Product_foldMap (Data.SemigroupInternal.Mk_Dual GHC.Base.∘
                                                                  (Data.SemigroupInternal.Mk_Endo GHC.Base.∘
                                                                   GHC.Base.flip f)) t)) z.

Local Definition Foldable__Product_foldr {inst_f} {inst_g}
  `{Data.Foldable.Foldable inst_f} `{Data.Foldable.Foldable inst_g}
   : forall {a} {b}, (a -> b -> b) -> b -> (Product inst_f inst_g) a -> b :=
  fun {a} {b} =>
    fun f z t =>
      Data.SemigroupInternal.appEndo (Foldable__Product_foldMap
                                      (Coq.Program.Basics.compose Data.SemigroupInternal.Mk_Endo f) t) z.

Local Definition Foldable__Product_foldl' {inst_f} {inst_g}
  `{Data.Foldable.Foldable inst_f} `{Data.Foldable.Foldable inst_g}
   : forall {b} {a}, (b -> a -> b) -> b -> (Product inst_f inst_g) a -> b :=
  fun {b} {a} =>
    fun f z0 xs =>
      let f' := fun x k z => k (f z x) in
      Foldable__Product_foldr f' GHC.Base.id xs z0.

Local Definition Foldable__Product_foldr' {inst_f} {inst_g}
  `{Data.Foldable.Foldable inst_f} `{Data.Foldable.Foldable inst_g}
   : forall {a} {b}, (a -> b -> b) -> b -> (Product inst_f inst_g) a -> b :=
  fun {a} {b} =>
    fun f z0 xs =>
      let f' := fun k x z => k (f x z) in
      Foldable__Product_foldl f' GHC.Base.id xs z0.

Local Definition Foldable__Product_length {inst_f} {inst_g}
  `{Data.Foldable.Foldable inst_f} `{Data.Foldable.Foldable inst_g}
   : forall {a}, (Product inst_f inst_g) a -> GHC.Num.Int :=
  fun {a} =>
    Foldable__Product_foldl' (fun arg_0__ arg_1__ =>
                                match arg_0__, arg_1__ with
                                | c, _ => c GHC.Num.+ #1
                                end) #0.

Local Definition Foldable__Product_null {inst_f} {inst_g}
  `{Data.Foldable.Foldable inst_f} `{Data.Foldable.Foldable inst_g}
   : forall {a}, (Product inst_f inst_g) a -> bool :=
  fun {a} => Foldable__Product_foldr (fun arg_0__ arg_1__ => false) true.

Local Definition Foldable__Product_product {inst_f} {inst_g}
  `{Data.Foldable.Foldable inst_f} `{Data.Foldable.Foldable inst_g}
   : forall {a}, forall `{GHC.Num.Num a}, (Product inst_f inst_g) a -> a :=
  fun {a} `{GHC.Num.Num a} =>
    Coq.Program.Basics.compose Data.SemigroupInternal.getProduct
                               (Foldable__Product_foldMap Data.SemigroupInternal.Mk_Product).

Local Definition Foldable__Product_sum {inst_f} {inst_g}
  `{Data.Foldable.Foldable inst_f} `{Data.Foldable.Foldable inst_g}
   : forall {a}, forall `{GHC.Num.Num a}, (Product inst_f inst_g) a -> a :=
  fun {a} `{GHC.Num.Num a} =>
    Coq.Program.Basics.compose Data.SemigroupInternal.getSum
                               (Foldable__Product_foldMap Data.SemigroupInternal.Mk_Sum).

Local Definition Foldable__Product_toList {inst_f} {inst_g}
  `{Data.Foldable.Foldable inst_f} `{Data.Foldable.Foldable inst_g}
   : forall {a}, (Product inst_f inst_g) a -> list a :=
  fun {a} =>
    fun t => GHC.Base.build' (fun _ => (fun c n => Foldable__Product_foldr c n t)).

Program Instance Foldable__Product {f} {g} `{Data.Foldable.Foldable f}
  `{Data.Foldable.Foldable g}
   : Data.Foldable.Foldable (Product f g) :=
  fun _ k__ =>
    k__ {| Data.Foldable.fold__ := fun {m} `{GHC.Base.Monoid m} =>
             Foldable__Product_fold ;
           Data.Foldable.foldMap__ := fun {m} {a} `{GHC.Base.Monoid m} =>
             Foldable__Product_foldMap ;
           Data.Foldable.foldl__ := fun {b} {a} => Foldable__Product_foldl ;
           Data.Foldable.foldl'__ := fun {b} {a} => Foldable__Product_foldl' ;
           Data.Foldable.foldr__ := fun {a} {b} => Foldable__Product_foldr ;
           Data.Foldable.foldr'__ := fun {a} {b} => Foldable__Product_foldr' ;
           Data.Foldable.length__ := fun {a} => Foldable__Product_length ;
           Data.Foldable.null__ := fun {a} => Foldable__Product_null ;
           Data.Foldable.product__ := fun {a} `{GHC.Num.Num a} =>
             Foldable__Product_product ;
           Data.Foldable.sum__ := fun {a} `{GHC.Num.Num a} => Foldable__Product_sum ;
           Data.Foldable.toList__ := fun {a} => Foldable__Product_toList |}.

Local Definition Traversable__Product_traverse {inst_f} {inst_g}
  `{Data.Traversable.Traversable inst_f} `{Data.Traversable.Traversable inst_g}
   : forall {f} {a} {b},
     forall `{GHC.Base.Applicative f},
     (a -> f b) -> (Product inst_f inst_g) a -> f ((Product inst_f inst_g) b) :=
  fun {f} {a} {b} `{GHC.Base.Applicative f} =>
    fun arg_0__ arg_1__ =>
      match arg_0__, arg_1__ with
      | f, Pair x y =>
          GHC.Base.liftA2 Pair (Data.Traversable.traverse f x) (Data.Traversable.traverse
                                                                f y)
      end.

Local Definition Traversable__Product_mapM {inst_f} {inst_g}
  `{Data.Traversable.Traversable inst_f} `{Data.Traversable.Traversable inst_g}
   : forall {m} {a} {b},
     forall `{GHC.Base.Monad m},
     (a -> m b) -> (Product inst_f inst_g) a -> m ((Product inst_f inst_g) b) :=
  fun {m} {a} {b} `{GHC.Base.Monad m} => Traversable__Product_traverse.

Local Definition Traversable__Product_sequenceA {inst_f} {inst_g}
  `{Data.Traversable.Traversable inst_f} `{Data.Traversable.Traversable inst_g}
   : forall {f} {a},
     forall `{GHC.Base.Applicative f},
     (Product inst_f inst_g) (f a) -> f ((Product inst_f inst_g) a) :=
  fun {f} {a} `{GHC.Base.Applicative f} =>
    Traversable__Product_traverse GHC.Base.id.

Local Definition Traversable__Product_sequence {inst_f} {inst_g}
  `{Data.Traversable.Traversable inst_f} `{Data.Traversable.Traversable inst_g}
   : forall {m} {a},
     forall `{GHC.Base.Monad m},
     (Product inst_f inst_g) (m a) -> m ((Product inst_f inst_g) a) :=
  fun {m} {a} `{GHC.Base.Monad m} => Traversable__Product_sequenceA.

Program Instance Traversable__Product {f} {g} `{Data.Traversable.Traversable f}
  `{Data.Traversable.Traversable g}
   : Data.Traversable.Traversable (Product f g) :=
  fun _ k__ =>
    k__ {| Data.Traversable.mapM__ := fun {m} {a} {b} `{GHC.Base.Monad m} =>
             Traversable__Product_mapM ;
           Data.Traversable.sequence__ := fun {m} {a} `{GHC.Base.Monad m} =>
             Traversable__Product_sequence ;
           Data.Traversable.sequenceA__ := fun {f} {a} `{GHC.Base.Applicative f} =>
             Traversable__Product_sequenceA ;
           Data.Traversable.traverse__ := fun {f} {a} {b} `{GHC.Base.Applicative f} =>
             Traversable__Product_traverse |}.

Local Definition Applicative__Product_liftA2 {inst_f} {inst_g}
  `{GHC.Base.Applicative inst_f} `{GHC.Base.Applicative inst_g}
   : forall {a} {b} {c},
     (a -> b -> c) ->
     (Product inst_f inst_g) a ->
     (Product inst_f inst_g) b -> (Product inst_f inst_g) c :=
  fun {a} {b} {c} =>
    fun arg_0__ arg_1__ arg_2__ =>
      match arg_0__, arg_1__, arg_2__ with
      | f, Pair a b, Pair x y => Pair (GHC.Base.liftA2 f a x) (GHC.Base.liftA2 f b y)
      end.

Local Definition Applicative__Product_op_zlztzg__ {inst_f} {inst_g}
  `{GHC.Base.Applicative inst_f} `{GHC.Base.Applicative inst_g}
   : forall {a} {b},
     (Product inst_f inst_g) (a -> b) ->
     (Product inst_f inst_g) a -> (Product inst_f inst_g) b :=
  fun {a} {b} =>
    fun arg_0__ arg_1__ =>
      match arg_0__, arg_1__ with
      | Pair f g, Pair x y => Pair (f GHC.Base.<*> x) (g GHC.Base.<*> y)
      end.

Local Definition Applicative__Product_op_ztzg__ {inst_f} {inst_g}
  `{GHC.Base.Applicative inst_f} `{GHC.Base.Applicative inst_g}
   : forall {a} {b},
     (Product inst_f inst_g) a ->
     (Product inst_f inst_g) b -> (Product inst_f inst_g) b :=
  fun {a} {b} =>
    fun a1 a2 => Applicative__Product_op_zlztzg__ (GHC.Base.id GHC.Base.<$ a1) a2.

Local Definition Applicative__Product_pure {inst_f} {inst_g}
  `{GHC.Base.Applicative inst_f} `{GHC.Base.Applicative inst_g}
   : forall {a}, a -> (Product inst_f inst_g) a :=
  fun {a} => fun x => Pair (GHC.Base.pure x) (GHC.Base.pure x).

Program Instance Applicative__Product {f} {g} `{GHC.Base.Applicative f}
  `{GHC.Base.Applicative g}
   : GHC.Base.Applicative (Product f g) :=
  fun _ k__ =>
    k__ {| GHC.Base.liftA2__ := fun {a} {b} {c} => Applicative__Product_liftA2 ;
           GHC.Base.op_zlztzg____ := fun {a} {b} => Applicative__Product_op_zlztzg__ ;
           GHC.Base.op_ztzg____ := fun {a} {b} => Applicative__Product_op_ztzg__ ;
           GHC.Base.pure__ := fun {a} => Applicative__Product_pure |}.

(* Skipping all instances of class `GHC.Base.Alternative', including
   `Data.Functor.Product.Alternative__Product' *)

Local Definition Monad__Product_op_zgzgze__ {inst_f} {inst_g} `{GHC.Base.Monad
  inst_f} `{GHC.Base.Monad inst_g}
   : forall {a} {b},
     (Product inst_f inst_g) a ->
     (a -> (Product inst_f inst_g) b) -> (Product inst_f inst_g) b :=
  fun {a} {b} =>
    fun arg_0__ arg_1__ =>
      match arg_0__, arg_1__ with
      | Pair m n, f =>
          let sndP := fun '(Pair _ b) => b in
          let fstP := fun '(Pair a _) => a in
          Pair (m GHC.Base.>>= (fstP GHC.Base.∘ f)) (n GHC.Base.>>= (sndP GHC.Base.∘ f))
      end.

Local Definition Monad__Product_op_zgzg__ {inst_f} {inst_g} `{GHC.Base.Monad
  inst_f} `{GHC.Base.Monad inst_g}
   : forall {a} {b},
     (Product inst_f inst_g) a ->
     (Product inst_f inst_g) b -> (Product inst_f inst_g) b :=
  fun {a} {b} => fun m k => Monad__Product_op_zgzgze__ m (fun arg_0__ => k).

Local Definition Monad__Product_return_ {inst_f} {inst_g} `{GHC.Base.Monad
  inst_f} `{GHC.Base.Monad inst_g}
   : forall {a}, a -> (Product inst_f inst_g) a :=
  fun {a} => GHC.Base.pure.

Program Instance Monad__Product {f} {g} `{GHC.Base.Monad f} `{GHC.Base.Monad g}
   : GHC.Base.Monad (Product f g) :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zgzg____ := fun {a} {b} => Monad__Product_op_zgzg__ ;
           GHC.Base.op_zgzgze____ := fun {a} {b} => Monad__Product_op_zgzgze__ ;
           GHC.Base.return___ := fun {a} => Monad__Product_return_ |}.

(* Skipping all instances of class `GHC.Base.MonadPlus', including
   `Data.Functor.Product.MonadPlus__Product' *)

(* Skipping all instances of class `Control.Monad.Fix.MonadFix', including
   `Data.Functor.Product.MonadFix__Product' *)

Local Definition MonadZip__Product_munzip {inst_f} {inst_g}
  `{Control.Monad.Zip.MonadZip inst_f} `{Control.Monad.Zip.MonadZip inst_g}
   : forall {a} {b},
     (Product inst_f inst_g) (a * b)%type ->
     ((Product inst_f inst_g) a * (Product inst_f inst_g) b)%type :=
  fun {a} {b} =>
    fun mab =>
      pair (GHC.Base.liftM Data.Tuple.fst mab) (GHC.Base.liftM Data.Tuple.snd mab).

Local Definition MonadZip__Product_mzipWith {inst_f} {inst_g}
  `{Control.Monad.Zip.MonadZip inst_f} `{Control.Monad.Zip.MonadZip inst_g}
   : forall {a} {b} {c},
     (a -> b -> c) ->
     (Product inst_f inst_g) a ->
     (Product inst_f inst_g) b -> (Product inst_f inst_g) c :=
  fun {a} {b} {c} =>
    fun arg_0__ arg_1__ arg_2__ =>
      match arg_0__, arg_1__, arg_2__ with
      | f, Pair x1 y1, Pair x2 y2 =>
          Pair (Control.Monad.Zip.mzipWith f x1 x2) (Control.Monad.Zip.mzipWith f y1 y2)
      end.

Local Definition MonadZip__Product_mzip {inst_f} {inst_g}
  `{Control.Monad.Zip.MonadZip inst_f} `{Control.Monad.Zip.MonadZip inst_g}
   : forall {a} {b},
     (Product inst_f inst_g) a ->
     (Product inst_f inst_g) b -> (Product inst_f inst_g) (a * b)%type :=
  fun {a} {b} => MonadZip__Product_mzipWith GHC.Tuple.pair2.

Program Instance MonadZip__Product {f} {g} `{Control.Monad.Zip.MonadZip f}
  `{Control.Monad.Zip.MonadZip g}
   : Control.Monad.Zip.MonadZip (Product f g) :=
  fun _ k__ =>
    k__ {| Control.Monad.Zip.munzip__ := fun {a} {b} => MonadZip__Product_munzip ;
           Control.Monad.Zip.mzip__ := fun {a} {b} => MonadZip__Product_mzip ;
           Control.Monad.Zip.mzipWith__ := fun {a} {b} {c} =>
             MonadZip__Product_mzipWith |}.

(* External variables:
     Gt Lt Type andb bool comparison false list negb op_zt__ pair true
     Control.Monad.Zip.MonadZip Control.Monad.Zip.munzip__ Control.Monad.Zip.mzipWith
     Control.Monad.Zip.mzipWith__ Control.Monad.Zip.mzip__ Coq.Program.Basics.compose
     Data.Foldable.Foldable Data.Foldable.foldMap Data.Foldable.foldMap__
     Data.Foldable.fold__ Data.Foldable.foldl'__ Data.Foldable.foldl__
     Data.Foldable.foldr'__ Data.Foldable.foldr__ Data.Foldable.length__
     Data.Foldable.null__ Data.Foldable.product__ Data.Foldable.sum__
     Data.Foldable.toList__ Data.Functor.Classes.Eq1 Data.Functor.Classes.Ord1
     Data.Functor.Classes.compare1 Data.Functor.Classes.eq1
     Data.Functor.Classes.liftCompare Data.Functor.Classes.liftCompare__
     Data.Functor.Classes.liftEq Data.Functor.Classes.liftEq__
     Data.SemigroupInternal.Mk_Dual Data.SemigroupInternal.Mk_Endo
     Data.SemigroupInternal.Mk_Product Data.SemigroupInternal.Mk_Sum
     Data.SemigroupInternal.appEndo Data.SemigroupInternal.getDual
     Data.SemigroupInternal.getProduct Data.SemigroupInternal.getSum
     Data.Traversable.Traversable Data.Traversable.mapM__
     Data.Traversable.sequenceA__ Data.Traversable.sequence__
     Data.Traversable.traverse Data.Traversable.traverse__ Data.Tuple.fst
     Data.Tuple.snd GHC.Base.Applicative GHC.Base.Eq_ GHC.Base.Functor GHC.Base.Monad
     GHC.Base.Monoid GHC.Base.Ord GHC.Base.build' GHC.Base.compare__ GHC.Base.const
     GHC.Base.flip GHC.Base.fmap GHC.Base.fmap__ GHC.Base.id GHC.Base.liftA2
     GHC.Base.liftA2__ GHC.Base.liftM GHC.Base.mappend GHC.Base.max__ GHC.Base.min__
     GHC.Base.op_z2218U__ GHC.Base.op_zeze__ GHC.Base.op_zeze____ GHC.Base.op_zg____
     GHC.Base.op_zgze____ GHC.Base.op_zgzg____ GHC.Base.op_zgzgze__
     GHC.Base.op_zgzgze____ GHC.Base.op_zl____ GHC.Base.op_zlzd__
     GHC.Base.op_zlzd____ GHC.Base.op_zlze____ GHC.Base.op_zlztzg__
     GHC.Base.op_zlztzg____ GHC.Base.op_zsze__ GHC.Base.op_zsze____
     GHC.Base.op_ztzg____ GHC.Base.pure GHC.Base.pure__ GHC.Base.return___
     GHC.Num.Int GHC.Num.Num GHC.Num.fromInteger GHC.Num.op_zp__ GHC.Tuple.pair2
*)
