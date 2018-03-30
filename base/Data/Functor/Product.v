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
Require Data.Functor.Classes.
Require Data.Monoid.
Require Data.Traversable.
Require GHC.Base.
Require GHC.Num.
Import GHC.Base.Notations.
Import GHC.Num.Notations.

(* Converted type declarations: *)

Inductive Product f g a : Type := Pair : (f a) -> (g a) -> Product f g a.

Arguments Pair {_} {_} {_} _ _.
(* Midamble *)

Definition mempty_Product {a} `{Num a} : Product a := Mk_Product #0.
Definition mappend_Product {a} `{Num a} (x: Product a) (y :Product a)  : Product a :=
  match x , y with
    | Mk_Product i , Mk_Product j => Mk_Product (i + j)
  end.
Instance instance_GHC_Base_Monoid__Product_a_ {a} `{Num a}:
  GHC.Base.Monoid (Product a) := fun _ k => k
 {| mappend__ := mappend_Product;
    mempty__  := mempty_Product;
    mconcat__ := foldr mappend_Product mempty_Product |}.


(* Converted value declarations: *)

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
  fun _ k =>
    k {| Data.Functor.Classes.liftEq__ := fun {a} {b} => Eq1__Product_liftEq |}.

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
  fun _ k =>
    k {| Data.Functor.Classes.liftCompare__ := fun {a} {b} =>
           Ord1__Product_liftCompare |}.

(* Translating `instance Read1__Product' failed: OOPS! Cannot find information
   for class Qualified "Data.Functor.Classes" "Read1" unsupported *)

(* Translating `instance Show1__Product' failed: OOPS! Cannot find information
   for class Qualified "Data.Functor.Classes" "Show1" unsupported *)

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
  fun _ k =>
    k {| GHC.Base.op_zeze____ := Eq___Product_op_zeze__ ;
         GHC.Base.op_zsze____ := Eq___Product_op_zsze__ |}.

Local Definition Ord__Product_compare {inst_f} {inst_g} {inst_a}
  `{Data.Functor.Classes.Ord1 inst_f} `{Data.Functor.Classes.Ord1 inst_g}
  `{GHC.Base.Ord inst_a}
   : (Product inst_f inst_g inst_a) ->
     (Product inst_f inst_g inst_a) -> comparison :=
  Data.Functor.Classes.compare1.

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
  fun _ k =>
    k {| GHC.Base.op_zl____ := Ord__Product_op_zl__ ;
         GHC.Base.op_zlze____ := Ord__Product_op_zlze__ ;
         GHC.Base.op_zg____ := Ord__Product_op_zg__ ;
         GHC.Base.op_zgze____ := Ord__Product_op_zgze__ ;
         GHC.Base.compare__ := Ord__Product_compare ;
         GHC.Base.max__ := Ord__Product_max ;
         GHC.Base.min__ := Ord__Product_min |}.

(* Translating `instance Read__Product' failed: OOPS! Cannot find information
   for class Qualified "GHC.Read" "Read" unsupported *)

(* Translating `instance Show__Product' failed: OOPS! Cannot find information
   for class Qualified "GHC.Show" "Show" unsupported *)

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
  fun {a} {b} => fun x => Functor__Product_fmap (GHC.Base.const x).

Program Instance Functor__Product {f} {g} `{GHC.Base.Functor f}
  `{GHC.Base.Functor g}
   : GHC.Base.Functor (Product f g) :=
  fun _ k =>
    k {| GHC.Base.op_zlzd____ := fun {a} {b} => Functor__Product_op_zlzd__ ;
         GHC.Base.fmap__ := fun {a} {b} => Functor__Product_fmap |}.

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

Local Definition Foldable__Product_foldl {inst_f} {inst_g}
  `{Data.Foldable.Foldable inst_f} `{Data.Foldable.Foldable inst_g}
   : forall {b} {a}, (b -> a -> b) -> b -> (Product inst_f inst_g) a -> b :=
  fun {b} {a} =>
    fun arg_19__ arg_20__ arg_21__ =>
      match arg_19__, arg_20__, arg_21__ with
      | f, z, t =>
          Data.Monoid.appEndo (Data.Monoid.getDual (Foldable__Product_foldMap
                                                    (Coq.Program.Basics.compose Data.Monoid.Mk_Dual
                                                                                (Coq.Program.Basics.compose
                                                                                 Data.Monoid.Mk_Endo (GHC.Base.flip f)))
                                                    t)) z
      end.

Local Definition Foldable__Product_foldr' {inst_f} {inst_g}
  `{Data.Foldable.Foldable inst_f} `{Data.Foldable.Foldable inst_g}
   : forall {a} {b}, (a -> b -> b) -> b -> (Product inst_f inst_g) a -> b :=
  fun {a} {b} =>
    fun arg_9__ arg_10__ arg_11__ =>
      match arg_9__, arg_10__, arg_11__ with
      | f, z0, xs =>
          let f' :=
            fun arg_12__ arg_13__ arg_14__ =>
              match arg_12__, arg_13__, arg_14__ with
              | k, x, z => k GHC.Base.$! f x z
              end in
          Foldable__Product_foldl f' GHC.Base.id xs z0
      end.

Local Definition Foldable__Product_foldr {inst_f} {inst_g}
  `{Data.Foldable.Foldable inst_f} `{Data.Foldable.Foldable inst_g}
   : forall {a} {b}, (a -> b -> b) -> b -> (Product inst_f inst_g) a -> b :=
  fun {a} {b} =>
    fun arg_4__ arg_5__ arg_6__ =>
      match arg_4__, arg_5__, arg_6__ with
      | f, z, t =>
          Data.Monoid.appEndo (Foldable__Product_foldMap (Data.Foldable.hash_compose
                                                          Data.Monoid.Mk_Endo f) t) z
      end.

Local Definition Foldable__Product_foldl' {inst_f} {inst_g}
  `{Data.Foldable.Foldable inst_f} `{Data.Foldable.Foldable inst_g}
   : forall {b} {a}, (b -> a -> b) -> b -> (Product inst_f inst_g) a -> b :=
  fun {b} {a} =>
    fun arg_24__ arg_25__ arg_26__ =>
      match arg_24__, arg_25__, arg_26__ with
      | f, z0, xs =>
          let f' :=
            fun arg_27__ arg_28__ arg_29__ =>
              match arg_27__, arg_28__, arg_29__ with
              | x, k, z => k GHC.Base.$! f z x
              end in
          Foldable__Product_foldr f' GHC.Base.id xs z0
      end.

Local Definition Foldable__Product_length {inst_f} {inst_g}
  `{Data.Foldable.Foldable inst_f} `{Data.Foldable.Foldable inst_g}
   : forall {a}, (Product inst_f inst_g) a -> GHC.Num.Int :=
  fun {a} =>
    Foldable__Product_foldl' (fun arg_64__ arg_65__ =>
                                match arg_64__, arg_65__ with
                                | c, _ => c GHC.Num.+ #1
                                end) #0.

Local Definition Foldable__Product_null {inst_f} {inst_g}
  `{Data.Foldable.Foldable inst_f} `{Data.Foldable.Foldable inst_g}
   : forall {a}, (Product inst_f inst_g) a -> bool :=
  fun {a} => Foldable__Product_foldr (fun arg_61__ arg_62__ => false) true.

Local Definition Foldable__Product_toList {inst_f} {inst_g}
  `{Data.Foldable.Foldable inst_f} `{Data.Foldable.Foldable inst_g}
   : forall {a}, (Product inst_f inst_g) a -> list a :=
  fun {a} =>
    fun arg_54__ =>
      let 't := arg_54__ in
      GHC.Base.build (fun _ arg_55__ arg_56__ =>
                        match arg_55__, arg_56__ with
                        | c, n => Foldable__Product_foldr c n t
                        end).

Local Definition Foldable__Product_product {inst_f} {inst_g}
  `{Data.Foldable.Foldable inst_f} `{Data.Foldable.Foldable inst_g}
   : forall {a}, forall `{GHC.Num.Num a}, (Product inst_f inst_g) a -> a :=
  fun {a} `{GHC.Num.Num a} =>
    Data.Foldable.hash_compose Data.Monoid.getProduct (Foldable__Product_foldMap
                                Data.Monoid.Mk_Product).

Local Definition Foldable__Product_sum {inst_f} {inst_g}
  `{Data.Foldable.Foldable inst_f} `{Data.Foldable.Foldable inst_g}
   : forall {a}, forall `{GHC.Num.Num a}, (Product inst_f inst_g) a -> a :=
  fun {a} `{GHC.Num.Num a} =>
    Data.Foldable.hash_compose Data.Monoid.getSum (Foldable__Product_foldMap
                                Data.Monoid.Mk_Sum).

Local Definition Foldable__Product_fold {inst_f} {inst_g}
  `{Data.Foldable.Foldable inst_f} `{Data.Foldable.Foldable inst_g}
   : forall {m}, forall `{GHC.Base.Monoid m}, (Product inst_f inst_g) m -> m :=
  fun {m} `{GHC.Base.Monoid m} => Foldable__Product_foldMap GHC.Base.id.

Local Definition Foldable__Product_elem {inst_f} {inst_g}
  `{Data.Foldable.Foldable inst_f} `{Data.Foldable.Foldable inst_g}
   : forall {a},
     forall `{GHC.Base.Eq_ a}, a -> (Product inst_f inst_g) a -> bool :=
  fun {a} `{GHC.Base.Eq_ a} =>
    Coq.Program.Basics.compose (fun arg_69__ =>
                                  let 'p := arg_69__ in
                                  Coq.Program.Basics.compose Data.Monoid.getAny (Foldable__Product_foldMap
                                                              (Coq.Program.Basics.compose Data.Monoid.Mk_Any p)))
                               _GHC.Base.==_.

Program Instance Foldable__Product {f} {g} `{Data.Foldable.Foldable f}
  `{Data.Foldable.Foldable g}
   : Data.Foldable.Foldable (Product f g) :=
  fun _ k =>
    k {| Data.Foldable.elem__ := fun {a} `{GHC.Base.Eq_ a} =>
           Foldable__Product_elem ;
         Data.Foldable.fold__ := fun {m} `{GHC.Base.Monoid m} => Foldable__Product_fold ;
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

Local Definition Traversable__Product_mapM {inst_f} {inst_g}
  `{Data.Traversable.Traversable inst_f} `{Data.Traversable.Traversable inst_g}
   : forall {m} {a} {b},
     forall `{GHC.Base.Monad m},
     (a -> m b) -> (Product inst_f inst_g) a -> m ((Product inst_f inst_g) b) :=
  fun {m} {a} {b} `{GHC.Base.Monad m} => Traversable__Product_traverse.

Program Instance Traversable__Product {f} {g} `{Data.Traversable.Traversable f}
  `{Data.Traversable.Traversable g}
   : Data.Traversable.Traversable (Product f g) :=
  fun _ k =>
    k {| Data.Traversable.mapM__ := fun {m} {a} {b} `{GHC.Base.Monad m} =>
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
    fun x y =>
      Applicative__Product_op_zlztzg__ (GHC.Base.fmap (GHC.Base.const GHC.Base.id) x)
                                       y.

Local Definition Applicative__Product_pure {inst_f} {inst_g}
  `{GHC.Base.Applicative inst_f} `{GHC.Base.Applicative inst_g}
   : forall {a}, a -> (Product inst_f inst_g) a :=
  fun {a} => fun x => Pair (GHC.Base.pure x) (GHC.Base.pure x).

Program Instance Applicative__Product {f} {g} `{GHC.Base.Applicative f}
  `{GHC.Base.Applicative g}
   : GHC.Base.Applicative (Product f g) :=
  fun _ k =>
    k {| GHC.Base.op_ztzg____ := fun {a} {b} => Applicative__Product_op_ztzg__ ;
         GHC.Base.op_zlztzg____ := fun {a} {b} => Applicative__Product_op_zlztzg__ ;
         GHC.Base.liftA2__ := fun {a} {b} {c} => Applicative__Product_liftA2 ;
         GHC.Base.pure__ := fun {a} => Applicative__Product_pure |}.

(* Translating `instance Alternative__Product' failed: OOPS! Cannot find
   information for class Qualified "GHC.Base" "Alternative" unsupported *)

Local Definition Monad__Product_op_zgzg__ {inst_f} {inst_g} `{GHC.Base.Monad
  inst_f} `{GHC.Base.Monad inst_g}
   : forall {a} {b},
     (Product inst_f inst_g) a ->
     (Product inst_f inst_g) b -> (Product inst_f inst_g) b :=
  fun {a} {b} => _GHC.Base.*>_.

Local Definition Monad__Product_op_zgzgze__ {inst_f} {inst_g} `{GHC.Base.Monad
  inst_f} `{GHC.Base.Monad inst_g}
   : forall {a} {b},
     (Product inst_f inst_g) a ->
     (a -> (Product inst_f inst_g) b) -> (Product inst_f inst_g) b :=
  fun {a} {b} =>
    fun arg_0__ arg_1__ =>
      match arg_0__, arg_1__ with
      | Pair m n, f =>
          let sndP := fun arg_2__ => let 'Pair _ b := arg_2__ in b in
          let fstP := fun arg_4__ => let 'Pair a _ := arg_4__ in a in
          Pair (m GHC.Base.>>= (fstP GHC.Base.∘ f)) (n GHC.Base.>>= (sndP GHC.Base.∘ f))
      end.

Local Definition Monad__Product_return_ {inst_f} {inst_g} `{GHC.Base.Monad
  inst_f} `{GHC.Base.Monad inst_g}
   : forall {a}, a -> (Product inst_f inst_g) a :=
  fun {a} => GHC.Base.pure.

Program Instance Monad__Product {f} {g} `{GHC.Base.Monad f} `{GHC.Base.Monad g}
   : GHC.Base.Monad (Product f g) :=
  fun _ k =>
    k {| GHC.Base.op_zgzg____ := fun {a} {b} => Monad__Product_op_zgzg__ ;
         GHC.Base.op_zgzgze____ := fun {a} {b} => Monad__Product_op_zgzgze__ ;
         GHC.Base.return___ := fun {a} => Monad__Product_return_ |}.

(* Translating `instance MonadPlus__Product' failed: OOPS! Cannot find
   information for class Qualified "GHC.Base" "MonadPlus" unsupported *)

(* Translating `instance MonadFix__Product' failed: OOPS! Cannot find
   information for class Qualified "Control.Monad.Fix" "MonadFix" unsupported *)

(* Translating `instance MonadZip__Product' failed: OOPS! Cannot find
   information for class Qualified "Control.Monad.Zip" "MonadZip" unsupported *)

(* Translating `instance Generic1__Product__5' failed: OOPS! Cannot find
   information for class Qualified "GHC.Generics" "Generic1" unsupported *)

(* Translating `instance Generic__Product' failed: OOPS! Cannot find information
   for class Qualified "GHC.Generics" "Generic" unsupported *)

(* Translating `instance Data__Product' failed: OOPS! Cannot find information
   for class Qualified "Data.Data" "Data" unsupported *)

(* Unbound variables:
     Gt Lt andb bool comparison false list negb true Coq.Program.Basics.compose
     Data.Foldable.Foldable Data.Foldable.foldMap Data.Foldable.hash_compose
     Data.Functor.Classes.Eq1 Data.Functor.Classes.Ord1 Data.Functor.Classes.compare1
     Data.Functor.Classes.eq1 Data.Functor.Classes.liftCompare
     Data.Functor.Classes.liftEq Data.Monoid.Mk_Any Data.Monoid.Mk_Dual
     Data.Monoid.Mk_Endo Data.Monoid.Mk_Product Data.Monoid.Mk_Sum
     Data.Monoid.appEndo Data.Monoid.getAny Data.Monoid.getDual
     Data.Monoid.getProduct Data.Monoid.getSum Data.Traversable.Traversable
     Data.Traversable.traverse GHC.Base.Applicative GHC.Base.Eq_ GHC.Base.Functor
     GHC.Base.Monad GHC.Base.Monoid GHC.Base.Ord GHC.Base.build GHC.Base.const
     GHC.Base.flip GHC.Base.fmap GHC.Base.id GHC.Base.liftA2 GHC.Base.mappend
     GHC.Base.op_z2218U__ GHC.Base.op_zdzn__ GHC.Base.op_zeze__ GHC.Base.op_zgzgze__
     GHC.Base.op_zlztzg__ GHC.Base.op_zsze__ GHC.Base.op_ztzg__ GHC.Base.pure
     GHC.Num.Int GHC.Num.Num GHC.Num.fromInteger GHC.Num.op_zp__
*)
