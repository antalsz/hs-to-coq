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
Require Import Data.Functor.Classes.
Require Data.SemigroupInternal.
Require Data.Traversable.
Require GHC.Base.
Require GHC.Num.
Import GHC.Base.Notations.

(* Converted type declarations: *)

Inductive Backwards (f : Type -> Type) (a : Type) : Type
  := Mk_Backwards : f a -> Backwards f a.

Arguments Mk_Backwards {_} {_} _.

Definition forwards {f : Type -> Type} {a : Type} (arg_0__ : Backwards f a) :=
  let 'Mk_Backwards forwards := arg_0__ in
  forwards.
(* Converted value declarations: *)

Local Definition Eq1__Backwards_liftEq {inst_f} `{(Eq1 inst_f)}
   : forall {a} {b},
     (a -> b -> bool) -> (Backwards inst_f) a -> (Backwards inst_f) b -> bool :=
  fun {a} {b} =>
    fun arg_0__ arg_1__ arg_2__ =>
      match arg_0__, arg_1__, arg_2__ with
      | eq, Mk_Backwards x, Mk_Backwards y => liftEq eq x y
      end.

Program Instance Eq1__Backwards {f} `{(Eq1 f)} : Eq1 (Backwards f) :=
  fun _ k => k {| liftEq__ := fun {a} {b} => Eq1__Backwards_liftEq |}.

Local Definition Ord1__Backwards_liftCompare {inst_f} `{(Ord1 inst_f)}
   : forall {a} {b},
     (a -> b -> comparison) ->
     (Backwards inst_f) a -> (Backwards inst_f) b -> comparison :=
  fun {a} {b} =>
    fun arg_0__ arg_1__ arg_2__ =>
      match arg_0__, arg_1__, arg_2__ with
      | comp, Mk_Backwards x, Mk_Backwards y => liftCompare comp x y
      end.

Program Instance Ord1__Backwards {f} `{(Ord1 f)} : Ord1 (Backwards f) :=
  fun _ k => k {| liftCompare__ := fun {a} {b} => Ord1__Backwards_liftCompare |}.

(* Translating `instance Read1__Backwards' failed: OOPS! Cannot find information
   for class Qualified "Data.Functor.Classes" "Read1" unsupported *)

(* Translating `instance Show1__Backwards' failed: OOPS! Cannot find information
   for class Qualified "Data.Functor.Classes" "Show1" unsupported *)

Local Definition Eq___Backwards_op_zeze__ {inst_f} {inst_a} `{Eq1 inst_f}
  `{GHC.Base.Eq_ inst_a}
   : (Backwards inst_f inst_a) -> (Backwards inst_f inst_a) -> bool :=
  eq1.

Local Definition Eq___Backwards_op_zsze__ {inst_f} {inst_a} `{Eq1 inst_f}
  `{GHC.Base.Eq_ inst_a}
   : (Backwards inst_f inst_a) -> (Backwards inst_f inst_a) -> bool :=
  fun x y => negb (Eq___Backwards_op_zeze__ x y).

Program Instance Eq___Backwards {f} {a} `{Eq1 f} `{GHC.Base.Eq_ a}
   : GHC.Base.Eq_ (Backwards f a) :=
  fun _ k =>
    k {| GHC.Base.op_zeze____ := Eq___Backwards_op_zeze__ ;
         GHC.Base.op_zsze____ := Eq___Backwards_op_zsze__ |}.

Local Definition Ord__Backwards_compare {inst_f} {inst_a} `{Ord1 inst_f}
  `{GHC.Base.Ord inst_a}
   : (Backwards inst_f inst_a) -> (Backwards inst_f inst_a) -> comparison :=
  compare1.

Local Definition Ord__Backwards_op_zg__ {inst_f} {inst_a} `{Ord1 inst_f}
  `{GHC.Base.Ord inst_a}
   : (Backwards inst_f inst_a) -> (Backwards inst_f inst_a) -> bool :=
  fun x y => Ord__Backwards_compare x y GHC.Base.== Gt.

Local Definition Ord__Backwards_op_zgze__ {inst_f} {inst_a} `{Ord1 inst_f}
  `{GHC.Base.Ord inst_a}
   : (Backwards inst_f inst_a) -> (Backwards inst_f inst_a) -> bool :=
  fun x y => Ord__Backwards_compare x y GHC.Base./= Lt.

Local Definition Ord__Backwards_op_zl__ {inst_f} {inst_a} `{Ord1 inst_f}
  `{GHC.Base.Ord inst_a}
   : (Backwards inst_f inst_a) -> (Backwards inst_f inst_a) -> bool :=
  fun x y => Ord__Backwards_compare x y GHC.Base.== Lt.

Local Definition Ord__Backwards_op_zlze__ {inst_f} {inst_a} `{Ord1 inst_f}
  `{GHC.Base.Ord inst_a}
   : (Backwards inst_f inst_a) -> (Backwards inst_f inst_a) -> bool :=
  fun x y => Ord__Backwards_compare x y GHC.Base./= Gt.

Local Definition Ord__Backwards_max {inst_f} {inst_a} `{Ord1 inst_f}
  `{GHC.Base.Ord inst_a}
   : (Backwards inst_f inst_a) ->
     (Backwards inst_f inst_a) -> (Backwards inst_f inst_a) :=
  fun x y => if Ord__Backwards_op_zlze__ x y : bool then y else x.

Local Definition Ord__Backwards_min {inst_f} {inst_a} `{Ord1 inst_f}
  `{GHC.Base.Ord inst_a}
   : (Backwards inst_f inst_a) ->
     (Backwards inst_f inst_a) -> (Backwards inst_f inst_a) :=
  fun x y => if Ord__Backwards_op_zlze__ x y : bool then x else y.

Program Instance Ord__Backwards {f} {a} `{Ord1 f} `{GHC.Base.Ord a}
   : GHC.Base.Ord (Backwards f a) :=
  fun _ k =>
    k {| GHC.Base.op_zl____ := Ord__Backwards_op_zl__ ;
         GHC.Base.op_zlze____ := Ord__Backwards_op_zlze__ ;
         GHC.Base.op_zg____ := Ord__Backwards_op_zg__ ;
         GHC.Base.op_zgze____ := Ord__Backwards_op_zgze__ ;
         GHC.Base.compare__ := Ord__Backwards_compare ;
         GHC.Base.max__ := Ord__Backwards_max ;
         GHC.Base.min__ := Ord__Backwards_min |}.

(* Translating `instance Read__Backwards' failed: OOPS! Cannot find information
   for class Qualified "GHC.Read" "Read" unsupported *)

(* Translating `instance Show__Backwards' failed: OOPS! Cannot find information
   for class Qualified "GHC.Show" "Show" unsupported *)

Local Definition Functor__Backwards_fmap {inst_f} `{(GHC.Base.Functor inst_f)}
   : forall {a} {b}, (a -> b) -> (Backwards inst_f) a -> (Backwards inst_f) b :=
  fun {a} {b} =>
    fun arg_0__ arg_1__ =>
      match arg_0__, arg_1__ with
      | f, Mk_Backwards a => Mk_Backwards (GHC.Base.fmap f a)
      end.

Local Definition Functor__Backwards_op_zlzd__ {inst_f} `{(GHC.Base.Functor
   inst_f)}
   : forall {a} {b}, a -> (Backwards inst_f) b -> (Backwards inst_f) a :=
  fun {a} {b} => fun x => Functor__Backwards_fmap (GHC.Base.const x).

Program Instance Functor__Backwards {f} `{(GHC.Base.Functor f)}
   : GHC.Base.Functor (Backwards f) :=
  fun _ k =>
    k {| GHC.Base.op_zlzd____ := fun {a} {b} => Functor__Backwards_op_zlzd__ ;
         GHC.Base.fmap__ := fun {a} {b} => Functor__Backwards_fmap |}.

Local Definition Applicative__Backwards_op_zlztzg__ {inst_f}
  `{(GHC.Base.Applicative inst_f)}
   : forall {a} {b},
     (Backwards inst_f) (a -> b) -> (Backwards inst_f) a -> (Backwards inst_f) b :=
  fun {a} {b} =>
    fun arg_0__ arg_1__ =>
      match arg_0__, arg_1__ with
      | Mk_Backwards f, Mk_Backwards a => Mk_Backwards (a GHC.Base.<**> f)
      end.

Local Definition Applicative__Backwards_op_ztzg__ {inst_f}
  `{(GHC.Base.Applicative inst_f)}
   : forall {a} {b},
     (Backwards inst_f) a -> (Backwards inst_f) b -> (Backwards inst_f) b :=
  fun {a} {b} =>
    fun x y =>
      Applicative__Backwards_op_zlztzg__ (GHC.Base.fmap (GHC.Base.const GHC.Base.id)
                                                        x) y.

Local Definition Applicative__Backwards_liftA2 {inst_f} `{(GHC.Base.Applicative
   inst_f)}
   : forall {a} {b} {c},
     (a -> b -> c) ->
     (Backwards inst_f) a -> (Backwards inst_f) b -> (Backwards inst_f) c :=
  fun {a} {b} {c} =>
    fun f x => Applicative__Backwards_op_zlztzg__ (GHC.Base.fmap f x).

Local Definition Applicative__Backwards_pure {inst_f} `{(GHC.Base.Applicative
   inst_f)}
   : forall {a}, a -> (Backwards inst_f) a :=
  fun {a} => fun a => Mk_Backwards (GHC.Base.pure a).

Program Instance Applicative__Backwards {f} `{(GHC.Base.Applicative f)}
   : GHC.Base.Applicative (Backwards f) :=
  fun _ k =>
    k {| GHC.Base.op_ztzg____ := fun {a} {b} => Applicative__Backwards_op_ztzg__ ;
         GHC.Base.op_zlztzg____ := fun {a} {b} => Applicative__Backwards_op_zlztzg__ ;
         GHC.Base.liftA2__ := fun {a} {b} {c} => Applicative__Backwards_liftA2 ;
         GHC.Base.pure__ := fun {a} => Applicative__Backwards_pure |}.

(* Translating `instance Alternative__Backwards' failed: OOPS! Cannot find
   information for class Qualified "GHC.Base" "Alternative" unsupported *)

Local Definition Foldable__Backwards_foldMap {inst_f} `{(Data.Foldable.Foldable
   inst_f)}
   : forall {m} {a},
     forall `{GHC.Base.Monoid m}, (a -> m) -> (Backwards inst_f) a -> m :=
  fun {m} {a} `{GHC.Base.Monoid m} =>
    fun arg_0__ arg_1__ =>
      match arg_0__, arg_1__ with
      | f, Mk_Backwards t => Data.Foldable.foldMap f t
      end.

Local Definition Foldable__Backwards_product {inst_f} `{(Data.Foldable.Foldable
   inst_f)}
   : forall {a}, forall `{GHC.Num.Num a}, (Backwards inst_f) a -> a :=
  fun {a} `{GHC.Num.Num a} =>
    Coq.Program.Basics.compose Data.SemigroupInternal.getProduct
                               (Foldable__Backwards_foldMap Data.SemigroupInternal.Mk_Product).

Local Definition Foldable__Backwards_sum {inst_f} `{(Data.Foldable.Foldable
   inst_f)}
   : forall {a}, forall `{GHC.Num.Num a}, (Backwards inst_f) a -> a :=
  fun {a} `{GHC.Num.Num a} =>
    Coq.Program.Basics.compose Data.SemigroupInternal.getSum
                               (Foldable__Backwards_foldMap Data.SemigroupInternal.Mk_Sum).

Local Definition Foldable__Backwards_fold {inst_f} `{(Data.Foldable.Foldable
   inst_f)}
   : forall {m}, forall `{GHC.Base.Monoid m}, (Backwards inst_f) m -> m :=
  fun {m} `{GHC.Base.Monoid m} => Foldable__Backwards_foldMap GHC.Base.id.

Local Definition Foldable__Backwards_elem {inst_f} `{(Data.Foldable.Foldable
   inst_f)}
   : forall {a}, forall `{GHC.Base.Eq_ a}, a -> (Backwards inst_f) a -> bool :=
  fun {a} `{GHC.Base.Eq_ a} =>
    Coq.Program.Basics.compose (fun arg_69__ =>
                                  let 'p := arg_69__ in
                                  Coq.Program.Basics.compose Data.SemigroupInternal.getAny
                                                             (Foldable__Backwards_foldMap (Coq.Program.Basics.compose
                                                                                           Data.SemigroupInternal.Mk_Any
                                                                                           p))) _GHC.Base.==_.

Local Definition Foldable__Backwards_foldl {inst_f} `{(Data.Foldable.Foldable
   inst_f)}
   : forall {b} {a}, (b -> a -> b) -> b -> (Backwards inst_f) a -> b :=
  fun {b} {a} =>
    fun arg_0__ arg_1__ arg_2__ =>
      match arg_0__, arg_1__, arg_2__ with
      | f, z, Mk_Backwards t => Data.Foldable.foldl f z t
      end.

Local Definition Foldable__Backwards_foldr' {inst_f} `{(Data.Foldable.Foldable
   inst_f)}
   : forall {a} {b}, (a -> b -> b) -> b -> (Backwards inst_f) a -> b :=
  fun {a} {b} =>
    fun arg_9__ arg_10__ arg_11__ =>
      match arg_9__, arg_10__, arg_11__ with
      | f, z0, xs =>
          let f' :=
            fun arg_12__ arg_13__ arg_14__ =>
              match arg_12__, arg_13__, arg_14__ with
              | k, x, z => k GHC.Base.$! f x z
              end in
          Foldable__Backwards_foldl f' GHC.Base.id xs z0
      end.

Local Definition Foldable__Backwards_foldr {inst_f} `{(Data.Foldable.Foldable
   inst_f)}
   : forall {a} {b}, (a -> b -> b) -> b -> (Backwards inst_f) a -> b :=
  fun {a} {b} =>
    fun arg_0__ arg_1__ arg_2__ =>
      match arg_0__, arg_1__, arg_2__ with
      | f, z, Mk_Backwards t => Data.Foldable.foldr f z t
      end.

Local Definition Foldable__Backwards_toList {inst_f} `{(Data.Foldable.Foldable
   inst_f)}
   : forall {a}, (Backwards inst_f) a -> list a :=
  fun {a} =>
    fun arg_54__ =>
      let 't := arg_54__ in
      GHC.Base.build (fun _ arg_55__ arg_56__ =>
                        match arg_55__, arg_56__ with
                        | c, n => Foldable__Backwards_foldr c n t
                        end).

Local Definition Foldable__Backwards_foldl' {inst_f} `{(Data.Foldable.Foldable
   inst_f)}
   : forall {b} {a}, (b -> a -> b) -> b -> (Backwards inst_f) a -> b :=
  fun {b} {a} =>
    fun arg_24__ arg_25__ arg_26__ =>
      match arg_24__, arg_25__, arg_26__ with
      | f, z0, xs =>
          let f' :=
            fun arg_27__ arg_28__ arg_29__ =>
              match arg_27__, arg_28__, arg_29__ with
              | x, k, z => k GHC.Base.$! f z x
              end in
          Foldable__Backwards_foldr f' GHC.Base.id xs z0
      end.

Local Definition Foldable__Backwards_length {inst_f} `{(Data.Foldable.Foldable
   inst_f)}
   : forall {a}, (Backwards inst_f) a -> GHC.Num.Int :=
  fun {a} =>
    fun arg_0__ => let 'Mk_Backwards t := arg_0__ in Data.Foldable.length t.

Local Definition Foldable__Backwards_null {inst_f} `{(Data.Foldable.Foldable
   inst_f)}
   : forall {a}, (Backwards inst_f) a -> bool :=
  fun {a} =>
    fun arg_0__ => let 'Mk_Backwards t := arg_0__ in Data.Foldable.null t.

Program Instance Foldable__Backwards {f} `{(Data.Foldable.Foldable f)}
   : Data.Foldable.Foldable (Backwards f) :=
  fun _ k =>
    k {| Data.Foldable.elem__ := fun {a} `{GHC.Base.Eq_ a} =>
           Foldable__Backwards_elem ;
         Data.Foldable.fold__ := fun {m} `{GHC.Base.Monoid m} =>
           Foldable__Backwards_fold ;
         Data.Foldable.foldMap__ := fun {m} {a} `{GHC.Base.Monoid m} =>
           Foldable__Backwards_foldMap ;
         Data.Foldable.foldl__ := fun {b} {a} => Foldable__Backwards_foldl ;
         Data.Foldable.foldl'__ := fun {b} {a} => Foldable__Backwards_foldl' ;
         Data.Foldable.foldr__ := fun {a} {b} => Foldable__Backwards_foldr ;
         Data.Foldable.foldr'__ := fun {a} {b} => Foldable__Backwards_foldr' ;
         Data.Foldable.length__ := fun {a} => Foldable__Backwards_length ;
         Data.Foldable.null__ := fun {a} => Foldable__Backwards_null ;
         Data.Foldable.product__ := fun {a} `{GHC.Num.Num a} =>
           Foldable__Backwards_product ;
         Data.Foldable.sum__ := fun {a} `{GHC.Num.Num a} => Foldable__Backwards_sum ;
         Data.Foldable.toList__ := fun {a} => Foldable__Backwards_toList |}.

Local Definition Traversable__Backwards_sequenceA {inst_f}
  `{(Data.Traversable.Traversable inst_f)}
   : forall {f} {a},
     forall `{GHC.Base.Applicative f},
     (Backwards inst_f) (f a) -> f ((Backwards inst_f) a) :=
  fun {f} {a} `{GHC.Base.Applicative f} =>
    fun arg_0__ =>
      let 'Mk_Backwards t := arg_0__ in
      GHC.Base.fmap Mk_Backwards (Data.Traversable.sequenceA t).

Local Definition Traversable__Backwards_sequence {inst_f}
  `{(Data.Traversable.Traversable inst_f)}
   : forall {m} {a},
     forall `{GHC.Base.Monad m},
     (Backwards inst_f) (m a) -> m ((Backwards inst_f) a) :=
  fun {m} {a} `{GHC.Base.Monad m} => Traversable__Backwards_sequenceA.

Local Definition Traversable__Backwards_traverse {inst_f}
  `{(Data.Traversable.Traversable inst_f)}
   : forall {f} {a} {b},
     forall `{GHC.Base.Applicative f},
     (a -> f b) -> (Backwards inst_f) a -> f ((Backwards inst_f) b) :=
  fun {f} {a} {b} `{GHC.Base.Applicative f} =>
    fun arg_0__ arg_1__ =>
      match arg_0__, arg_1__ with
      | f, Mk_Backwards t =>
          GHC.Base.fmap Mk_Backwards (Data.Traversable.traverse f t)
      end.

Local Definition Traversable__Backwards_mapM {inst_f}
  `{(Data.Traversable.Traversable inst_f)}
   : forall {m} {a} {b},
     forall `{GHC.Base.Monad m},
     (a -> m b) -> (Backwards inst_f) a -> m ((Backwards inst_f) b) :=
  fun {m} {a} {b} `{GHC.Base.Monad m} => Traversable__Backwards_traverse.

Program Instance Traversable__Backwards {f} `{(Data.Traversable.Traversable f)}
   : Data.Traversable.Traversable (Backwards f) :=
  fun _ k =>
    k {| Data.Traversable.mapM__ := fun {m} {a} {b} `{GHC.Base.Monad m} =>
           Traversable__Backwards_mapM ;
         Data.Traversable.sequence__ := fun {m} {a} `{GHC.Base.Monad m} =>
           Traversable__Backwards_sequence ;
         Data.Traversable.sequenceA__ := fun {f} {a} `{GHC.Base.Applicative f} =>
           Traversable__Backwards_sequenceA ;
         Data.Traversable.traverse__ := fun {f} {a} {b} `{GHC.Base.Applicative f} =>
           Traversable__Backwards_traverse |}.

(* External variables:
     Eq1 Gt Lt Ord1 Type bool compare1 comparison eq1 liftCompare liftCompare__
     liftEq liftEq__ list negb Coq.Program.Basics.compose Data.Foldable.Foldable
     Data.Foldable.elem__ Data.Foldable.foldMap Data.Foldable.foldMap__
     Data.Foldable.fold__ Data.Foldable.foldl Data.Foldable.foldl'__
     Data.Foldable.foldl__ Data.Foldable.foldr Data.Foldable.foldr'__
     Data.Foldable.foldr__ Data.Foldable.length Data.Foldable.length__
     Data.Foldable.null Data.Foldable.null__ Data.Foldable.product__
     Data.Foldable.sum__ Data.Foldable.toList__ Data.SemigroupInternal.Mk_Any
     Data.SemigroupInternal.Mk_Product Data.SemigroupInternal.Mk_Sum
     Data.SemigroupInternal.getAny Data.SemigroupInternal.getProduct
     Data.SemigroupInternal.getSum Data.Traversable.Traversable
     Data.Traversable.mapM__ Data.Traversable.sequenceA Data.Traversable.sequenceA__
     Data.Traversable.sequence__ Data.Traversable.traverse
     Data.Traversable.traverse__ GHC.Base.Applicative GHC.Base.Eq_ GHC.Base.Functor
     GHC.Base.Monad GHC.Base.Monoid GHC.Base.Ord GHC.Base.build GHC.Base.compare__
     GHC.Base.const GHC.Base.fmap GHC.Base.fmap__ GHC.Base.id GHC.Base.liftA2__
     GHC.Base.max__ GHC.Base.min__ GHC.Base.op_zdzn__ GHC.Base.op_zeze__
     GHC.Base.op_zeze____ GHC.Base.op_zg____ GHC.Base.op_zgze____ GHC.Base.op_zl____
     GHC.Base.op_zlzd____ GHC.Base.op_zlze____ GHC.Base.op_zlztzg____
     GHC.Base.op_zlztztzg__ GHC.Base.op_zsze__ GHC.Base.op_zsze____
     GHC.Base.op_ztzg____ GHC.Base.pure GHC.Base.pure__ GHC.Num.Int GHC.Num.Num
*)
