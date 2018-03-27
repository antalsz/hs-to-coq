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
Require Data.Either.
Require Data.Foldable.
Require Data.Functor.
Require Import Data.Functor.Classes.
Require Data.Functor.Constant.
Require Import Data.Monoid.
Require Data.Traversable.
Require Import GHC.Base.
Require GHC.Num.
Import Data.Functor.Notations.
Import GHC.Num.Notations.

(* Converted type declarations: *)

Inductive Lift f a : Type := Pure : a -> Lift f a |  Other : (f a) -> Lift f a.

Definition Errors e :=
  (Lift (Data.Functor.Constant.Constant e))%type.

Arguments Pure {_} {_} _.

Arguments Other {_} {_} _.
(* Converted value declarations: *)

Local Definition Eq1__Lift_liftEq {inst_f} `{(Eq1 inst_f)}
   : forall {a} {b},
     (a -> b -> bool) -> (Lift inst_f) a -> (Lift inst_f) b -> bool :=
  fun {a} {b} =>
    fun arg_0__ arg_1__ arg_2__ =>
      match arg_0__, arg_1__, arg_2__ with
      | eq, Pure x1, Pure x2 => eq x1 x2
      | _, Pure _, Other _ => false
      | _, Other _, Pure _ => false
      | eq, Other y1, Other y2 => liftEq eq y1 y2
      end.

Program Instance Eq1__Lift {f} `{(Eq1 f)} : Eq1 (Lift f) :=
  fun _ k => k {| liftEq__ := fun {a} {b} => Eq1__Lift_liftEq |}.

Local Definition Ord1__Lift_liftCompare {inst_f} `{(Ord1 inst_f)}
   : forall {a} {b},
     (a -> b -> comparison) -> (Lift inst_f) a -> (Lift inst_f) b -> comparison :=
  fun {a} {b} =>
    fun arg_0__ arg_1__ arg_2__ =>
      match arg_0__, arg_1__, arg_2__ with
      | comp, Pure x1, Pure x2 => comp x1 x2
      | _, Pure _, Other _ => Lt
      | _, Other _, Pure _ => Gt
      | comp, Other y1, Other y2 => liftCompare comp y1 y2
      end.

Program Instance Ord1__Lift {f} `{(Ord1 f)} : Ord1 (Lift f) :=
  fun _ k => k {| liftCompare__ := fun {a} {b} => Ord1__Lift_liftCompare |}.

(* Translating `instance Read1__Lift' failed: OOPS! Cannot find information for
   class Qualified "Data.Functor.Classes" "Read1" unsupported *)

(* Translating `instance Show1__Lift' failed: OOPS! Cannot find information for
   class Qualified "Data.Functor.Classes" "Show1" unsupported *)

Local Definition Eq___Lift_op_zeze__ {inst_f} {inst_a} `{Eq1 inst_f} `{Eq_
  inst_a}
   : (Lift inst_f inst_a) -> (Lift inst_f inst_a) -> bool :=
  eq1.

Local Definition Eq___Lift_op_zsze__ {inst_f} {inst_a} `{Eq1 inst_f} `{Eq_
  inst_a}
   : (Lift inst_f inst_a) -> (Lift inst_f inst_a) -> bool :=
  fun x y => negb (Eq___Lift_op_zeze__ x y).

Program Instance Eq___Lift {f} {a} `{Eq1 f} `{Eq_ a} : Eq_ (Lift f a) :=
  fun _ k =>
    k {| op_zeze____ := Eq___Lift_op_zeze__ ; op_zsze____ := Eq___Lift_op_zsze__ |}.

Local Definition Ord__Lift_compare {inst_f} {inst_a} `{Ord1 inst_f} `{Ord
  inst_a}
   : (Lift inst_f inst_a) -> (Lift inst_f inst_a) -> comparison :=
  compare1.

Local Definition Ord__Lift_op_zg__ {inst_f} {inst_a} `{Ord1 inst_f} `{Ord
  inst_a}
   : (Lift inst_f inst_a) -> (Lift inst_f inst_a) -> bool :=
  fun x y => _==_ (Ord__Lift_compare x y) Gt.

Local Definition Ord__Lift_op_zgze__ {inst_f} {inst_a} `{Ord1 inst_f} `{Ord
  inst_a}
   : (Lift inst_f inst_a) -> (Lift inst_f inst_a) -> bool :=
  fun x y => _/=_ (Ord__Lift_compare x y) Lt.

Local Definition Ord__Lift_op_zl__ {inst_f} {inst_a} `{Ord1 inst_f} `{Ord
  inst_a}
   : (Lift inst_f inst_a) -> (Lift inst_f inst_a) -> bool :=
  fun x y => _==_ (Ord__Lift_compare x y) Lt.

Local Definition Ord__Lift_op_zlze__ {inst_f} {inst_a} `{Ord1 inst_f} `{Ord
  inst_a}
   : (Lift inst_f inst_a) -> (Lift inst_f inst_a) -> bool :=
  fun x y => _/=_ (Ord__Lift_compare x y) Gt.

Local Definition Ord__Lift_max {inst_f} {inst_a} `{Ord1 inst_f} `{Ord inst_a}
   : (Lift inst_f inst_a) -> (Lift inst_f inst_a) -> (Lift inst_f inst_a) :=
  fun x y => if Ord__Lift_op_zlze__ x y : bool then y else x.

Local Definition Ord__Lift_min {inst_f} {inst_a} `{Ord1 inst_f} `{Ord inst_a}
   : (Lift inst_f inst_a) -> (Lift inst_f inst_a) -> (Lift inst_f inst_a) :=
  fun x y => if Ord__Lift_op_zlze__ x y : bool then x else y.

Program Instance Ord__Lift {f} {a} `{Ord1 f} `{Ord a} : Ord (Lift f a) :=
  fun _ k =>
    k {| op_zl____ := Ord__Lift_op_zl__ ;
         op_zlze____ := Ord__Lift_op_zlze__ ;
         op_zg____ := Ord__Lift_op_zg__ ;
         op_zgze____ := Ord__Lift_op_zgze__ ;
         compare__ := Ord__Lift_compare ;
         max__ := Ord__Lift_max ;
         min__ := Ord__Lift_min |}.

(* Translating `instance Read__Lift' failed: OOPS! Cannot find information for
   class Qualified "GHC.Read" "Read" unsupported *)

(* Translating `instance Show__Lift' failed: OOPS! Cannot find information for
   class Qualified "GHC.Show" "Show" unsupported *)

Local Definition Functor__Lift_fmap {inst_f} `{(Functor inst_f)}
   : forall {a} {b}, (a -> b) -> (Lift inst_f) a -> (Lift inst_f) b :=
  fun {a} {b} =>
    fun arg_0__ arg_1__ =>
      match arg_0__, arg_1__ with
      | f, Pure x => Pure (f x)
      | f, Other y => Other (fmap f y)
      end.

Local Definition Functor__Lift_op_zlzd__ {inst_f} `{(Functor inst_f)}
   : forall {a} {b}, a -> (Lift inst_f) b -> (Lift inst_f) a :=
  fun {a} {b} => fun x => Functor__Lift_fmap (const x).

Program Instance Functor__Lift {f} `{(Functor f)} : Functor (Lift f) :=
  fun _ k =>
    k {| op_zlzd____ := fun {a} {b} => Functor__Lift_op_zlzd__ ;
         fmap__ := fun {a} {b} => Functor__Lift_fmap |}.

Local Definition Foldable__Lift_foldMap {inst_f} `{(Data.Foldable.Foldable
   inst_f)}
   : forall {m} {a}, forall `{Monoid m}, (a -> m) -> (Lift inst_f) a -> m :=
  fun {m} {a} `{Monoid m} =>
    fun arg_0__ arg_1__ =>
      match arg_0__, arg_1__ with
      | f, Pure x => f x
      | f, Other y => Data.Foldable.foldMap f y
      end.

Local Definition Foldable__Lift_foldl {inst_f} `{(Data.Foldable.Foldable
   inst_f)}
   : forall {b} {a}, (b -> a -> b) -> b -> (Lift inst_f) a -> b :=
  fun {b} {a} =>
    fun arg_19__ arg_20__ arg_21__ =>
      match arg_19__, arg_20__, arg_21__ with
      | f, z, t =>
          appEndo (getDual (Foldable__Lift_foldMap (Coq.Program.Basics.compose Mk_Dual
                                                                               (Coq.Program.Basics.compose Mk_Endo (flip
                                                                                                            f))) t)) z
      end.

Local Definition Foldable__Lift_foldr' {inst_f} `{(Data.Foldable.Foldable
   inst_f)}
   : forall {a} {b}, (a -> b -> b) -> b -> (Lift inst_f) a -> b :=
  fun {a} {b} =>
    fun arg_9__ arg_10__ arg_11__ =>
      match arg_9__, arg_10__, arg_11__ with
      | f, z0, xs =>
          let f' :=
            fun arg_12__ arg_13__ arg_14__ =>
              match arg_12__, arg_13__, arg_14__ with
              | k, x, z => _$!_ k (f x z)
              end in
          Foldable__Lift_foldl f' id xs z0
      end.

Local Definition Foldable__Lift_foldr {inst_f} `{(Data.Foldable.Foldable
   inst_f)}
   : forall {a} {b}, (a -> b -> b) -> b -> (Lift inst_f) a -> b :=
  fun {a} {b} =>
    fun arg_4__ arg_5__ arg_6__ =>
      match arg_4__, arg_5__, arg_6__ with
      | f, z, t =>
          appEndo (Foldable__Lift_foldMap (Data.Foldable.hash_compose Mk_Endo f) t) z
      end.

Local Definition Foldable__Lift_foldl' {inst_f} `{(Data.Foldable.Foldable
   inst_f)}
   : forall {b} {a}, (b -> a -> b) -> b -> (Lift inst_f) a -> b :=
  fun {b} {a} =>
    fun arg_24__ arg_25__ arg_26__ =>
      match arg_24__, arg_25__, arg_26__ with
      | f, z0, xs =>
          let f' :=
            fun arg_27__ arg_28__ arg_29__ =>
              match arg_27__, arg_28__, arg_29__ with
              | x, k, z => _$!_ k (f z x)
              end in
          Foldable__Lift_foldr f' id xs z0
      end.

Local Definition Foldable__Lift_length {inst_f} `{(Data.Foldable.Foldable
   inst_f)}
   : forall {a}, (Lift inst_f) a -> GHC.Num.Int :=
  fun {a} =>
    Foldable__Lift_foldl' (fun arg_64__ arg_65__ =>
                             match arg_64__, arg_65__ with
                             | c, _ => _GHC.Num.+_ c #1
                             end) #0.

Local Definition Foldable__Lift_null {inst_f} `{(Data.Foldable.Foldable inst_f)}
   : forall {a}, (Lift inst_f) a -> bool :=
  fun {a} => Foldable__Lift_foldr (fun arg_61__ arg_62__ => false) true.

Local Definition Foldable__Lift_toList {inst_f} `{(Data.Foldable.Foldable
   inst_f)}
   : forall {a}, (Lift inst_f) a -> list a :=
  fun {a} =>
    fun arg_54__ =>
      let 't := arg_54__ in
      build (fun _ arg_55__ arg_56__ =>
               match arg_55__, arg_56__ with
               | c, n => Foldable__Lift_foldr c n t
               end).

Local Definition Foldable__Lift_product {inst_f} `{(Data.Foldable.Foldable
   inst_f)}
   : forall {a}, forall `{GHC.Num.Num a}, (Lift inst_f) a -> a :=
  fun {a} `{GHC.Num.Num a} =>
    Data.Foldable.hash_compose getProduct (Foldable__Lift_foldMap Mk_Product).

Local Definition Foldable__Lift_sum {inst_f} `{(Data.Foldable.Foldable inst_f)}
   : forall {a}, forall `{GHC.Num.Num a}, (Lift inst_f) a -> a :=
  fun {a} `{GHC.Num.Num a} =>
    Data.Foldable.hash_compose getSum (Foldable__Lift_foldMap Mk_Sum).

Local Definition Foldable__Lift_fold {inst_f} `{(Data.Foldable.Foldable inst_f)}
   : forall {m}, forall `{Monoid m}, (Lift inst_f) m -> m :=
  fun {m} `{Monoid m} => Foldable__Lift_foldMap id.

Local Definition Foldable__Lift_elem {inst_f} `{(Data.Foldable.Foldable inst_f)}
   : forall {a}, forall `{Eq_ a}, a -> (Lift inst_f) a -> bool :=
  fun {a} `{Eq_ a} =>
    Coq.Program.Basics.compose (fun arg_69__ =>
                                  let 'p := arg_69__ in
                                  Coq.Program.Basics.compose getAny (Foldable__Lift_foldMap
                                                              (Coq.Program.Basics.compose Mk_Any p))) _==_.

Program Instance Foldable__Lift {f} `{(Data.Foldable.Foldable f)}
   : Data.Foldable.Foldable (Lift f) :=
  fun _ k =>
    k {| Data.Foldable.elem__ := fun {a} `{Eq_ a} => Foldable__Lift_elem ;
         Data.Foldable.fold__ := fun {m} `{Monoid m} => Foldable__Lift_fold ;
         Data.Foldable.foldMap__ := fun {m} {a} `{Monoid m} => Foldable__Lift_foldMap ;
         Data.Foldable.foldl__ := fun {b} {a} => Foldable__Lift_foldl ;
         Data.Foldable.foldl'__ := fun {b} {a} => Foldable__Lift_foldl' ;
         Data.Foldable.foldr__ := fun {a} {b} => Foldable__Lift_foldr ;
         Data.Foldable.foldr'__ := fun {a} {b} => Foldable__Lift_foldr' ;
         Data.Foldable.length__ := fun {a} => Foldable__Lift_length ;
         Data.Foldable.null__ := fun {a} => Foldable__Lift_null ;
         Data.Foldable.product__ := fun {a} `{GHC.Num.Num a} => Foldable__Lift_product ;
         Data.Foldable.sum__ := fun {a} `{GHC.Num.Num a} => Foldable__Lift_sum ;
         Data.Foldable.toList__ := fun {a} => Foldable__Lift_toList |}.

Local Definition Traversable__Lift_traverse {inst_f}
  `{(Data.Traversable.Traversable inst_f)}
   : forall {f} {a} {b},
     forall `{Applicative f}, (a -> f b) -> (Lift inst_f) a -> f ((Lift inst_f) b) :=
  fun {f} {a} {b} `{Applicative f} =>
    fun arg_0__ arg_1__ =>
      match arg_0__, arg_1__ with
      | f, Pure x => Pure Data.Functor.<$> f x
      | f, Other y => Other Data.Functor.<$> Data.Traversable.traverse f y
      end.

Local Definition Traversable__Lift_sequenceA {inst_f}
  `{(Data.Traversable.Traversable inst_f)}
   : forall {f} {a},
     forall `{Applicative f}, (Lift inst_f) (f a) -> f ((Lift inst_f) a) :=
  fun {f} {a} `{Applicative f} => Traversable__Lift_traverse id.

Local Definition Traversable__Lift_sequence {inst_f}
  `{(Data.Traversable.Traversable inst_f)}
   : forall {m} {a},
     forall `{Monad m}, (Lift inst_f) (m a) -> m ((Lift inst_f) a) :=
  fun {m} {a} `{Monad m} => Traversable__Lift_sequenceA.

Local Definition Traversable__Lift_mapM {inst_f} `{(Data.Traversable.Traversable
   inst_f)}
   : forall {m} {a} {b},
     forall `{Monad m}, (a -> m b) -> (Lift inst_f) a -> m ((Lift inst_f) b) :=
  fun {m} {a} {b} `{Monad m} => Traversable__Lift_traverse.

Program Instance Traversable__Lift {f} `{(Data.Traversable.Traversable f)}
   : Data.Traversable.Traversable (Lift f) :=
  fun _ k =>
    k {| Data.Traversable.mapM__ := fun {m} {a} {b} `{Monad m} =>
           Traversable__Lift_mapM ;
         Data.Traversable.sequence__ := fun {m} {a} `{Monad m} =>
           Traversable__Lift_sequence ;
         Data.Traversable.sequenceA__ := fun {f} {a} `{Applicative f} =>
           Traversable__Lift_sequenceA ;
         Data.Traversable.traverse__ := fun {f} {a} {b} `{Applicative f} =>
           Traversable__Lift_traverse |}.

Local Definition Applicative__Lift_op_zlztzg__ {inst_f} `{(Applicative inst_f)}
   : forall {a} {b},
     (Lift inst_f) (a -> b) -> (Lift inst_f) a -> (Lift inst_f) b :=
  fun {a} {b} =>
    fun arg_0__ arg_1__ =>
      match arg_0__, arg_1__ with
      | Pure f, Pure x => Pure (f x)
      | Pure f, Other y => Other (f Data.Functor.<$> y)
      | Other f, Pure x => Other ((fun arg_4__ => arg_4__ x) Data.Functor.<$> f)
      | Other f, Other y => Other (f <*> y)
      end.

Local Definition Applicative__Lift_op_ztzg__ {inst_f} `{(Applicative inst_f)}
   : forall {a} {b}, (Lift inst_f) a -> (Lift inst_f) b -> (Lift inst_f) b :=
  fun {a} {b} => fun x y => Applicative__Lift_op_zlztzg__ (fmap (const id) x) y.

Local Definition Applicative__Lift_pure {inst_f} `{(Applicative inst_f)}
   : forall {a}, a -> (Lift inst_f) a :=
  fun {a} => Pure.

Program Instance Applicative__Lift {f} `{(Applicative f)}
   : Applicative (Lift f) :=
  fun _ k =>
    k {| op_ztzg____ := fun {a} {b} => Applicative__Lift_op_ztzg__ ;
         op_zlztzg____ := fun {a} {b} => Applicative__Lift_op_zlztzg__ ;
         pure__ := fun {a} => Applicative__Lift_pure |}.

(* Translating `instance Alternative__Lift' failed: OOPS! Cannot find
   information for class Qualified "GHC.Base" "Alternative" unsupported *)

Definition elimLift {a} {r} {f} : (a -> r) -> (f a -> r) -> Lift f a -> r :=
  fun arg_0__ arg_1__ arg_2__ =>
    match arg_0__, arg_1__, arg_2__ with
    | f, _, Pure x => f x
    | _, g, Other e => g e
    end.

Definition failure {e} {a} : e -> Errors e a :=
  fun e => Other (Data.Functor.Constant.Mk_Constant e).

Definition eitherToErrors {e} {a} : Data.Either.Either e a -> Errors e a :=
  Data.Either.either failure Pure.

Definition mapLift {f} {a} {g} : (f a -> g a) -> Lift f a -> Lift g a :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | _, Pure x => Pure x
    | f, Other e => Other (f e)
    end.

Definition runErrors {e} {a} : Errors e a -> Data.Either.Either e a :=
  fun arg_0__ =>
    match arg_0__ with
    | Other (Data.Functor.Constant.Mk_Constant e) => Data.Either.Left e
    | Pure x => Data.Either.Right x
    end.

Definition unLift {f} {a} `{(Applicative f)} : Lift f a -> f a :=
  fun arg_0__ => match arg_0__ with | Pure x => pure x | Other e => e end.

(* Unbound variables:
     Applicative Eq1 Eq_ Functor Gt Lt Mk_Any Mk_Dual Mk_Endo Mk_Product Mk_Sum Monad
     Monoid Ord Ord1 appEndo bool build compare1 comparison const eq1 false flip fmap
     getAny getDual getProduct getSum id liftCompare liftEq list negb op_zdzn__
     op_zeze__ op_zlztzg__ op_zsze__ pure true Coq.Program.Basics.compose
     Data.Either.Either Data.Either.Left Data.Either.Right Data.Either.either
     Data.Foldable.Foldable Data.Foldable.foldMap Data.Foldable.hash_compose
     Data.Functor.op_zlzdzg__ Data.Functor.Constant.Constant
     Data.Functor.Constant.Mk_Constant Data.Traversable.Traversable
     Data.Traversable.traverse GHC.Num.Int GHC.Num.Num GHC.Num.fromInteger
     GHC.Num.op_zp__
*)
