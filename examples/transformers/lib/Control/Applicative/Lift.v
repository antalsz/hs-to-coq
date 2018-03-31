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
Require Data.Semigroup.Internal.
Require Data.Traversable.
Require GHC.Base.
Require GHC.Num.
Import Data.Functor.Notations.
Import GHC.Base.Notations.
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

Local Definition Eq___Lift_op_zeze__ {inst_f} {inst_a} `{Eq1 inst_f}
  `{GHC.Base.Eq_ inst_a}
   : (Lift inst_f inst_a) -> (Lift inst_f inst_a) -> bool :=
  eq1.

Local Definition Eq___Lift_op_zsze__ {inst_f} {inst_a} `{Eq1 inst_f}
  `{GHC.Base.Eq_ inst_a}
   : (Lift inst_f inst_a) -> (Lift inst_f inst_a) -> bool :=
  fun x y => negb (Eq___Lift_op_zeze__ x y).

Program Instance Eq___Lift {f} {a} `{Eq1 f} `{GHC.Base.Eq_ a}
   : GHC.Base.Eq_ (Lift f a) :=
  fun _ k =>
    k {| GHC.Base.op_zeze____ := Eq___Lift_op_zeze__ ;
         GHC.Base.op_zsze____ := Eq___Lift_op_zsze__ |}.

Local Definition Ord__Lift_compare {inst_f} {inst_a} `{Ord1 inst_f}
  `{GHC.Base.Ord inst_a}
   : (Lift inst_f inst_a) -> (Lift inst_f inst_a) -> comparison :=
  compare1.

Local Definition Ord__Lift_op_zg__ {inst_f} {inst_a} `{Ord1 inst_f}
  `{GHC.Base.Ord inst_a}
   : (Lift inst_f inst_a) -> (Lift inst_f inst_a) -> bool :=
  fun x y => Ord__Lift_compare x y GHC.Base.== Gt.

Local Definition Ord__Lift_op_zgze__ {inst_f} {inst_a} `{Ord1 inst_f}
  `{GHC.Base.Ord inst_a}
   : (Lift inst_f inst_a) -> (Lift inst_f inst_a) -> bool :=
  fun x y => Ord__Lift_compare x y GHC.Base./= Lt.

Local Definition Ord__Lift_op_zl__ {inst_f} {inst_a} `{Ord1 inst_f}
  `{GHC.Base.Ord inst_a}
   : (Lift inst_f inst_a) -> (Lift inst_f inst_a) -> bool :=
  fun x y => Ord__Lift_compare x y GHC.Base.== Lt.

Local Definition Ord__Lift_op_zlze__ {inst_f} {inst_a} `{Ord1 inst_f}
  `{GHC.Base.Ord inst_a}
   : (Lift inst_f inst_a) -> (Lift inst_f inst_a) -> bool :=
  fun x y => Ord__Lift_compare x y GHC.Base./= Gt.

Local Definition Ord__Lift_max {inst_f} {inst_a} `{Ord1 inst_f} `{GHC.Base.Ord
  inst_a}
   : (Lift inst_f inst_a) -> (Lift inst_f inst_a) -> (Lift inst_f inst_a) :=
  fun x y => if Ord__Lift_op_zlze__ x y : bool then y else x.

Local Definition Ord__Lift_min {inst_f} {inst_a} `{Ord1 inst_f} `{GHC.Base.Ord
  inst_a}
   : (Lift inst_f inst_a) -> (Lift inst_f inst_a) -> (Lift inst_f inst_a) :=
  fun x y => if Ord__Lift_op_zlze__ x y : bool then x else y.

Program Instance Ord__Lift {f} {a} `{Ord1 f} `{GHC.Base.Ord a}
   : GHC.Base.Ord (Lift f a) :=
  fun _ k =>
    k {| GHC.Base.op_zl____ := Ord__Lift_op_zl__ ;
         GHC.Base.op_zlze____ := Ord__Lift_op_zlze__ ;
         GHC.Base.op_zg____ := Ord__Lift_op_zg__ ;
         GHC.Base.op_zgze____ := Ord__Lift_op_zgze__ ;
         GHC.Base.compare__ := Ord__Lift_compare ;
         GHC.Base.max__ := Ord__Lift_max ;
         GHC.Base.min__ := Ord__Lift_min |}.

(* Translating `instance Read__Lift' failed: OOPS! Cannot find information for
   class Qualified "GHC.Read" "Read" unsupported *)

(* Translating `instance Show__Lift' failed: OOPS! Cannot find information for
   class Qualified "GHC.Show" "Show" unsupported *)

Local Definition Functor__Lift_fmap {inst_f} `{(GHC.Base.Functor inst_f)}
   : forall {a} {b}, (a -> b) -> (Lift inst_f) a -> (Lift inst_f) b :=
  fun {a} {b} =>
    fun arg_0__ arg_1__ =>
      match arg_0__, arg_1__ with
      | f, Pure x => Pure (f x)
      | f, Other y => Other (GHC.Base.fmap f y)
      end.

Local Definition Functor__Lift_op_zlzd__ {inst_f} `{(GHC.Base.Functor inst_f)}
   : forall {a} {b}, a -> (Lift inst_f) b -> (Lift inst_f) a :=
  fun {a} {b} => fun x => Functor__Lift_fmap (GHC.Base.const x).

Program Instance Functor__Lift {f} `{(GHC.Base.Functor f)}
   : GHC.Base.Functor (Lift f) :=
  fun _ k =>
    k {| GHC.Base.op_zlzd____ := fun {a} {b} => Functor__Lift_op_zlzd__ ;
         GHC.Base.fmap__ := fun {a} {b} => Functor__Lift_fmap |}.

Local Definition Foldable__Lift_foldMap {inst_f} `{(Data.Foldable.Foldable
   inst_f)}
   : forall {m} {a},
     forall `{GHC.Base.Monoid m}, (a -> m) -> (Lift inst_f) a -> m :=
  fun {m} {a} `{GHC.Base.Monoid m} =>
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
          Data.Semigroup.Internal.appEndo (Data.Semigroup.Internal.getDual
                                           (Foldable__Lift_foldMap (Coq.Program.Basics.compose
                                                                    Data.Semigroup.Internal.Mk_Dual
                                                                    (Coq.Program.Basics.compose
                                                                     Data.Semigroup.Internal.Mk_Endo (GHC.Base.flip f)))
                                            t)) z
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
              | k, x, z => k GHC.Base.$! f x z
              end in
          Foldable__Lift_foldl f' GHC.Base.id xs z0
      end.

Local Definition Foldable__Lift_foldr {inst_f} `{(Data.Foldable.Foldable
   inst_f)}
   : forall {a} {b}, (a -> b -> b) -> b -> (Lift inst_f) a -> b :=
  fun {a} {b} =>
    fun arg_4__ arg_5__ arg_6__ =>
      match arg_4__, arg_5__, arg_6__ with
      | f, z, t =>
          Data.Semigroup.Internal.appEndo (Foldable__Lift_foldMap
                                           (Coq.Program.Basics.compose Data.Semigroup.Internal.Mk_Endo f) t) z
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
              | x, k, z => k GHC.Base.$! f z x
              end in
          Foldable__Lift_foldr f' GHC.Base.id xs z0
      end.

Local Definition Foldable__Lift_length {inst_f} `{(Data.Foldable.Foldable
   inst_f)}
   : forall {a}, (Lift inst_f) a -> GHC.Num.Int :=
  fun {a} =>
    Foldable__Lift_foldl' (fun arg_64__ arg_65__ =>
                             match arg_64__, arg_65__ with
                             | c, _ => c GHC.Num.+ #1
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
      GHC.Base.build (fun _ arg_55__ arg_56__ =>
                        match arg_55__, arg_56__ with
                        | c, n => Foldable__Lift_foldr c n t
                        end).

Local Definition Foldable__Lift_product {inst_f} `{(Data.Foldable.Foldable
   inst_f)}
   : forall {a}, forall `{GHC.Num.Num a}, (Lift inst_f) a -> a :=
  fun {a} `{GHC.Num.Num a} =>
    Coq.Program.Basics.compose Data.Semigroup.Internal.getProduct
                               (Foldable__Lift_foldMap Data.Semigroup.Internal.Mk_Product).

Local Definition Foldable__Lift_sum {inst_f} `{(Data.Foldable.Foldable inst_f)}
   : forall {a}, forall `{GHC.Num.Num a}, (Lift inst_f) a -> a :=
  fun {a} `{GHC.Num.Num a} =>
    Coq.Program.Basics.compose Data.Semigroup.Internal.getSum
                               (Foldable__Lift_foldMap Data.Semigroup.Internal.Mk_Sum).

Local Definition Foldable__Lift_fold {inst_f} `{(Data.Foldable.Foldable inst_f)}
   : forall {m}, forall `{GHC.Base.Monoid m}, (Lift inst_f) m -> m :=
  fun {m} `{GHC.Base.Monoid m} => Foldable__Lift_foldMap GHC.Base.id.

Local Definition Foldable__Lift_elem {inst_f} `{(Data.Foldable.Foldable inst_f)}
   : forall {a}, forall `{GHC.Base.Eq_ a}, a -> (Lift inst_f) a -> bool :=
  fun {a} `{GHC.Base.Eq_ a} =>
    Coq.Program.Basics.compose (fun arg_69__ =>
                                  let 'p := arg_69__ in
                                  Coq.Program.Basics.compose Data.Semigroup.Internal.getAny
                                                             (Foldable__Lift_foldMap (Coq.Program.Basics.compose
                                                                                      Data.Semigroup.Internal.Mk_Any
                                                                                      p))) _GHC.Base.==_.

Program Instance Foldable__Lift {f} `{(Data.Foldable.Foldable f)}
   : Data.Foldable.Foldable (Lift f) :=
  fun _ k =>
    k {| Data.Foldable.elem__ := fun {a} `{GHC.Base.Eq_ a} => Foldable__Lift_elem ;
         Data.Foldable.fold__ := fun {m} `{GHC.Base.Monoid m} => Foldable__Lift_fold ;
         Data.Foldable.foldMap__ := fun {m} {a} `{GHC.Base.Monoid m} =>
           Foldable__Lift_foldMap ;
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
     forall `{GHC.Base.Applicative f},
     (a -> f b) -> (Lift inst_f) a -> f ((Lift inst_f) b) :=
  fun {f} {a} {b} `{GHC.Base.Applicative f} =>
    fun arg_0__ arg_1__ =>
      match arg_0__, arg_1__ with
      | f, Pure x => Pure Data.Functor.<$> f x
      | f, Other y => Other Data.Functor.<$> Data.Traversable.traverse f y
      end.

Local Definition Traversable__Lift_sequenceA {inst_f}
  `{(Data.Traversable.Traversable inst_f)}
   : forall {f} {a},
     forall `{GHC.Base.Applicative f}, (Lift inst_f) (f a) -> f ((Lift inst_f) a) :=
  fun {f} {a} `{GHC.Base.Applicative f} => Traversable__Lift_traverse GHC.Base.id.

Local Definition Traversable__Lift_sequence {inst_f}
  `{(Data.Traversable.Traversable inst_f)}
   : forall {m} {a},
     forall `{GHC.Base.Monad m}, (Lift inst_f) (m a) -> m ((Lift inst_f) a) :=
  fun {m} {a} `{GHC.Base.Monad m} => Traversable__Lift_sequenceA.

Local Definition Traversable__Lift_mapM {inst_f} `{(Data.Traversable.Traversable
   inst_f)}
   : forall {m} {a} {b},
     forall `{GHC.Base.Monad m},
     (a -> m b) -> (Lift inst_f) a -> m ((Lift inst_f) b) :=
  fun {m} {a} {b} `{GHC.Base.Monad m} => Traversable__Lift_traverse.

Program Instance Traversable__Lift {f} `{(Data.Traversable.Traversable f)}
   : Data.Traversable.Traversable (Lift f) :=
  fun _ k =>
    k {| Data.Traversable.mapM__ := fun {m} {a} {b} `{GHC.Base.Monad m} =>
           Traversable__Lift_mapM ;
         Data.Traversable.sequence__ := fun {m} {a} `{GHC.Base.Monad m} =>
           Traversable__Lift_sequence ;
         Data.Traversable.sequenceA__ := fun {f} {a} `{GHC.Base.Applicative f} =>
           Traversable__Lift_sequenceA ;
         Data.Traversable.traverse__ := fun {f} {a} {b} `{GHC.Base.Applicative f} =>
           Traversable__Lift_traverse |}.

Local Definition Applicative__Lift_op_zlztzg__ {inst_f} `{(GHC.Base.Applicative
   inst_f)}
   : forall {a} {b},
     (Lift inst_f) (a -> b) -> (Lift inst_f) a -> (Lift inst_f) b :=
  fun {a} {b} =>
    fun arg_0__ arg_1__ =>
      match arg_0__, arg_1__ with
      | Pure f, Pure x => Pure (f x)
      | Pure f, Other y => Other (f Data.Functor.<$> y)
      | Other f, Pure x => Other ((fun arg_4__ => arg_4__ x) Data.Functor.<$> f)
      | Other f, Other y => Other (f GHC.Base.<*> y)
      end.

Local Definition Applicative__Lift_op_ztzg__ {inst_f} `{(GHC.Base.Applicative
   inst_f)}
   : forall {a} {b}, (Lift inst_f) a -> (Lift inst_f) b -> (Lift inst_f) b :=
  fun {a} {b} =>
    fun x y =>
      Applicative__Lift_op_zlztzg__ (GHC.Base.fmap (GHC.Base.const GHC.Base.id) x) y.

Local Definition Applicative__Lift_liftA2 {inst_f} `{(GHC.Base.Applicative
   inst_f)}
   : forall {a} {b} {c},
     (a -> b -> c) -> (Lift inst_f) a -> (Lift inst_f) b -> (Lift inst_f) c :=
  fun {a} {b} {c} => fun f x => Applicative__Lift_op_zlztzg__ (GHC.Base.fmap f x).

Local Definition Applicative__Lift_pure {inst_f} `{(GHC.Base.Applicative
   inst_f)}
   : forall {a}, a -> (Lift inst_f) a :=
  fun {a} => Pure.

Program Instance Applicative__Lift {f} `{(GHC.Base.Applicative f)}
   : GHC.Base.Applicative (Lift f) :=
  fun _ k =>
    k {| GHC.Base.op_ztzg____ := fun {a} {b} => Applicative__Lift_op_ztzg__ ;
         GHC.Base.op_zlztzg____ := fun {a} {b} => Applicative__Lift_op_zlztzg__ ;
         GHC.Base.liftA2__ := fun {a} {b} {c} => Applicative__Lift_liftA2 ;
         GHC.Base.pure__ := fun {a} => Applicative__Lift_pure |}.

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

Definition unLift {f} {a} `{(GHC.Base.Applicative f)} : Lift f a -> f a :=
  fun arg_0__ =>
    match arg_0__ with
    | Pure x => GHC.Base.pure x
    | Other e => e
    end.

(* Unbound variables:
     Eq1 Gt Lt Ord1 bool compare1 comparison eq1 false liftCompare liftEq list negb
     true Coq.Program.Basics.compose Data.Either.Either Data.Either.Left
     Data.Either.Right Data.Either.either Data.Foldable.Foldable
     Data.Foldable.foldMap Data.Functor.op_zlzdzg__ Data.Functor.Constant.Constant
     Data.Functor.Constant.Mk_Constant Data.Semigroup.Internal.Mk_Any
     Data.Semigroup.Internal.Mk_Dual Data.Semigroup.Internal.Mk_Endo
     Data.Semigroup.Internal.Mk_Product Data.Semigroup.Internal.Mk_Sum
     Data.Semigroup.Internal.appEndo Data.Semigroup.Internal.getAny
     Data.Semigroup.Internal.getDual Data.Semigroup.Internal.getProduct
     Data.Semigroup.Internal.getSum Data.Traversable.Traversable
     Data.Traversable.traverse GHC.Base.Applicative GHC.Base.Eq_ GHC.Base.Functor
     GHC.Base.Monad GHC.Base.Monoid GHC.Base.Ord GHC.Base.build GHC.Base.const
     GHC.Base.flip GHC.Base.fmap GHC.Base.id GHC.Base.op_zdzn__ GHC.Base.op_zeze__
     GHC.Base.op_zlztzg__ GHC.Base.op_zsze__ GHC.Base.pure GHC.Num.Int GHC.Num.Num
     GHC.Num.fromInteger GHC.Num.op_zp__
*)
