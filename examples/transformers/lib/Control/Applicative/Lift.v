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
Require Data.Functor.Classes.
Require Data.Functor.Constant.
Require Data.SemigroupInternal.
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

Local Definition Eq1__Lift_liftEq {inst_f} `{(Data.Functor.Classes.Eq1 inst_f)}
   : forall {a} {b},
     (a -> b -> bool) -> (Lift inst_f) a -> (Lift inst_f) b -> bool :=
  fun {a} {b} =>
    fun arg_0__ arg_1__ arg_2__ =>
      match arg_0__, arg_1__, arg_2__ with
      | eq, Pure x1, Pure x2 => eq x1 x2
      | _, Pure _, Other _ => false
      | _, Other _, Pure _ => false
      | eq, Other y1, Other y2 => Data.Functor.Classes.liftEq eq y1 y2
      end.

Program Instance Eq1__Lift {f} `{(Data.Functor.Classes.Eq1 f)}
   : Data.Functor.Classes.Eq1 (Lift f) :=
  fun _ k =>
    k {| Data.Functor.Classes.liftEq__ := fun {a} {b} => Eq1__Lift_liftEq |}.

Local Definition Ord1__Lift_liftCompare {inst_f} `{(Data.Functor.Classes.Ord1
   inst_f)}
   : forall {a} {b},
     (a -> b -> comparison) -> (Lift inst_f) a -> (Lift inst_f) b -> comparison :=
  fun {a} {b} =>
    fun arg_0__ arg_1__ arg_2__ =>
      match arg_0__, arg_1__, arg_2__ with
      | comp, Pure x1, Pure x2 => comp x1 x2
      | _, Pure _, Other _ => Lt
      | _, Other _, Pure _ => Gt
      | comp, Other y1, Other y2 => Data.Functor.Classes.liftCompare comp y1 y2
      end.

Program Instance Ord1__Lift {f} `{(Data.Functor.Classes.Ord1 f)}
   : Data.Functor.Classes.Ord1 (Lift f) :=
  fun _ k =>
    k {| Data.Functor.Classes.liftCompare__ := fun {a} {b} =>
           Ord1__Lift_liftCompare |}.

(* Skipping instance Read1__Lift of class Read1 *)

(* Skipping instance Show1__Lift of class Show1 *)

Local Definition Eq___Lift_op_zeze__ {inst_f} {inst_a}
  `{Data.Functor.Classes.Eq1 inst_f} `{GHC.Base.Eq_ inst_a}
   : (Lift inst_f inst_a) -> (Lift inst_f inst_a) -> bool :=
  Data.Functor.Classes.eq1.

Local Definition Eq___Lift_op_zsze__ {inst_f} {inst_a}
  `{Data.Functor.Classes.Eq1 inst_f} `{GHC.Base.Eq_ inst_a}
   : (Lift inst_f inst_a) -> (Lift inst_f inst_a) -> bool :=
  fun x y => negb (Eq___Lift_op_zeze__ x y).

Program Instance Eq___Lift {f} {a} `{Data.Functor.Classes.Eq1 f} `{GHC.Base.Eq_
  a}
   : GHC.Base.Eq_ (Lift f a) :=
  fun _ k =>
    k {| GHC.Base.op_zeze____ := Eq___Lift_op_zeze__ ;
         GHC.Base.op_zsze____ := Eq___Lift_op_zsze__ |}.

Local Definition Ord__Lift_compare {inst_f} {inst_a} `{Data.Functor.Classes.Ord1
  inst_f} `{GHC.Base.Ord inst_a}
   : (Lift inst_f inst_a) -> (Lift inst_f inst_a) -> comparison :=
  Data.Functor.Classes.compare1.

Local Definition Ord__Lift_op_zgze__ {inst_f} {inst_a}
  `{Data.Functor.Classes.Ord1 inst_f} `{GHC.Base.Ord inst_a}
   : (Lift inst_f inst_a) -> (Lift inst_f inst_a) -> bool :=
  fun x y => Ord__Lift_compare x y GHC.Base./= Lt.

Local Definition Ord__Lift_op_zg__ {inst_f} {inst_a} `{Data.Functor.Classes.Ord1
  inst_f} `{GHC.Base.Ord inst_a}
   : (Lift inst_f inst_a) -> (Lift inst_f inst_a) -> bool :=
  fun x y => Ord__Lift_compare x y GHC.Base.== Gt.

Local Definition Ord__Lift_op_zlze__ {inst_f} {inst_a}
  `{Data.Functor.Classes.Ord1 inst_f} `{GHC.Base.Ord inst_a}
   : (Lift inst_f inst_a) -> (Lift inst_f inst_a) -> bool :=
  fun x y => Ord__Lift_compare x y GHC.Base./= Gt.

Local Definition Ord__Lift_max {inst_f} {inst_a} `{Data.Functor.Classes.Ord1
  inst_f} `{GHC.Base.Ord inst_a}
   : (Lift inst_f inst_a) -> (Lift inst_f inst_a) -> (Lift inst_f inst_a) :=
  fun x y => if Ord__Lift_op_zlze__ x y : bool then y else x.

Local Definition Ord__Lift_min {inst_f} {inst_a} `{Data.Functor.Classes.Ord1
  inst_f} `{GHC.Base.Ord inst_a}
   : (Lift inst_f inst_a) -> (Lift inst_f inst_a) -> (Lift inst_f inst_a) :=
  fun x y => if Ord__Lift_op_zlze__ x y : bool then x else y.

Local Definition Ord__Lift_op_zl__ {inst_f} {inst_a} `{Data.Functor.Classes.Ord1
  inst_f} `{GHC.Base.Ord inst_a}
   : (Lift inst_f inst_a) -> (Lift inst_f inst_a) -> bool :=
  fun x y => Ord__Lift_compare x y GHC.Base.== Lt.

Program Instance Ord__Lift {f} {a} `{Data.Functor.Classes.Ord1 f} `{GHC.Base.Ord
  a}
   : GHC.Base.Ord (Lift f a) :=
  fun _ k =>
    k {| GHC.Base.op_zl____ := Ord__Lift_op_zl__ ;
         GHC.Base.op_zlze____ := Ord__Lift_op_zlze__ ;
         GHC.Base.op_zg____ := Ord__Lift_op_zg__ ;
         GHC.Base.op_zgze____ := Ord__Lift_op_zgze__ ;
         GHC.Base.compare__ := Ord__Lift_compare ;
         GHC.Base.max__ := Ord__Lift_max ;
         GHC.Base.min__ := Ord__Lift_min |}.

(* Skipping instance Read__Lift of class Read *)

(* Skipping instance Show__Lift of class Show *)

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
  fun {a} {b} => Functor__Lift_fmap GHC.Base.∘ GHC.Base.const.

Program Instance Functor__Lift {f} `{(GHC.Base.Functor f)}
   : GHC.Base.Functor (Lift f) :=
  fun _ k =>
    k {| GHC.Base.fmap__ := fun {a} {b} => Functor__Lift_fmap ;
         GHC.Base.op_zlzd____ := fun {a} {b} => Functor__Lift_op_zlzd__ |}.

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
    fun f z t =>
      Data.SemigroupInternal.appEndo (Data.SemigroupInternal.getDual
                                      (Foldable__Lift_foldMap (Data.SemigroupInternal.Mk_Dual GHC.Base.∘
                                                               (Data.SemigroupInternal.Mk_Endo GHC.Base.∘
                                                                GHC.Base.flip f)) t)) z.

Local Definition Foldable__Lift_foldr' {inst_f} `{(Data.Foldable.Foldable
   inst_f)}
   : forall {a} {b}, (a -> b -> b) -> b -> (Lift inst_f) a -> b :=
  fun {a} {b} =>
    fun f z0 xs =>
      let f' := fun k x z => k (f x z) in Foldable__Lift_foldl f' GHC.Base.id xs z0.

Local Definition Foldable__Lift_foldr {inst_f} `{(Data.Foldable.Foldable
   inst_f)}
   : forall {a} {b}, (a -> b -> b) -> b -> (Lift inst_f) a -> b :=
  fun {a} {b} =>
    fun f z t =>
      Data.SemigroupInternal.appEndo (Foldable__Lift_foldMap
                                      (Coq.Program.Basics.compose Data.SemigroupInternal.Mk_Endo f) t) z.

Local Definition Foldable__Lift_foldl' {inst_f} `{(Data.Foldable.Foldable
   inst_f)}
   : forall {b} {a}, (b -> a -> b) -> b -> (Lift inst_f) a -> b :=
  fun {b} {a} =>
    fun f z0 xs =>
      let f' := fun x k z => k (f z x) in Foldable__Lift_foldr f' GHC.Base.id xs z0.

Local Definition Foldable__Lift_length {inst_f} `{(Data.Foldable.Foldable
   inst_f)}
   : forall {a}, (Lift inst_f) a -> GHC.Num.Int :=
  fun {a} =>
    Foldable__Lift_foldl' (fun arg_0__ arg_1__ =>
                             match arg_0__, arg_1__ with
                             | c, _ => c GHC.Num.+ #1
                             end) #0.

Local Definition Foldable__Lift_null {inst_f} `{(Data.Foldable.Foldable inst_f)}
   : forall {a}, (Lift inst_f) a -> bool :=
  fun {a} => Foldable__Lift_foldr (fun arg_0__ arg_1__ => false) true.

Local Definition Foldable__Lift_toList {inst_f} `{(Data.Foldable.Foldable
   inst_f)}
   : forall {a}, (Lift inst_f) a -> list a :=
  fun {a} =>
    fun t => GHC.Base.build' (fun _ => (fun c n => Foldable__Lift_foldr c n t)).

Local Definition Foldable__Lift_product {inst_f} `{(Data.Foldable.Foldable
   inst_f)}
   : forall {a}, forall `{GHC.Num.Num a}, (Lift inst_f) a -> a :=
  fun {a} `{GHC.Num.Num a} =>
    Coq.Program.Basics.compose Data.SemigroupInternal.getProduct
                               (Foldable__Lift_foldMap Data.SemigroupInternal.Mk_Product).

Local Definition Foldable__Lift_sum {inst_f} `{(Data.Foldable.Foldable inst_f)}
   : forall {a}, forall `{GHC.Num.Num a}, (Lift inst_f) a -> a :=
  fun {a} `{GHC.Num.Num a} =>
    Coq.Program.Basics.compose Data.SemigroupInternal.getSum (Foldable__Lift_foldMap
                                Data.SemigroupInternal.Mk_Sum).

Local Definition Foldable__Lift_fold {inst_f} `{(Data.Foldable.Foldable inst_f)}
   : forall {m}, forall `{GHC.Base.Monoid m}, (Lift inst_f) m -> m :=
  fun {m} `{GHC.Base.Monoid m} => Foldable__Lift_foldMap GHC.Base.id.

Program Instance Foldable__Lift {f} `{(Data.Foldable.Foldable f)}
   : Data.Foldable.Foldable (Lift f) :=
  fun _ k =>
    k {| Data.Foldable.fold__ := fun {m} `{GHC.Base.Monoid m} =>
           Foldable__Lift_fold ;
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

Local Definition Applicative__Lift_pure {inst_f} `{(GHC.Base.Applicative
   inst_f)}
   : forall {a}, a -> (Lift inst_f) a :=
  fun {a} => Pure.

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
    fun a1 a2 => Applicative__Lift_op_zlztzg__ (GHC.Base.id GHC.Base.<$ a1) a2.

Local Definition Applicative__Lift_liftA2 {inst_f} `{(GHC.Base.Applicative
   inst_f)}
   : forall {a} {b} {c},
     (a -> b -> c) -> (Lift inst_f) a -> (Lift inst_f) b -> (Lift inst_f) c :=
  fun {a} {b} {c} => fun f x => Applicative__Lift_op_zlztzg__ (GHC.Base.fmap f x).

Program Instance Applicative__Lift {f} `{(GHC.Base.Applicative f)}
   : GHC.Base.Applicative (Lift f) :=
  fun _ k =>
    k {| GHC.Base.liftA2__ := fun {a} {b} {c} => Applicative__Lift_liftA2 ;
         GHC.Base.op_zlztzg____ := fun {a} {b} => Applicative__Lift_op_zlztzg__ ;
         GHC.Base.op_ztzg____ := fun {a} {b} => Applicative__Lift_op_ztzg__ ;
         GHC.Base.pure__ := fun {a} => Applicative__Lift_pure |}.

(* Skipping instance Alternative__Lift of class Alternative *)

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

(* External variables:
     Gt Lt bool comparison false list negb true Coq.Program.Basics.compose
     Data.Either.Either Data.Either.Left Data.Either.Right Data.Either.either
     Data.Foldable.Foldable Data.Foldable.foldMap Data.Foldable.foldMap__
     Data.Foldable.fold__ Data.Foldable.foldl'__ Data.Foldable.foldl__
     Data.Foldable.foldr'__ Data.Foldable.foldr__ Data.Foldable.length__
     Data.Foldable.null__ Data.Foldable.product__ Data.Foldable.sum__
     Data.Foldable.toList__ Data.Functor.op_zlzdzg__ Data.Functor.Classes.Eq1
     Data.Functor.Classes.Ord1 Data.Functor.Classes.compare1 Data.Functor.Classes.eq1
     Data.Functor.Classes.liftCompare Data.Functor.Classes.liftCompare__
     Data.Functor.Classes.liftEq Data.Functor.Classes.liftEq__
     Data.Functor.Constant.Constant Data.Functor.Constant.Mk_Constant
     Data.SemigroupInternal.Mk_Dual Data.SemigroupInternal.Mk_Endo
     Data.SemigroupInternal.Mk_Product Data.SemigroupInternal.Mk_Sum
     Data.SemigroupInternal.appEndo Data.SemigroupInternal.getDual
     Data.SemigroupInternal.getProduct Data.SemigroupInternal.getSum
     Data.Traversable.Traversable Data.Traversable.mapM__
     Data.Traversable.sequenceA__ Data.Traversable.sequence__
     Data.Traversable.traverse Data.Traversable.traverse__ GHC.Base.Applicative
     GHC.Base.Eq_ GHC.Base.Functor GHC.Base.Monad GHC.Base.Monoid GHC.Base.Ord
     GHC.Base.build' GHC.Base.compare__ GHC.Base.const GHC.Base.flip GHC.Base.fmap
     GHC.Base.fmap__ GHC.Base.id GHC.Base.liftA2__ GHC.Base.max__ GHC.Base.min__
     GHC.Base.op_z2218U__ GHC.Base.op_zeze__ GHC.Base.op_zeze____ GHC.Base.op_zg____
     GHC.Base.op_zgze____ GHC.Base.op_zl____ GHC.Base.op_zlzd__ GHC.Base.op_zlzd____
     GHC.Base.op_zlze____ GHC.Base.op_zlztzg__ GHC.Base.op_zlztzg____
     GHC.Base.op_zsze__ GHC.Base.op_zsze____ GHC.Base.op_ztzg____ GHC.Base.pure
     GHC.Base.pure__ GHC.Num.Int GHC.Num.Num GHC.Num.fromInteger GHC.Num.op_zp__
*)
