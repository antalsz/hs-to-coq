(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Coq.Program.Tactics.
Require Coq.Program.Wf.

(* Converted imports: *)

Require Control.Monad.Fail.
Require Coq.Program.Basics.
Require Data.Foldable.
Require Data.Functor.Classes.
Require Data.SemigroupInternal.
Require GHC.Base.
Require GHC.Num.
Import GHC.Base.Notations.

(* Converted type declarations: *)

Inductive Reverse (f : Type -> Type) (a : Type) : Type
  := Mk_Reverse (getReverse : f a) : Reverse f a.

Arguments Mk_Reverse {_} {_} _.

Definition getReverse {f : Type -> Type} {a : Type} (arg_0__ : Reverse f a) :=
  let 'Mk_Reverse getReverse := arg_0__ in
  getReverse.

(* Converted value declarations: *)

(* Skipping instance `Data.Functor.Reverse.Traversable__Reverse' of class
   `Data.Traversable.Traversable' *)

Local Definition Foldable__Reverse_foldMap {inst_f} `{(Data.Foldable.Foldable
   inst_f)}
   : forall {m} {a},
     forall `{GHC.Base.Monoid m}, (a -> m) -> (Reverse inst_f) a -> m :=
  fun {m} {a} `{GHC.Base.Monoid m} =>
    fun arg_0__ arg_1__ =>
      match arg_0__, arg_1__ with
      | f, Mk_Reverse t =>
          Data.SemigroupInternal.getDual (Data.Foldable.foldMap
                                          (Data.SemigroupInternal.Mk_Dual GHC.Base.∘ f) t)
      end.

Local Definition Foldable__Reverse_fold {inst_f} `{(Data.Foldable.Foldable
   inst_f)}
   : forall {m}, forall `{GHC.Base.Monoid m}, (Reverse inst_f) m -> m :=
  fun {m} `{GHC.Base.Monoid m} => Foldable__Reverse_foldMap GHC.Base.id.

Local Definition Foldable__Reverse_foldl {inst_f} `{(Data.Foldable.Foldable
   inst_f)}
   : forall {b} {a}, (b -> a -> b) -> b -> (Reverse inst_f) a -> b :=
  fun {b} {a} =>
    fun arg_0__ arg_1__ arg_2__ =>
      match arg_0__, arg_1__, arg_2__ with
      | f, z, Mk_Reverse t => Data.Foldable.foldr (GHC.Base.flip f) z t
      end.

Local Definition Foldable__Reverse_foldr {inst_f} `{(Data.Foldable.Foldable
   inst_f)}
   : forall {a} {b}, (a -> b -> b) -> b -> (Reverse inst_f) a -> b :=
  fun {a} {b} =>
    fun arg_0__ arg_1__ arg_2__ =>
      match arg_0__, arg_1__, arg_2__ with
      | f, z, Mk_Reverse t => Data.Foldable.foldl (GHC.Base.flip f) z t
      end.

Local Definition Foldable__Reverse_foldl' {inst_f} `{(Data.Foldable.Foldable
   inst_f)}
   : forall {b} {a}, (b -> a -> b) -> b -> (Reverse inst_f) a -> b :=
  fun {b} {a} =>
    fun f z0 xs =>
      let f' := fun x k z => k (f z x) in
      Foldable__Reverse_foldr f' GHC.Base.id xs z0.

Local Definition Foldable__Reverse_foldr' {inst_f} `{(Data.Foldable.Foldable
   inst_f)}
   : forall {a} {b}, (a -> b -> b) -> b -> (Reverse inst_f) a -> b :=
  fun {a} {b} =>
    fun f z0 xs =>
      let f' := fun k x z => k (f x z) in
      Foldable__Reverse_foldl f' GHC.Base.id xs z0.

Local Definition Foldable__Reverse_length {inst_f} `{(Data.Foldable.Foldable
   inst_f)}
   : forall {a}, (Reverse inst_f) a -> GHC.Num.Int :=
  fun {a} => fun '(Mk_Reverse t) => Data.Foldable.length t.

Local Definition Foldable__Reverse_null {inst_f} `{(Data.Foldable.Foldable
   inst_f)}
   : forall {a}, (Reverse inst_f) a -> bool :=
  fun {a} => fun '(Mk_Reverse t) => Data.Foldable.null t.

Local Definition Foldable__Reverse_product {inst_f} `{(Data.Foldable.Foldable
   inst_f)}
   : forall {a}, forall `{GHC.Num.Num a}, (Reverse inst_f) a -> a :=
  fun {a} `{GHC.Num.Num a} =>
    Coq.Program.Basics.compose Data.SemigroupInternal.getProduct
                               (Foldable__Reverse_foldMap Data.SemigroupInternal.Mk_Product).

Local Definition Foldable__Reverse_sum {inst_f} `{(Data.Foldable.Foldable
   inst_f)}
   : forall {a}, forall `{GHC.Num.Num a}, (Reverse inst_f) a -> a :=
  fun {a} `{GHC.Num.Num a} =>
    Coq.Program.Basics.compose Data.SemigroupInternal.getSum
                               (Foldable__Reverse_foldMap Data.SemigroupInternal.Mk_Sum).

Local Definition Foldable__Reverse_toList {inst_f} `{(Data.Foldable.Foldable
   inst_f)}
   : forall {a}, (Reverse inst_f) a -> list a :=
  fun {a} =>
    fun t => GHC.Base.build' (fun _ => (fun c n => Foldable__Reverse_foldr c n t)).

Program Instance Foldable__Reverse {f} `{(Data.Foldable.Foldable f)}
   : Data.Foldable.Foldable (Reverse f) :=
  fun _ k__ =>
    k__ {| Data.Foldable.fold__ := fun {m} `{GHC.Base.Monoid m} =>
             Foldable__Reverse_fold ;
           Data.Foldable.foldMap__ := fun {m} {a} `{GHC.Base.Monoid m} =>
             Foldable__Reverse_foldMap ;
           Data.Foldable.foldl__ := fun {b} {a} => Foldable__Reverse_foldl ;
           Data.Foldable.foldl'__ := fun {b} {a} => Foldable__Reverse_foldl' ;
           Data.Foldable.foldr__ := fun {a} {b} => Foldable__Reverse_foldr ;
           Data.Foldable.foldr'__ := fun {a} {b} => Foldable__Reverse_foldr' ;
           Data.Foldable.length__ := fun {a} => Foldable__Reverse_length ;
           Data.Foldable.null__ := fun {a} => Foldable__Reverse_null ;
           Data.Foldable.product__ := fun {a} `{GHC.Num.Num a} =>
             Foldable__Reverse_product ;
           Data.Foldable.sum__ := fun {a} `{GHC.Num.Num a} => Foldable__Reverse_sum ;
           Data.Foldable.toList__ := fun {a} => Foldable__Reverse_toList |}.

(* Skipping all instances of class `GHC.Base.MonadPlus', including
   `Data.Functor.Reverse.MonadPlus__Reverse' *)

Local Definition MonadFail__Reverse_fail {inst_m}
  `{(Control.Monad.Fail.MonadFail inst_m)}
   : forall {a}, GHC.Base.String -> (Reverse inst_m) a :=
  fun {a} => fun msg => Mk_Reverse (Control.Monad.Fail.fail msg).

Local Definition Monad__Reverse_op_zgzgze__ {inst_m} `{(GHC.Base.Monad inst_m)}
   : forall {a} {b},
     (Reverse inst_m) a -> (a -> (Reverse inst_m) b) -> (Reverse inst_m) b :=
  fun {a} {b} =>
    fun m f => Mk_Reverse (getReverse m GHC.Base.>>= (getReverse GHC.Base.∘ f)).

Local Definition Applicative__Reverse_op_zlztzg__ {inst_f}
  `{(GHC.Base.Applicative inst_f)}
   : forall {a} {b},
     (Reverse inst_f) (a -> b) -> (Reverse inst_f) a -> (Reverse inst_f) b :=
  fun {a} {b} =>
    fun arg_0__ arg_1__ =>
      match arg_0__, arg_1__ with
      | Mk_Reverse f, Mk_Reverse a => Mk_Reverse (f GHC.Base.<*> a)
      end.

Local Definition Functor__Reverse_fmap {inst_f} `{(GHC.Base.Functor inst_f)}
   : forall {a} {b}, (a -> b) -> (Reverse inst_f) a -> (Reverse inst_f) b :=
  fun {a} {b} =>
    fun arg_0__ arg_1__ =>
      match arg_0__, arg_1__ with
      | f, Mk_Reverse a => Mk_Reverse (GHC.Base.fmap f a)
      end.

Local Definition Functor__Reverse_op_zlzd__ {inst_f} `{(GHC.Base.Functor
   inst_f)}
   : forall {a} {b}, a -> (Reverse inst_f) b -> (Reverse inst_f) a :=
  fun {a} {b} => Functor__Reverse_fmap GHC.Base.∘ GHC.Base.const.

Program Instance Functor__Reverse {f} `{(GHC.Base.Functor f)}
   : GHC.Base.Functor (Reverse f) :=
  fun _ k__ =>
    k__ {| GHC.Base.fmap__ := fun {a} {b} => Functor__Reverse_fmap ;
           GHC.Base.op_zlzd____ := fun {a} {b} => Functor__Reverse_op_zlzd__ |}.

Local Definition Applicative__Reverse_liftA2 {inst_f} `{(GHC.Base.Applicative
   inst_f)}
   : forall {a} {b} {c},
     (a -> b -> c) ->
     (Reverse inst_f) a -> (Reverse inst_f) b -> (Reverse inst_f) c :=
  fun {a} {b} {c} =>
    fun f x => Applicative__Reverse_op_zlztzg__ (GHC.Base.fmap f x).

Local Definition Applicative__Reverse_op_ztzg__ {inst_f} `{(GHC.Base.Applicative
   inst_f)}
   : forall {a} {b},
     (Reverse inst_f) a -> (Reverse inst_f) b -> (Reverse inst_f) b :=
  fun {a} {b} =>
    fun a1 a2 => Applicative__Reverse_op_zlztzg__ (GHC.Base.id GHC.Base.<$ a1) a2.

Local Definition Applicative__Reverse_pure {inst_f} `{(GHC.Base.Applicative
   inst_f)}
   : forall {a}, a -> (Reverse inst_f) a :=
  fun {a} => fun a => Mk_Reverse (GHC.Base.pure a).

Program Instance Applicative__Reverse {f} `{(GHC.Base.Applicative f)}
   : GHC.Base.Applicative (Reverse f) :=
  fun _ k__ =>
    k__ {| GHC.Base.liftA2__ := fun {a} {b} {c} => Applicative__Reverse_liftA2 ;
           GHC.Base.op_zlztzg____ := fun {a} {b} => Applicative__Reverse_op_zlztzg__ ;
           GHC.Base.op_ztzg____ := fun {a} {b} => Applicative__Reverse_op_ztzg__ ;
           GHC.Base.pure__ := fun {a} => Applicative__Reverse_pure |}.

Local Definition Monad__Reverse_op_zgzg__ {inst_m} `{(GHC.Base.Monad inst_m)}
   : forall {a} {b},
     (Reverse inst_m) a -> (Reverse inst_m) b -> (Reverse inst_m) b :=
  fun {a} {b} => fun m k => Monad__Reverse_op_zgzgze__ m (fun arg_0__ => k).

Local Definition Monad__Reverse_return_ {inst_m} `{(GHC.Base.Monad inst_m)}
   : forall {a}, a -> (Reverse inst_m) a :=
  fun {a} => GHC.Base.pure.

Program Instance Monad__Reverse {m} `{(GHC.Base.Monad m)}
   : GHC.Base.Monad (Reverse m) :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zgzg____ := fun {a} {b} => Monad__Reverse_op_zgzg__ ;
           GHC.Base.op_zgzgze____ := fun {a} {b} => Monad__Reverse_op_zgzgze__ ;
           GHC.Base.return___ := fun {a} => Monad__Reverse_return_ |}.

Program Instance MonadFail__Reverse {m} `{(Control.Monad.Fail.MonadFail m)}
   : Control.Monad.Fail.MonadFail (Reverse m) :=
  fun _ k__ =>
    k__ {| Control.Monad.Fail.fail__ := fun {a} => MonadFail__Reverse_fail |}.

(* Skipping all instances of class `GHC.Base.Alternative', including
   `Data.Functor.Reverse.Alternative__Reverse' *)

(* Skipping all instances of class `GHC.Show.Show', including
   `Data.Functor.Reverse.Show__Reverse' *)

(* Skipping all instances of class `GHC.Read.Read', including
   `Data.Functor.Reverse.Read__Reverse' *)

Local Definition Ord1__Reverse_liftCompare {inst_f} `{(Data.Functor.Classes.Ord1
   inst_f)}
   : forall {a} {b},
     (a -> b -> comparison) ->
     (Reverse inst_f) a -> (Reverse inst_f) b -> comparison :=
  fun {a} {b} =>
    fun arg_0__ arg_1__ arg_2__ =>
      match arg_0__, arg_1__, arg_2__ with
      | comp, Mk_Reverse x, Mk_Reverse y => Data.Functor.Classes.liftCompare comp x y
      end.

Local Definition Eq1__Reverse_liftEq {inst_f} `{(Data.Functor.Classes.Eq1
   inst_f)}
   : forall {a} {b},
     (a -> b -> bool) -> (Reverse inst_f) a -> (Reverse inst_f) b -> bool :=
  fun {a} {b} =>
    fun arg_0__ arg_1__ arg_2__ =>
      match arg_0__, arg_1__, arg_2__ with
      | eq, Mk_Reverse x, Mk_Reverse y => Data.Functor.Classes.liftEq eq x y
      end.

Program Instance Eq1__Reverse {f} `{(Data.Functor.Classes.Eq1 f)}
   : Data.Functor.Classes.Eq1 (Reverse f) :=
  fun _ k__ =>
    k__ {| Data.Functor.Classes.liftEq__ := fun {a} {b} => Eq1__Reverse_liftEq |}.

Program Instance Ord1__Reverse {f} `{(Data.Functor.Classes.Ord1 f)}
   : Data.Functor.Classes.Ord1 (Reverse f) :=
  fun _ k__ =>
    k__ {| Data.Functor.Classes.liftCompare__ := fun {a} {b} =>
             Ord1__Reverse_liftCompare |}.

Local Definition Ord__Reverse_compare {inst_f} {inst_a}
  `{Data.Functor.Classes.Ord1 inst_f} `{GHC.Base.Ord inst_a}
   : (Reverse inst_f inst_a) -> (Reverse inst_f inst_a) -> comparison :=
  Data.Functor.Classes.compare1.

Local Definition Ord__Reverse_op_zl__ {inst_f} {inst_a}
  `{Data.Functor.Classes.Ord1 inst_f} `{GHC.Base.Ord inst_a}
   : (Reverse inst_f inst_a) -> (Reverse inst_f inst_a) -> bool :=
  fun x y => Ord__Reverse_compare x y GHC.Base.== Lt.

Local Definition Ord__Reverse_op_zlze__ {inst_f} {inst_a}
  `{Data.Functor.Classes.Ord1 inst_f} `{GHC.Base.Ord inst_a}
   : (Reverse inst_f inst_a) -> (Reverse inst_f inst_a) -> bool :=
  fun x y => Ord__Reverse_compare x y GHC.Base./= Gt.

Local Definition Ord__Reverse_op_zg__ {inst_f} {inst_a}
  `{Data.Functor.Classes.Ord1 inst_f} `{GHC.Base.Ord inst_a}
   : (Reverse inst_f inst_a) -> (Reverse inst_f inst_a) -> bool :=
  fun x y => Ord__Reverse_compare x y GHC.Base.== Gt.

Local Definition Ord__Reverse_op_zgze__ {inst_f} {inst_a}
  `{Data.Functor.Classes.Ord1 inst_f} `{GHC.Base.Ord inst_a}
   : (Reverse inst_f inst_a) -> (Reverse inst_f inst_a) -> bool :=
  fun x y => Ord__Reverse_compare x y GHC.Base./= Lt.

Local Definition Ord__Reverse_max {inst_f} {inst_a} `{Data.Functor.Classes.Ord1
  inst_f} `{GHC.Base.Ord inst_a}
   : (Reverse inst_f inst_a) ->
     (Reverse inst_f inst_a) -> (Reverse inst_f inst_a) :=
  fun x y => if Ord__Reverse_op_zlze__ x y : bool then y else x.

Local Definition Ord__Reverse_min {inst_f} {inst_a} `{Data.Functor.Classes.Ord1
  inst_f} `{GHC.Base.Ord inst_a}
   : (Reverse inst_f inst_a) ->
     (Reverse inst_f inst_a) -> (Reverse inst_f inst_a) :=
  fun x y => if Ord__Reverse_op_zlze__ x y : bool then x else y.

Local Definition Eq___Reverse_op_zeze__ {inst_f} {inst_a}
  `{Data.Functor.Classes.Eq1 inst_f} `{GHC.Base.Eq_ inst_a}
   : (Reverse inst_f inst_a) -> (Reverse inst_f inst_a) -> bool :=
  Data.Functor.Classes.eq1.

Local Definition Eq___Reverse_op_zsze__ {inst_f} {inst_a}
  `{Data.Functor.Classes.Eq1 inst_f} `{GHC.Base.Eq_ inst_a}
   : (Reverse inst_f inst_a) -> (Reverse inst_f inst_a) -> bool :=
  fun x y => negb (Eq___Reverse_op_zeze__ x y).

Program Instance Eq___Reverse {f} {a} `{Data.Functor.Classes.Eq1 f}
  `{GHC.Base.Eq_ a}
   : GHC.Base.Eq_ (Reverse f a) :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zeze____ := Eq___Reverse_op_zeze__ ;
           GHC.Base.op_zsze____ := Eq___Reverse_op_zsze__ |}.

Program Instance Ord__Reverse {f} {a} `{Data.Functor.Classes.Ord1 f}
  `{GHC.Base.Ord a}
   : GHC.Base.Ord (Reverse f a) :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zl____ := Ord__Reverse_op_zl__ ;
           GHC.Base.op_zlze____ := Ord__Reverse_op_zlze__ ;
           GHC.Base.op_zg____ := Ord__Reverse_op_zg__ ;
           GHC.Base.op_zgze____ := Ord__Reverse_op_zgze__ ;
           GHC.Base.compare__ := Ord__Reverse_compare ;
           GHC.Base.max__ := Ord__Reverse_max ;
           GHC.Base.min__ := Ord__Reverse_min |}.

(* Skipping all instances of class `Data.Functor.Classes.Show1', including
   `Data.Functor.Reverse.Show1__Reverse' *)

(* Skipping all instances of class `Data.Functor.Classes.Read1', including
   `Data.Functor.Reverse.Read1__Reverse' *)

(* External variables:
     Gt Lt Type bool comparison list negb Control.Monad.Fail.MonadFail
     Control.Monad.Fail.fail Control.Monad.Fail.fail__ Coq.Program.Basics.compose
     Data.Foldable.Foldable Data.Foldable.foldMap Data.Foldable.foldMap__
     Data.Foldable.fold__ Data.Foldable.foldl Data.Foldable.foldl'__
     Data.Foldable.foldl__ Data.Foldable.foldr Data.Foldable.foldr'__
     Data.Foldable.foldr__ Data.Foldable.length Data.Foldable.length__
     Data.Foldable.null Data.Foldable.null__ Data.Foldable.product__
     Data.Foldable.sum__ Data.Foldable.toList__ Data.Functor.Classes.Eq1
     Data.Functor.Classes.Ord1 Data.Functor.Classes.compare1 Data.Functor.Classes.eq1
     Data.Functor.Classes.liftCompare Data.Functor.Classes.liftCompare__
     Data.Functor.Classes.liftEq Data.Functor.Classes.liftEq__
     Data.SemigroupInternal.Mk_Dual Data.SemigroupInternal.Mk_Product
     Data.SemigroupInternal.Mk_Sum Data.SemigroupInternal.getDual
     Data.SemigroupInternal.getProduct Data.SemigroupInternal.getSum
     GHC.Base.Applicative GHC.Base.Eq_ GHC.Base.Functor GHC.Base.Monad
     GHC.Base.Monoid GHC.Base.Ord GHC.Base.String GHC.Base.build' GHC.Base.compare__
     GHC.Base.const GHC.Base.flip GHC.Base.fmap GHC.Base.fmap__ GHC.Base.id
     GHC.Base.liftA2__ GHC.Base.max__ GHC.Base.min__ GHC.Base.op_z2218U__
     GHC.Base.op_zeze__ GHC.Base.op_zeze____ GHC.Base.op_zg____ GHC.Base.op_zgze____
     GHC.Base.op_zgzg____ GHC.Base.op_zgzgze__ GHC.Base.op_zgzgze____
     GHC.Base.op_zl____ GHC.Base.op_zlzd__ GHC.Base.op_zlzd____ GHC.Base.op_zlze____
     GHC.Base.op_zlztzg__ GHC.Base.op_zlztzg____ GHC.Base.op_zsze__
     GHC.Base.op_zsze____ GHC.Base.op_ztzg____ GHC.Base.pure GHC.Base.pure__
     GHC.Base.return___ GHC.Num.Int GHC.Num.Num
*)
