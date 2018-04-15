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
Require Control.Monad.Signatures.
Require Control.Monad.Trans.Class.
Require Coq.Program.Basics.
Require Data.Foldable.
Require Data.Functor.
Require Import Data.Functor.Classes.
Require Data.SemigroupInternal.
Require Data.Traversable.
Require GHC.Base.
Require GHC.Num.
Import Data.Functor.Notations.
Import GHC.Base.Notations.

(* Converted type declarations: *)

Inductive IdentityT (f : Type -> Type) a : Type
  := Mk_IdentityT : f a -> IdentityT f a.

Arguments Mk_IdentityT {_} {_} _.

Definition runIdentityT {f : Type -> Type} {a} (arg_0__ : IdentityT f a) :=
  let 'Mk_IdentityT runIdentityT := arg_0__ in
  runIdentityT.
(* Converted value declarations: *)

Local Definition Eq1__IdentityT_liftEq {inst_f} `{(Eq1 inst_f)}
   : forall {a} {b},
     (a -> b -> bool) -> (IdentityT inst_f) a -> (IdentityT inst_f) b -> bool :=
  fun {a} {b} =>
    fun arg_0__ arg_1__ arg_2__ =>
      match arg_0__, arg_1__, arg_2__ with
      | eq, Mk_IdentityT x, Mk_IdentityT y => liftEq eq x y
      end.

Program Instance Eq1__IdentityT {f} `{(Eq1 f)} : Eq1 (IdentityT f) :=
  fun _ k => k {| liftEq__ := fun {a} {b} => Eq1__IdentityT_liftEq |}.

Local Definition Ord1__IdentityT_liftCompare {inst_f} `{(Ord1 inst_f)}
   : forall {a} {b},
     (a -> b -> comparison) ->
     (IdentityT inst_f) a -> (IdentityT inst_f) b -> comparison :=
  fun {a} {b} =>
    fun arg_0__ arg_1__ arg_2__ =>
      match arg_0__, arg_1__, arg_2__ with
      | comp, Mk_IdentityT x, Mk_IdentityT y => liftCompare comp x y
      end.

Program Instance Ord1__IdentityT {f} `{(Ord1 f)} : Ord1 (IdentityT f) :=
  fun _ k => k {| liftCompare__ := fun {a} {b} => Ord1__IdentityT_liftCompare |}.

(* Skipping instance Read1__IdentityT of class Read1 *)

(* Skipping instance Show1__IdentityT of class Show1 *)

Local Definition Eq___IdentityT_op_zeze__ {inst_f} {inst_a} `{Eq1 inst_f}
  `{GHC.Base.Eq_ inst_a}
   : (IdentityT inst_f inst_a) -> (IdentityT inst_f inst_a) -> bool :=
  eq1.

Local Definition Eq___IdentityT_op_zsze__ {inst_f} {inst_a} `{Eq1 inst_f}
  `{GHC.Base.Eq_ inst_a}
   : (IdentityT inst_f inst_a) -> (IdentityT inst_f inst_a) -> bool :=
  fun x y => negb (Eq___IdentityT_op_zeze__ x y).

Program Instance Eq___IdentityT {f} {a} `{Eq1 f} `{GHC.Base.Eq_ a}
   : GHC.Base.Eq_ (IdentityT f a) :=
  fun _ k =>
    k {| GHC.Base.op_zeze____ := Eq___IdentityT_op_zeze__ ;
         GHC.Base.op_zsze____ := Eq___IdentityT_op_zsze__ |}.

Local Definition Ord__IdentityT_compare {inst_f} {inst_a} `{Ord1 inst_f}
  `{GHC.Base.Ord inst_a}
   : (IdentityT inst_f inst_a) -> (IdentityT inst_f inst_a) -> comparison :=
  compare1.

Local Definition Ord__IdentityT_op_zgze__ {inst_f} {inst_a} `{Ord1 inst_f}
  `{GHC.Base.Ord inst_a}
   : (IdentityT inst_f inst_a) -> (IdentityT inst_f inst_a) -> bool :=
  fun x y => Ord__IdentityT_compare x y GHC.Base./= Lt.

Local Definition Ord__IdentityT_op_zg__ {inst_f} {inst_a} `{Ord1 inst_f}
  `{GHC.Base.Ord inst_a}
   : (IdentityT inst_f inst_a) -> (IdentityT inst_f inst_a) -> bool :=
  fun x y => Ord__IdentityT_compare x y GHC.Base.== Gt.

Local Definition Ord__IdentityT_op_zlze__ {inst_f} {inst_a} `{Ord1 inst_f}
  `{GHC.Base.Ord inst_a}
   : (IdentityT inst_f inst_a) -> (IdentityT inst_f inst_a) -> bool :=
  fun x y => Ord__IdentityT_compare x y GHC.Base./= Gt.

Local Definition Ord__IdentityT_max {inst_f} {inst_a} `{Ord1 inst_f}
  `{GHC.Base.Ord inst_a}
   : (IdentityT inst_f inst_a) ->
     (IdentityT inst_f inst_a) -> (IdentityT inst_f inst_a) :=
  fun x y => if Ord__IdentityT_op_zlze__ x y : bool then y else x.

Local Definition Ord__IdentityT_min {inst_f} {inst_a} `{Ord1 inst_f}
  `{GHC.Base.Ord inst_a}
   : (IdentityT inst_f inst_a) ->
     (IdentityT inst_f inst_a) -> (IdentityT inst_f inst_a) :=
  fun x y => if Ord__IdentityT_op_zlze__ x y : bool then x else y.

Local Definition Ord__IdentityT_op_zl__ {inst_f} {inst_a} `{Ord1 inst_f}
  `{GHC.Base.Ord inst_a}
   : (IdentityT inst_f inst_a) -> (IdentityT inst_f inst_a) -> bool :=
  fun x y => Ord__IdentityT_compare x y GHC.Base.== Lt.

Program Instance Ord__IdentityT {f} {a} `{Ord1 f} `{GHC.Base.Ord a}
   : GHC.Base.Ord (IdentityT f a) :=
  fun _ k =>
    k {| GHC.Base.op_zl____ := Ord__IdentityT_op_zl__ ;
         GHC.Base.op_zlze____ := Ord__IdentityT_op_zlze__ ;
         GHC.Base.op_zg____ := Ord__IdentityT_op_zg__ ;
         GHC.Base.op_zgze____ := Ord__IdentityT_op_zgze__ ;
         GHC.Base.compare__ := Ord__IdentityT_compare ;
         GHC.Base.max__ := Ord__IdentityT_max ;
         GHC.Base.min__ := Ord__IdentityT_min |}.

(* Skipping instance Read__IdentityT of class Read *)

(* Skipping instance Show__IdentityT of class Show *)

Local Definition Foldable__IdentityT_null {inst_f} `{(Data.Foldable.Foldable
   inst_f)}
   : forall {a}, (IdentityT inst_f) a -> bool :=
  fun {a} => fun '(Mk_IdentityT t) => Data.Foldable.null t.

Local Definition Foldable__IdentityT_length {inst_f} `{(Data.Foldable.Foldable
   inst_f)}
   : forall {a}, (IdentityT inst_f) a -> GHC.Num.Int :=
  fun {a} => fun '(Mk_IdentityT t) => Data.Foldable.length t.

Local Definition Foldable__IdentityT_foldr {inst_f} `{(Data.Foldable.Foldable
   inst_f)}
   : forall {a} {b}, (a -> b -> b) -> b -> (IdentityT inst_f) a -> b :=
  fun {a} {b} =>
    fun arg_0__ arg_1__ arg_2__ =>
      match arg_0__, arg_1__, arg_2__ with
      | f, z, Mk_IdentityT t => Data.Foldable.foldr f z t
      end.

Local Definition Foldable__IdentityT_toList {inst_f} `{(Data.Foldable.Foldable
   inst_f)}
   : forall {a}, (IdentityT inst_f) a -> list a :=
  fun {a} =>
    fun t =>
      GHC.Base.build' (fun _ => (fun c n => Foldable__IdentityT_foldr c n t)).

Local Definition Foldable__IdentityT_foldl' {inst_f} `{(Data.Foldable.Foldable
   inst_f)}
   : forall {b} {a}, (b -> a -> b) -> b -> (IdentityT inst_f) a -> b :=
  fun {b} {a} =>
    fun f z0 xs =>
      let f' := fun x k z => k (f z x) in
      Foldable__IdentityT_foldr f' GHC.Base.id xs z0.

Local Definition Foldable__IdentityT_foldl {inst_f} `{(Data.Foldable.Foldable
   inst_f)}
   : forall {b} {a}, (b -> a -> b) -> b -> (IdentityT inst_f) a -> b :=
  fun {b} {a} =>
    fun arg_0__ arg_1__ arg_2__ =>
      match arg_0__, arg_1__, arg_2__ with
      | f, z, Mk_IdentityT t => Data.Foldable.foldl f z t
      end.

Local Definition Foldable__IdentityT_foldr' {inst_f} `{(Data.Foldable.Foldable
   inst_f)}
   : forall {a} {b}, (a -> b -> b) -> b -> (IdentityT inst_f) a -> b :=
  fun {a} {b} =>
    fun f z0 xs =>
      let f' := fun k x z => k (f x z) in
      Foldable__IdentityT_foldl f' GHC.Base.id xs z0.

Local Definition Foldable__IdentityT_foldMap {inst_f} `{(Data.Foldable.Foldable
   inst_f)}
   : forall {m} {a},
     forall `{GHC.Base.Monoid m}, (a -> m) -> (IdentityT inst_f) a -> m :=
  fun {m} {a} `{GHC.Base.Monoid m} =>
    fun arg_0__ arg_1__ =>
      match arg_0__, arg_1__ with
      | f, Mk_IdentityT t => Data.Foldable.foldMap f t
      end.

Local Definition Foldable__IdentityT_product {inst_f} `{(Data.Foldable.Foldable
   inst_f)}
   : forall {a}, forall `{GHC.Num.Num a}, (IdentityT inst_f) a -> a :=
  fun {a} `{GHC.Num.Num a} =>
    Coq.Program.Basics.compose Data.SemigroupInternal.getProduct
                               (Foldable__IdentityT_foldMap Data.SemigroupInternal.Mk_Product).

Local Definition Foldable__IdentityT_sum {inst_f} `{(Data.Foldable.Foldable
   inst_f)}
   : forall {a}, forall `{GHC.Num.Num a}, (IdentityT inst_f) a -> a :=
  fun {a} `{GHC.Num.Num a} =>
    Coq.Program.Basics.compose Data.SemigroupInternal.getSum
                               (Foldable__IdentityT_foldMap Data.SemigroupInternal.Mk_Sum).

Local Definition Foldable__IdentityT_fold {inst_f} `{(Data.Foldable.Foldable
   inst_f)}
   : forall {m}, forall `{GHC.Base.Monoid m}, (IdentityT inst_f) m -> m :=
  fun {m} `{GHC.Base.Monoid m} => Foldable__IdentityT_foldMap GHC.Base.id.

Program Instance Foldable__IdentityT {f} `{(Data.Foldable.Foldable f)}
   : Data.Foldable.Foldable (IdentityT f) :=
  fun _ k =>
    k {| Data.Foldable.fold__ := fun {m} `{GHC.Base.Monoid m} =>
           Foldable__IdentityT_fold ;
         Data.Foldable.foldMap__ := fun {m} {a} `{GHC.Base.Monoid m} =>
           Foldable__IdentityT_foldMap ;
         Data.Foldable.foldl__ := fun {b} {a} => Foldable__IdentityT_foldl ;
         Data.Foldable.foldl'__ := fun {b} {a} => Foldable__IdentityT_foldl' ;
         Data.Foldable.foldr__ := fun {a} {b} => Foldable__IdentityT_foldr ;
         Data.Foldable.foldr'__ := fun {a} {b} => Foldable__IdentityT_foldr' ;
         Data.Foldable.length__ := fun {a} => Foldable__IdentityT_length ;
         Data.Foldable.null__ := fun {a} => Foldable__IdentityT_null ;
         Data.Foldable.product__ := fun {a} `{GHC.Num.Num a} =>
           Foldable__IdentityT_product ;
         Data.Foldable.sum__ := fun {a} `{GHC.Num.Num a} => Foldable__IdentityT_sum ;
         Data.Foldable.toList__ := fun {a} => Foldable__IdentityT_toList |}.

Local Definition Traversable__IdentityT_traverse {inst_f}
  `{(Data.Traversable.Traversable inst_f)}
   : forall {f} {a} {b},
     forall `{GHC.Base.Applicative f},
     (a -> f b) -> (IdentityT inst_f) a -> f ((IdentityT inst_f) b) :=
  fun {f} {a} {b} `{GHC.Base.Applicative f} =>
    fun arg_0__ arg_1__ =>
      match arg_0__, arg_1__ with
      | f, Mk_IdentityT a =>
          Mk_IdentityT Data.Functor.<$> Data.Traversable.traverse f a
      end.

Local Definition Traversable__IdentityT_sequenceA {inst_f}
  `{(Data.Traversable.Traversable inst_f)}
   : forall {f} {a},
     forall `{GHC.Base.Applicative f},
     (IdentityT inst_f) (f a) -> f ((IdentityT inst_f) a) :=
  fun {f} {a} `{GHC.Base.Applicative f} =>
    Traversable__IdentityT_traverse GHC.Base.id.

Local Definition Traversable__IdentityT_sequence {inst_f}
  `{(Data.Traversable.Traversable inst_f)}
   : forall {m} {a},
     forall `{GHC.Base.Monad m},
     (IdentityT inst_f) (m a) -> m ((IdentityT inst_f) a) :=
  fun {m} {a} `{GHC.Base.Monad m} => Traversable__IdentityT_sequenceA.

Local Definition Traversable__IdentityT_mapM {inst_f}
  `{(Data.Traversable.Traversable inst_f)}
   : forall {m} {a} {b},
     forall `{GHC.Base.Monad m},
     (a -> m b) -> (IdentityT inst_f) a -> m ((IdentityT inst_f) b) :=
  fun {m} {a} {b} `{GHC.Base.Monad m} => Traversable__IdentityT_traverse.

Local Definition Applicative__IdentityT_pure {inst_m} `{(GHC.Base.Applicative
   inst_m)}
   : forall {a}, a -> (IdentityT inst_m) a :=
  fun {a} => fun x => Mk_IdentityT (GHC.Base.pure x).

(* Skipping instance Alternative__IdentityT of class Alternative *)

Local Definition Monad__IdentityT_op_zgzgze__ {inst_m} `{(GHC.Base.Monad
   inst_m)}
   : forall {a} {b},
     (IdentityT inst_m) a -> (a -> (IdentityT inst_m) b) -> (IdentityT inst_m) b :=
  fun {a} {b} =>
    fun m k =>
      Mk_IdentityT ((runIdentityT GHC.Base.∘ k) GHC.Base.=<< runIdentityT m).

Local Definition MonadFail__IdentityT_fail {inst_m}
  `{(Control.Monad.Fail.MonadFail inst_m)}
   : forall {a}, GHC.Base.String -> (IdentityT inst_m) a :=
  fun {a} => fun msg => Mk_IdentityT (Control.Monad.Fail.fail msg).

(* Skipping instance MonadPlus__IdentityT of class MonadPlus *)

(* Skipping instance MonadFix__IdentityT of class MonadFix *)

(* Skipping instance MonadIO__IdentityT of class MonadIO *)

(* Skipping instance MonadZip__IdentityT of class MonadZip *)

Local Definition MonadTrans__IdentityT_lift
   : forall {m} {a}, forall `{(GHC.Base.Monad m)}, m a -> IdentityT m a :=
  fun {m} {a} `{(GHC.Base.Monad m)} => Mk_IdentityT.

Program Instance MonadTrans__IdentityT
   : Control.Monad.Trans.Class.MonadTrans IdentityT :=
  fun _ k =>
    k {| Control.Monad.Trans.Class.lift__ := fun {m} {a} `{(GHC.Base.Monad m)} =>
           MonadTrans__IdentityT_lift |}.

Definition lift2IdentityT {m} {a} {n} {b} {p} {c}
   : (m a -> n b -> p c) -> IdentityT m a -> IdentityT n b -> IdentityT p c :=
  fun f a b => Mk_IdentityT (f (runIdentityT a) (runIdentityT b)).

Local Definition Applicative__IdentityT_op_zlztzg__ {inst_m}
  `{(GHC.Base.Applicative inst_m)}
   : forall {a} {b},
     (IdentityT inst_m) (a -> b) -> (IdentityT inst_m) a -> (IdentityT inst_m) b :=
  fun {a} {b} => lift2IdentityT _GHC.Base.<*>_.

Definition liftCallCC {m} {a} {b}
   : Control.Monad.Signatures.CallCC m a b ->
     Control.Monad.Signatures.CallCC (IdentityT m) a b :=
  fun callCC f =>
    Mk_IdentityT (callCC (fun c => runIdentityT (f (Mk_IdentityT GHC.Base.∘ c)))).

Definition mapIdentityT {m} {a} {n} {b}
   : (m a -> n b) -> IdentityT m a -> IdentityT n b :=
  fun f => Mk_IdentityT GHC.Base.∘ (f GHC.Base.∘ runIdentityT).

Local Definition Functor__IdentityT_fmap {inst_m} `{(GHC.Base.Functor inst_m)}
   : forall {a} {b}, (a -> b) -> (IdentityT inst_m) a -> (IdentityT inst_m) b :=
  fun {a} {b} => fun f => mapIdentityT (GHC.Base.fmap f).

Local Definition Functor__IdentityT_op_zlzd__ {inst_m} `{(GHC.Base.Functor
   inst_m)}
   : forall {a} {b}, a -> (IdentityT inst_m) b -> (IdentityT inst_m) a :=
  fun {a} {b} => Functor__IdentityT_fmap GHC.Base.∘ GHC.Base.const.

Program Instance Functor__IdentityT {m} `{(GHC.Base.Functor m)}
   : GHC.Base.Functor (IdentityT m) :=
  fun _ k =>
    k {| GHC.Base.fmap__ := fun {a} {b} => Functor__IdentityT_fmap ;
         GHC.Base.op_zlzd____ := fun {a} {b} => Functor__IdentityT_op_zlzd__ |}.

Local Definition Applicative__IdentityT_liftA2 {inst_m} `{(GHC.Base.Applicative
   inst_m)}
   : forall {a} {b} {c},
     (a -> b -> c) ->
     (IdentityT inst_m) a -> (IdentityT inst_m) b -> (IdentityT inst_m) c :=
  fun {a} {b} {c} =>
    fun f x => Applicative__IdentityT_op_zlztzg__ (GHC.Base.fmap f x).

Local Definition Applicative__IdentityT_op_ztzg__ {inst_m}
  `{(GHC.Base.Applicative inst_m)}
   : forall {a} {b},
     (IdentityT inst_m) a -> (IdentityT inst_m) b -> (IdentityT inst_m) b :=
  fun {a} {b} => lift2IdentityT _GHC.Base.*>_.

Program Instance Applicative__IdentityT {m} `{(GHC.Base.Applicative m)}
   : GHC.Base.Applicative (IdentityT m) :=
  fun _ k =>
    k {| GHC.Base.liftA2__ := fun {a} {b} {c} => Applicative__IdentityT_liftA2 ;
         GHC.Base.op_zlztzg____ := fun {a} {b} => Applicative__IdentityT_op_zlztzg__ ;
         GHC.Base.op_ztzg____ := fun {a} {b} => Applicative__IdentityT_op_ztzg__ ;
         GHC.Base.pure__ := fun {a} => Applicative__IdentityT_pure |}.

Local Definition Monad__IdentityT_op_zgzg__ {inst_m} `{(GHC.Base.Monad inst_m)}
   : forall {a} {b},
     (IdentityT inst_m) a -> (IdentityT inst_m) b -> (IdentityT inst_m) b :=
  fun {a} {b} => fun m k => Monad__IdentityT_op_zgzgze__ m (fun arg_0__ => k).

Local Definition Monad__IdentityT_return_ {inst_m} `{(GHC.Base.Monad inst_m)}
   : forall {a}, a -> (IdentityT inst_m) a :=
  fun {a} => GHC.Base.pure.

Program Instance Monad__IdentityT {m} `{(GHC.Base.Monad m)}
   : GHC.Base.Monad (IdentityT m) :=
  fun _ k =>
    k {| GHC.Base.op_zgzg____ := fun {a} {b} => Monad__IdentityT_op_zgzg__ ;
         GHC.Base.op_zgzgze____ := fun {a} {b} => Monad__IdentityT_op_zgzgze__ ;
         GHC.Base.return___ := fun {a} => Monad__IdentityT_return_ |}.

Program Instance MonadFail__IdentityT {m} `{(Control.Monad.Fail.MonadFail m)}
   : Control.Monad.Fail.MonadFail (IdentityT m) :=
  fun _ k =>
    k {| Control.Monad.Fail.fail__ := fun {a} => MonadFail__IdentityT_fail |}.

Program Instance Traversable__IdentityT {f} `{(Data.Traversable.Traversable f)}
   : Data.Traversable.Traversable (IdentityT f) :=
  fun _ k =>
    k {| Data.Traversable.mapM__ := fun {m} {a} {b} `{GHC.Base.Monad m} =>
           Traversable__IdentityT_mapM ;
         Data.Traversable.sequence__ := fun {m} {a} `{GHC.Base.Monad m} =>
           Traversable__IdentityT_sequence ;
         Data.Traversable.sequenceA__ := fun {f} {a} `{GHC.Base.Applicative f} =>
           Traversable__IdentityT_sequenceA ;
         Data.Traversable.traverse__ := fun {f} {a} {b} `{GHC.Base.Applicative f} =>
           Traversable__IdentityT_traverse |}.

(* External variables:
     Eq1 Gt Lt Ord1 Type bool compare1 comparison eq1 liftCompare liftCompare__
     liftEq liftEq__ list negb Control.Monad.Fail.MonadFail Control.Monad.Fail.fail
     Control.Monad.Fail.fail__ Control.Monad.Signatures.CallCC
     Control.Monad.Trans.Class.MonadTrans Control.Monad.Trans.Class.lift__
     Coq.Program.Basics.compose Data.Foldable.Foldable Data.Foldable.foldMap
     Data.Foldable.foldMap__ Data.Foldable.fold__ Data.Foldable.foldl
     Data.Foldable.foldl'__ Data.Foldable.foldl__ Data.Foldable.foldr
     Data.Foldable.foldr'__ Data.Foldable.foldr__ Data.Foldable.length
     Data.Foldable.length__ Data.Foldable.null Data.Foldable.null__
     Data.Foldable.product__ Data.Foldable.sum__ Data.Foldable.toList__
     Data.Functor.op_zlzdzg__ Data.SemigroupInternal.Mk_Product
     Data.SemigroupInternal.Mk_Sum Data.SemigroupInternal.getProduct
     Data.SemigroupInternal.getSum Data.Traversable.Traversable
     Data.Traversable.mapM__ Data.Traversable.sequenceA__ Data.Traversable.sequence__
     Data.Traversable.traverse Data.Traversable.traverse__ GHC.Base.Applicative
     GHC.Base.Eq_ GHC.Base.Functor GHC.Base.Monad GHC.Base.Monoid GHC.Base.Ord
     GHC.Base.String GHC.Base.build' GHC.Base.compare__ GHC.Base.const GHC.Base.fmap
     GHC.Base.fmap__ GHC.Base.id GHC.Base.liftA2__ GHC.Base.max__ GHC.Base.min__
     GHC.Base.op_z2218U__ GHC.Base.op_zeze__ GHC.Base.op_zeze____
     GHC.Base.op_zezlzl__ GHC.Base.op_zg____ GHC.Base.op_zgze____
     GHC.Base.op_zgzg____ GHC.Base.op_zgzgze____ GHC.Base.op_zl____
     GHC.Base.op_zlzd____ GHC.Base.op_zlze____ GHC.Base.op_zlztzg__
     GHC.Base.op_zlztzg____ GHC.Base.op_zsze__ GHC.Base.op_zsze____
     GHC.Base.op_ztzg__ GHC.Base.op_ztzg____ GHC.Base.pure GHC.Base.pure__
     GHC.Base.return___ GHC.Num.Int GHC.Num.Num
*)
