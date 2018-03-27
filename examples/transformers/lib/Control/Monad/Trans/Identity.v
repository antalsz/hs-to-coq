(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Coq.Program.Tactics.
Require Coq.Program.Wf.

(* Converted imports: *)

Require Control.Monad.Signatures.
Require Control.Monad.Trans.Class.
Require Coq.Program.Basics.
Require Data.Foldable.
Require Data.Functor.
Require Import Data.Functor.Classes.
Require Import Data.Monoid.
Require Data.Traversable.
Require Import GHC.Base.
Require GHC.Num.
Import Data.Functor.Notations.

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

(* Translating `instance Read1__IdentityT' failed: OOPS! Cannot find information
   for class Qualified "Data.Functor.Classes" "Read1" unsupported *)

(* Translating `instance Show1__IdentityT' failed: OOPS! Cannot find information
   for class Qualified "Data.Functor.Classes" "Show1" unsupported *)

Local Definition Eq___IdentityT_op_zeze__ {inst_f} {inst_a} `{Eq1 inst_f} `{Eq_
  inst_a}
   : (IdentityT inst_f inst_a) -> (IdentityT inst_f inst_a) -> bool :=
  eq1.

Local Definition Eq___IdentityT_op_zsze__ {inst_f} {inst_a} `{Eq1 inst_f} `{Eq_
  inst_a}
   : (IdentityT inst_f inst_a) -> (IdentityT inst_f inst_a) -> bool :=
  fun x y => negb (Eq___IdentityT_op_zeze__ x y).

Program Instance Eq___IdentityT {f} {a} `{Eq1 f} `{Eq_ a}
   : Eq_ (IdentityT f a) :=
  fun _ k =>
    k {| op_zeze____ := Eq___IdentityT_op_zeze__ ;
         op_zsze____ := Eq___IdentityT_op_zsze__ |}.

Local Definition Ord__IdentityT_compare {inst_f} {inst_a} `{Ord1 inst_f} `{Ord
  inst_a}
   : (IdentityT inst_f inst_a) -> (IdentityT inst_f inst_a) -> comparison :=
  compare1.

Local Definition Ord__IdentityT_op_zg__ {inst_f} {inst_a} `{Ord1 inst_f} `{Ord
  inst_a}
   : (IdentityT inst_f inst_a) -> (IdentityT inst_f inst_a) -> bool :=
  fun x y => _==_ (Ord__IdentityT_compare x y) Gt.

Local Definition Ord__IdentityT_op_zgze__ {inst_f} {inst_a} `{Ord1 inst_f} `{Ord
  inst_a}
   : (IdentityT inst_f inst_a) -> (IdentityT inst_f inst_a) -> bool :=
  fun x y => _/=_ (Ord__IdentityT_compare x y) Lt.

Local Definition Ord__IdentityT_op_zl__ {inst_f} {inst_a} `{Ord1 inst_f} `{Ord
  inst_a}
   : (IdentityT inst_f inst_a) -> (IdentityT inst_f inst_a) -> bool :=
  fun x y => _==_ (Ord__IdentityT_compare x y) Lt.

Local Definition Ord__IdentityT_op_zlze__ {inst_f} {inst_a} `{Ord1 inst_f} `{Ord
  inst_a}
   : (IdentityT inst_f inst_a) -> (IdentityT inst_f inst_a) -> bool :=
  fun x y => _/=_ (Ord__IdentityT_compare x y) Gt.

Local Definition Ord__IdentityT_max {inst_f} {inst_a} `{Ord1 inst_f} `{Ord
  inst_a}
   : (IdentityT inst_f inst_a) ->
     (IdentityT inst_f inst_a) -> (IdentityT inst_f inst_a) :=
  fun x y => if Ord__IdentityT_op_zlze__ x y : bool then y else x.

Local Definition Ord__IdentityT_min {inst_f} {inst_a} `{Ord1 inst_f} `{Ord
  inst_a}
   : (IdentityT inst_f inst_a) ->
     (IdentityT inst_f inst_a) -> (IdentityT inst_f inst_a) :=
  fun x y => if Ord__IdentityT_op_zlze__ x y : bool then x else y.

Program Instance Ord__IdentityT {f} {a} `{Ord1 f} `{Ord a}
   : Ord (IdentityT f a) :=
  fun _ k =>
    k {| op_zl____ := Ord__IdentityT_op_zl__ ;
         op_zlze____ := Ord__IdentityT_op_zlze__ ;
         op_zg____ := Ord__IdentityT_op_zg__ ;
         op_zgze____ := Ord__IdentityT_op_zgze__ ;
         compare__ := Ord__IdentityT_compare ;
         max__ := Ord__IdentityT_max ;
         min__ := Ord__IdentityT_min |}.

(* Translating `instance Read__IdentityT' failed: OOPS! Cannot find information
   for class Qualified "GHC.Read" "Read" unsupported *)

(* Translating `instance Show__IdentityT' failed: OOPS! Cannot find information
   for class Qualified "GHC.Show" "Show" unsupported *)

Local Definition Foldable__IdentityT_foldMap {inst_f} `{(Data.Foldable.Foldable
   inst_f)}
   : forall {m} {a}, forall `{Monoid m}, (a -> m) -> (IdentityT inst_f) a -> m :=
  fun {m} {a} `{Monoid m} =>
    fun arg_0__ arg_1__ =>
      match arg_0__, arg_1__ with
      | f, Mk_IdentityT t => Data.Foldable.foldMap f t
      end.

Local Definition Foldable__IdentityT_product {inst_f} `{(Data.Foldable.Foldable
   inst_f)}
   : forall {a}, forall `{GHC.Num.Num a}, (IdentityT inst_f) a -> a :=
  fun {a} `{GHC.Num.Num a} =>
    Data.Foldable.hash_compose getProduct (Foldable__IdentityT_foldMap Mk_Product).

Local Definition Foldable__IdentityT_sum {inst_f} `{(Data.Foldable.Foldable
   inst_f)}
   : forall {a}, forall `{GHC.Num.Num a}, (IdentityT inst_f) a -> a :=
  fun {a} `{GHC.Num.Num a} =>
    Data.Foldable.hash_compose getSum (Foldable__IdentityT_foldMap Mk_Sum).

Local Definition Foldable__IdentityT_fold {inst_f} `{(Data.Foldable.Foldable
   inst_f)}
   : forall {m}, forall `{Monoid m}, (IdentityT inst_f) m -> m :=
  fun {m} `{Monoid m} => Foldable__IdentityT_foldMap id.

Local Definition Foldable__IdentityT_elem {inst_f} `{(Data.Foldable.Foldable
   inst_f)}
   : forall {a}, forall `{Eq_ a}, a -> (IdentityT inst_f) a -> bool :=
  fun {a} `{Eq_ a} =>
    Coq.Program.Basics.compose (fun arg_69__ =>
                                  let 'p := arg_69__ in
                                  Coq.Program.Basics.compose getAny (Foldable__IdentityT_foldMap
                                                              (Coq.Program.Basics.compose Mk_Any p))) _==_.

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
    fun arg_9__ arg_10__ arg_11__ =>
      match arg_9__, arg_10__, arg_11__ with
      | f, z0, xs =>
          let f' :=
            fun arg_12__ arg_13__ arg_14__ =>
              match arg_12__, arg_13__, arg_14__ with
              | k, x, z => _$!_ k (f x z)
              end in
          Foldable__IdentityT_foldl f' id xs z0
      end.

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
    fun arg_54__ =>
      let 't := arg_54__ in
      build (fun _ arg_55__ arg_56__ =>
               match arg_55__, arg_56__ with
               | c, n => Foldable__IdentityT_foldr c n t
               end).

Local Definition Foldable__IdentityT_foldl' {inst_f} `{(Data.Foldable.Foldable
   inst_f)}
   : forall {b} {a}, (b -> a -> b) -> b -> (IdentityT inst_f) a -> b :=
  fun {b} {a} =>
    fun arg_24__ arg_25__ arg_26__ =>
      match arg_24__, arg_25__, arg_26__ with
      | f, z0, xs =>
          let f' :=
            fun arg_27__ arg_28__ arg_29__ =>
              match arg_27__, arg_28__, arg_29__ with
              | x, k, z => _$!_ k (f z x)
              end in
          Foldable__IdentityT_foldr f' id xs z0
      end.

Local Definition Foldable__IdentityT_length {inst_f} `{(Data.Foldable.Foldable
   inst_f)}
   : forall {a}, (IdentityT inst_f) a -> GHC.Num.Int :=
  fun {a} =>
    fun arg_0__ => let 'Mk_IdentityT t := arg_0__ in Data.Foldable.length t.

Local Definition Foldable__IdentityT_null {inst_f} `{(Data.Foldable.Foldable
   inst_f)}
   : forall {a}, (IdentityT inst_f) a -> bool :=
  fun {a} =>
    fun arg_0__ => let 'Mk_IdentityT t := arg_0__ in Data.Foldable.null t.

Program Instance Foldable__IdentityT {f} `{(Data.Foldable.Foldable f)}
   : Data.Foldable.Foldable (IdentityT f) :=
  fun _ k =>
    k {| Data.Foldable.elem__ := fun {a} `{Eq_ a} => Foldable__IdentityT_elem ;
         Data.Foldable.fold__ := fun {m} `{Monoid m} => Foldable__IdentityT_fold ;
         Data.Foldable.foldMap__ := fun {m} {a} `{Monoid m} =>
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
     forall `{Applicative f},
     (a -> f b) -> (IdentityT inst_f) a -> f ((IdentityT inst_f) b) :=
  fun {f} {a} {b} `{Applicative f} =>
    fun arg_0__ arg_1__ =>
      match arg_0__, arg_1__ with
      | f, Mk_IdentityT a =>
          Mk_IdentityT Data.Functor.<$> Data.Traversable.traverse f a
      end.

Local Definition Traversable__IdentityT_sequenceA {inst_f}
  `{(Data.Traversable.Traversable inst_f)}
   : forall {f} {a},
     forall `{Applicative f}, (IdentityT inst_f) (f a) -> f ((IdentityT inst_f) a) :=
  fun {f} {a} `{Applicative f} => Traversable__IdentityT_traverse id.

Local Definition Traversable__IdentityT_sequence {inst_f}
  `{(Data.Traversable.Traversable inst_f)}
   : forall {m} {a},
     forall `{Monad m}, (IdentityT inst_f) (m a) -> m ((IdentityT inst_f) a) :=
  fun {m} {a} `{Monad m} => Traversable__IdentityT_sequenceA.

Local Definition Traversable__IdentityT_mapM {inst_f}
  `{(Data.Traversable.Traversable inst_f)}
   : forall {m} {a} {b},
     forall `{Monad m},
     (a -> m b) -> (IdentityT inst_f) a -> m ((IdentityT inst_f) b) :=
  fun {m} {a} {b} `{Monad m} => Traversable__IdentityT_traverse.

Local Definition Applicative__IdentityT_pure {inst_m} `{(Applicative inst_m)}
   : forall {a}, a -> (IdentityT inst_m) a :=
  fun {a} => fun x => Mk_IdentityT (pure x).

(* Translating `instance Alternative__IdentityT' failed: OOPS! Cannot find
   information for class Qualified "GHC.Base" "Alternative" unsupported *)

Local Definition Monad__IdentityT_op_zgzgze__ {inst_m} `{(Monad inst_m)}
   : forall {a} {b},
     (IdentityT inst_m) a -> (a -> (IdentityT inst_m) b) -> (IdentityT inst_m) b :=
  fun {a} {b} =>
    fun m k => Mk_IdentityT (_=<<_ (runIdentityT ∘ k) (runIdentityT m)).

(* Translating `instance MonadFail__IdentityT' failed: OOPS! Cannot find
   information for class Qualified "Control.Monad.Fail" "MonadFail" unsupported *)

(* Translating `instance MonadPlus__IdentityT' failed: OOPS! Cannot find
   information for class Qualified "GHC.Base" "MonadPlus" unsupported *)

(* Translating `instance MonadFix__IdentityT' failed: OOPS! Cannot find
   information for class Qualified "Control.Monad.Fix" "MonadFix" unsupported *)

(* Translating `instance MonadIO__IdentityT' failed: OOPS! Cannot find
   information for class Qualified "Control.Monad.IO.Class" "MonadIO"
   unsupported *)

(* Translating `instance MonadZip__IdentityT' failed: OOPS! Cannot find
   information for class Qualified "Control.Monad.Zip" "MonadZip" unsupported *)

Local Definition MonadTrans__IdentityT_lift
   : forall {m} {a} `{Monad m}, m a -> IdentityT m a :=
  fun {m} {a} `{Monad m} => Mk_IdentityT.

Program Instance MonadTrans__IdentityT
   : Control.Monad.Trans.Class.MonadTrans IdentityT :=
  fun _ k =>
    k {| Control.Monad.Trans.Class.lift__ := fun {m} {a} `{Monad m} =>
           MonadTrans__IdentityT_lift |}.

Definition lift2IdentityT {m} {a} {n} {b} {p} {c}
   : (m a -> n b -> p c) -> IdentityT m a -> IdentityT n b -> IdentityT p c :=
  fun f a b => Mk_IdentityT (f (runIdentityT a) (runIdentityT b)).

Local Definition Applicative__IdentityT_op_ztzg__ {inst_m} `{(Applicative
   inst_m)}
   : forall {a} {b},
     (IdentityT inst_m) a -> (IdentityT inst_m) b -> (IdentityT inst_m) b :=
  fun {a} {b} => lift2IdentityT _*>_.

Local Definition Applicative__IdentityT_op_zlztzg__ {inst_m} `{(Applicative
   inst_m)}
   : forall {a} {b},
     (IdentityT inst_m) (a -> b) -> (IdentityT inst_m) a -> (IdentityT inst_m) b :=
  fun {a} {b} => lift2IdentityT _<*>_.

Definition liftCallCC {m} {a} {b}
   : Control.Monad.Signatures.CallCC m a b ->
     Control.Monad.Signatures.CallCC (IdentityT m) a b :=
  fun callCC f =>
    Mk_IdentityT (callCC (fun c => runIdentityT (f (Mk_IdentityT ∘ c)))).

Definition mapIdentityT {m} {a} {n} {b}
   : (m a -> n b) -> IdentityT m a -> IdentityT n b :=
  fun f => Mk_IdentityT ∘ (f ∘ runIdentityT).

Local Definition Functor__IdentityT_fmap {inst_m} `{(Functor inst_m)}
   : forall {a} {b}, (a -> b) -> (IdentityT inst_m) a -> (IdentityT inst_m) b :=
  fun {a} {b} => fun f => mapIdentityT (fmap f).

Local Definition Functor__IdentityT_op_zlzd__ {inst_m} `{(Functor inst_m)}
   : forall {a} {b}, a -> (IdentityT inst_m) b -> (IdentityT inst_m) a :=
  fun {a} {b} => fun x => Functor__IdentityT_fmap (const x).

Program Instance Functor__IdentityT {m} `{(Functor m)}
   : Functor (IdentityT m) :=
  fun _ k =>
    k {| op_zlzd____ := fun {a} {b} => Functor__IdentityT_op_zlzd__ ;
         fmap__ := fun {a} {b} => Functor__IdentityT_fmap |}.

Program Instance Applicative__IdentityT {m} `{(Applicative m)}
   : Applicative (IdentityT m) :=
  fun _ k =>
    k {| op_ztzg____ := fun {a} {b} => Applicative__IdentityT_op_ztzg__ ;
         op_zlztzg____ := fun {a} {b} => Applicative__IdentityT_op_zlztzg__ ;
         pure__ := fun {a} => Applicative__IdentityT_pure |}.

Local Definition Monad__IdentityT_op_zgzg__ {inst_m} `{(Monad inst_m)}
   : forall {a} {b},
     (IdentityT inst_m) a -> (IdentityT inst_m) b -> (IdentityT inst_m) b :=
  fun {a} {b} => _*>_.

Local Definition Monad__IdentityT_return_ {inst_m} `{(Monad inst_m)}
   : forall {a}, a -> (IdentityT inst_m) a :=
  fun {a} => pure.

Program Instance Monad__IdentityT {m} `{(Monad m)} : Monad (IdentityT m) :=
  fun _ k =>
    k {| op_zgzg____ := fun {a} {b} => Monad__IdentityT_op_zgzg__ ;
         op_zgzgze____ := fun {a} {b} => Monad__IdentityT_op_zgzgze__ ;
         return___ := fun {a} => Monad__IdentityT_return_ |}.

Program Instance Traversable__IdentityT {f} `{(Data.Traversable.Traversable f)}
   : Data.Traversable.Traversable (IdentityT f) :=
  fun _ k =>
    k {| Data.Traversable.mapM__ := fun {m} {a} {b} `{Monad m} =>
           Traversable__IdentityT_mapM ;
         Data.Traversable.sequence__ := fun {m} {a} `{Monad m} =>
           Traversable__IdentityT_sequence ;
         Data.Traversable.sequenceA__ := fun {f} {a} `{Applicative f} =>
           Traversable__IdentityT_sequenceA ;
         Data.Traversable.traverse__ := fun {f} {a} {b} `{Applicative f} =>
           Traversable__IdentityT_traverse |}.

(* Unbound variables:
     Applicative Eq1 Eq_ Functor Gt Lt Mk_Any Mk_Product Mk_Sum Monad Monoid Ord Ord1
     Type bool build compare1 comparison const eq1 fmap getAny getProduct getSum id
     liftCompare liftEq list negb op_z2218U__ op_zdzn__ op_zeze__ op_zezlzl__
     op_zlztzg__ op_zsze__ op_ztzg__ pure Control.Monad.Signatures.CallCC
     Control.Monad.Trans.Class.MonadTrans Coq.Program.Basics.compose
     Data.Foldable.Foldable Data.Foldable.foldMap Data.Foldable.foldl
     Data.Foldable.foldr Data.Foldable.hash_compose Data.Foldable.length
     Data.Foldable.null Data.Functor.op_zlzdzg__ Data.Traversable.Traversable
     Data.Traversable.traverse GHC.Num.Int GHC.Num.Num
*)
