(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Coq.Program.Tactics.
Require Coq.Program.Wf.

(* Preamble *)

(* Fix the type parameter of Const *)
Implicit Type b : Type.

(* A hack to make a few kind-polymorpic definitions go through *)
Class unit_class.
Instance unit_class_instance : unit_class := {}.
Implicit Type inst_k: unit_class.

(* Converted imports: *)

Require Coq.Program.Basics.
Require Data.Foldable.
Require Data.SemigroupInternal.
Require GHC.Base.
Require GHC.Num.
Require GHC.Prim.
Import GHC.Base.Notations.
Import GHC.Num.Notations.

(* Converted type declarations: *)

Inductive Const a b : Type := | Mk_Const (getConst : a) : Const a b.

Arguments Mk_Const {_} {_} _.

Definition getConst {a} {b} (arg_0__ : Const a b) :=
  let 'Mk_Const getConst := arg_0__ in
  getConst.

(* Converted value declarations: *)

(* Skipping all instances of class `Data.Bits.Bits', including
   `Data.Functor.Const.Bits__Const' *)

(* Skipping all instances of class `GHC.Enum.Bounded', including
   `Data.Functor.Const.Bounded__Const' *)

(* Skipping all instances of class `GHC.Enum.Enum', including
   `Data.Functor.Const.Enum__Const' *)

Instance Unpeel_Const a b : GHC.Prim.Unpeel (Const a b) a :=
  GHC.Prim.Build_Unpeel _ _ getConst Mk_Const.

Local Definition Eq___Const_op_zeze__ {inst_a} {inst_b} `{GHC.Base.Eq_ inst_a}
   : (Const inst_a inst_b : GHC.Prim.TYPE GHC.Types.LiftedRep) ->
     (Const inst_a inst_b : GHC.Prim.TYPE GHC.Types.LiftedRep) -> bool :=
  GHC.Prim.coerce _GHC.Base.==_.

Local Definition Eq___Const_op_zsze__ {inst_a} {inst_b} `{GHC.Base.Eq_ inst_a}
   : (Const inst_a inst_b : GHC.Prim.TYPE GHC.Types.LiftedRep) ->
     (Const inst_a inst_b : GHC.Prim.TYPE GHC.Types.LiftedRep) -> bool :=
  GHC.Prim.coerce _GHC.Base./=_.

Program Instance Eq___Const {a} {b} `{GHC.Base.Eq_ a}
   : GHC.Base.Eq_ (Const a b : GHC.Prim.TYPE GHC.Types.LiftedRep) :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zeze____ := Eq___Const_op_zeze__ ;
           GHC.Base.op_zsze____ := Eq___Const_op_zsze__ |}.

(* Skipping all instances of class `Data.Bits.FiniteBits', including
   `Data.Functor.Const.FiniteBits__Const' *)

(* Skipping all instances of class `GHC.Float.Floating', including
   `Data.Functor.Const.Floating__Const' *)

(* Skipping all instances of class `GHC.Real.Fractional', including
   `Data.Functor.Const.Fractional__Const' *)

(* Skipping all instances of class `GHC.Generics.Generic', including
   `Data.Functor.Const.Generic__Const' *)

(* Skipping all instances of class `GHC.Generics.Generic1', including
   `Data.Functor.Const.Generic1__Const__5' *)

(* Skipping all instances of class `GHC.Real.Integral', including
   `Data.Functor.Const.Integral__Const' *)

(* Skipping all instances of class `GHC.Arr.Ix', including
   `Data.Functor.Const.Ix__Const' *)

Local Definition Semigroup__Const_op_zlzlzgzg__ {inst_a} {inst_b}
  `{GHC.Base.Semigroup inst_a}
   : (Const inst_a inst_b : GHC.Prim.TYPE GHC.Types.LiftedRep) ->
     (Const inst_a inst_b : GHC.Prim.TYPE GHC.Types.LiftedRep) ->
     (Const inst_a inst_b : GHC.Prim.TYPE GHC.Types.LiftedRep) :=
  GHC.Prim.coerce _GHC.Base.<<>>_.

Program Instance Semigroup__Const {a} {b} `{GHC.Base.Semigroup a}
   : GHC.Base.Semigroup (Const a b : GHC.Prim.TYPE GHC.Types.LiftedRep) :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zlzlzgzg____ := Semigroup__Const_op_zlzlzgzg__ |}.

Local Definition Monoid__Const_mappend {inst_a} {inst_b} `{GHC.Base.Monoid
  inst_a}
   : (Const inst_a inst_b : GHC.Prim.TYPE GHC.Types.LiftedRep) ->
     (Const inst_a inst_b : GHC.Prim.TYPE GHC.Types.LiftedRep) ->
     (Const inst_a inst_b : GHC.Prim.TYPE GHC.Types.LiftedRep) :=
  GHC.Prim.coerce GHC.Base.mappend.

Local Definition Monoid__Const_mconcat {inst_a} {inst_b} `{GHC.Base.Monoid
  inst_a}
   : list (Const inst_a inst_b : GHC.Prim.TYPE GHC.Types.LiftedRep) ->
     (Const inst_a inst_b : GHC.Prim.TYPE GHC.Types.LiftedRep) :=
  GHC.Prim.coerce GHC.Base.mconcat.

Local Definition Monoid__Const_mempty {inst_a} {inst_b} `{GHC.Base.Monoid
  inst_a}
   : Const inst_a inst_b : GHC.Prim.TYPE GHC.Types.LiftedRep :=
  GHC.Prim.coerce GHC.Base.mempty.

Program Instance Monoid__Const {a} {b} `{GHC.Base.Monoid a}
   : GHC.Base.Monoid (Const a b : GHC.Prim.TYPE GHC.Types.LiftedRep) :=
  fun _ k__ =>
    k__ {| GHC.Base.mappend__ := Monoid__Const_mappend ;
           GHC.Base.mconcat__ := Monoid__Const_mconcat ;
           GHC.Base.mempty__ := Monoid__Const_mempty |}.

(* Skipping all instances of class `GHC.Num.Num', including
   `Data.Functor.Const.Num__Const' *)

Local Definition Ord__Const_op_zl__ {inst_a} {inst_b} `{GHC.Base.Ord inst_a}
   : (Const inst_a inst_b : GHC.Prim.TYPE GHC.Types.LiftedRep) ->
     (Const inst_a inst_b : GHC.Prim.TYPE GHC.Types.LiftedRep) -> bool :=
  GHC.Prim.coerce _GHC.Base.<_.

Local Definition Ord__Const_op_zlze__ {inst_a} {inst_b} `{GHC.Base.Ord inst_a}
   : (Const inst_a inst_b : GHC.Prim.TYPE GHC.Types.LiftedRep) ->
     (Const inst_a inst_b : GHC.Prim.TYPE GHC.Types.LiftedRep) -> bool :=
  GHC.Prim.coerce _GHC.Base.<=_.

Local Definition Ord__Const_op_zg__ {inst_a} {inst_b} `{GHC.Base.Ord inst_a}
   : (Const inst_a inst_b : GHC.Prim.TYPE GHC.Types.LiftedRep) ->
     (Const inst_a inst_b : GHC.Prim.TYPE GHC.Types.LiftedRep) -> bool :=
  GHC.Prim.coerce _GHC.Base.>_.

Local Definition Ord__Const_op_zgze__ {inst_a} {inst_b} `{GHC.Base.Ord inst_a}
   : (Const inst_a inst_b : GHC.Prim.TYPE GHC.Types.LiftedRep) ->
     (Const inst_a inst_b : GHC.Prim.TYPE GHC.Types.LiftedRep) -> bool :=
  GHC.Prim.coerce _GHC.Base.>=_.

Local Definition Ord__Const_compare {inst_a} {inst_b} `{GHC.Base.Ord inst_a}
   : (Const inst_a inst_b : GHC.Prim.TYPE GHC.Types.LiftedRep) ->
     (Const inst_a inst_b : GHC.Prim.TYPE GHC.Types.LiftedRep) -> comparison :=
  GHC.Prim.coerce GHC.Base.compare.

Local Definition Ord__Const_max {inst_a} {inst_b} `{GHC.Base.Ord inst_a}
   : (Const inst_a inst_b : GHC.Prim.TYPE GHC.Types.LiftedRep) ->
     (Const inst_a inst_b : GHC.Prim.TYPE GHC.Types.LiftedRep) ->
     (Const inst_a inst_b : GHC.Prim.TYPE GHC.Types.LiftedRep) :=
  GHC.Prim.coerce GHC.Base.max.

Local Definition Ord__Const_min {inst_a} {inst_b} `{GHC.Base.Ord inst_a}
   : (Const inst_a inst_b : GHC.Prim.TYPE GHC.Types.LiftedRep) ->
     (Const inst_a inst_b : GHC.Prim.TYPE GHC.Types.LiftedRep) ->
     (Const inst_a inst_b : GHC.Prim.TYPE GHC.Types.LiftedRep) :=
  GHC.Prim.coerce GHC.Base.min.

Program Instance Ord__Const {a} {b} `{GHC.Base.Ord a}
   : GHC.Base.Ord (Const a b : GHC.Prim.TYPE GHC.Types.LiftedRep) :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zl____ := Ord__Const_op_zl__ ;
           GHC.Base.op_zlze____ := Ord__Const_op_zlze__ ;
           GHC.Base.op_zg____ := Ord__Const_op_zg__ ;
           GHC.Base.op_zgze____ := Ord__Const_op_zgze__ ;
           GHC.Base.compare__ := Ord__Const_compare ;
           GHC.Base.max__ := Ord__Const_max ;
           GHC.Base.min__ := Ord__Const_min |}.

(* Skipping all instances of class `GHC.Real.Real', including
   `Data.Functor.Const.Real__Const' *)

(* Skipping all instances of class `GHC.Real.RealFrac', including
   `Data.Functor.Const.RealFrac__Const' *)

(* Skipping all instances of class `GHC.Float.RealFloat', including
   `Data.Functor.Const.RealFloat__Const' *)

(* Skipping all instances of class `Foreign.Storable.Storable', including
   `Data.Functor.Const.Storable__Const' *)

(* Skipping all instances of class `GHC.Read.Read', including
   `Data.Functor.Const.Read__Const' *)

(* Skipping all instances of class `GHC.Show.Show', including
   `Data.Functor.Const.Show__Const' *)

Local Definition Foldable__Const_foldMap {inst_m}
   : forall {m} {a},
     forall `{GHC.Base.Monoid m}, (a -> m) -> (Const inst_m) a -> m :=
  fun {m} {a} `{GHC.Base.Monoid m} => fun arg_0__ arg_1__ => GHC.Base.mempty.

Local Definition Foldable__Const_fold {inst_m}
   : forall {m}, forall `{GHC.Base.Monoid m}, (Const inst_m) m -> m :=
  fun {m} `{GHC.Base.Monoid m} => Foldable__Const_foldMap GHC.Base.id.

Local Definition Foldable__Const_foldl {inst_m}
   : forall {b} {a}, (b -> a -> b) -> b -> (Const inst_m) a -> b :=
  fun {b} {a} =>
    fun f z t =>
      Data.SemigroupInternal.appEndo (Data.SemigroupInternal.getDual
                                      (Foldable__Const_foldMap (Data.SemigroupInternal.Mk_Dual GHC.Base.∘
                                                                (Data.SemigroupInternal.Mk_Endo GHC.Base.∘
                                                                 GHC.Base.flip f)) t)) z.

Local Definition Foldable__Const_foldr {inst_m}
   : forall {a} {b}, (a -> b -> b) -> b -> (Const inst_m) a -> b :=
  fun {a} {b} =>
    fun f z t =>
      Data.SemigroupInternal.appEndo (Foldable__Const_foldMap
                                      (Coq.Program.Basics.compose Data.SemigroupInternal.Mk_Endo f) t) z.

Local Definition Foldable__Const_foldl' {inst_m}
   : forall {b} {a}, (b -> a -> b) -> b -> (Const inst_m) a -> b :=
  fun {b} {a} =>
    fun f z0 xs =>
      let f' := fun x k z => k (f z x) in Foldable__Const_foldr f' GHC.Base.id xs z0.

Local Definition Foldable__Const_foldr' {inst_m}
   : forall {a} {b}, (a -> b -> b) -> b -> (Const inst_m) a -> b :=
  fun {a} {b} =>
    fun f z0 xs =>
      let f' := fun k x z => k (f x z) in Foldable__Const_foldl f' GHC.Base.id xs z0.

Local Definition Foldable__Const_length {inst_m}
   : forall {a}, (Const inst_m) a -> GHC.Num.Int :=
  fun {a} =>
    Foldable__Const_foldl' (fun arg_0__ arg_1__ =>
                              match arg_0__, arg_1__ with
                              | c, _ => c GHC.Num.+ #1
                              end) #0.

Local Definition Foldable__Const_null {inst_m}
   : forall {a}, (Const inst_m) a -> bool :=
  fun {a} => Foldable__Const_foldr (fun arg_0__ arg_1__ => false) true.

Local Definition Foldable__Const_product {inst_m}
   : forall {a}, forall `{GHC.Num.Num a}, (Const inst_m) a -> a :=
  fun {a} `{GHC.Num.Num a} =>
    Coq.Program.Basics.compose Data.SemigroupInternal.getProduct
                               (Foldable__Const_foldMap Data.SemigroupInternal.Mk_Product).

Local Definition Foldable__Const_sum {inst_m}
   : forall {a}, forall `{GHC.Num.Num a}, (Const inst_m) a -> a :=
  fun {a} `{GHC.Num.Num a} =>
    Coq.Program.Basics.compose Data.SemigroupInternal.getSum
                               (Foldable__Const_foldMap Data.SemigroupInternal.Mk_Sum).

Local Definition Foldable__Const_toList {inst_m}
   : forall {a}, (Const inst_m) a -> list a :=
  fun {a} =>
    fun t => GHC.Base.build' (fun _ => (fun c n => Foldable__Const_foldr c n t)).

Program Instance Foldable__Const {m} : Data.Foldable.Foldable (Const m) :=
  fun _ k__ =>
    k__ {| Data.Foldable.fold__ := fun {m} `{GHC.Base.Monoid m} =>
             Foldable__Const_fold ;
           Data.Foldable.foldMap__ := fun {m} {a} `{GHC.Base.Monoid m} =>
             Foldable__Const_foldMap ;
           Data.Foldable.foldl__ := fun {b} {a} => Foldable__Const_foldl ;
           Data.Foldable.foldl'__ := fun {b} {a} => Foldable__Const_foldl' ;
           Data.Foldable.foldr__ := fun {a} {b} => Foldable__Const_foldr ;
           Data.Foldable.foldr'__ := fun {a} {b} => Foldable__Const_foldr' ;
           Data.Foldable.length__ := fun {a} => Foldable__Const_length ;
           Data.Foldable.null__ := fun {a} => Foldable__Const_null ;
           Data.Foldable.product__ := fun {a} `{GHC.Num.Num a} => Foldable__Const_product ;
           Data.Foldable.sum__ := fun {a} `{GHC.Num.Num a} => Foldable__Const_sum ;
           Data.Foldable.toList__ := fun {a} => Foldable__Const_toList |}.

Local Definition Functor__Const_fmap {inst_m}
   : forall {a} {b}, (a -> b) -> (Const inst_m) a -> (Const inst_m) b :=
  fun {a} {b} =>
    fun arg_0__ arg_1__ =>
      match arg_0__, arg_1__ with
      | _, Mk_Const v => Mk_Const v
      end.

Local Definition Functor__Const_op_zlzd__ {inst_m}
   : forall {a} {b}, a -> (Const inst_m) b -> (Const inst_m) a :=
  fun {a} {b} => Functor__Const_fmap GHC.Base.∘ GHC.Base.const.

Program Instance Functor__Const {m} : GHC.Base.Functor (Const m) :=
  fun _ k__ =>
    k__ {| GHC.Base.fmap__ := fun {a} {b} => Functor__Const_fmap ;
           GHC.Base.op_zlzd____ := fun {a} {b} => Functor__Const_op_zlzd__ |}.

Local Definition Applicative__Const_liftA2 {inst_m} `{GHC.Base.Monoid inst_m}
   : forall {a} {b} {c},
     (a -> b -> c) -> (Const inst_m) a -> (Const inst_m) b -> (Const inst_m) c :=
  fun {a} {b} {c} =>
    fun arg_0__ arg_1__ arg_2__ =>
      match arg_0__, arg_1__, arg_2__ with
      | _, Mk_Const x, Mk_Const y => Mk_Const (GHC.Base.mappend x y)
      end.

Local Definition Applicative__Const_op_zlztzg__ {inst_m} `{GHC.Base.Monoid
  inst_m}
   : forall {a} {b}, Const inst_m (a -> b) -> Const inst_m a -> Const inst_m b :=
  fun {a} {b} => GHC.Prim.coerce GHC.Base.mappend.

Local Definition Applicative__Const_op_ztzg__ {inst_m} `{GHC.Base.Monoid inst_m}
   : forall {a} {b}, (Const inst_m) a -> (Const inst_m) b -> (Const inst_m) b :=
  fun {a} {b} =>
    fun a1 a2 => Applicative__Const_op_zlztzg__ (GHC.Base.id GHC.Base.<$ a1) a2.

Local Definition Applicative__Const_pure {inst_m} `{GHC.Base.Monoid inst_m}
   : forall {a}, a -> (Const inst_m) a :=
  fun {a} => fun arg_0__ => Mk_Const GHC.Base.mempty.

Program Instance Applicative__Const {m} `{GHC.Base.Monoid m}
   : GHC.Base.Applicative (Const m) :=
  fun _ k__ =>
    k__ {| GHC.Base.liftA2__ := fun {a} {b} {c} => Applicative__Const_liftA2 ;
           GHC.Base.op_zlztzg____ := fun {a} {b} => Applicative__Const_op_zlztzg__ ;
           GHC.Base.op_ztzg____ := fun {a} {b} => Applicative__Const_op_ztzg__ ;
           GHC.Base.pure__ := fun {a} => Applicative__Const_pure |}.

(* External variables:
     bool comparison false list true Coq.Program.Basics.compose
     Data.Foldable.Foldable Data.Foldable.foldMap__ Data.Foldable.fold__
     Data.Foldable.foldl'__ Data.Foldable.foldl__ Data.Foldable.foldr'__
     Data.Foldable.foldr__ Data.Foldable.length__ Data.Foldable.null__
     Data.Foldable.product__ Data.Foldable.sum__ Data.Foldable.toList__
     Data.SemigroupInternal.Mk_Dual Data.SemigroupInternal.Mk_Endo
     Data.SemigroupInternal.Mk_Product Data.SemigroupInternal.Mk_Sum
     Data.SemigroupInternal.appEndo Data.SemigroupInternal.getDual
     Data.SemigroupInternal.getProduct Data.SemigroupInternal.getSum
     GHC.Base.Applicative GHC.Base.Eq_ GHC.Base.Functor GHC.Base.Monoid GHC.Base.Ord
     GHC.Base.Semigroup GHC.Base.build' GHC.Base.compare GHC.Base.compare__
     GHC.Base.const GHC.Base.flip GHC.Base.fmap__ GHC.Base.id GHC.Base.liftA2__
     GHC.Base.mappend GHC.Base.mappend__ GHC.Base.max GHC.Base.max__ GHC.Base.mconcat
     GHC.Base.mconcat__ GHC.Base.mempty GHC.Base.mempty__ GHC.Base.min GHC.Base.min__
     GHC.Base.op_z2218U__ GHC.Base.op_zeze__ GHC.Base.op_zeze____ GHC.Base.op_zg__
     GHC.Base.op_zg____ GHC.Base.op_zgze__ GHC.Base.op_zgze____ GHC.Base.op_zl__
     GHC.Base.op_zl____ GHC.Base.op_zlzd__ GHC.Base.op_zlzd____ GHC.Base.op_zlze__
     GHC.Base.op_zlze____ GHC.Base.op_zlzlzgzg__ GHC.Base.op_zlzlzgzg____
     GHC.Base.op_zlztzg____ GHC.Base.op_zsze__ GHC.Base.op_zsze____
     GHC.Base.op_ztzg____ GHC.Base.pure__ GHC.Num.Int GHC.Num.Num GHC.Num.fromInteger
     GHC.Num.op_zp__ GHC.Prim.Build_Unpeel GHC.Prim.TYPE GHC.Prim.Unpeel
     GHC.Prim.coerce GHC.Types.LiftedRep
*)
