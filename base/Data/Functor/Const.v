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
Local Class unit_class.
Local Instance unit_class_instance : unit_class.
Implicit Type inst_k: unit_class.

(* Converted imports: *)

Require Coq.Program.Basics.
Require Data.Foldable.
Require Data.Semigroup.Internal.
Require GHC.Base.
Require GHC.Num.
Require GHC.Prim.
Import GHC.Base.Notations.
Import GHC.Num.Notations.

(* Converted type declarations: *)

Inductive Const a b : Type := Mk_Const : a -> Const a b.

Arguments Mk_Const {_} {_} _.

Definition getConst {a} {b} (arg_0__ : Const a b) :=
  let 'Mk_Const getConst := arg_0__ in
  getConst.
(* Converted value declarations: *)

Instance Unpeel_Const a b : GHC.Prim.Unpeel (Const a b) a :=
  GHC.Prim.Build_Unpeel _ _ getConst Mk_Const.

(* Translating `instance Read__Const' failed: OOPS! Cannot find information for
   class Qualified "GHC.Read" "Read" unsupported *)

(* Translating `instance Show__Const' failed: OOPS! Cannot find information for
   class Qualified "GHC.Show" "Show" unsupported *)

Local Definition Foldable__Const_foldMap {inst_m}
   : forall {m} {a},
     forall `{GHC.Base.Monoid m}, (a -> m) -> (Const inst_m) a -> m :=
  fun {m} {a} `{GHC.Base.Monoid m} => fun arg_0__ arg_1__ => GHC.Base.mempty.

Local Definition Foldable__Const_foldl {inst_m}
   : forall {b} {a}, (b -> a -> b) -> b -> (Const inst_m) a -> b :=
  fun {b} {a} =>
    fun arg_19__ arg_20__ arg_21__ =>
      match arg_19__, arg_20__, arg_21__ with
      | f, z, t =>
          Data.Semigroup.Internal.appEndo (Data.Semigroup.Internal.getDual
                                           (Foldable__Const_foldMap (Coq.Program.Basics.compose
                                                                     Data.Semigroup.Internal.Mk_Dual
                                                                     (Coq.Program.Basics.compose
                                                                      Data.Semigroup.Internal.Mk_Endo (GHC.Base.flip
                                                                       f))) t)) z
      end.

Local Definition Foldable__Const_foldr' {inst_m}
   : forall {a} {b}, (a -> b -> b) -> b -> (Const inst_m) a -> b :=
  fun {a} {b} =>
    fun arg_9__ arg_10__ arg_11__ =>
      match arg_9__, arg_10__, arg_11__ with
      | f, z0, xs =>
          let f' :=
            fun arg_12__ arg_13__ arg_14__ =>
              match arg_12__, arg_13__, arg_14__ with
              | k, x, z => k GHC.Base.$! f x z
              end in
          Foldable__Const_foldl f' GHC.Base.id xs z0
      end.

Local Definition Foldable__Const_foldr {inst_m}
   : forall {a} {b}, (a -> b -> b) -> b -> (Const inst_m) a -> b :=
  fun {a} {b} =>
    fun arg_4__ arg_5__ arg_6__ =>
      match arg_4__, arg_5__, arg_6__ with
      | f, z, t =>
          Data.Semigroup.Internal.appEndo (Foldable__Const_foldMap
                                           (Coq.Program.Basics.compose Data.Semigroup.Internal.Mk_Endo f) t) z
      end.

Local Definition Foldable__Const_foldl' {inst_m}
   : forall {b} {a}, (b -> a -> b) -> b -> (Const inst_m) a -> b :=
  fun {b} {a} =>
    fun arg_24__ arg_25__ arg_26__ =>
      match arg_24__, arg_25__, arg_26__ with
      | f, z0, xs =>
          let f' :=
            fun arg_27__ arg_28__ arg_29__ =>
              match arg_27__, arg_28__, arg_29__ with
              | x, k, z => k GHC.Base.$! f z x
              end in
          Foldable__Const_foldr f' GHC.Base.id xs z0
      end.

Local Definition Foldable__Const_length {inst_m}
   : forall {a}, (Const inst_m) a -> GHC.Num.Int :=
  fun {a} =>
    Foldable__Const_foldl' (fun arg_64__ arg_65__ =>
                              match arg_64__, arg_65__ with
                              | c, _ => c GHC.Num.+ #1
                              end) #0.

Local Definition Foldable__Const_null {inst_m}
   : forall {a}, (Const inst_m) a -> bool :=
  fun {a} => Foldable__Const_foldr (fun arg_61__ arg_62__ => false) true.

Local Definition Foldable__Const_toList {inst_m}
   : forall {a}, (Const inst_m) a -> list a :=
  fun {a} =>
    fun arg_54__ =>
      let 't := arg_54__ in
      GHC.Base.build (fun _ arg_55__ arg_56__ =>
                        match arg_55__, arg_56__ with
                        | c, n => Foldable__Const_foldr c n t
                        end).

Local Definition Foldable__Const_product {inst_m}
   : forall {a}, forall `{GHC.Num.Num a}, (Const inst_m) a -> a :=
  fun {a} `{GHC.Num.Num a} =>
    Coq.Program.Basics.compose Data.Semigroup.Internal.getProduct
                               (Foldable__Const_foldMap Data.Semigroup.Internal.Mk_Product).

Local Definition Foldable__Const_sum {inst_m}
   : forall {a}, forall `{GHC.Num.Num a}, (Const inst_m) a -> a :=
  fun {a} `{GHC.Num.Num a} =>
    Coq.Program.Basics.compose Data.Semigroup.Internal.getSum
                               (Foldable__Const_foldMap Data.Semigroup.Internal.Mk_Sum).

Local Definition Foldable__Const_fold {inst_m}
   : forall {m}, forall `{GHC.Base.Monoid m}, (Const inst_m) m -> m :=
  fun {m} `{GHC.Base.Monoid m} => Foldable__Const_foldMap GHC.Base.id.

Local Definition Foldable__Const_elem {inst_m}
   : forall {a}, forall `{GHC.Base.Eq_ a}, a -> (Const inst_m) a -> bool :=
  fun {a} `{GHC.Base.Eq_ a} =>
    Coq.Program.Basics.compose (fun arg_69__ =>
                                  let 'p := arg_69__ in
                                  Coq.Program.Basics.compose Data.Semigroup.Internal.getAny
                                                             (Foldable__Const_foldMap (Coq.Program.Basics.compose
                                                                                       Data.Semigroup.Internal.Mk_Any
                                                                                       p))) _GHC.Base.==_.

Program Instance Foldable__Const {m} : Data.Foldable.Foldable (Const m) :=
  fun _ k =>
    k {| Data.Foldable.elem__ := fun {a} `{GHC.Base.Eq_ a} => Foldable__Const_elem ;
         Data.Foldable.fold__ := fun {m} `{GHC.Base.Monoid m} => Foldable__Const_fold ;
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
  fun {a} {b} => fun x => Functor__Const_fmap (GHC.Base.const x).

Program Instance Functor__Const {m} : GHC.Base.Functor (Const m) :=
  fun _ k =>
    k {| GHC.Base.op_zlzd____ := fun {a} {b} => Functor__Const_op_zlzd__ ;
         GHC.Base.fmap__ := fun {a} {b} => Functor__Const_fmap |}.

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
    fun x y =>
      Applicative__Const_op_zlztzg__ (GHC.Base.fmap (GHC.Base.const GHC.Base.id) x) y.

Local Definition Applicative__Const_pure {inst_m} `{GHC.Base.Monoid inst_m}
   : forall {a}, a -> (Const inst_m) a :=
  fun {a} => fun arg_0__ => Mk_Const GHC.Base.mempty.

Program Instance Applicative__Const {m} `{GHC.Base.Monoid m}
   : GHC.Base.Applicative (Const m) :=
  fun _ k =>
    k {| GHC.Base.op_ztzg____ := fun {a} {b} => Applicative__Const_op_ztzg__ ;
         GHC.Base.op_zlztzg____ := fun {a} {b} => Applicative__Const_op_zlztzg__ ;
         GHC.Base.liftA2__ := fun {a} {b} {c} => Applicative__Const_liftA2 ;
         GHC.Base.pure__ := fun {a} => Applicative__Const_pure |}.

(* Translating `instance Storable__Const' failed: OOPS! Cannot find information
   for class Qualified "Foreign.Storable" "Storable" unsupported *)

(* Translating `instance RealFloat__Const' failed: OOPS! Cannot find information
   for class Qualified "GHC.Float" "RealFloat" unsupported *)

(* Translating `instance RealFrac__Const' failed: OOPS! Cannot find information
   for class Qualified "GHC.Real" "RealFrac" unsupported *)

(* Translating `instance Real__Const' failed: OOPS! Cannot find information for
   class Qualified "GHC.Real" "Real" unsupported *)

Local Definition Ord__Const_compare {inst_a} {inst_k} {inst_b} `{GHC.Base.Ord
  inst_a}
   : (Const inst_a inst_b : GHC.Prim.TYPE GHC.Types.LiftedRep) ->
     (Const inst_a inst_b : GHC.Prim.TYPE GHC.Types.LiftedRep) -> comparison :=
  GHC.Prim.coerce GHC.Base.compare.

Local Definition Ord__Const_max {inst_a} {inst_k} {inst_b} `{GHC.Base.Ord
  inst_a}
   : (Const inst_a inst_b : GHC.Prim.TYPE GHC.Types.LiftedRep) ->
     (Const inst_a inst_b : GHC.Prim.TYPE GHC.Types.LiftedRep) ->
     (Const inst_a inst_b : GHC.Prim.TYPE GHC.Types.LiftedRep) :=
  GHC.Prim.coerce GHC.Base.max.

Local Definition Ord__Const_min {inst_a} {inst_k} {inst_b} `{GHC.Base.Ord
  inst_a}
   : (Const inst_a inst_b : GHC.Prim.TYPE GHC.Types.LiftedRep) ->
     (Const inst_a inst_b : GHC.Prim.TYPE GHC.Types.LiftedRep) ->
     (Const inst_a inst_b : GHC.Prim.TYPE GHC.Types.LiftedRep) :=
  GHC.Prim.coerce GHC.Base.min.

Local Definition Ord__Const_op_zg__ {inst_a} {inst_k} {inst_b} `{GHC.Base.Ord
  inst_a}
   : (Const inst_a inst_b : GHC.Prim.TYPE GHC.Types.LiftedRep) ->
     (Const inst_a inst_b : GHC.Prim.TYPE GHC.Types.LiftedRep) -> bool :=
  GHC.Prim.coerce _GHC.Base.>_.

Local Definition Ord__Const_op_zgze__ {inst_a} {inst_k} {inst_b} `{GHC.Base.Ord
  inst_a}
   : (Const inst_a inst_b : GHC.Prim.TYPE GHC.Types.LiftedRep) ->
     (Const inst_a inst_b : GHC.Prim.TYPE GHC.Types.LiftedRep) -> bool :=
  GHC.Prim.coerce _GHC.Base.>=_.

Local Definition Ord__Const_op_zl__ {inst_a} {inst_k} {inst_b} `{GHC.Base.Ord
  inst_a}
   : (Const inst_a inst_b : GHC.Prim.TYPE GHC.Types.LiftedRep) ->
     (Const inst_a inst_b : GHC.Prim.TYPE GHC.Types.LiftedRep) -> bool :=
  GHC.Prim.coerce _GHC.Base.<_.

Local Definition Ord__Const_op_zlze__ {inst_a} {inst_k} {inst_b} `{GHC.Base.Ord
  inst_a}
   : (Const inst_a inst_b : GHC.Prim.TYPE GHC.Types.LiftedRep) ->
     (Const inst_a inst_b : GHC.Prim.TYPE GHC.Types.LiftedRep) -> bool :=
  GHC.Prim.coerce _GHC.Base.<=_.

(* Translating `instance Num__Const' failed: OOPS! Cannot find information for
   class Qualified "GHC.Num" "Num" unsupported *)

Local Definition Monoid__Const_mappend {inst_a} {inst_k} {inst_b}
  `{GHC.Base.Monoid inst_a}
   : (Const inst_a inst_b : GHC.Prim.TYPE GHC.Types.LiftedRep) ->
     (Const inst_a inst_b : GHC.Prim.TYPE GHC.Types.LiftedRep) ->
     (Const inst_a inst_b : GHC.Prim.TYPE GHC.Types.LiftedRep) :=
  GHC.Prim.coerce GHC.Base.mappend.

Local Definition Monoid__Const_mconcat {inst_a} {inst_k} {inst_b}
  `{GHC.Base.Monoid inst_a}
   : list (Const inst_a inst_b : GHC.Prim.TYPE GHC.Types.LiftedRep) ->
     (Const inst_a inst_b : GHC.Prim.TYPE GHC.Types.LiftedRep) :=
  GHC.Prim.coerce GHC.Base.mconcat.

Local Definition Monoid__Const_mempty {inst_a} {inst_k} {inst_b}
  `{GHC.Base.Monoid inst_a}
   : Const inst_a inst_b : GHC.Prim.TYPE GHC.Types.LiftedRep :=
  GHC.Prim.coerce GHC.Base.mempty.

Local Definition Semigroup__Const_op_zlzlzgzg__ {inst_a} {inst_k} {inst_b}
  `{GHC.Base.Semigroup inst_a}
   : (Const inst_a inst_b : GHC.Prim.TYPE GHC.Types.LiftedRep) ->
     (Const inst_a inst_b : GHC.Prim.TYPE GHC.Types.LiftedRep) ->
     (Const inst_a inst_b : GHC.Prim.TYPE GHC.Types.LiftedRep) :=
  GHC.Prim.coerce _GHC.Base.<<>>_.

Instance Semigroup__Const {a} {b} `{GHC.Base.Semigroup a}
   : GHC.Base.Semigroup (Const a b) :=
  fun _ k => k (GHC.Base.Semigroup__Dict_Build _ Semigroup__Const_op_zlzlzgzg__).

Instance Monoid__Const {a} {b} `{GHC.Base.Monoid a}
   : GHC.Base.Monoid (Const a b) :=
  fun _ k =>
    k (GHC.Base.Monoid__Dict_Build _ Monoid__Const_mappend Monoid__Const_mconcat
                                   Monoid__Const_mempty).

(* Translating `instance Ix__Const' failed: OOPS! Cannot find information for
   class Qualified "GHC.Arr" "Ix" unsupported *)

(* Translating `instance Integral__Const' failed: OOPS! Cannot find information
   for class Qualified "GHC.Real" "Integral" unsupported *)

(* Translating `instance Generic1__Const__5' failed: type class instance
   head:App (App (Qualid (Qualified "GHC.Generics" "Generic1")) (PosArg (Qualid
   (Bare "k")) :| [])) (PosArg (HasType (App (Qualid (Qualified
   "Data.Functor.Const" "Const")) (PosArg (Qualid (Bare "a")) :| [])) (Arrow
   (Qualid (Bare "k")) (App (Qualid (Qualified "GHC.Prim" "TYPE")) (PosArg (Qualid
   (Qualified "GHC.Types" "LiftedRep")) :| [])))) :| []) unsupported *)

(* Translating `instance Generic__Const' failed: OOPS! Cannot find information
   for class Qualified "GHC.Generics" "Generic" unsupported *)

(* Translating `instance Fractional__Const' failed: OOPS! Cannot find
   information for class Qualified "GHC.Real" "Fractional" unsupported *)

(* Translating `instance Floating__Const' failed: OOPS! Cannot find information
   for class Qualified "GHC.Float" "Floating" unsupported *)

(* Translating `instance FiniteBits__Const' failed: OOPS! Cannot find
   information for class Qualified "Data.Bits" "FiniteBits" unsupported *)

Local Definition Eq___Const_op_zeze__ {inst_a} {inst_k} {inst_b} `{GHC.Base.Eq_
  inst_a}
   : (Const inst_a inst_b : GHC.Prim.TYPE GHC.Types.LiftedRep) ->
     (Const inst_a inst_b : GHC.Prim.TYPE GHC.Types.LiftedRep) -> bool :=
  GHC.Prim.coerce _GHC.Base.==_.

Local Definition Eq___Const_op_zsze__ {inst_a} {inst_k} {inst_b} `{GHC.Base.Eq_
  inst_a}
   : (Const inst_a inst_b : GHC.Prim.TYPE GHC.Types.LiftedRep) ->
     (Const inst_a inst_b : GHC.Prim.TYPE GHC.Types.LiftedRep) -> bool :=
  GHC.Prim.coerce _GHC.Base./=_.

Instance Eq___Const {a} {b} `{GHC.Base.Eq_ a} : GHC.Base.Eq_ (Const a b) :=
  fun _ k =>
    k (GHC.Base.Eq___Dict_Build _ Eq___Const_op_zeze__ Eq___Const_op_zsze__).

Instance Ord__Const {a} {b} `{GHC.Base.Ord a} : GHC.Base.Ord (Const a b) :=
  fun _ k =>
    k (GHC.Base.Ord__Dict_Build _ Ord__Const_op_zl__ Ord__Const_op_zlze__
                                Ord__Const_op_zg__ Ord__Const_op_zgze__ Ord__Const_compare Ord__Const_max
                                Ord__Const_min).

(* Translating `instance Enum__Const' failed: OOPS! Cannot find information for
   class Qualified "GHC.Enum" "Enum" unsupported *)

(* Translating `instance Bounded__Const' failed: OOPS! Cannot find information
   for class Qualified "GHC.Enum" "Bounded" unsupported *)

(* Translating `instance Bits__Const' failed: OOPS! Cannot find information for
   class Qualified "Data.Bits" "Bits" unsupported *)

(* Unbound variables:
     bool comparison false list true Coq.Program.Basics.compose
     Data.Foldable.Foldable Data.Semigroup.Internal.Mk_Any
     Data.Semigroup.Internal.Mk_Dual Data.Semigroup.Internal.Mk_Endo
     Data.Semigroup.Internal.Mk_Product Data.Semigroup.Internal.Mk_Sum
     Data.Semigroup.Internal.appEndo Data.Semigroup.Internal.getAny
     Data.Semigroup.Internal.getDual Data.Semigroup.Internal.getProduct
     Data.Semigroup.Internal.getSum GHC.Base.Applicative GHC.Base.Eq_
     GHC.Base.Eq___Dict_Build GHC.Base.Functor GHC.Base.Monoid
     GHC.Base.Monoid__Dict_Build GHC.Base.Ord GHC.Base.Ord__Dict_Build
     GHC.Base.Semigroup GHC.Base.Semigroup__Dict_Build GHC.Base.build
     GHC.Base.compare GHC.Base.const GHC.Base.flip GHC.Base.fmap GHC.Base.id
     GHC.Base.mappend GHC.Base.max GHC.Base.mconcat GHC.Base.mempty GHC.Base.min
     GHC.Base.op_zdzn__ GHC.Base.op_zeze__ GHC.Base.op_zg__ GHC.Base.op_zgze__
     GHC.Base.op_zl__ GHC.Base.op_zlze__ GHC.Base.op_zlzlzgzg__ GHC.Base.op_zsze__
     GHC.Num.Int GHC.Num.Num GHC.Num.fromInteger GHC.Num.op_zp__
     GHC.Prim.Build_Unpeel GHC.Prim.TYPE GHC.Prim.Unpeel GHC.Prim.coerce
     GHC.Types.LiftedRep
*)
