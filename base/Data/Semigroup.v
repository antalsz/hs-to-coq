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
Require Data.Functor.
Require Data.Maybe.
Require Data.Semigroup.Internal.
Require Data.Traversable.
Require GHC.Base.
Require GHC.Num.
Require GHC.Prim.
Import Data.Functor.Notations.
Import GHC.Base.Notations.
Import GHC.Num.Notations.

(* Converted type declarations: *)

Inductive WrappedMonoid m : Type := WrapMonoid : m -> WrappedMonoid m.

Inductive Option a : Type := Mk_Option : option a -> Option a.

Inductive Min a : Type := Mk_Min : a -> Min a.

Inductive Max a : Type := Mk_Max : a -> Max a.

Inductive Last a : Type := Mk_Last : a -> Last a.

Inductive First a : Type := Mk_First : a -> First a.

Inductive Arg a b : Type := Mk_Arg : a -> b -> Arg a b.

Definition ArgMax a b :=
  (Max (Arg a b))%type.

Definition ArgMin a b :=
  (Min (Arg a b))%type.

Arguments WrapMonoid {_} _.

Arguments Mk_Option {_} _.

Arguments Mk_Min {_} _.

Arguments Mk_Max {_} _.

Arguments Mk_Last {_} _.

Arguments Mk_First {_} _.

Arguments Mk_Arg {_} {_} _ _.

Definition unwrapMonoid {m} (arg_0__ : WrappedMonoid m) :=
  let 'WrapMonoid unwrapMonoid := arg_0__ in
  unwrapMonoid.

Definition getOption {a} (arg_1__ : Option a) :=
  let 'Mk_Option getOption := arg_1__ in
  getOption.

Definition getMin {a} (arg_2__ : Min a) :=
  let 'Mk_Min getMin := arg_2__ in
  getMin.

Definition getMax {a} (arg_3__ : Max a) :=
  let 'Mk_Max getMax := arg_3__ in
  getMax.

Definition getLast {a} (arg_4__ : Last a) :=
  let 'Mk_Last getLast := arg_4__ in
  getLast.

Definition getFirst {a} (arg_5__ : First a) :=
  let 'Mk_First getFirst := arg_5__ in
  getFirst.
(* Midamble *)

Require Data.List.NonEmpty.

Definition sconcat {a} `{GHC.Base.Semigroup a} : GHC.Base.NonEmpty a -> a :=
  Data.List.NonEmpty.NonEmpty_foldr1 (@GHC.Base.op_zlzlzgzg__ a _).

(* ------------------------- *)

(* These two instances are here because we don't mangle the instance names
   enough. This file creates instances for Monoid.First and Semigroup.First
   (which are different types.) But we produce the same names for them.
*)

Local Definition Semigroup__SFirst_op_zlzlzgzg__ {inst_a} : (First inst_a) -> (First
                                                       inst_a) -> (First inst_a) :=
  fun arg_0__ arg_1__ => match arg_0__ , arg_1__ with | a , _ => a end.

Local Definition Semigroup__SFirst_sconcat {inst_a} : GHC.Base.NonEmpty
                                                     (First inst_a) -> (First inst_a) :=
  fun arg_0__ =>
    match arg_0__ with
      | GHC.Base.NEcons a as_ => let fix go arg_1__ arg_2__
                                                     := match arg_1__ , arg_2__ with
                                                          | b , cons c cs => Semigroup__SFirst_op_zlzlzgzg__ b (go c cs)
                                                          | b , nil => b
                                                        end in
                                           go a as_
    end.



Program Instance Semigroup__SFirst {a} : GHC.Base.Semigroup (First a) := fun _ k =>
    k {| GHC.Base.op_zlzlzgzg____ := Semigroup__SFirst_op_zlzlzgzg__ |}.

Local Definition Semigroup__SLast_op_zlzlzgzg__ {inst_a} : (Last inst_a) -> (Last
                                                      inst_a) -> (Last inst_a) :=
  fun arg_0__ arg_1__ => match arg_0__ , arg_1__ with | _ , b => b end.

Local Definition Semigroup__SLast_sconcat {inst_a} : GHC.Base.NonEmpty
                                                    (Last inst_a) -> (Last inst_a) :=
  fun arg_0__ =>
    match arg_0__ with
      | GHC.Base.NEcons a as_ => let fix go arg_1__ arg_2__
                                                     := match arg_1__ , arg_2__ with
                                                          | b , cons c cs => Semigroup__SLast_op_zlzlzgzg__ b (go c cs)
                                                          | b , nil => b
                                                        end in
                                           go a as_
    end.


Program Instance Semigroup__SLast {a} : GHC.Base.Semigroup (Last a) := fun _ k =>
    k {| GHC.Base.op_zlzlzgzg____ := Semigroup__SLast_op_zlzlzgzg__ |}.

(* ------------------------- *)

(* Converted value declarations: *)

Instance Unpeel_Option a : GHC.Prim.Unpeel (Option a) (option a) :=
  GHC.Prim.Build_Unpeel _ _ getOption Mk_Option.

Instance Unpeel_WrappedMonoid a : GHC.Prim.Unpeel (WrappedMonoid a) a :=
  GHC.Prim.Build_Unpeel _ _ unwrapMonoid WrapMonoid.

Instance Unpeel_Last a : GHC.Prim.Unpeel (Last a) a :=
  GHC.Prim.Build_Unpeel _ _ getLast Mk_Last.

Instance Unpeel_First a : GHC.Prim.Unpeel (First a) a :=
  GHC.Prim.Build_Unpeel _ _ getFirst Mk_First.

Instance Unpeel_Max a : GHC.Prim.Unpeel (Max a) a :=
  GHC.Prim.Build_Unpeel _ _ getMax Mk_Max.

Instance Unpeel_Min a : GHC.Prim.Unpeel (Min a) a :=
  GHC.Prim.Build_Unpeel _ _ getMin Mk_Min.

Local Definition Functor__Option_fmap
   : forall {a} {b}, (a -> b) -> Option a -> Option b :=
  fun {a} {b} =>
    fun arg_0__ arg_1__ =>
      match arg_0__, arg_1__ with
      | f, Mk_Option a => Mk_Option (GHC.Base.fmap f a)
      end.

Local Definition Functor__Option_op_zlzd__
   : forall {a} {b}, a -> Option b -> Option a :=
  fun {a} {b} => fun x => Functor__Option_fmap (GHC.Base.const x).

Program Instance Functor__Option : GHC.Base.Functor Option :=
  fun _ k =>
    k {| GHC.Base.op_zlzd____ := fun {a} {b} => Functor__Option_op_zlzd__ ;
         GHC.Base.fmap__ := fun {a} {b} => Functor__Option_fmap |}.

Local Definition Applicative__Option_liftA2
   : forall {a} {b} {c}, (a -> b -> c) -> Option a -> Option b -> Option c :=
  fun {a} {b} {c} =>
    fun arg_0__ arg_1__ arg_2__ =>
      match arg_0__, arg_1__, arg_2__ with
      | f, Mk_Option x, Mk_Option y => Mk_Option (GHC.Base.liftA2 f x y)
      end.

Local Definition Applicative__Option_op_zlztzg__
   : forall {a} {b}, Option (a -> b) -> Option a -> Option b :=
  fun {a} {b} =>
    fun arg_0__ arg_1__ =>
      match arg_0__, arg_1__ with
      | Mk_Option a, Mk_Option b => Mk_Option (a GHC.Base.<*> b)
      end.

Local Definition Applicative__Option_op_ztzg__
   : forall {a} {b}, Option a -> Option b -> Option b :=
  fun {a} {b} =>
    fun arg_0__ arg_1__ =>
      match arg_0__, arg_1__ with
      | Mk_Option None, _ => Mk_Option None
      | _, b => b
      end.

Local Definition Applicative__Option_pure : forall {a}, a -> Option a :=
  fun {a} => fun a => Mk_Option (Some a).

Program Instance Applicative__Option : GHC.Base.Applicative Option :=
  fun _ k =>
    k {| GHC.Base.op_ztzg____ := fun {a} {b} => Applicative__Option_op_ztzg__ ;
         GHC.Base.op_zlztzg____ := fun {a} {b} => Applicative__Option_op_zlztzg__ ;
         GHC.Base.liftA2__ := fun {a} {b} {c} => Applicative__Option_liftA2 ;
         GHC.Base.pure__ := fun {a} => Applicative__Option_pure |}.

Local Definition Monad__Option_op_zgzg__
   : forall {a} {b}, Option a -> Option b -> Option b :=
  fun {a} {b} => _GHC.Base.*>_.

Local Definition Monad__Option_op_zgzgze__
   : forall {a} {b}, Option a -> (a -> Option b) -> Option b :=
  fun {a} {b} =>
    fun arg_0__ arg_1__ =>
      match arg_0__, arg_1__ with
      | Mk_Option (Some a), k => k a
      | _, _ => Mk_Option None
      end.

Local Definition Monad__Option_return_ : forall {a}, a -> Option a :=
  fun {a} => GHC.Base.pure.

Program Instance Monad__Option : GHC.Base.Monad Option :=
  fun _ k =>
    k {| GHC.Base.op_zgzg____ := fun {a} {b} => Monad__Option_op_zgzg__ ;
         GHC.Base.op_zgzgze____ := fun {a} {b} => Monad__Option_op_zgzgze__ ;
         GHC.Base.return___ := fun {a} => Monad__Option_return_ |}.

(* Translating `instance Alternative__Option' failed: OOPS! Cannot find
   information for class Qualified "GHC.Base" "Alternative" unsupported *)

(* Translating `instance MonadPlus__Option' failed: OOPS! Cannot find
   information for class Qualified "GHC.Base" "MonadPlus" unsupported *)

(* Translating `instance MonadFix__Option' failed: OOPS! Cannot find information
   for class Qualified "Control.Monad.Fix" "MonadFix" unsupported *)

Local Definition Foldable__Option_foldMap
   : forall {m} {a}, forall `{GHC.Base.Monoid m}, (a -> m) -> Option a -> m :=
  fun {m} {a} `{GHC.Base.Monoid m} =>
    fun arg_0__ arg_1__ =>
      match arg_0__, arg_1__ with
      | f, Mk_Option (Some m) => f m
      | _, Mk_Option None => GHC.Base.mempty
      end.

Local Definition Foldable__Option_foldl
   : forall {b} {a}, (b -> a -> b) -> b -> Option a -> b :=
  fun {b} {a} =>
    fun arg_19__ arg_20__ arg_21__ =>
      match arg_19__, arg_20__, arg_21__ with
      | f, z, t =>
          Data.Semigroup.Internal.appEndo (Data.Semigroup.Internal.getDual
                                           (Foldable__Option_foldMap (Coq.Program.Basics.compose
                                                                      Data.Semigroup.Internal.Mk_Dual
                                                                      (Coq.Program.Basics.compose
                                                                       Data.Semigroup.Internal.Mk_Endo (GHC.Base.flip
                                                                        f))) t)) z
      end.

Local Definition Foldable__Option_foldr'
   : forall {a} {b}, (a -> b -> b) -> b -> Option a -> b :=
  fun {a} {b} =>
    fun arg_9__ arg_10__ arg_11__ =>
      match arg_9__, arg_10__, arg_11__ with
      | f, z0, xs =>
          let f' :=
            fun arg_12__ arg_13__ arg_14__ =>
              match arg_12__, arg_13__, arg_14__ with
              | k, x, z => k GHC.Base.$! f x z
              end in
          Foldable__Option_foldl f' GHC.Base.id xs z0
      end.

Local Definition Foldable__Option_foldr
   : forall {a} {b}, (a -> b -> b) -> b -> Option a -> b :=
  fun {a} {b} =>
    fun arg_4__ arg_5__ arg_6__ =>
      match arg_4__, arg_5__, arg_6__ with
      | f, z, t =>
          Data.Semigroup.Internal.appEndo (Foldable__Option_foldMap
                                           (Coq.Program.Basics.compose Data.Semigroup.Internal.Mk_Endo f) t) z
      end.

Local Definition Foldable__Option_foldl'
   : forall {b} {a}, (b -> a -> b) -> b -> Option a -> b :=
  fun {b} {a} =>
    fun arg_24__ arg_25__ arg_26__ =>
      match arg_24__, arg_25__, arg_26__ with
      | f, z0, xs =>
          let f' :=
            fun arg_27__ arg_28__ arg_29__ =>
              match arg_27__, arg_28__, arg_29__ with
              | x, k, z => k GHC.Base.$! f z x
              end in
          Foldable__Option_foldr f' GHC.Base.id xs z0
      end.

Local Definition Foldable__Option_length
   : forall {a}, Option a -> GHC.Num.Int :=
  fun {a} =>
    Foldable__Option_foldl' (fun arg_64__ arg_65__ =>
                               match arg_64__, arg_65__ with
                               | c, _ => c GHC.Num.+ #1
                               end) #0.

Local Definition Foldable__Option_null : forall {a}, Option a -> bool :=
  fun {a} => Foldable__Option_foldr (fun arg_61__ arg_62__ => false) true.

Local Definition Foldable__Option_toList : forall {a}, Option a -> list a :=
  fun {a} =>
    fun arg_54__ =>
      let 't := arg_54__ in
      GHC.Base.build (fun _ arg_55__ arg_56__ =>
                        match arg_55__, arg_56__ with
                        | c, n => Foldable__Option_foldr c n t
                        end).

Local Definition Foldable__Option_product
   : forall {a}, forall `{GHC.Num.Num a}, Option a -> a :=
  fun {a} `{GHC.Num.Num a} =>
    Coq.Program.Basics.compose Data.Semigroup.Internal.getProduct
                               (Foldable__Option_foldMap Data.Semigroup.Internal.Mk_Product).

Local Definition Foldable__Option_sum
   : forall {a}, forall `{GHC.Num.Num a}, Option a -> a :=
  fun {a} `{GHC.Num.Num a} =>
    Coq.Program.Basics.compose Data.Semigroup.Internal.getSum
                               (Foldable__Option_foldMap Data.Semigroup.Internal.Mk_Sum).

Local Definition Foldable__Option_fold
   : forall {m}, forall `{GHC.Base.Monoid m}, Option m -> m :=
  fun {m} `{GHC.Base.Monoid m} => Foldable__Option_foldMap GHC.Base.id.

Local Definition Foldable__Option_elem
   : forall {a}, forall `{GHC.Base.Eq_ a}, a -> Option a -> bool :=
  fun {a} `{GHC.Base.Eq_ a} =>
    Coq.Program.Basics.compose (fun arg_69__ =>
                                  let 'p := arg_69__ in
                                  Coq.Program.Basics.compose Data.Semigroup.Internal.getAny
                                                             (Foldable__Option_foldMap (Coq.Program.Basics.compose
                                                                                        Data.Semigroup.Internal.Mk_Any
                                                                                        p))) _GHC.Base.==_.

Program Instance Foldable__Option : Data.Foldable.Foldable Option :=
  fun _ k =>
    k {| Data.Foldable.elem__ := fun {a} `{GHC.Base.Eq_ a} =>
           Foldable__Option_elem ;
         Data.Foldable.fold__ := fun {m} `{GHC.Base.Monoid m} => Foldable__Option_fold ;
         Data.Foldable.foldMap__ := fun {m} {a} `{GHC.Base.Monoid m} =>
           Foldable__Option_foldMap ;
         Data.Foldable.foldl__ := fun {b} {a} => Foldable__Option_foldl ;
         Data.Foldable.foldl'__ := fun {b} {a} => Foldable__Option_foldl' ;
         Data.Foldable.foldr__ := fun {a} {b} => Foldable__Option_foldr ;
         Data.Foldable.foldr'__ := fun {a} {b} => Foldable__Option_foldr' ;
         Data.Foldable.length__ := fun {a} => Foldable__Option_length ;
         Data.Foldable.null__ := fun {a} => Foldable__Option_null ;
         Data.Foldable.product__ := fun {a} `{GHC.Num.Num a} =>
           Foldable__Option_product ;
         Data.Foldable.sum__ := fun {a} `{GHC.Num.Num a} => Foldable__Option_sum ;
         Data.Foldable.toList__ := fun {a} => Foldable__Option_toList |}.

Local Definition Traversable__Option_traverse
   : forall {f} {a} {b},
     forall `{GHC.Base.Applicative f}, (a -> f b) -> Option a -> f (Option b) :=
  fun {f} {a} {b} `{GHC.Base.Applicative f} =>
    fun arg_0__ arg_1__ =>
      match arg_0__, arg_1__ with
      | f, Mk_Option (Some a) => (Mk_Option GHC.Base.∘ Some) Data.Functor.<$> f a
      | _, Mk_Option None => GHC.Base.pure (Mk_Option None)
      end.

Local Definition Traversable__Option_sequenceA
   : forall {f} {a},
     forall `{GHC.Base.Applicative f}, Option (f a) -> f (Option a) :=
  fun {f} {a} `{GHC.Base.Applicative f} =>
    Traversable__Option_traverse GHC.Base.id.

Local Definition Traversable__Option_sequence
   : forall {m} {a}, forall `{GHC.Base.Monad m}, Option (m a) -> m (Option a) :=
  fun {m} {a} `{GHC.Base.Monad m} => Traversable__Option_sequenceA.

Local Definition Traversable__Option_mapM
   : forall {m} {a} {b},
     forall `{GHC.Base.Monad m}, (a -> m b) -> Option a -> m (Option b) :=
  fun {m} {a} {b} `{GHC.Base.Monad m} => Traversable__Option_traverse.

Program Instance Traversable__Option : Data.Traversable.Traversable Option :=
  fun _ k =>
    k {| Data.Traversable.mapM__ := fun {m} {a} {b} `{GHC.Base.Monad m} =>
           Traversable__Option_mapM ;
         Data.Traversable.sequence__ := fun {m} {a} `{GHC.Base.Monad m} =>
           Traversable__Option_sequence ;
         Data.Traversable.sequenceA__ := fun {f} {a} `{GHC.Base.Applicative f} =>
           Traversable__Option_sequenceA ;
         Data.Traversable.traverse__ := fun {f} {a} {b} `{GHC.Base.Applicative f} =>
           Traversable__Option_traverse |}.

Local Definition Semigroup__Option_op_zlzlzgzg__ {inst_a} `{_
   : GHC.Base.Semigroup inst_a}
   : Option inst_a -> Option inst_a -> Option inst_a :=
  GHC.Prim.coerce (@GHC.Base.op_zlzlzgzg__ (option inst_a) _).

Program Instance Semigroup__Option {a} `{GHC.Base.Semigroup a}
   : GHC.Base.Semigroup (Option a) :=
  fun _ k => k {| GHC.Base.op_zlzlzgzg____ := Semigroup__Option_op_zlzlzgzg__ |}.

Local Definition Monoid__Option_mappend {inst_a} `{GHC.Base.Semigroup inst_a}
   : (Option inst_a) -> (Option inst_a) -> (Option inst_a) :=
  _GHC.Base.<<>>_.

Local Definition Monoid__Option_mempty {inst_a} `{GHC.Base.Semigroup inst_a}
   : (Option inst_a) :=
  Mk_Option None.

Local Definition Monoid__Option_mconcat {inst_a} `{GHC.Base.Semigroup inst_a}
   : list (Option inst_a) -> (Option inst_a) :=
  GHC.Base.foldr Monoid__Option_mappend Monoid__Option_mempty.

Program Instance Monoid__Option {a} `{GHC.Base.Semigroup a}
   : GHC.Base.Monoid (Option a) :=
  fun _ k =>
    k {| GHC.Base.mappend__ := Monoid__Option_mappend ;
         GHC.Base.mconcat__ := Monoid__Option_mconcat ;
         GHC.Base.mempty__ := Monoid__Option_mempty |}.

Local Definition Semigroup__WrappedMonoid_op_zlzlzgzg__ {inst_m} `{_
   : GHC.Base.Monoid inst_m}
   : WrappedMonoid inst_m -> WrappedMonoid inst_m -> WrappedMonoid inst_m :=
  GHC.Prim.coerce (@GHC.Base.mappend inst_m _ _).

Program Instance Semigroup__WrappedMonoid {m} `{GHC.Base.Monoid m}
   : GHC.Base.Semigroup (WrappedMonoid m) :=
  fun _ k =>
    k {| GHC.Base.op_zlzlzgzg____ := Semigroup__WrappedMonoid_op_zlzlzgzg__ |}.

Local Definition Monoid__WrappedMonoid_mappend {inst_m} `{GHC.Base.Monoid
  inst_m}
   : (WrappedMonoid inst_m) -> (WrappedMonoid inst_m) -> (WrappedMonoid inst_m) :=
  _GHC.Base.<<>>_.

Local Definition Monoid__WrappedMonoid_mempty {inst_m} `{GHC.Base.Monoid inst_m}
   : (WrappedMonoid inst_m) :=
  WrapMonoid GHC.Base.mempty.

Local Definition Monoid__WrappedMonoid_mconcat {inst_m} `{GHC.Base.Monoid
  inst_m}
   : list (WrappedMonoid inst_m) -> (WrappedMonoid inst_m) :=
  GHC.Base.foldr Monoid__WrappedMonoid_mappend Monoid__WrappedMonoid_mempty.

Program Instance Monoid__WrappedMonoid {m} `{GHC.Base.Monoid m}
   : GHC.Base.Monoid (WrappedMonoid m) :=
  fun _ k =>
    k {| GHC.Base.mappend__ := Monoid__WrappedMonoid_mappend ;
         GHC.Base.mconcat__ := Monoid__WrappedMonoid_mconcat ;
         GHC.Base.mempty__ := Monoid__WrappedMonoid_mempty |}.

(* Translating `instance Enum__WrappedMonoid' failed: OOPS! Cannot find
   information for class Qualified "GHC.Enum" "Enum" unsupported *)

(* Translating `instance Enum__Last' failed: OOPS! Cannot find information for
   class Qualified "GHC.Enum" "Enum" unsupported *)

Local Definition Semigroup__Last_op_zlzlzgzg__ {inst_a}
   : (Last inst_a) -> (Last inst_a) -> (Last inst_a) :=
  fun arg_0__ arg_1__ => match arg_0__, arg_1__ with | _, b => b end.

Program Instance Semigroup__Last {a} : GHC.Base.Semigroup (Last a) :=
  fun _ k => k {| GHC.Base.op_zlzlzgzg____ := Semigroup__Last_op_zlzlzgzg__ |}.

Local Definition Functor__Last_fmap
   : forall {a} {b}, (a -> b) -> Last a -> Last b :=
  fun {a} {b} =>
    fun arg_0__ arg_1__ =>
      match arg_0__, arg_1__ with
      | f, Mk_Last x => Mk_Last (f x)
      end.

Local Definition Functor__Last_op_zlzd__
   : forall {a} {b}, a -> Last b -> Last a :=
  fun {a} {b} =>
    fun arg_0__ arg_1__ => match arg_0__, arg_1__ with | a, _ => Mk_Last a end.

Program Instance Functor__Last : GHC.Base.Functor Last :=
  fun _ k =>
    k {| GHC.Base.op_zlzd____ := fun {a} {b} => Functor__Last_op_zlzd__ ;
         GHC.Base.fmap__ := fun {a} {b} => Functor__Last_fmap |}.

Local Definition Foldable__Last_foldMap
   : forall {m} {a}, forall `{GHC.Base.Monoid m}, (a -> m) -> Last a -> m :=
  fun {m} {a} `{GHC.Base.Monoid m} =>
    fun arg_0__ arg_1__ => match arg_0__, arg_1__ with | f, Mk_Last a => f a end.

Local Definition Foldable__Last_foldl
   : forall {b} {a}, (b -> a -> b) -> b -> Last a -> b :=
  fun {b} {a} =>
    fun arg_19__ arg_20__ arg_21__ =>
      match arg_19__, arg_20__, arg_21__ with
      | f, z, t =>
          Data.Semigroup.Internal.appEndo (Data.Semigroup.Internal.getDual
                                           (Foldable__Last_foldMap (Coq.Program.Basics.compose
                                                                    Data.Semigroup.Internal.Mk_Dual
                                                                    (Coq.Program.Basics.compose
                                                                     Data.Semigroup.Internal.Mk_Endo (GHC.Base.flip f)))
                                            t)) z
      end.

Local Definition Foldable__Last_foldr'
   : forall {a} {b}, (a -> b -> b) -> b -> Last a -> b :=
  fun {a} {b} =>
    fun arg_9__ arg_10__ arg_11__ =>
      match arg_9__, arg_10__, arg_11__ with
      | f, z0, xs =>
          let f' :=
            fun arg_12__ arg_13__ arg_14__ =>
              match arg_12__, arg_13__, arg_14__ with
              | k, x, z => k GHC.Base.$! f x z
              end in
          Foldable__Last_foldl f' GHC.Base.id xs z0
      end.

Local Definition Foldable__Last_foldr
   : forall {a} {b}, (a -> b -> b) -> b -> Last a -> b :=
  fun {a} {b} =>
    fun arg_4__ arg_5__ arg_6__ =>
      match arg_4__, arg_5__, arg_6__ with
      | f, z, t =>
          Data.Semigroup.Internal.appEndo (Foldable__Last_foldMap
                                           (Coq.Program.Basics.compose Data.Semigroup.Internal.Mk_Endo f) t) z
      end.

Local Definition Foldable__Last_foldl'
   : forall {b} {a}, (b -> a -> b) -> b -> Last a -> b :=
  fun {b} {a} =>
    fun arg_24__ arg_25__ arg_26__ =>
      match arg_24__, arg_25__, arg_26__ with
      | f, z0, xs =>
          let f' :=
            fun arg_27__ arg_28__ arg_29__ =>
              match arg_27__, arg_28__, arg_29__ with
              | x, k, z => k GHC.Base.$! f z x
              end in
          Foldable__Last_foldr f' GHC.Base.id xs z0
      end.

Local Definition Foldable__Last_length : forall {a}, Last a -> GHC.Num.Int :=
  fun {a} =>
    Foldable__Last_foldl' (fun arg_64__ arg_65__ =>
                             match arg_64__, arg_65__ with
                             | c, _ => c GHC.Num.+ #1
                             end) #0.

Local Definition Foldable__Last_null : forall {a}, Last a -> bool :=
  fun {a} => Foldable__Last_foldr (fun arg_61__ arg_62__ => false) true.

Local Definition Foldable__Last_toList : forall {a}, Last a -> list a :=
  fun {a} =>
    fun arg_54__ =>
      let 't := arg_54__ in
      GHC.Base.build (fun _ arg_55__ arg_56__ =>
                        match arg_55__, arg_56__ with
                        | c, n => Foldable__Last_foldr c n t
                        end).

Local Definition Foldable__Last_product
   : forall {a}, forall `{GHC.Num.Num a}, Last a -> a :=
  fun {a} `{GHC.Num.Num a} =>
    Coq.Program.Basics.compose Data.Semigroup.Internal.getProduct
                               (Foldable__Last_foldMap Data.Semigroup.Internal.Mk_Product).

Local Definition Foldable__Last_sum
   : forall {a}, forall `{GHC.Num.Num a}, Last a -> a :=
  fun {a} `{GHC.Num.Num a} =>
    Coq.Program.Basics.compose Data.Semigroup.Internal.getSum
                               (Foldable__Last_foldMap Data.Semigroup.Internal.Mk_Sum).

Local Definition Foldable__Last_fold
   : forall {m}, forall `{GHC.Base.Monoid m}, Last m -> m :=
  fun {m} `{GHC.Base.Monoid m} => Foldable__Last_foldMap GHC.Base.id.

Local Definition Foldable__Last_elem
   : forall {a}, forall `{GHC.Base.Eq_ a}, a -> Last a -> bool :=
  fun {a} `{GHC.Base.Eq_ a} =>
    Coq.Program.Basics.compose (fun arg_69__ =>
                                  let 'p := arg_69__ in
                                  Coq.Program.Basics.compose Data.Semigroup.Internal.getAny
                                                             (Foldable__Last_foldMap (Coq.Program.Basics.compose
                                                                                      Data.Semigroup.Internal.Mk_Any
                                                                                      p))) _GHC.Base.==_.

Program Instance Foldable__Last : Data.Foldable.Foldable Last :=
  fun _ k =>
    k {| Data.Foldable.elem__ := fun {a} `{GHC.Base.Eq_ a} => Foldable__Last_elem ;
         Data.Foldable.fold__ := fun {m} `{GHC.Base.Monoid m} => Foldable__Last_fold ;
         Data.Foldable.foldMap__ := fun {m} {a} `{GHC.Base.Monoid m} =>
           Foldable__Last_foldMap ;
         Data.Foldable.foldl__ := fun {b} {a} => Foldable__Last_foldl ;
         Data.Foldable.foldl'__ := fun {b} {a} => Foldable__Last_foldl' ;
         Data.Foldable.foldr__ := fun {a} {b} => Foldable__Last_foldr ;
         Data.Foldable.foldr'__ := fun {a} {b} => Foldable__Last_foldr' ;
         Data.Foldable.length__ := fun {a} => Foldable__Last_length ;
         Data.Foldable.null__ := fun {a} => Foldable__Last_null ;
         Data.Foldable.product__ := fun {a} `{GHC.Num.Num a} => Foldable__Last_product ;
         Data.Foldable.sum__ := fun {a} `{GHC.Num.Num a} => Foldable__Last_sum ;
         Data.Foldable.toList__ := fun {a} => Foldable__Last_toList |}.

Local Definition Traversable__Last_traverse
   : forall {f} {a} {b},
     forall `{GHC.Base.Applicative f}, (a -> f b) -> Last a -> f (Last b) :=
  fun {f} {a} {b} `{GHC.Base.Applicative f} =>
    fun arg_0__ arg_1__ =>
      match arg_0__, arg_1__ with
      | f, Mk_Last a => Mk_Last Data.Functor.<$> f a
      end.

Local Definition Traversable__Last_sequenceA
   : forall {f} {a}, forall `{GHC.Base.Applicative f}, Last (f a) -> f (Last a) :=
  fun {f} {a} `{GHC.Base.Applicative f} => Traversable__Last_traverse GHC.Base.id.

Local Definition Traversable__Last_sequence
   : forall {m} {a}, forall `{GHC.Base.Monad m}, Last (m a) -> m (Last a) :=
  fun {m} {a} `{GHC.Base.Monad m} => Traversable__Last_sequenceA.

Local Definition Traversable__Last_mapM
   : forall {m} {a} {b},
     forall `{GHC.Base.Monad m}, (a -> m b) -> Last a -> m (Last b) :=
  fun {m} {a} {b} `{GHC.Base.Monad m} => Traversable__Last_traverse.

Program Instance Traversable__Last : Data.Traversable.Traversable Last :=
  fun _ k =>
    k {| Data.Traversable.mapM__ := fun {m} {a} {b} `{GHC.Base.Monad m} =>
           Traversable__Last_mapM ;
         Data.Traversable.sequence__ := fun {m} {a} `{GHC.Base.Monad m} =>
           Traversable__Last_sequence ;
         Data.Traversable.sequenceA__ := fun {f} {a} `{GHC.Base.Applicative f} =>
           Traversable__Last_sequenceA ;
         Data.Traversable.traverse__ := fun {f} {a} {b} `{GHC.Base.Applicative f} =>
           Traversable__Last_traverse |}.

Local Definition Applicative__Last_liftA2
   : forall {a} {b} {c}, (a -> b -> c) -> Last a -> Last b -> Last c :=
  fun {a} {b} {c} => GHC.Prim.coerce.

Local Definition Applicative__Last_op_zlztzg__
   : forall {a} {b}, Last (a -> b) -> Last a -> Last b :=
  fun {a} {b} => GHC.Prim.coerce.

Local Definition Applicative__Last_op_ztzg__
   : forall {a} {b}, Last a -> Last b -> Last b :=
  fun {a} {b} =>
    fun arg_0__ arg_1__ => match arg_0__, arg_1__ with | _, a => a end.

Local Definition Applicative__Last_pure : forall {a}, a -> Last a :=
  fun {a} => Mk_Last.

Program Instance Applicative__Last : GHC.Base.Applicative Last :=
  fun _ k =>
    k {| GHC.Base.op_ztzg____ := fun {a} {b} => Applicative__Last_op_ztzg__ ;
         GHC.Base.op_zlztzg____ := fun {a} {b} => Applicative__Last_op_zlztzg__ ;
         GHC.Base.liftA2__ := fun {a} {b} {c} => Applicative__Last_liftA2 ;
         GHC.Base.pure__ := fun {a} => Applicative__Last_pure |}.

Local Definition Monad__Last_op_zgzg__
   : forall {a} {b}, Last a -> Last b -> Last b :=
  fun {a} {b} => _GHC.Base.*>_.

Local Definition Monad__Last_op_zgzgze__
   : forall {a} {b}, Last a -> (a -> Last b) -> Last b :=
  fun {a} {b} =>
    fun arg_0__ arg_1__ => match arg_0__, arg_1__ with | Mk_Last a, f => f a end.

Local Definition Monad__Last_return_ : forall {a}, a -> Last a :=
  fun {a} => GHC.Base.pure.

Program Instance Monad__Last : GHC.Base.Monad Last :=
  fun _ k =>
    k {| GHC.Base.op_zgzg____ := fun {a} {b} => Monad__Last_op_zgzg__ ;
         GHC.Base.op_zgzgze____ := fun {a} {b} => Monad__Last_op_zgzgze__ ;
         GHC.Base.return___ := fun {a} => Monad__Last_return_ |}.

(* Translating `instance MonadFix__Last' failed: OOPS! Cannot find information
   for class Qualified "Control.Monad.Fix" "MonadFix" unsupported *)

(* Translating `instance Enum__First' failed: OOPS! Cannot find information for
   class Qualified "GHC.Enum" "Enum" unsupported *)

Local Definition Semigroup__First_op_zlzlzgzg__ {inst_a}
   : (First inst_a) -> (First inst_a) -> (First inst_a) :=
  fun arg_0__ arg_1__ => match arg_0__, arg_1__ with | a, _ => a end.

Program Instance Semigroup__First {a} : GHC.Base.Semigroup (First a) :=
  fun _ k => k {| GHC.Base.op_zlzlzgzg____ := Semigroup__First_op_zlzlzgzg__ |}.

Local Definition Functor__First_fmap
   : forall {a} {b}, (a -> b) -> First a -> First b :=
  fun {a} {b} =>
    fun arg_0__ arg_1__ =>
      match arg_0__, arg_1__ with
      | f, Mk_First x => Mk_First (f x)
      end.

Local Definition Functor__First_op_zlzd__
   : forall {a} {b}, a -> First b -> First a :=
  fun {a} {b} => fun x => Functor__First_fmap (GHC.Base.const x).

Program Instance Functor__First : GHC.Base.Functor First :=
  fun _ k =>
    k {| GHC.Base.op_zlzd____ := fun {a} {b} => Functor__First_op_zlzd__ ;
         GHC.Base.fmap__ := fun {a} {b} => Functor__First_fmap |}.

Local Definition Foldable__First_foldMap
   : forall {m} {a}, forall `{GHC.Base.Monoid m}, (a -> m) -> First a -> m :=
  fun {m} {a} `{GHC.Base.Monoid m} =>
    fun arg_0__ arg_1__ => match arg_0__, arg_1__ with | f, Mk_First a => f a end.

Local Definition Foldable__First_foldl
   : forall {b} {a}, (b -> a -> b) -> b -> First a -> b :=
  fun {b} {a} =>
    fun arg_19__ arg_20__ arg_21__ =>
      match arg_19__, arg_20__, arg_21__ with
      | f, z, t =>
          Data.Semigroup.Internal.appEndo (Data.Semigroup.Internal.getDual
                                           (Foldable__First_foldMap (Coq.Program.Basics.compose
                                                                     Data.Semigroup.Internal.Mk_Dual
                                                                     (Coq.Program.Basics.compose
                                                                      Data.Semigroup.Internal.Mk_Endo (GHC.Base.flip
                                                                       f))) t)) z
      end.

Local Definition Foldable__First_foldr'
   : forall {a} {b}, (a -> b -> b) -> b -> First a -> b :=
  fun {a} {b} =>
    fun arg_9__ arg_10__ arg_11__ =>
      match arg_9__, arg_10__, arg_11__ with
      | f, z0, xs =>
          let f' :=
            fun arg_12__ arg_13__ arg_14__ =>
              match arg_12__, arg_13__, arg_14__ with
              | k, x, z => k GHC.Base.$! f x z
              end in
          Foldable__First_foldl f' GHC.Base.id xs z0
      end.

Local Definition Foldable__First_foldr
   : forall {a} {b}, (a -> b -> b) -> b -> First a -> b :=
  fun {a} {b} =>
    fun arg_4__ arg_5__ arg_6__ =>
      match arg_4__, arg_5__, arg_6__ with
      | f, z, t =>
          Data.Semigroup.Internal.appEndo (Foldable__First_foldMap
                                           (Coq.Program.Basics.compose Data.Semigroup.Internal.Mk_Endo f) t) z
      end.

Local Definition Foldable__First_foldl'
   : forall {b} {a}, (b -> a -> b) -> b -> First a -> b :=
  fun {b} {a} =>
    fun arg_24__ arg_25__ arg_26__ =>
      match arg_24__, arg_25__, arg_26__ with
      | f, z0, xs =>
          let f' :=
            fun arg_27__ arg_28__ arg_29__ =>
              match arg_27__, arg_28__, arg_29__ with
              | x, k, z => k GHC.Base.$! f z x
              end in
          Foldable__First_foldr f' GHC.Base.id xs z0
      end.

Local Definition Foldable__First_length : forall {a}, First a -> GHC.Num.Int :=
  fun {a} =>
    Foldable__First_foldl' (fun arg_64__ arg_65__ =>
                              match arg_64__, arg_65__ with
                              | c, _ => c GHC.Num.+ #1
                              end) #0.

Local Definition Foldable__First_null : forall {a}, First a -> bool :=
  fun {a} => Foldable__First_foldr (fun arg_61__ arg_62__ => false) true.

Local Definition Foldable__First_toList : forall {a}, First a -> list a :=
  fun {a} =>
    fun arg_54__ =>
      let 't := arg_54__ in
      GHC.Base.build (fun _ arg_55__ arg_56__ =>
                        match arg_55__, arg_56__ with
                        | c, n => Foldable__First_foldr c n t
                        end).

Local Definition Foldable__First_product
   : forall {a}, forall `{GHC.Num.Num a}, First a -> a :=
  fun {a} `{GHC.Num.Num a} =>
    Coq.Program.Basics.compose Data.Semigroup.Internal.getProduct
                               (Foldable__First_foldMap Data.Semigroup.Internal.Mk_Product).

Local Definition Foldable__First_sum
   : forall {a}, forall `{GHC.Num.Num a}, First a -> a :=
  fun {a} `{GHC.Num.Num a} =>
    Coq.Program.Basics.compose Data.Semigroup.Internal.getSum
                               (Foldable__First_foldMap Data.Semigroup.Internal.Mk_Sum).

Local Definition Foldable__First_fold
   : forall {m}, forall `{GHC.Base.Monoid m}, First m -> m :=
  fun {m} `{GHC.Base.Monoid m} => Foldable__First_foldMap GHC.Base.id.

Local Definition Foldable__First_elem
   : forall {a}, forall `{GHC.Base.Eq_ a}, a -> First a -> bool :=
  fun {a} `{GHC.Base.Eq_ a} =>
    Coq.Program.Basics.compose (fun arg_69__ =>
                                  let 'p := arg_69__ in
                                  Coq.Program.Basics.compose Data.Semigroup.Internal.getAny
                                                             (Foldable__First_foldMap (Coq.Program.Basics.compose
                                                                                       Data.Semigroup.Internal.Mk_Any
                                                                                       p))) _GHC.Base.==_.

Program Instance Foldable__First : Data.Foldable.Foldable First :=
  fun _ k =>
    k {| Data.Foldable.elem__ := fun {a} `{GHC.Base.Eq_ a} => Foldable__First_elem ;
         Data.Foldable.fold__ := fun {m} `{GHC.Base.Monoid m} => Foldable__First_fold ;
         Data.Foldable.foldMap__ := fun {m} {a} `{GHC.Base.Monoid m} =>
           Foldable__First_foldMap ;
         Data.Foldable.foldl__ := fun {b} {a} => Foldable__First_foldl ;
         Data.Foldable.foldl'__ := fun {b} {a} => Foldable__First_foldl' ;
         Data.Foldable.foldr__ := fun {a} {b} => Foldable__First_foldr ;
         Data.Foldable.foldr'__ := fun {a} {b} => Foldable__First_foldr' ;
         Data.Foldable.length__ := fun {a} => Foldable__First_length ;
         Data.Foldable.null__ := fun {a} => Foldable__First_null ;
         Data.Foldable.product__ := fun {a} `{GHC.Num.Num a} => Foldable__First_product ;
         Data.Foldable.sum__ := fun {a} `{GHC.Num.Num a} => Foldable__First_sum ;
         Data.Foldable.toList__ := fun {a} => Foldable__First_toList |}.

Local Definition Traversable__First_traverse
   : forall {f} {a} {b},
     forall `{GHC.Base.Applicative f}, (a -> f b) -> First a -> f (First b) :=
  fun {f} {a} {b} `{GHC.Base.Applicative f} =>
    fun arg_0__ arg_1__ =>
      match arg_0__, arg_1__ with
      | f, Mk_First a => Mk_First Data.Functor.<$> f a
      end.

Local Definition Traversable__First_sequenceA
   : forall {f} {a},
     forall `{GHC.Base.Applicative f}, First (f a) -> f (First a) :=
  fun {f} {a} `{GHC.Base.Applicative f} =>
    Traversable__First_traverse GHC.Base.id.

Local Definition Traversable__First_sequence
   : forall {m} {a}, forall `{GHC.Base.Monad m}, First (m a) -> m (First a) :=
  fun {m} {a} `{GHC.Base.Monad m} => Traversable__First_sequenceA.

Local Definition Traversable__First_mapM
   : forall {m} {a} {b},
     forall `{GHC.Base.Monad m}, (a -> m b) -> First a -> m (First b) :=
  fun {m} {a} {b} `{GHC.Base.Monad m} => Traversable__First_traverse.

Program Instance Traversable__First : Data.Traversable.Traversable First :=
  fun _ k =>
    k {| Data.Traversable.mapM__ := fun {m} {a} {b} `{GHC.Base.Monad m} =>
           Traversable__First_mapM ;
         Data.Traversable.sequence__ := fun {m} {a} `{GHC.Base.Monad m} =>
           Traversable__First_sequence ;
         Data.Traversable.sequenceA__ := fun {f} {a} `{GHC.Base.Applicative f} =>
           Traversable__First_sequenceA ;
         Data.Traversable.traverse__ := fun {f} {a} {b} `{GHC.Base.Applicative f} =>
           Traversable__First_traverse |}.

Local Definition Applicative__First_liftA2
   : forall {a} {b} {c}, (a -> b -> c) -> First a -> First b -> First c :=
  fun {a} {b} {c} => GHC.Prim.coerce.

Local Definition Applicative__First_op_zlztzg__
   : forall {a} {b}, First (a -> b) -> First a -> First b :=
  fun {a} {b} => GHC.Prim.coerce.

Local Definition Applicative__First_op_ztzg__
   : forall {a} {b}, First a -> First b -> First b :=
  fun {a} {b} =>
    fun arg_0__ arg_1__ => match arg_0__, arg_1__ with | _, a => a end.

Local Definition Applicative__First_pure : forall {a}, a -> First a :=
  fun {a} => fun x => Mk_First x.

Program Instance Applicative__First : GHC.Base.Applicative First :=
  fun _ k =>
    k {| GHC.Base.op_ztzg____ := fun {a} {b} => Applicative__First_op_ztzg__ ;
         GHC.Base.op_zlztzg____ := fun {a} {b} => Applicative__First_op_zlztzg__ ;
         GHC.Base.liftA2__ := fun {a} {b} {c} => Applicative__First_liftA2 ;
         GHC.Base.pure__ := fun {a} => Applicative__First_pure |}.

Local Definition Monad__First_op_zgzg__
   : forall {a} {b}, First a -> First b -> First b :=
  fun {a} {b} => _GHC.Base.*>_.

Local Definition Monad__First_op_zgzgze__
   : forall {a} {b}, First a -> (a -> First b) -> First b :=
  fun {a} {b} =>
    fun arg_0__ arg_1__ => match arg_0__, arg_1__ with | Mk_First a, f => f a end.

Local Definition Monad__First_return_ : forall {a}, a -> First a :=
  fun {a} => GHC.Base.pure.

Program Instance Monad__First : GHC.Base.Monad First :=
  fun _ k =>
    k {| GHC.Base.op_zgzg____ := fun {a} {b} => Monad__First_op_zgzg__ ;
         GHC.Base.op_zgzgze____ := fun {a} {b} => Monad__First_op_zgzgze__ ;
         GHC.Base.return___ := fun {a} => Monad__First_return_ |}.

(* Translating `instance MonadFix__First' failed: OOPS! Cannot find information
   for class Qualified "Control.Monad.Fix" "MonadFix" unsupported *)

Local Definition Functor__Arg_fmap {inst_a}
   : forall {a} {b}, (a -> b) -> (Arg inst_a) a -> (Arg inst_a) b :=
  fun {a} {b} =>
    fun arg_0__ arg_1__ =>
      match arg_0__, arg_1__ with
      | f, Mk_Arg x a => Mk_Arg x (f a)
      end.

Local Definition Functor__Arg_op_zlzd__ {inst_a}
   : forall {a} {b}, a -> (Arg inst_a) b -> (Arg inst_a) a :=
  fun {a} {b} => fun x => Functor__Arg_fmap (GHC.Base.const x).

Program Instance Functor__Arg {a} : GHC.Base.Functor (Arg a) :=
  fun _ k =>
    k {| GHC.Base.op_zlzd____ := fun {a} {b} => Functor__Arg_op_zlzd__ ;
         GHC.Base.fmap__ := fun {a} {b} => Functor__Arg_fmap |}.

Local Definition Foldable__Arg_foldMap {inst_a}
   : forall {m} {a},
     forall `{GHC.Base.Monoid m}, (a -> m) -> (Arg inst_a) a -> m :=
  fun {m} {a} `{GHC.Base.Monoid m} =>
    fun arg_0__ arg_1__ => match arg_0__, arg_1__ with | f, Mk_Arg _ a => f a end.

Local Definition Foldable__Arg_foldl {inst_a}
   : forall {b} {a}, (b -> a -> b) -> b -> (Arg inst_a) a -> b :=
  fun {b} {a} =>
    fun arg_19__ arg_20__ arg_21__ =>
      match arg_19__, arg_20__, arg_21__ with
      | f, z, t =>
          Data.Semigroup.Internal.appEndo (Data.Semigroup.Internal.getDual
                                           (Foldable__Arg_foldMap (Coq.Program.Basics.compose
                                                                   Data.Semigroup.Internal.Mk_Dual
                                                                   (Coq.Program.Basics.compose
                                                                    Data.Semigroup.Internal.Mk_Endo (GHC.Base.flip f)))
                                            t)) z
      end.

Local Definition Foldable__Arg_foldr' {inst_a}
   : forall {a} {b}, (a -> b -> b) -> b -> (Arg inst_a) a -> b :=
  fun {a} {b} =>
    fun arg_9__ arg_10__ arg_11__ =>
      match arg_9__, arg_10__, arg_11__ with
      | f, z0, xs =>
          let f' :=
            fun arg_12__ arg_13__ arg_14__ =>
              match arg_12__, arg_13__, arg_14__ with
              | k, x, z => k GHC.Base.$! f x z
              end in
          Foldable__Arg_foldl f' GHC.Base.id xs z0
      end.

Local Definition Foldable__Arg_foldr {inst_a}
   : forall {a} {b}, (a -> b -> b) -> b -> (Arg inst_a) a -> b :=
  fun {a} {b} =>
    fun arg_4__ arg_5__ arg_6__ =>
      match arg_4__, arg_5__, arg_6__ with
      | f, z, t =>
          Data.Semigroup.Internal.appEndo (Foldable__Arg_foldMap
                                           (Coq.Program.Basics.compose Data.Semigroup.Internal.Mk_Endo f) t) z
      end.

Local Definition Foldable__Arg_foldl' {inst_a}
   : forall {b} {a}, (b -> a -> b) -> b -> (Arg inst_a) a -> b :=
  fun {b} {a} =>
    fun arg_24__ arg_25__ arg_26__ =>
      match arg_24__, arg_25__, arg_26__ with
      | f, z0, xs =>
          let f' :=
            fun arg_27__ arg_28__ arg_29__ =>
              match arg_27__, arg_28__, arg_29__ with
              | x, k, z => k GHC.Base.$! f z x
              end in
          Foldable__Arg_foldr f' GHC.Base.id xs z0
      end.

Local Definition Foldable__Arg_length {inst_a}
   : forall {a}, (Arg inst_a) a -> GHC.Num.Int :=
  fun {a} =>
    Foldable__Arg_foldl' (fun arg_64__ arg_65__ =>
                            match arg_64__, arg_65__ with
                            | c, _ => c GHC.Num.+ #1
                            end) #0.

Local Definition Foldable__Arg_null {inst_a}
   : forall {a}, (Arg inst_a) a -> bool :=
  fun {a} => Foldable__Arg_foldr (fun arg_61__ arg_62__ => false) true.

Local Definition Foldable__Arg_toList {inst_a}
   : forall {a}, (Arg inst_a) a -> list a :=
  fun {a} =>
    fun arg_54__ =>
      let 't := arg_54__ in
      GHC.Base.build (fun _ arg_55__ arg_56__ =>
                        match arg_55__, arg_56__ with
                        | c, n => Foldable__Arg_foldr c n t
                        end).

Local Definition Foldable__Arg_product {inst_a}
   : forall {a}, forall `{GHC.Num.Num a}, (Arg inst_a) a -> a :=
  fun {a} `{GHC.Num.Num a} =>
    Coq.Program.Basics.compose Data.Semigroup.Internal.getProduct
                               (Foldable__Arg_foldMap Data.Semigroup.Internal.Mk_Product).

Local Definition Foldable__Arg_sum {inst_a}
   : forall {a}, forall `{GHC.Num.Num a}, (Arg inst_a) a -> a :=
  fun {a} `{GHC.Num.Num a} =>
    Coq.Program.Basics.compose Data.Semigroup.Internal.getSum (Foldable__Arg_foldMap
                                Data.Semigroup.Internal.Mk_Sum).

Local Definition Foldable__Arg_fold {inst_a}
   : forall {m}, forall `{GHC.Base.Monoid m}, (Arg inst_a) m -> m :=
  fun {m} `{GHC.Base.Monoid m} => Foldable__Arg_foldMap GHC.Base.id.

Local Definition Foldable__Arg_elem {inst_a}
   : forall {a}, forall `{GHC.Base.Eq_ a}, a -> (Arg inst_a) a -> bool :=
  fun {a} `{GHC.Base.Eq_ a} =>
    Coq.Program.Basics.compose (fun arg_69__ =>
                                  let 'p := arg_69__ in
                                  Coq.Program.Basics.compose Data.Semigroup.Internal.getAny (Foldable__Arg_foldMap
                                                              (Coq.Program.Basics.compose Data.Semigroup.Internal.Mk_Any
                                                                                          p))) _GHC.Base.==_.

Program Instance Foldable__Arg {a} : Data.Foldable.Foldable (Arg a) :=
  fun _ k =>
    k {| Data.Foldable.elem__ := fun {a} `{GHC.Base.Eq_ a} => Foldable__Arg_elem ;
         Data.Foldable.fold__ := fun {m} `{GHC.Base.Monoid m} => Foldable__Arg_fold ;
         Data.Foldable.foldMap__ := fun {m} {a} `{GHC.Base.Monoid m} =>
           Foldable__Arg_foldMap ;
         Data.Foldable.foldl__ := fun {b} {a} => Foldable__Arg_foldl ;
         Data.Foldable.foldl'__ := fun {b} {a} => Foldable__Arg_foldl' ;
         Data.Foldable.foldr__ := fun {a} {b} => Foldable__Arg_foldr ;
         Data.Foldable.foldr'__ := fun {a} {b} => Foldable__Arg_foldr' ;
         Data.Foldable.length__ := fun {a} => Foldable__Arg_length ;
         Data.Foldable.null__ := fun {a} => Foldable__Arg_null ;
         Data.Foldable.product__ := fun {a} `{GHC.Num.Num a} => Foldable__Arg_product ;
         Data.Foldable.sum__ := fun {a} `{GHC.Num.Num a} => Foldable__Arg_sum ;
         Data.Foldable.toList__ := fun {a} => Foldable__Arg_toList |}.

Local Definition Traversable__Arg_traverse {inst_a}
   : forall {f} {a} {b},
     forall `{GHC.Base.Applicative f},
     (a -> f b) -> (Arg inst_a) a -> f ((Arg inst_a) b) :=
  fun {f} {a} {b} `{GHC.Base.Applicative f} =>
    fun arg_0__ arg_1__ =>
      match arg_0__, arg_1__ with
      | f, Mk_Arg x a => Mk_Arg x Data.Functor.<$> f a
      end.

Local Definition Traversable__Arg_sequenceA {inst_a}
   : forall {f} {a},
     forall `{GHC.Base.Applicative f}, (Arg inst_a) (f a) -> f ((Arg inst_a) a) :=
  fun {f} {a} `{GHC.Base.Applicative f} => Traversable__Arg_traverse GHC.Base.id.

Local Definition Traversable__Arg_sequence {inst_a}
   : forall {m} {a},
     forall `{GHC.Base.Monad m}, (Arg inst_a) (m a) -> m ((Arg inst_a) a) :=
  fun {m} {a} `{GHC.Base.Monad m} => Traversable__Arg_sequenceA.

Local Definition Traversable__Arg_mapM {inst_a}
   : forall {m} {a} {b},
     forall `{GHC.Base.Monad m},
     (a -> m b) -> (Arg inst_a) a -> m ((Arg inst_a) b) :=
  fun {m} {a} {b} `{GHC.Base.Monad m} => Traversable__Arg_traverse.

Program Instance Traversable__Arg {a} : Data.Traversable.Traversable (Arg a) :=
  fun _ k =>
    k {| Data.Traversable.mapM__ := fun {m} {a} {b} `{GHC.Base.Monad m} =>
           Traversable__Arg_mapM ;
         Data.Traversable.sequence__ := fun {m} {a} `{GHC.Base.Monad m} =>
           Traversable__Arg_sequence ;
         Data.Traversable.sequenceA__ := fun {f} {a} `{GHC.Base.Applicative f} =>
           Traversable__Arg_sequenceA ;
         Data.Traversable.traverse__ := fun {f} {a} {b} `{GHC.Base.Applicative f} =>
           Traversable__Arg_traverse |}.

Local Definition Eq___Arg_op_zeze__ {inst_a} {inst_b} `{GHC.Base.Eq_ inst_a}
   : (Arg inst_a inst_b) -> (Arg inst_a inst_b) -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | Mk_Arg a _, Mk_Arg b _ => a GHC.Base.== b
    end.

Local Definition Eq___Arg_op_zsze__ {inst_a} {inst_b} `{GHC.Base.Eq_ inst_a}
   : (Arg inst_a inst_b) -> (Arg inst_a inst_b) -> bool :=
  fun x y => negb (Eq___Arg_op_zeze__ x y).

Program Instance Eq___Arg {a} {b} `{GHC.Base.Eq_ a} : GHC.Base.Eq_ (Arg a b) :=
  fun _ k =>
    k {| GHC.Base.op_zeze____ := Eq___Arg_op_zeze__ ;
         GHC.Base.op_zsze____ := Eq___Arg_op_zsze__ |}.

(* Skipping instance Ord__Arg *)

(* Translating `instance Bifunctor__Arg' failed: missing Qualified
   "Data.Bifunctor" "first" in fromList [(Qualified "Data.Bifunctor"
   "bimap",Qualified "Data.Semigroup" "Bifunctor__Arg_bimap")] unsupported *)

(* Translating `instance Bifoldable__Arg' failed: OOPS! Cannot find information
   for class Qualified "Data.Bifoldable" "Bifoldable" unsupported *)

(* Translating `instance Bitraversable__Arg' failed: OOPS! Cannot find
   information for class Qualified "Data.Bitraversable" "Bitraversable"
   unsupported *)

(* Translating `instance Enum__Max' failed: OOPS! Cannot find information for
   class Qualified "GHC.Enum" "Enum" unsupported *)

Local Definition Semigroup__Max_op_zlzlzgzg__ {inst_a} `{_
   : GHC.Base.Ord inst_a}
   : Max inst_a -> Max inst_a -> Max inst_a :=
  GHC.Prim.coerce (@GHC.Base.max inst_a _ _).

Program Instance Semigroup__Max {a} `{GHC.Base.Ord a}
   : GHC.Base.Semigroup (Max a) :=
  fun _ k => k {| GHC.Base.op_zlzlzgzg____ := Semigroup__Max_op_zlzlzgzg__ |}.

(* Skipping instance Monoid__Max *)

Local Definition Functor__Max_fmap
   : forall {a} {b}, (a -> b) -> Max a -> Max b :=
  fun {a} {b} =>
    fun arg_0__ arg_1__ =>
      match arg_0__, arg_1__ with
      | f, Mk_Max x => Mk_Max (f x)
      end.

Local Definition Functor__Max_op_zlzd__ : forall {a} {b}, a -> Max b -> Max a :=
  fun {a} {b} => fun x => Functor__Max_fmap (GHC.Base.const x).

Program Instance Functor__Max : GHC.Base.Functor Max :=
  fun _ k =>
    k {| GHC.Base.op_zlzd____ := fun {a} {b} => Functor__Max_op_zlzd__ ;
         GHC.Base.fmap__ := fun {a} {b} => Functor__Max_fmap |}.

Local Definition Foldable__Max_foldMap
   : forall {m} {a}, forall `{GHC.Base.Monoid m}, (a -> m) -> Max a -> m :=
  fun {m} {a} `{GHC.Base.Monoid m} =>
    fun arg_0__ arg_1__ => match arg_0__, arg_1__ with | f, Mk_Max a => f a end.

Local Definition Foldable__Max_foldl
   : forall {b} {a}, (b -> a -> b) -> b -> Max a -> b :=
  fun {b} {a} =>
    fun arg_19__ arg_20__ arg_21__ =>
      match arg_19__, arg_20__, arg_21__ with
      | f, z, t =>
          Data.Semigroup.Internal.appEndo (Data.Semigroup.Internal.getDual
                                           (Foldable__Max_foldMap (Coq.Program.Basics.compose
                                                                   Data.Semigroup.Internal.Mk_Dual
                                                                   (Coq.Program.Basics.compose
                                                                    Data.Semigroup.Internal.Mk_Endo (GHC.Base.flip f)))
                                            t)) z
      end.

Local Definition Foldable__Max_foldr'
   : forall {a} {b}, (a -> b -> b) -> b -> Max a -> b :=
  fun {a} {b} =>
    fun arg_9__ arg_10__ arg_11__ =>
      match arg_9__, arg_10__, arg_11__ with
      | f, z0, xs =>
          let f' :=
            fun arg_12__ arg_13__ arg_14__ =>
              match arg_12__, arg_13__, arg_14__ with
              | k, x, z => k GHC.Base.$! f x z
              end in
          Foldable__Max_foldl f' GHC.Base.id xs z0
      end.

Local Definition Foldable__Max_foldr
   : forall {a} {b}, (a -> b -> b) -> b -> Max a -> b :=
  fun {a} {b} =>
    fun arg_4__ arg_5__ arg_6__ =>
      match arg_4__, arg_5__, arg_6__ with
      | f, z, t =>
          Data.Semigroup.Internal.appEndo (Foldable__Max_foldMap
                                           (Coq.Program.Basics.compose Data.Semigroup.Internal.Mk_Endo f) t) z
      end.

Local Definition Foldable__Max_foldl'
   : forall {b} {a}, (b -> a -> b) -> b -> Max a -> b :=
  fun {b} {a} =>
    fun arg_24__ arg_25__ arg_26__ =>
      match arg_24__, arg_25__, arg_26__ with
      | f, z0, xs =>
          let f' :=
            fun arg_27__ arg_28__ arg_29__ =>
              match arg_27__, arg_28__, arg_29__ with
              | x, k, z => k GHC.Base.$! f z x
              end in
          Foldable__Max_foldr f' GHC.Base.id xs z0
      end.

Local Definition Foldable__Max_length : forall {a}, Max a -> GHC.Num.Int :=
  fun {a} =>
    Foldable__Max_foldl' (fun arg_64__ arg_65__ =>
                            match arg_64__, arg_65__ with
                            | c, _ => c GHC.Num.+ #1
                            end) #0.

Local Definition Foldable__Max_null : forall {a}, Max a -> bool :=
  fun {a} => Foldable__Max_foldr (fun arg_61__ arg_62__ => false) true.

Local Definition Foldable__Max_toList : forall {a}, Max a -> list a :=
  fun {a} =>
    fun arg_54__ =>
      let 't := arg_54__ in
      GHC.Base.build (fun _ arg_55__ arg_56__ =>
                        match arg_55__, arg_56__ with
                        | c, n => Foldable__Max_foldr c n t
                        end).

Local Definition Foldable__Max_product
   : forall {a}, forall `{GHC.Num.Num a}, Max a -> a :=
  fun {a} `{GHC.Num.Num a} =>
    Coq.Program.Basics.compose Data.Semigroup.Internal.getProduct
                               (Foldable__Max_foldMap Data.Semigroup.Internal.Mk_Product).

Local Definition Foldable__Max_sum
   : forall {a}, forall `{GHC.Num.Num a}, Max a -> a :=
  fun {a} `{GHC.Num.Num a} =>
    Coq.Program.Basics.compose Data.Semigroup.Internal.getSum (Foldable__Max_foldMap
                                Data.Semigroup.Internal.Mk_Sum).

Local Definition Foldable__Max_fold
   : forall {m}, forall `{GHC.Base.Monoid m}, Max m -> m :=
  fun {m} `{GHC.Base.Monoid m} => Foldable__Max_foldMap GHC.Base.id.

Local Definition Foldable__Max_elem
   : forall {a}, forall `{GHC.Base.Eq_ a}, a -> Max a -> bool :=
  fun {a} `{GHC.Base.Eq_ a} =>
    Coq.Program.Basics.compose (fun arg_69__ =>
                                  let 'p := arg_69__ in
                                  Coq.Program.Basics.compose Data.Semigroup.Internal.getAny (Foldable__Max_foldMap
                                                              (Coq.Program.Basics.compose Data.Semigroup.Internal.Mk_Any
                                                                                          p))) _GHC.Base.==_.

Program Instance Foldable__Max : Data.Foldable.Foldable Max :=
  fun _ k =>
    k {| Data.Foldable.elem__ := fun {a} `{GHC.Base.Eq_ a} => Foldable__Max_elem ;
         Data.Foldable.fold__ := fun {m} `{GHC.Base.Monoid m} => Foldable__Max_fold ;
         Data.Foldable.foldMap__ := fun {m} {a} `{GHC.Base.Monoid m} =>
           Foldable__Max_foldMap ;
         Data.Foldable.foldl__ := fun {b} {a} => Foldable__Max_foldl ;
         Data.Foldable.foldl'__ := fun {b} {a} => Foldable__Max_foldl' ;
         Data.Foldable.foldr__ := fun {a} {b} => Foldable__Max_foldr ;
         Data.Foldable.foldr'__ := fun {a} {b} => Foldable__Max_foldr' ;
         Data.Foldable.length__ := fun {a} => Foldable__Max_length ;
         Data.Foldable.null__ := fun {a} => Foldable__Max_null ;
         Data.Foldable.product__ := fun {a} `{GHC.Num.Num a} => Foldable__Max_product ;
         Data.Foldable.sum__ := fun {a} `{GHC.Num.Num a} => Foldable__Max_sum ;
         Data.Foldable.toList__ := fun {a} => Foldable__Max_toList |}.

Local Definition Traversable__Max_traverse
   : forall {f} {a} {b},
     forall `{GHC.Base.Applicative f}, (a -> f b) -> Max a -> f (Max b) :=
  fun {f} {a} {b} `{GHC.Base.Applicative f} =>
    fun arg_0__ arg_1__ =>
      match arg_0__, arg_1__ with
      | f, Mk_Max a => Mk_Max Data.Functor.<$> f a
      end.

Local Definition Traversable__Max_sequenceA
   : forall {f} {a}, forall `{GHC.Base.Applicative f}, Max (f a) -> f (Max a) :=
  fun {f} {a} `{GHC.Base.Applicative f} => Traversable__Max_traverse GHC.Base.id.

Local Definition Traversable__Max_sequence
   : forall {m} {a}, forall `{GHC.Base.Monad m}, Max (m a) -> m (Max a) :=
  fun {m} {a} `{GHC.Base.Monad m} => Traversable__Max_sequenceA.

Local Definition Traversable__Max_mapM
   : forall {m} {a} {b},
     forall `{GHC.Base.Monad m}, (a -> m b) -> Max a -> m (Max b) :=
  fun {m} {a} {b} `{GHC.Base.Monad m} => Traversable__Max_traverse.

Program Instance Traversable__Max : Data.Traversable.Traversable Max :=
  fun _ k =>
    k {| Data.Traversable.mapM__ := fun {m} {a} {b} `{GHC.Base.Monad m} =>
           Traversable__Max_mapM ;
         Data.Traversable.sequence__ := fun {m} {a} `{GHC.Base.Monad m} =>
           Traversable__Max_sequence ;
         Data.Traversable.sequenceA__ := fun {f} {a} `{GHC.Base.Applicative f} =>
           Traversable__Max_sequenceA ;
         Data.Traversable.traverse__ := fun {f} {a} {b} `{GHC.Base.Applicative f} =>
           Traversable__Max_traverse |}.

Local Definition Applicative__Max_liftA2
   : forall {a} {b} {c}, (a -> b -> c) -> Max a -> Max b -> Max c :=
  fun {a} {b} {c} => GHC.Prim.coerce.

Local Definition Applicative__Max_op_zlztzg__
   : forall {a} {b}, Max (a -> b) -> Max a -> Max b :=
  fun {a} {b} => GHC.Prim.coerce.

Local Definition Applicative__Max_op_ztzg__
   : forall {a} {b}, Max a -> Max b -> Max b :=
  fun {a} {b} =>
    fun arg_0__ arg_1__ => match arg_0__, arg_1__ with | _, a => a end.

Local Definition Applicative__Max_pure : forall {a}, a -> Max a :=
  fun {a} => Mk_Max.

Program Instance Applicative__Max : GHC.Base.Applicative Max :=
  fun _ k =>
    k {| GHC.Base.op_ztzg____ := fun {a} {b} => Applicative__Max_op_ztzg__ ;
         GHC.Base.op_zlztzg____ := fun {a} {b} => Applicative__Max_op_zlztzg__ ;
         GHC.Base.liftA2__ := fun {a} {b} {c} => Applicative__Max_liftA2 ;
         GHC.Base.pure__ := fun {a} => Applicative__Max_pure |}.

Local Definition Monad__Max_op_zgzg__
   : forall {a} {b}, Max a -> Max b -> Max b :=
  fun {a} {b} => _GHC.Base.*>_.

Local Definition Monad__Max_op_zgzgze__
   : forall {a} {b}, Max a -> (a -> Max b) -> Max b :=
  fun {a} {b} =>
    fun arg_0__ arg_1__ => match arg_0__, arg_1__ with | Mk_Max a, f => f a end.

Local Definition Monad__Max_return_ : forall {a}, a -> Max a :=
  fun {a} => GHC.Base.pure.

Program Instance Monad__Max : GHC.Base.Monad Max :=
  fun _ k =>
    k {| GHC.Base.op_zgzg____ := fun {a} {b} => Monad__Max_op_zgzg__ ;
         GHC.Base.op_zgzgze____ := fun {a} {b} => Monad__Max_op_zgzgze__ ;
         GHC.Base.return___ := fun {a} => Monad__Max_return_ |}.

(* Translating `instance MonadFix__Max' failed: OOPS! Cannot find information
   for class Qualified "Control.Monad.Fix" "MonadFix" unsupported *)

(* Translating `instance Num__Max' failed: OOPS! Cannot find information for
   class Qualified "GHC.Num" "Num" unsupported *)

(* Translating `instance Enum__Min' failed: OOPS! Cannot find information for
   class Qualified "GHC.Enum" "Enum" unsupported *)

Local Definition Semigroup__Min_op_zlzlzgzg__ {inst_a} `{_
   : GHC.Base.Ord inst_a}
   : Min inst_a -> Min inst_a -> Min inst_a :=
  GHC.Prim.coerce (@GHC.Base.min inst_a _ _).

Program Instance Semigroup__Min {a} `{GHC.Base.Ord a}
   : GHC.Base.Semigroup (Min a) :=
  fun _ k => k {| GHC.Base.op_zlzlzgzg____ := Semigroup__Min_op_zlzlzgzg__ |}.

(* Skipping instance Monoid__Min *)

Local Definition Functor__Min_fmap
   : forall {a} {b}, (a -> b) -> Min a -> Min b :=
  fun {a} {b} =>
    fun arg_0__ arg_1__ =>
      match arg_0__, arg_1__ with
      | f, Mk_Min x => Mk_Min (f x)
      end.

Local Definition Functor__Min_op_zlzd__ : forall {a} {b}, a -> Min b -> Min a :=
  fun {a} {b} => fun x => Functor__Min_fmap (GHC.Base.const x).

Program Instance Functor__Min : GHC.Base.Functor Min :=
  fun _ k =>
    k {| GHC.Base.op_zlzd____ := fun {a} {b} => Functor__Min_op_zlzd__ ;
         GHC.Base.fmap__ := fun {a} {b} => Functor__Min_fmap |}.

Local Definition Foldable__Min_foldMap
   : forall {m} {a}, forall `{GHC.Base.Monoid m}, (a -> m) -> Min a -> m :=
  fun {m} {a} `{GHC.Base.Monoid m} =>
    fun arg_0__ arg_1__ => match arg_0__, arg_1__ with | f, Mk_Min a => f a end.

Local Definition Foldable__Min_foldl
   : forall {b} {a}, (b -> a -> b) -> b -> Min a -> b :=
  fun {b} {a} =>
    fun arg_19__ arg_20__ arg_21__ =>
      match arg_19__, arg_20__, arg_21__ with
      | f, z, t =>
          Data.Semigroup.Internal.appEndo (Data.Semigroup.Internal.getDual
                                           (Foldable__Min_foldMap (Coq.Program.Basics.compose
                                                                   Data.Semigroup.Internal.Mk_Dual
                                                                   (Coq.Program.Basics.compose
                                                                    Data.Semigroup.Internal.Mk_Endo (GHC.Base.flip f)))
                                            t)) z
      end.

Local Definition Foldable__Min_foldr'
   : forall {a} {b}, (a -> b -> b) -> b -> Min a -> b :=
  fun {a} {b} =>
    fun arg_9__ arg_10__ arg_11__ =>
      match arg_9__, arg_10__, arg_11__ with
      | f, z0, xs =>
          let f' :=
            fun arg_12__ arg_13__ arg_14__ =>
              match arg_12__, arg_13__, arg_14__ with
              | k, x, z => k GHC.Base.$! f x z
              end in
          Foldable__Min_foldl f' GHC.Base.id xs z0
      end.

Local Definition Foldable__Min_foldr
   : forall {a} {b}, (a -> b -> b) -> b -> Min a -> b :=
  fun {a} {b} =>
    fun arg_4__ arg_5__ arg_6__ =>
      match arg_4__, arg_5__, arg_6__ with
      | f, z, t =>
          Data.Semigroup.Internal.appEndo (Foldable__Min_foldMap
                                           (Coq.Program.Basics.compose Data.Semigroup.Internal.Mk_Endo f) t) z
      end.

Local Definition Foldable__Min_foldl'
   : forall {b} {a}, (b -> a -> b) -> b -> Min a -> b :=
  fun {b} {a} =>
    fun arg_24__ arg_25__ arg_26__ =>
      match arg_24__, arg_25__, arg_26__ with
      | f, z0, xs =>
          let f' :=
            fun arg_27__ arg_28__ arg_29__ =>
              match arg_27__, arg_28__, arg_29__ with
              | x, k, z => k GHC.Base.$! f z x
              end in
          Foldable__Min_foldr f' GHC.Base.id xs z0
      end.

Local Definition Foldable__Min_length : forall {a}, Min a -> GHC.Num.Int :=
  fun {a} =>
    Foldable__Min_foldl' (fun arg_64__ arg_65__ =>
                            match arg_64__, arg_65__ with
                            | c, _ => c GHC.Num.+ #1
                            end) #0.

Local Definition Foldable__Min_null : forall {a}, Min a -> bool :=
  fun {a} => Foldable__Min_foldr (fun arg_61__ arg_62__ => false) true.

Local Definition Foldable__Min_toList : forall {a}, Min a -> list a :=
  fun {a} =>
    fun arg_54__ =>
      let 't := arg_54__ in
      GHC.Base.build (fun _ arg_55__ arg_56__ =>
                        match arg_55__, arg_56__ with
                        | c, n => Foldable__Min_foldr c n t
                        end).

Local Definition Foldable__Min_product
   : forall {a}, forall `{GHC.Num.Num a}, Min a -> a :=
  fun {a} `{GHC.Num.Num a} =>
    Coq.Program.Basics.compose Data.Semigroup.Internal.getProduct
                               (Foldable__Min_foldMap Data.Semigroup.Internal.Mk_Product).

Local Definition Foldable__Min_sum
   : forall {a}, forall `{GHC.Num.Num a}, Min a -> a :=
  fun {a} `{GHC.Num.Num a} =>
    Coq.Program.Basics.compose Data.Semigroup.Internal.getSum (Foldable__Min_foldMap
                                Data.Semigroup.Internal.Mk_Sum).

Local Definition Foldable__Min_fold
   : forall {m}, forall `{GHC.Base.Monoid m}, Min m -> m :=
  fun {m} `{GHC.Base.Monoid m} => Foldable__Min_foldMap GHC.Base.id.

Local Definition Foldable__Min_elem
   : forall {a}, forall `{GHC.Base.Eq_ a}, a -> Min a -> bool :=
  fun {a} `{GHC.Base.Eq_ a} =>
    Coq.Program.Basics.compose (fun arg_69__ =>
                                  let 'p := arg_69__ in
                                  Coq.Program.Basics.compose Data.Semigroup.Internal.getAny (Foldable__Min_foldMap
                                                              (Coq.Program.Basics.compose Data.Semigroup.Internal.Mk_Any
                                                                                          p))) _GHC.Base.==_.

Program Instance Foldable__Min : Data.Foldable.Foldable Min :=
  fun _ k =>
    k {| Data.Foldable.elem__ := fun {a} `{GHC.Base.Eq_ a} => Foldable__Min_elem ;
         Data.Foldable.fold__ := fun {m} `{GHC.Base.Monoid m} => Foldable__Min_fold ;
         Data.Foldable.foldMap__ := fun {m} {a} `{GHC.Base.Monoid m} =>
           Foldable__Min_foldMap ;
         Data.Foldable.foldl__ := fun {b} {a} => Foldable__Min_foldl ;
         Data.Foldable.foldl'__ := fun {b} {a} => Foldable__Min_foldl' ;
         Data.Foldable.foldr__ := fun {a} {b} => Foldable__Min_foldr ;
         Data.Foldable.foldr'__ := fun {a} {b} => Foldable__Min_foldr' ;
         Data.Foldable.length__ := fun {a} => Foldable__Min_length ;
         Data.Foldable.null__ := fun {a} => Foldable__Min_null ;
         Data.Foldable.product__ := fun {a} `{GHC.Num.Num a} => Foldable__Min_product ;
         Data.Foldable.sum__ := fun {a} `{GHC.Num.Num a} => Foldable__Min_sum ;
         Data.Foldable.toList__ := fun {a} => Foldable__Min_toList |}.

Local Definition Traversable__Min_traverse
   : forall {f} {a} {b},
     forall `{GHC.Base.Applicative f}, (a -> f b) -> Min a -> f (Min b) :=
  fun {f} {a} {b} `{GHC.Base.Applicative f} =>
    fun arg_0__ arg_1__ =>
      match arg_0__, arg_1__ with
      | f, Mk_Min a => Mk_Min Data.Functor.<$> f a
      end.

Local Definition Traversable__Min_sequenceA
   : forall {f} {a}, forall `{GHC.Base.Applicative f}, Min (f a) -> f (Min a) :=
  fun {f} {a} `{GHC.Base.Applicative f} => Traversable__Min_traverse GHC.Base.id.

Local Definition Traversable__Min_sequence
   : forall {m} {a}, forall `{GHC.Base.Monad m}, Min (m a) -> m (Min a) :=
  fun {m} {a} `{GHC.Base.Monad m} => Traversable__Min_sequenceA.

Local Definition Traversable__Min_mapM
   : forall {m} {a} {b},
     forall `{GHC.Base.Monad m}, (a -> m b) -> Min a -> m (Min b) :=
  fun {m} {a} {b} `{GHC.Base.Monad m} => Traversable__Min_traverse.

Program Instance Traversable__Min : Data.Traversable.Traversable Min :=
  fun _ k =>
    k {| Data.Traversable.mapM__ := fun {m} {a} {b} `{GHC.Base.Monad m} =>
           Traversable__Min_mapM ;
         Data.Traversable.sequence__ := fun {m} {a} `{GHC.Base.Monad m} =>
           Traversable__Min_sequence ;
         Data.Traversable.sequenceA__ := fun {f} {a} `{GHC.Base.Applicative f} =>
           Traversable__Min_sequenceA ;
         Data.Traversable.traverse__ := fun {f} {a} {b} `{GHC.Base.Applicative f} =>
           Traversable__Min_traverse |}.

Local Definition Applicative__Min_liftA2
   : forall {a} {b} {c}, (a -> b -> c) -> Min a -> Min b -> Min c :=
  fun {a} {b} {c} => GHC.Prim.coerce.

Local Definition Applicative__Min_op_zlztzg__
   : forall {a} {b}, Min (a -> b) -> Min a -> Min b :=
  fun {a} {b} => GHC.Prim.coerce.

Local Definition Applicative__Min_op_ztzg__
   : forall {a} {b}, Min a -> Min b -> Min b :=
  fun {a} {b} =>
    fun arg_0__ arg_1__ => match arg_0__, arg_1__ with | _, a => a end.

Local Definition Applicative__Min_pure : forall {a}, a -> Min a :=
  fun {a} => Mk_Min.

Program Instance Applicative__Min : GHC.Base.Applicative Min :=
  fun _ k =>
    k {| GHC.Base.op_ztzg____ := fun {a} {b} => Applicative__Min_op_ztzg__ ;
         GHC.Base.op_zlztzg____ := fun {a} {b} => Applicative__Min_op_zlztzg__ ;
         GHC.Base.liftA2__ := fun {a} {b} {c} => Applicative__Min_liftA2 ;
         GHC.Base.pure__ := fun {a} => Applicative__Min_pure |}.

Local Definition Monad__Min_op_zgzg__
   : forall {a} {b}, Min a -> Min b -> Min b :=
  fun {a} {b} => _GHC.Base.*>_.

Local Definition Monad__Min_op_zgzgze__
   : forall {a} {b}, Min a -> (a -> Min b) -> Min b :=
  fun {a} {b} =>
    fun arg_0__ arg_1__ => match arg_0__, arg_1__ with | Mk_Min a, f => f a end.

Local Definition Monad__Min_return_ : forall {a}, a -> Min a :=
  fun {a} => GHC.Base.pure.

Program Instance Monad__Min : GHC.Base.Monad Min :=
  fun _ k =>
    k {| GHC.Base.op_zgzg____ := fun {a} {b} => Monad__Min_op_zgzg__ ;
         GHC.Base.op_zgzgze____ := fun {a} {b} => Monad__Min_op_zgzgze__ ;
         GHC.Base.return___ := fun {a} => Monad__Min_return_ |}.

(* Translating `instance MonadFix__Min' failed: OOPS! Cannot find information
   for class Qualified "Control.Monad.Fix" "MonadFix" unsupported *)

(* Translating `instance Num__Min' failed: OOPS! Cannot find information for
   class Qualified "GHC.Num" "Num" unsupported *)

(* Translating `instance Generic1__TYPE__Option__LiftedRep' failed: type class
   instance head:App (App (Qualid (Qualified "GHC.Generics" "Generic1")) (PosArg
   (App (Qualid (Qualified "GHC.Prim" "TYPE")) (PosArg (Qualid (Qualified
   "GHC.Types" "LiftedRep")) :| [])) :| [])) (PosArg (Qualid (Qualified
   "Data.Semigroup" "Option")) :| []) unsupported *)

(* Translating `instance Generic__Option' failed: OOPS! Cannot find information
   for class Qualified "GHC.Generics" "Generic" unsupported *)

(* Translating `instance Data__Option' failed: OOPS! Cannot find information for
   class Qualified "Data.Data" "Data" unsupported *)

(* Translating `instance Read__Option' failed: OOPS! Cannot find information for
   class Qualified "GHC.Read" "Read" unsupported *)

(* Translating `instance Show__Option' failed: OOPS! Cannot find information for
   class Qualified "GHC.Show" "Show" unsupported *)

Local Definition Ord__Option_compare {inst_a} `{GHC.Base.Ord inst_a}
   : Option inst_a -> Option inst_a -> comparison :=
  GHC.Prim.coerce GHC.Base.compare.

Local Definition Ord__Option_max {inst_a} `{GHC.Base.Ord inst_a}
   : Option inst_a -> Option inst_a -> Option inst_a :=
  GHC.Prim.coerce GHC.Base.max.

Local Definition Ord__Option_min {inst_a} `{GHC.Base.Ord inst_a}
   : Option inst_a -> Option inst_a -> Option inst_a :=
  GHC.Prim.coerce GHC.Base.min.

Local Definition Ord__Option_op_zg__ {inst_a} `{GHC.Base.Ord inst_a}
   : Option inst_a -> Option inst_a -> bool :=
  GHC.Prim.coerce _GHC.Base.>_.

Local Definition Ord__Option_op_zgze__ {inst_a} `{GHC.Base.Ord inst_a}
   : Option inst_a -> Option inst_a -> bool :=
  GHC.Prim.coerce _GHC.Base.>=_.

Local Definition Ord__Option_op_zl__ {inst_a} `{GHC.Base.Ord inst_a}
   : Option inst_a -> Option inst_a -> bool :=
  GHC.Prim.coerce _GHC.Base.<_.

Local Definition Ord__Option_op_zlze__ {inst_a} `{GHC.Base.Ord inst_a}
   : Option inst_a -> Option inst_a -> bool :=
  GHC.Prim.coerce _GHC.Base.<=_.

Local Definition Eq___Option_op_zeze__ {inst_a} `{GHC.Base.Eq_ inst_a}
   : Option inst_a -> Option inst_a -> bool :=
  GHC.Prim.coerce _GHC.Base.==_.

Local Definition Eq___Option_op_zsze__ {inst_a} `{GHC.Base.Eq_ inst_a}
   : Option inst_a -> Option inst_a -> bool :=
  GHC.Prim.coerce _GHC.Base./=_.

Program Instance Eq___Option {a} `{GHC.Base.Eq_ a} : GHC.Base.Eq_ (Option a) :=
  fun _ k =>
    k {| GHC.Base.op_zeze____ := Eq___Option_op_zeze__ ;
         GHC.Base.op_zsze____ := Eq___Option_op_zsze__ |}.

Program Instance Ord__Option {a} `{GHC.Base.Ord a} : GHC.Base.Ord (Option a) :=
  fun _ k =>
    k {| GHC.Base.op_zl____ := Ord__Option_op_zl__ ;
         GHC.Base.op_zlze____ := Ord__Option_op_zlze__ ;
         GHC.Base.op_zg____ := Ord__Option_op_zg__ ;
         GHC.Base.op_zgze____ := Ord__Option_op_zgze__ ;
         GHC.Base.compare__ := Ord__Option_compare ;
         GHC.Base.max__ := Ord__Option_max ;
         GHC.Base.min__ := Ord__Option_min |}.

(* Translating `instance Generic1__TYPE__WrappedMonoid__LiftedRep' failed: type
   class instance head:App (App (Qualid (Qualified "GHC.Generics" "Generic1"))
   (PosArg (App (Qualid (Qualified "GHC.Prim" "TYPE")) (PosArg (Qualid (Qualified
   "GHC.Types" "LiftedRep")) :| [])) :| [])) (PosArg (Qualid (Qualified
   "Data.Semigroup" "WrappedMonoid")) :| []) unsupported *)

(* Translating `instance Generic__WrappedMonoid' failed: OOPS! Cannot find
   information for class Qualified "GHC.Generics" "Generic" unsupported *)

(* Translating `instance Data__WrappedMonoid' failed: OOPS! Cannot find
   information for class Qualified "Data.Data" "Data" unsupported *)

(* Translating `instance Read__WrappedMonoid' failed: OOPS! Cannot find
   information for class Qualified "GHC.Read" "Read" unsupported *)

(* Translating `instance Show__WrappedMonoid' failed: OOPS! Cannot find
   information for class Qualified "GHC.Show" "Show" unsupported *)

Local Definition Ord__WrappedMonoid_compare {inst_m} `{GHC.Base.Ord inst_m}
   : WrappedMonoid inst_m -> WrappedMonoid inst_m -> comparison :=
  GHC.Prim.coerce GHC.Base.compare.

Local Definition Ord__WrappedMonoid_max {inst_m} `{GHC.Base.Ord inst_m}
   : WrappedMonoid inst_m -> WrappedMonoid inst_m -> WrappedMonoid inst_m :=
  GHC.Prim.coerce GHC.Base.max.

Local Definition Ord__WrappedMonoid_min {inst_m} `{GHC.Base.Ord inst_m}
   : WrappedMonoid inst_m -> WrappedMonoid inst_m -> WrappedMonoid inst_m :=
  GHC.Prim.coerce GHC.Base.min.

Local Definition Ord__WrappedMonoid_op_zg__ {inst_m} `{GHC.Base.Ord inst_m}
   : WrappedMonoid inst_m -> WrappedMonoid inst_m -> bool :=
  GHC.Prim.coerce _GHC.Base.>_.

Local Definition Ord__WrappedMonoid_op_zgze__ {inst_m} `{GHC.Base.Ord inst_m}
   : WrappedMonoid inst_m -> WrappedMonoid inst_m -> bool :=
  GHC.Prim.coerce _GHC.Base.>=_.

Local Definition Ord__WrappedMonoid_op_zl__ {inst_m} `{GHC.Base.Ord inst_m}
   : WrappedMonoid inst_m -> WrappedMonoid inst_m -> bool :=
  GHC.Prim.coerce _GHC.Base.<_.

Local Definition Ord__WrappedMonoid_op_zlze__ {inst_m} `{GHC.Base.Ord inst_m}
   : WrappedMonoid inst_m -> WrappedMonoid inst_m -> bool :=
  GHC.Prim.coerce _GHC.Base.<=_.

Local Definition Eq___WrappedMonoid_op_zeze__ {inst_m} `{GHC.Base.Eq_ inst_m}
   : WrappedMonoid inst_m -> WrappedMonoid inst_m -> bool :=
  GHC.Prim.coerce _GHC.Base.==_.

Local Definition Eq___WrappedMonoid_op_zsze__ {inst_m} `{GHC.Base.Eq_ inst_m}
   : WrappedMonoid inst_m -> WrappedMonoid inst_m -> bool :=
  GHC.Prim.coerce _GHC.Base./=_.

Program Instance Eq___WrappedMonoid {m} `{GHC.Base.Eq_ m}
   : GHC.Base.Eq_ (WrappedMonoid m) :=
  fun _ k =>
    k {| GHC.Base.op_zeze____ := Eq___WrappedMonoid_op_zeze__ ;
         GHC.Base.op_zsze____ := Eq___WrappedMonoid_op_zsze__ |}.

Program Instance Ord__WrappedMonoid {m} `{GHC.Base.Ord m}
   : GHC.Base.Ord (WrappedMonoid m) :=
  fun _ k =>
    k {| GHC.Base.op_zl____ := Ord__WrappedMonoid_op_zl__ ;
         GHC.Base.op_zlze____ := Ord__WrappedMonoid_op_zlze__ ;
         GHC.Base.op_zg____ := Ord__WrappedMonoid_op_zg__ ;
         GHC.Base.op_zgze____ := Ord__WrappedMonoid_op_zgze__ ;
         GHC.Base.compare__ := Ord__WrappedMonoid_compare ;
         GHC.Base.max__ := Ord__WrappedMonoid_max ;
         GHC.Base.min__ := Ord__WrappedMonoid_min |}.

(* Translating `instance Bounded__WrappedMonoid' failed: OOPS! Cannot find
   information for class Qualified "GHC.Enum" "Bounded" unsupported *)

(* Translating `instance Generic1__TYPE__Last__LiftedRep' failed: type class
   instance head:App (App (Qualid (Qualified "GHC.Generics" "Generic1")) (PosArg
   (App (Qualid (Qualified "GHC.Prim" "TYPE")) (PosArg (Qualid (Qualified
   "GHC.Types" "LiftedRep")) :| [])) :| [])) (PosArg (Qualid (Qualified
   "Data.Semigroup" "Last")) :| []) unsupported *)

(* Translating `instance Generic__Last' failed: OOPS! Cannot find information
   for class Qualified "GHC.Generics" "Generic" unsupported *)

(* Translating `instance Data__Last' failed: OOPS! Cannot find information for
   class Qualified "Data.Data" "Data" unsupported *)

(* Translating `instance Read__Last' failed: OOPS! Cannot find information for
   class Qualified "GHC.Read" "Read" unsupported *)

(* Translating `instance Show__Last' failed: OOPS! Cannot find information for
   class Qualified "GHC.Show" "Show" unsupported *)

Local Definition Ord__Last_compare {inst_a} `{GHC.Base.Ord inst_a}
   : Last inst_a -> Last inst_a -> comparison :=
  GHC.Prim.coerce GHC.Base.compare.

Local Definition Ord__Last_max {inst_a} `{GHC.Base.Ord inst_a}
   : Last inst_a -> Last inst_a -> Last inst_a :=
  GHC.Prim.coerce GHC.Base.max.

Local Definition Ord__Last_min {inst_a} `{GHC.Base.Ord inst_a}
   : Last inst_a -> Last inst_a -> Last inst_a :=
  GHC.Prim.coerce GHC.Base.min.

Local Definition Ord__Last_op_zg__ {inst_a} `{GHC.Base.Ord inst_a}
   : Last inst_a -> Last inst_a -> bool :=
  GHC.Prim.coerce _GHC.Base.>_.

Local Definition Ord__Last_op_zgze__ {inst_a} `{GHC.Base.Ord inst_a}
   : Last inst_a -> Last inst_a -> bool :=
  GHC.Prim.coerce _GHC.Base.>=_.

Local Definition Ord__Last_op_zl__ {inst_a} `{GHC.Base.Ord inst_a}
   : Last inst_a -> Last inst_a -> bool :=
  GHC.Prim.coerce _GHC.Base.<_.

Local Definition Ord__Last_op_zlze__ {inst_a} `{GHC.Base.Ord inst_a}
   : Last inst_a -> Last inst_a -> bool :=
  GHC.Prim.coerce _GHC.Base.<=_.

Local Definition Eq___Last_op_zeze__ {inst_a} `{GHC.Base.Eq_ inst_a}
   : Last inst_a -> Last inst_a -> bool :=
  GHC.Prim.coerce _GHC.Base.==_.

Local Definition Eq___Last_op_zsze__ {inst_a} `{GHC.Base.Eq_ inst_a}
   : Last inst_a -> Last inst_a -> bool :=
  GHC.Prim.coerce _GHC.Base./=_.

Program Instance Eq___Last {a} `{GHC.Base.Eq_ a} : GHC.Base.Eq_ (Last a) :=
  fun _ k =>
    k {| GHC.Base.op_zeze____ := Eq___Last_op_zeze__ ;
         GHC.Base.op_zsze____ := Eq___Last_op_zsze__ |}.

Program Instance Ord__Last {a} `{GHC.Base.Ord a} : GHC.Base.Ord (Last a) :=
  fun _ k =>
    k {| GHC.Base.op_zl____ := Ord__Last_op_zl__ ;
         GHC.Base.op_zlze____ := Ord__Last_op_zlze__ ;
         GHC.Base.op_zg____ := Ord__Last_op_zg__ ;
         GHC.Base.op_zgze____ := Ord__Last_op_zgze__ ;
         GHC.Base.compare__ := Ord__Last_compare ;
         GHC.Base.max__ := Ord__Last_max ;
         GHC.Base.min__ := Ord__Last_min |}.

(* Translating `instance Bounded__Last' failed: OOPS! Cannot find information
   for class Qualified "GHC.Enum" "Bounded" unsupported *)

(* Translating `instance Generic1__TYPE__First__LiftedRep' failed: type class
   instance head:App (App (Qualid (Qualified "GHC.Generics" "Generic1")) (PosArg
   (App (Qualid (Qualified "GHC.Prim" "TYPE")) (PosArg (Qualid (Qualified
   "GHC.Types" "LiftedRep")) :| [])) :| [])) (PosArg (Qualid (Qualified
   "Data.Semigroup" "First")) :| []) unsupported *)

(* Translating `instance Generic__First' failed: OOPS! Cannot find information
   for class Qualified "GHC.Generics" "Generic" unsupported *)

(* Translating `instance Data__First' failed: OOPS! Cannot find information for
   class Qualified "Data.Data" "Data" unsupported *)

(* Translating `instance Read__First' failed: OOPS! Cannot find information for
   class Qualified "GHC.Read" "Read" unsupported *)

(* Translating `instance Show__First' failed: OOPS! Cannot find information for
   class Qualified "GHC.Show" "Show" unsupported *)

Local Definition Ord__First_compare {inst_a} `{GHC.Base.Ord inst_a}
   : First inst_a -> First inst_a -> comparison :=
  GHC.Prim.coerce GHC.Base.compare.

Local Definition Ord__First_max {inst_a} `{GHC.Base.Ord inst_a}
   : First inst_a -> First inst_a -> First inst_a :=
  GHC.Prim.coerce GHC.Base.max.

Local Definition Ord__First_min {inst_a} `{GHC.Base.Ord inst_a}
   : First inst_a -> First inst_a -> First inst_a :=
  GHC.Prim.coerce GHC.Base.min.

Local Definition Ord__First_op_zg__ {inst_a} `{GHC.Base.Ord inst_a}
   : First inst_a -> First inst_a -> bool :=
  GHC.Prim.coerce _GHC.Base.>_.

Local Definition Ord__First_op_zgze__ {inst_a} `{GHC.Base.Ord inst_a}
   : First inst_a -> First inst_a -> bool :=
  GHC.Prim.coerce _GHC.Base.>=_.

Local Definition Ord__First_op_zl__ {inst_a} `{GHC.Base.Ord inst_a}
   : First inst_a -> First inst_a -> bool :=
  GHC.Prim.coerce _GHC.Base.<_.

Local Definition Ord__First_op_zlze__ {inst_a} `{GHC.Base.Ord inst_a}
   : First inst_a -> First inst_a -> bool :=
  GHC.Prim.coerce _GHC.Base.<=_.

Local Definition Eq___First_op_zeze__ {inst_a} `{GHC.Base.Eq_ inst_a}
   : First inst_a -> First inst_a -> bool :=
  GHC.Prim.coerce _GHC.Base.==_.

Local Definition Eq___First_op_zsze__ {inst_a} `{GHC.Base.Eq_ inst_a}
   : First inst_a -> First inst_a -> bool :=
  GHC.Prim.coerce _GHC.Base./=_.

Program Instance Eq___First {a} `{GHC.Base.Eq_ a} : GHC.Base.Eq_ (First a) :=
  fun _ k =>
    k {| GHC.Base.op_zeze____ := Eq___First_op_zeze__ ;
         GHC.Base.op_zsze____ := Eq___First_op_zsze__ |}.

Program Instance Ord__First {a} `{GHC.Base.Ord a} : GHC.Base.Ord (First a) :=
  fun _ k =>
    k {| GHC.Base.op_zl____ := Ord__First_op_zl__ ;
         GHC.Base.op_zlze____ := Ord__First_op_zlze__ ;
         GHC.Base.op_zg____ := Ord__First_op_zg__ ;
         GHC.Base.op_zgze____ := Ord__First_op_zgze__ ;
         GHC.Base.compare__ := Ord__First_compare ;
         GHC.Base.max__ := Ord__First_max ;
         GHC.Base.min__ := Ord__First_min |}.

(* Translating `instance Bounded__First' failed: OOPS! Cannot find information
   for class Qualified "GHC.Enum" "Bounded" unsupported *)

(* Translating `instance Generic1__TYPE__Arg__LiftedRep' failed: type class
   instance head:App (App (Qualid (Qualified "GHC.Generics" "Generic1")) (PosArg
   (App (Qualid (Qualified "GHC.Prim" "TYPE")) (PosArg (Qualid (Qualified
   "GHC.Types" "LiftedRep")) :| [])) :| [])) (PosArg (App (Qualid (Qualified
   "Data.Semigroup" "Arg")) (PosArg (Qualid (Bare "a")) :| [])) :| [])
   unsupported *)

(* Translating `instance Generic__Arg' failed: OOPS! Cannot find information for
   class Qualified "GHC.Generics" "Generic" unsupported *)

(* Translating `instance Data__Arg' failed: OOPS! Cannot find information for
   class Qualified "Data.Data" "Data" unsupported *)

(* Translating `instance Read__Arg' failed: OOPS! Cannot find information for
   class Qualified "GHC.Read" "Read" unsupported *)

(* Translating `instance Show__Arg' failed: OOPS! Cannot find information for
   class Qualified "GHC.Show" "Show" unsupported *)

(* Translating `instance Generic1__TYPE__Max__LiftedRep' failed: type class
   instance head:App (App (Qualid (Qualified "GHC.Generics" "Generic1")) (PosArg
   (App (Qualid (Qualified "GHC.Prim" "TYPE")) (PosArg (Qualid (Qualified
   "GHC.Types" "LiftedRep")) :| [])) :| [])) (PosArg (Qualid (Qualified
   "Data.Semigroup" "Max")) :| []) unsupported *)

(* Translating `instance Generic__Max' failed: OOPS! Cannot find information for
   class Qualified "GHC.Generics" "Generic" unsupported *)

(* Translating `instance Data__Max' failed: OOPS! Cannot find information for
   class Qualified "Data.Data" "Data" unsupported *)

(* Translating `instance Read__Max' failed: OOPS! Cannot find information for
   class Qualified "GHC.Read" "Read" unsupported *)

(* Translating `instance Show__Max' failed: OOPS! Cannot find information for
   class Qualified "GHC.Show" "Show" unsupported *)

Local Definition Ord__Max_compare {inst_a} `{GHC.Base.Ord inst_a}
   : Max inst_a -> Max inst_a -> comparison :=
  GHC.Prim.coerce GHC.Base.compare.

Local Definition Ord__Max_max {inst_a} `{GHC.Base.Ord inst_a}
   : Max inst_a -> Max inst_a -> Max inst_a :=
  GHC.Prim.coerce GHC.Base.max.

Local Definition Ord__Max_min {inst_a} `{GHC.Base.Ord inst_a}
   : Max inst_a -> Max inst_a -> Max inst_a :=
  GHC.Prim.coerce GHC.Base.min.

Local Definition Ord__Max_op_zg__ {inst_a} `{GHC.Base.Ord inst_a}
   : Max inst_a -> Max inst_a -> bool :=
  GHC.Prim.coerce _GHC.Base.>_.

Local Definition Ord__Max_op_zgze__ {inst_a} `{GHC.Base.Ord inst_a}
   : Max inst_a -> Max inst_a -> bool :=
  GHC.Prim.coerce _GHC.Base.>=_.

Local Definition Ord__Max_op_zl__ {inst_a} `{GHC.Base.Ord inst_a}
   : Max inst_a -> Max inst_a -> bool :=
  GHC.Prim.coerce _GHC.Base.<_.

Local Definition Ord__Max_op_zlze__ {inst_a} `{GHC.Base.Ord inst_a}
   : Max inst_a -> Max inst_a -> bool :=
  GHC.Prim.coerce _GHC.Base.<=_.

Local Definition Eq___Max_op_zeze__ {inst_a} `{GHC.Base.Eq_ inst_a}
   : Max inst_a -> Max inst_a -> bool :=
  GHC.Prim.coerce _GHC.Base.==_.

Local Definition Eq___Max_op_zsze__ {inst_a} `{GHC.Base.Eq_ inst_a}
   : Max inst_a -> Max inst_a -> bool :=
  GHC.Prim.coerce _GHC.Base./=_.

Program Instance Eq___Max {a} `{GHC.Base.Eq_ a} : GHC.Base.Eq_ (Max a) :=
  fun _ k =>
    k {| GHC.Base.op_zeze____ := Eq___Max_op_zeze__ ;
         GHC.Base.op_zsze____ := Eq___Max_op_zsze__ |}.

Program Instance Ord__Max {a} `{GHC.Base.Ord a} : GHC.Base.Ord (Max a) :=
  fun _ k =>
    k {| GHC.Base.op_zl____ := Ord__Max_op_zl__ ;
         GHC.Base.op_zlze____ := Ord__Max_op_zlze__ ;
         GHC.Base.op_zg____ := Ord__Max_op_zg__ ;
         GHC.Base.op_zgze____ := Ord__Max_op_zgze__ ;
         GHC.Base.compare__ := Ord__Max_compare ;
         GHC.Base.max__ := Ord__Max_max ;
         GHC.Base.min__ := Ord__Max_min |}.

(* Translating `instance Bounded__Max' failed: OOPS! Cannot find information for
   class Qualified "GHC.Enum" "Bounded" unsupported *)

(* Translating `instance Generic1__TYPE__Min__LiftedRep' failed: type class
   instance head:App (App (Qualid (Qualified "GHC.Generics" "Generic1")) (PosArg
   (App (Qualid (Qualified "GHC.Prim" "TYPE")) (PosArg (Qualid (Qualified
   "GHC.Types" "LiftedRep")) :| [])) :| [])) (PosArg (Qualid (Qualified
   "Data.Semigroup" "Min")) :| []) unsupported *)

(* Translating `instance Generic__Min' failed: OOPS! Cannot find information for
   class Qualified "GHC.Generics" "Generic" unsupported *)

(* Translating `instance Data__Min' failed: OOPS! Cannot find information for
   class Qualified "Data.Data" "Data" unsupported *)

(* Translating `instance Read__Min' failed: OOPS! Cannot find information for
   class Qualified "GHC.Read" "Read" unsupported *)

(* Translating `instance Show__Min' failed: OOPS! Cannot find information for
   class Qualified "GHC.Show" "Show" unsupported *)

Local Definition Ord__Min_compare {inst_a} `{GHC.Base.Ord inst_a}
   : Min inst_a -> Min inst_a -> comparison :=
  GHC.Prim.coerce GHC.Base.compare.

Local Definition Ord__Min_max {inst_a} `{GHC.Base.Ord inst_a}
   : Min inst_a -> Min inst_a -> Min inst_a :=
  GHC.Prim.coerce GHC.Base.max.

Local Definition Ord__Min_min {inst_a} `{GHC.Base.Ord inst_a}
   : Min inst_a -> Min inst_a -> Min inst_a :=
  GHC.Prim.coerce GHC.Base.min.

Local Definition Ord__Min_op_zg__ {inst_a} `{GHC.Base.Ord inst_a}
   : Min inst_a -> Min inst_a -> bool :=
  GHC.Prim.coerce _GHC.Base.>_.

Local Definition Ord__Min_op_zgze__ {inst_a} `{GHC.Base.Ord inst_a}
   : Min inst_a -> Min inst_a -> bool :=
  GHC.Prim.coerce _GHC.Base.>=_.

Local Definition Ord__Min_op_zl__ {inst_a} `{GHC.Base.Ord inst_a}
   : Min inst_a -> Min inst_a -> bool :=
  GHC.Prim.coerce _GHC.Base.<_.

Local Definition Ord__Min_op_zlze__ {inst_a} `{GHC.Base.Ord inst_a}
   : Min inst_a -> Min inst_a -> bool :=
  GHC.Prim.coerce _GHC.Base.<=_.

Local Definition Eq___Min_op_zeze__ {inst_a} `{GHC.Base.Eq_ inst_a}
   : Min inst_a -> Min inst_a -> bool :=
  GHC.Prim.coerce _GHC.Base.==_.

Local Definition Eq___Min_op_zsze__ {inst_a} `{GHC.Base.Eq_ inst_a}
   : Min inst_a -> Min inst_a -> bool :=
  GHC.Prim.coerce _GHC.Base./=_.

Program Instance Eq___Min {a} `{GHC.Base.Eq_ a} : GHC.Base.Eq_ (Min a) :=
  fun _ k =>
    k {| GHC.Base.op_zeze____ := Eq___Min_op_zeze__ ;
         GHC.Base.op_zsze____ := Eq___Min_op_zsze__ |}.

Program Instance Ord__Min {a} `{GHC.Base.Ord a} : GHC.Base.Ord (Min a) :=
  fun _ k =>
    k {| GHC.Base.op_zl____ := Ord__Min_op_zl__ ;
         GHC.Base.op_zlze____ := Ord__Min_op_zlze__ ;
         GHC.Base.op_zg____ := Ord__Min_op_zg__ ;
         GHC.Base.op_zgze____ := Ord__Min_op_zgze__ ;
         GHC.Base.compare__ := Ord__Min_compare ;
         GHC.Base.max__ := Ord__Min_max ;
         GHC.Base.min__ := Ord__Min_min |}.

(* Translating `instance Bounded__Min' failed: OOPS! Cannot find information for
   class Qualified "GHC.Enum" "Bounded" unsupported *)

Definition destruct_option {b} {a} : b -> (a -> b) -> Option a -> b :=
  fun arg_0__ arg_1__ arg_2__ =>
    match arg_0__, arg_1__, arg_2__ with
    | n, j, Mk_Option m => Data.Maybe.maybe n j m
    end.

Definition diff {m} `{GHC.Base.Semigroup m}
   : m -> Data.Semigroup.Internal.Endo m :=
  Data.Semigroup.Internal.Mk_Endo GHC.Base.∘ _GHC.Base.<<>>_.

(* Unbound variables:
     None Some bool comparison false list negb option true Coq.Program.Basics.compose
     Data.Foldable.Foldable Data.Functor.op_zlzdzg__ Data.Maybe.maybe
     Data.Semigroup.Internal.Endo Data.Semigroup.Internal.Mk_Any
     Data.Semigroup.Internal.Mk_Dual Data.Semigroup.Internal.Mk_Endo
     Data.Semigroup.Internal.Mk_Product Data.Semigroup.Internal.Mk_Sum
     Data.Semigroup.Internal.appEndo Data.Semigroup.Internal.getAny
     Data.Semigroup.Internal.getDual Data.Semigroup.Internal.getProduct
     Data.Semigroup.Internal.getSum Data.Traversable.Traversable GHC.Base.Applicative
     GHC.Base.Eq_ GHC.Base.Functor GHC.Base.Monad GHC.Base.Monoid GHC.Base.Ord
     GHC.Base.Semigroup GHC.Base.build GHC.Base.compare GHC.Base.const GHC.Base.flip
     GHC.Base.fmap GHC.Base.foldr GHC.Base.id GHC.Base.liftA2 GHC.Base.mappend
     GHC.Base.max GHC.Base.mempty GHC.Base.min GHC.Base.op_z2218U__
     GHC.Base.op_zdzn__ GHC.Base.op_zeze__ GHC.Base.op_zg__ GHC.Base.op_zgze__
     GHC.Base.op_zl__ GHC.Base.op_zlze__ GHC.Base.op_zlzlzgzg__ GHC.Base.op_zlztzg__
     GHC.Base.op_zsze__ GHC.Base.op_ztzg__ GHC.Base.pure GHC.Num.Int GHC.Num.Num
     GHC.Num.fromInteger GHC.Num.op_zp__ GHC.Prim.Build_Unpeel GHC.Prim.Unpeel
     GHC.Prim.coerce
*)
