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
Require Data.Traversable.
Require GHC.Base.
Require GHC.Num.
Require GHC.Prim.

(* Converted type declarations: *)

Inductive Identity a : Type := Mk_Identity : a -> Identity a.

Arguments Mk_Identity {_} _.

Definition runIdentity {a} (arg_0__ : Identity a) :=
  match arg_0__ with
    | Mk_Identity runIdentity => runIdentity
  end.
(* Midamble *)

Instance Unpeel_Identity a : Prim.Unpeel (Identity a) a :=
 Prim.Build_Unpeel _ _  (fun arg => match arg with | Mk_Identity x => x end) Mk_Identity.

(* Converted value declarations: *)

(* Translating `instance forall {a}, forall `{(GHC.Read.Read a)}, GHC.Read.Read
   (Identity a)' failed: OOPS! Cannot find information for class "GHC.Read.Read"
   unsupported *)

(* Translating `instance forall {a}, forall `{(GHC.Show.Show a)}, GHC.Show.Show
   (Identity a)' failed: OOPS! Cannot find information for class "GHC.Show.Show"
   unsupported *)

Local Definition instance_Data_Foldable_Foldable_Identity_foldMap : forall {m}
                                                                           {a},
                                                                      forall `{GHC.Base.Monoid m},
                                                                        (a -> m) -> Identity a -> m :=
  fun {m} {a} `{GHC.Base.Monoid m} => GHC.Prim.coerce.

Local Definition instance_Data_Foldable_Foldable_Identity_fold : forall {m},
                                                                   forall `{GHC.Base.Monoid m}, Identity m -> m :=
  fun {m} `{GHC.Base.Monoid m} =>
    instance_Data_Foldable_Foldable_Identity_foldMap GHC.Base.id.

Local Definition instance_Data_Foldable_Foldable_Identity_foldl : forall {b}
                                                                         {a},
                                                                    (b -> a -> b) -> b -> Identity a -> b :=
  fun {b} {a} => GHC.Prim.coerce.

Local Definition instance_Data_Foldable_Foldable_Identity_foldl' : forall {b}
                                                                          {a},
                                                                     (b -> a -> b) -> b -> Identity a -> b :=
  fun {b} {a} => GHC.Prim.coerce.

Local Definition instance_Data_Foldable_Foldable_Identity_foldr : forall {a}
                                                                         {b},
                                                                    (a -> b -> b) -> b -> Identity a -> b :=
  fun {a} {b} =>
    fun arg_22__ arg_23__ arg_24__ =>
      match arg_22__ , arg_23__ , arg_24__ with
        | f , z , Mk_Identity x => f x z
      end.

Local Definition instance_Data_Foldable_Foldable_Identity_foldr' : forall {a}
                                                                          {b},
                                                                     (a -> b -> b) -> b -> Identity a -> b :=
  fun {a} {b} => instance_Data_Foldable_Foldable_Identity_foldr.

Local Definition instance_Data_Foldable_Foldable_Identity_length : forall {a},
                                                                     Identity a -> GHC.Num.Int :=
  fun {a} => fun arg_28__ => GHC.Num.fromInteger 1.

Local Definition instance_Data_Foldable_Foldable_Identity_null : forall {a},
                                                                   Identity a -> bool :=
  fun {a} => fun arg_31__ => false.

Local Definition instance_Data_Foldable_Foldable_Identity_product : forall {a},
                                                                      forall `{GHC.Num.Num a}, Identity a -> a :=
  fun {a} `{GHC.Num.Num a} => runIdentity.

Local Definition instance_Data_Foldable_Foldable_Identity_sum : forall {a},
                                                                  forall `{GHC.Num.Num a}, Identity a -> a :=
  fun {a} `{GHC.Num.Num a} => runIdentity.

Local Definition instance_Data_Foldable_Foldable_Identity_toList : forall {a},
                                                                     Identity a -> list a :=
  fun {a} =>
    fun arg_32__ => match arg_32__ with | Mk_Identity x => cons x nil end.

Local Definition instance_GHC_Base_Functor_Identity_fmap : forall {a} {b},
                                                             (a -> b) -> Identity a -> Identity b :=
  fun {a} {b} => GHC.Prim.coerce.

Local Definition instance_GHC_Base_Functor_Identity_op_zlzd__ : forall {a} {b},
                                                                  a -> Identity b -> Identity a :=
  fun {a} {b} =>
    fun x => instance_GHC_Base_Functor_Identity_fmap (GHC.Base.const x).

Program Instance instance_GHC_Base_Functor_Identity : GHC.Base.Functor
                                                      Identity := fun _ k =>
    k {|GHC.Base.op_zlzd____ := fun {a} {b} =>
        instance_GHC_Base_Functor_Identity_op_zlzd__ ;
      GHC.Base.fmap__ := fun {a} {b} => instance_GHC_Base_Functor_Identity_fmap |}.

Local Definition instance_GHC_Base_Applicative_Identity_op_zlztzg__ : forall {a}
                                                                             {b},
                                                                        Identity (a -> b) -> Identity a -> Identity b :=
  fun {a} {b} => GHC.Prim.coerce.

Local Definition instance_GHC_Base_Applicative_Identity_op_ztzg__ : forall {a}
                                                                           {b},
                                                                      Identity a -> Identity b -> Identity b :=
  fun {a} {b} =>
    fun x y =>
      instance_GHC_Base_Applicative_Identity_op_zlztzg__ (GHC.Base.fmap
                                                         (GHC.Base.const GHC.Base.id) x) y.

Local Definition instance_GHC_Base_Applicative_Identity_pure : forall {a},
                                                                 a -> Identity a :=
  fun {a} => Mk_Identity.

Program Instance instance_GHC_Base_Applicative_Identity : GHC.Base.Applicative
                                                          Identity := fun _ k =>
    k {|GHC.Base.op_ztzg____ := fun {a} {b} =>
        instance_GHC_Base_Applicative_Identity_op_ztzg__ ;
      GHC.Base.op_zlztzg____ := fun {a} {b} =>
        instance_GHC_Base_Applicative_Identity_op_zlztzg__ ;
      GHC.Base.pure__ := fun {a} => instance_GHC_Base_Applicative_Identity_pure |}.

Local Definition instance_GHC_Base_Monad_Identity_op_zgzg__ : forall {a} {b},
                                                                Identity a -> Identity b -> Identity b :=
  fun {a} {b} => GHC.Base.op_ztzg__.

Local Definition instance_GHC_Base_Monad_Identity_op_zgzgze__ : forall {a} {b},
                                                                  Identity a -> (a -> Identity b) -> Identity b :=
  fun {a} {b} => fun m k => k (runIdentity m).

Local Definition instance_GHC_Base_Monad_Identity_return_ : forall {a},
                                                              a -> Identity a :=
  fun {a} => GHC.Base.pure.

Program Instance instance_GHC_Base_Monad_Identity : GHC.Base.Monad Identity :=
  fun _ k =>
    k {|GHC.Base.op_zgzg____ := fun {a} {b} =>
        instance_GHC_Base_Monad_Identity_op_zgzg__ ;
      GHC.Base.op_zgzgze____ := fun {a} {b} =>
        instance_GHC_Base_Monad_Identity_op_zgzgze__ ;
      GHC.Base.return___ := fun {a} => instance_GHC_Base_Monad_Identity_return_ |}.

(* Translating `instance Control.Monad.Fix.MonadFix Identity' failed: OOPS!
   Cannot find information for class "Control.Monad.Fix.MonadFix" unsupported *)

(* Translating `instance Control.Monad.Zip.MonadZip Identity' failed: OOPS!
   Cannot find information for class "Control.Monad.Zip.MonadZip" unsupported *)

Local Definition instance_Data_Traversable_Traversable_Identity_traverse
    : forall {f} {a} {b},
        forall `{GHC.Base.Applicative f}, (a -> f b) -> Identity a -> f (Identity b) :=
  fun {f} {a} {b} `{GHC.Base.Applicative f} =>
    fun arg_13__ arg_14__ =>
      match arg_13__ , arg_14__ with
        | f , Mk_Identity a1 => GHC.Base.fmap (fun b1 => Mk_Identity b1) (f a1)
      end.

Local Definition instance_Data_Traversable_Traversable_Identity_sequenceA
    : forall {f} {a},
        forall `{GHC.Base.Applicative f}, Identity (f a) -> f (Identity a) :=
  fun {f} {a} `{GHC.Base.Applicative f} =>
    instance_Data_Traversable_Traversable_Identity_traverse GHC.Base.id.

Local Definition instance_Data_Traversable_Traversable_Identity_sequence
    : forall {m} {a},
        forall `{GHC.Base.Monad m}, Identity (m a) -> m (Identity a) :=
  fun {m} {a} `{GHC.Base.Monad m} =>
    instance_Data_Traversable_Traversable_Identity_sequenceA.

Local Definition instance_Data_Traversable_Traversable_Identity_mapM
    : forall {m} {a} {b},
        forall `{GHC.Base.Monad m}, (a -> m b) -> Identity a -> m (Identity b) :=
  fun {m} {a} {b} `{GHC.Base.Monad m} =>
    instance_Data_Traversable_Traversable_Identity_traverse.

(* Translating `instance forall {a}, forall `{Foreign.Storable.Storable a},
   Foreign.Storable.Storable (Identity a)' failed: OOPS! Cannot find information
   for class "Foreign.Storable.Storable" unsupported *)

(* Translating `instance forall {a}, forall `{Data.Semigroup.Semigroup a},
   Data.Semigroup.Semigroup (Identity a)' failed: OOPS! Cannot find information for
   class "Data.Semigroup.Semigroup" unsupported *)

(* Translating `instance forall {a}, forall `{GHC.Float.RealFloat a},
   GHC.Float.RealFloat (Identity a)' failed: OOPS! Cannot find information for
   class "GHC.Float.RealFloat" unsupported *)

(* Translating `instance forall {a}, forall `{GHC.Real.RealFrac a},
   GHC.Real.RealFrac (Identity a)' failed: OOPS! Cannot find information for class
   "GHC.Real.RealFrac" unsupported *)

(* Translating `instance forall {a}, forall `{GHC.Real.Real a}, GHC.Real.Real
   (Identity a)' failed: OOPS! Cannot find information for class "GHC.Real.Real"
   unsupported *)

Local Definition instance_forall___GHC_Base_Ord_a___GHC_Base_Ord__Identity_a__compare {inst_a}
                                                                                      `{GHC.Base.Ord inst_a} : Identity
                                                                                                               inst_a -> Identity
                                                                                                               inst_a -> comparison :=
  GHC.Prim.coerce GHC.Base.compare.

Local Definition instance_forall___GHC_Base_Ord_a___GHC_Base_Ord__Identity_a__max {inst_a}
                                                                                  `{GHC.Base.Ord inst_a} : Identity
                                                                                                           inst_a -> Identity
                                                                                                           inst_a -> Identity
                                                                                                           inst_a :=
  GHC.Prim.coerce GHC.Base.max.

Local Definition instance_forall___GHC_Base_Ord_a___GHC_Base_Ord__Identity_a__min {inst_a}
                                                                                  `{GHC.Base.Ord inst_a} : Identity
                                                                                                           inst_a -> Identity
                                                                                                           inst_a -> Identity
                                                                                                           inst_a :=
  GHC.Prim.coerce GHC.Base.min.

Local Definition instance_forall___GHC_Base_Ord_a___GHC_Base_Ord__Identity_a__op_zg__ {inst_a}
                                                                                      `{GHC.Base.Ord inst_a} : Identity
                                                                                                               inst_a -> Identity
                                                                                                               inst_a -> bool :=
  GHC.Prim.coerce GHC.Base.op_zg__.

Local Definition instance_forall___GHC_Base_Ord_a___GHC_Base_Ord__Identity_a__op_zgze__ {inst_a}
                                                                                        `{GHC.Base.Ord inst_a}
    : Identity inst_a -> Identity inst_a -> bool :=
  GHC.Prim.coerce GHC.Base.op_zgze__.

Local Definition instance_forall___GHC_Base_Ord_a___GHC_Base_Ord__Identity_a__op_zl__ {inst_a}
                                                                                      `{GHC.Base.Ord inst_a} : Identity
                                                                                                               inst_a -> Identity
                                                                                                               inst_a -> bool :=
  GHC.Prim.coerce GHC.Base.op_zl__.

Local Definition instance_forall___GHC_Base_Ord_a___GHC_Base_Ord__Identity_a__op_zlze__ {inst_a}
                                                                                        `{GHC.Base.Ord inst_a}
    : Identity inst_a -> Identity inst_a -> bool :=
  GHC.Prim.coerce GHC.Base.op_zlze__.

(* Translating `instance forall {a}, forall `{GHC.Num.Num a}, GHC.Num.Num
   (Identity a)' failed: OOPS! Cannot find information for class "GHC.Num.Num"
   unsupported *)

Local Definition instance_forall___GHC_Base_Monoid_a___GHC_Base_Monoid__Identity_a__mappend {inst_a}
                                                                                            `{GHC.Base.Monoid inst_a}
    : Identity inst_a -> Identity inst_a -> Identity inst_a :=
  GHC.Prim.coerce GHC.Base.mappend.

Local Definition instance_forall___GHC_Base_Monoid_a___GHC_Base_Monoid__Identity_a__mconcat {inst_a}
                                                                                            `{GHC.Base.Monoid inst_a}
    : list (Identity inst_a) -> Identity inst_a :=
  GHC.Prim.coerce GHC.Base.mconcat.

Local Definition instance_forall___GHC_Base_Monoid_a___GHC_Base_Monoid__Identity_a__mempty {inst_a}
                                                                                           `{GHC.Base.Monoid inst_a}
    : Identity inst_a :=
  GHC.Prim.coerce GHC.Base.mempty.

Program Instance instance_forall___GHC_Base_Monoid_a___GHC_Base_Monoid__Identity_a_ {a}
                                                                                    `{GHC.Base.Monoid a}
  : GHC.Base.Monoid (Identity a) := fun _ k =>
    k
    {|GHC.Base.mappend__ := instance_forall___GHC_Base_Monoid_a___GHC_Base_Monoid__Identity_a__mappend ;
    GHC.Base.mconcat__ := instance_forall___GHC_Base_Monoid_a___GHC_Base_Monoid__Identity_a__mconcat ;
    GHC.Base.mempty__ := instance_forall___GHC_Base_Monoid_a___GHC_Base_Monoid__Identity_a__mempty |}.

(* Translating `instance forall {a}, forall `{GHC.Arr.Ix a}, GHC.Arr.Ix
   (Identity a)' failed: OOPS! Cannot find information for class "GHC.Arr.Ix"
   unsupported *)

(* Translating `instance forall {a}, forall `{Data.String.IsString a},
   Data.String.IsString (Identity a)' failed: OOPS! Cannot find information for
   class "Data.String.IsString" unsupported *)

(* Translating `instance forall {a}, forall `{GHC.Real.Integral a},
   GHC.Real.Integral (Identity a)' failed: OOPS! Cannot find information for class
   "GHC.Real.Integral" unsupported *)

(* Translating `instance GHC.Generics.Generic1 Identity' failed: OOPS! Cannot
   find information for class "GHC.Generics.Generic1" unsupported *)

(* Translating `instance forall {a}, GHC.Generics.Generic (Identity a)' failed:
   OOPS! Cannot find information for class "GHC.Generics.Generic" unsupported *)

(* Translating `instance forall {a}, forall `{GHC.Real.Fractional a},
   GHC.Real.Fractional (Identity a)' failed: OOPS! Cannot find information for
   class "GHC.Real.Fractional" unsupported *)

(* Translating `instance forall {a}, forall `{GHC.Float.Floating a},
   GHC.Float.Floating (Identity a)' failed: OOPS! Cannot find information for class
   "GHC.Float.Floating" unsupported *)

(* Translating `instance forall {a}, forall `{Data.Bits.FiniteBits a},
   Data.Bits.FiniteBits (Identity a)' failed: OOPS! Cannot find information for
   class "Data.Bits.FiniteBits" unsupported *)

Local Definition instance_forall___GHC_Base_Eq__a___GHC_Base_Eq___Identity_a__op_zeze__ {inst_a}
                                                                                        `{GHC.Base.Eq_ inst_a}
    : Identity inst_a -> Identity inst_a -> bool :=
  GHC.Prim.coerce GHC.Base.op_zeze__.

Local Definition instance_forall___GHC_Base_Eq__a___GHC_Base_Eq___Identity_a__op_zsze__ {inst_a}
                                                                                        `{GHC.Base.Eq_ inst_a}
    : Identity inst_a -> Identity inst_a -> bool :=
  GHC.Prim.coerce GHC.Base.op_zsze__.

Program Instance instance_forall___GHC_Base_Eq__a___GHC_Base_Eq___Identity_a_ {a}
                                                                              `{GHC.Base.Eq_ a} : GHC.Base.Eq_ (Identity
                                                                                                               a) :=
  fun _ k =>
    k
    {|GHC.Base.op_zeze____ := instance_forall___GHC_Base_Eq__a___GHC_Base_Eq___Identity_a__op_zeze__ ;
    GHC.Base.op_zsze____ := instance_forall___GHC_Base_Eq__a___GHC_Base_Eq___Identity_a__op_zsze__ |}.

Program Instance instance_forall___GHC_Base_Ord_a___GHC_Base_Ord__Identity_a_ {a}
                                                                              `{GHC.Base.Ord a} : GHC.Base.Ord (Identity
                                                                                                               a) :=
  fun _ k =>
    k
    {|GHC.Base.op_zl____ := instance_forall___GHC_Base_Ord_a___GHC_Base_Ord__Identity_a__op_zl__ ;
    GHC.Base.op_zlze____ := instance_forall___GHC_Base_Ord_a___GHC_Base_Ord__Identity_a__op_zlze__ ;
    GHC.Base.op_zg____ := instance_forall___GHC_Base_Ord_a___GHC_Base_Ord__Identity_a__op_zg__ ;
    GHC.Base.op_zgze____ := instance_forall___GHC_Base_Ord_a___GHC_Base_Ord__Identity_a__op_zgze__ ;
    GHC.Base.compare__ := instance_forall___GHC_Base_Ord_a___GHC_Base_Ord__Identity_a__compare ;
    GHC.Base.max__ := instance_forall___GHC_Base_Ord_a___GHC_Base_Ord__Identity_a__max ;
    GHC.Base.min__ := instance_forall___GHC_Base_Ord_a___GHC_Base_Ord__Identity_a__min |}.

(* Translating `instance forall {a}, forall `{GHC.Enum.Enum a}, GHC.Enum.Enum
   (Identity a)' failed: OOPS! Cannot find information for class "GHC.Enum.Enum"
   unsupported *)

(* Translating `instance forall {a}, forall `{Data.Data.Data a}, Data.Data.Data
   (Identity a)' failed: OOPS! Cannot find information for class "Data.Data.Data"
   unsupported *)

(* Translating `instance forall {a}, forall `{GHC.Enum.Bounded a},
   GHC.Enum.Bounded (Identity a)' failed: OOPS! Cannot find information for class
   "GHC.Enum.Bounded" unsupported *)

(* Translating `instance forall {a}, forall `{Data.Bits.Bits a}, Data.Bits.Bits
   (Identity a)' failed: OOPS! Cannot find information for class "Data.Bits.Bits"
   unsupported *)

Definition hash_compose {a} {b} {c} :=
  (@Coq.Program.Basics.compose a b c).

Local Definition instance_Data_Foldable_Foldable_Identity_elem : forall {a},
                                                                   forall `{GHC.Base.Eq_ a}, a -> Identity a -> bool :=
  fun {a} `{GHC.Base.Eq_ a} =>
    hash_compose (fun arg_19__ => Coq.Program.Basics.compose arg_19__ runIdentity)
                 GHC.Base.op_zeze__.

Program Instance instance_Data_Foldable_Foldable_Identity
  : Data.Foldable.Foldable Identity := fun _ k =>
    k {|Data.Foldable.elem__ := fun {a} `{GHC.Base.Eq_ a} =>
        instance_Data_Foldable_Foldable_Identity_elem ;
      Data.Foldable.fold__ := fun {m} `{GHC.Base.Monoid m} =>
        instance_Data_Foldable_Foldable_Identity_fold ;
      Data.Foldable.foldMap__ := fun {m} {a} `{GHC.Base.Monoid m} =>
        instance_Data_Foldable_Foldable_Identity_foldMap ;
      Data.Foldable.foldl__ := fun {b} {a} =>
        instance_Data_Foldable_Foldable_Identity_foldl ;
      Data.Foldable.foldl'__ := fun {b} {a} =>
        instance_Data_Foldable_Foldable_Identity_foldl' ;
      Data.Foldable.foldr__ := fun {a} {b} =>
        instance_Data_Foldable_Foldable_Identity_foldr ;
      Data.Foldable.foldr'__ := fun {a} {b} =>
        instance_Data_Foldable_Foldable_Identity_foldr' ;
      Data.Foldable.length__ := fun {a} =>
        instance_Data_Foldable_Foldable_Identity_length ;
      Data.Foldable.null__ := fun {a} =>
        instance_Data_Foldable_Foldable_Identity_null ;
      Data.Foldable.product__ := fun {a} `{GHC.Num.Num a} =>
        instance_Data_Foldable_Foldable_Identity_product ;
      Data.Foldable.sum__ := fun {a} `{GHC.Num.Num a} =>
        instance_Data_Foldable_Foldable_Identity_sum ;
      Data.Foldable.toList__ := fun {a} =>
        instance_Data_Foldable_Foldable_Identity_toList |}.

Program Instance instance_Data_Traversable_Traversable_Identity
  : Data.Traversable.Traversable Identity := fun _ k =>
    k {|Data.Traversable.mapM__ := fun {m} {a} {b} `{GHC.Base.Monad m} =>
        instance_Data_Traversable_Traversable_Identity_mapM ;
      Data.Traversable.sequence__ := fun {m} {a} `{GHC.Base.Monad m} =>
        instance_Data_Traversable_Traversable_Identity_sequence ;
      Data.Traversable.sequenceA__ := fun {f} {a} `{GHC.Base.Applicative f} =>
        instance_Data_Traversable_Traversable_Identity_sequenceA ;
      Data.Traversable.traverse__ := fun {f} {a} {b} `{GHC.Base.Applicative f} =>
        instance_Data_Traversable_Traversable_Identity_traverse |}.

(* Unbound variables:
     Coq.Program.Basics.compose Data.Foldable.Foldable Data.Traversable.Traversable
     GHC.Base.Applicative GHC.Base.Eq_ GHC.Base.Functor GHC.Base.Monad
     GHC.Base.Monoid GHC.Base.Ord GHC.Base.compare GHC.Base.const GHC.Base.fmap
     GHC.Base.id GHC.Base.mappend GHC.Base.max GHC.Base.mconcat GHC.Base.mempty
     GHC.Base.min GHC.Base.op_zeze__ GHC.Base.op_zg__ GHC.Base.op_zgze__
     GHC.Base.op_zl__ GHC.Base.op_zlze__ GHC.Base.op_zsze__ GHC.Base.op_ztzg__
     GHC.Base.pure GHC.Num.Int GHC.Num.Num GHC.Prim.coerce bool comparison cons false
     list nil
*)
