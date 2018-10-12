(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Coq.Program.Tactics.
Require Coq.Program.Wf.

(* Converted imports: *)

Require Data.Foldable.
Require GHC.Base.
Require GHC.Num.
Require GHC.Prim.
Import GHC.Base.Notations.
Import GHC.Num.Notations.

(* Converted type declarations: *)

Inductive Identity a : Type := Mk_Identity (runIdentity : a) : Identity a.

Arguments Mk_Identity {_} _.

Definition runIdentity {a} (arg_0__ : Identity a) :=
  let 'Mk_Identity runIdentity := arg_0__ in
  runIdentity.
(* Midamble *)

Instance Unpeel_Identity a : Prim.Unpeel (Identity a) a :=
 Prim.Build_Unpeel _ _  (fun arg => match arg with | Mk_Identity x => x end) Mk_Identity.

(* Converted value declarations: *)

(* Skipping instance Read__Identity of class Read *)

(* Skipping instance Show__Identity of class Show *)

Local Definition Foldable__Identity_toList : forall {a}, Identity a -> list a :=
  fun {a} => fun '(Mk_Identity x) => cons x nil.

Local Definition Foldable__Identity_sum
   : forall {a}, forall `{GHC.Num.Num a}, Identity a -> a :=
  fun {a} `{GHC.Num.Num a} => runIdentity.

Local Definition Foldable__Identity_product
   : forall {a}, forall `{GHC.Num.Num a}, Identity a -> a :=
  fun {a} `{GHC.Num.Num a} => runIdentity.

Local Definition Foldable__Identity_null : forall {a}, Identity a -> bool :=
  fun {a} => fun arg_0__ => false.

Local Definition Foldable__Identity_length
   : forall {a}, Identity a -> GHC.Num.Int :=
  fun {a} => fun arg_0__ => #1.

Local Definition Foldable__Identity_foldr
   : forall {a} {b}, (a -> b -> b) -> b -> Identity a -> b :=
  fun {a} {b} =>
    fun arg_0__ arg_1__ arg_2__ =>
      match arg_0__, arg_1__, arg_2__ with
      | f, z, Mk_Identity x => f x z
      end.

Local Definition Foldable__Identity_foldr'
   : forall {a} {b}, (a -> b -> b) -> b -> Identity a -> b :=
  fun {a} {b} => Foldable__Identity_foldr.

Local Definition Foldable__Identity_foldl'
   : forall {b} {a}, (b -> a -> b) -> b -> Identity a -> b :=
  fun {b} {a} => GHC.Prim.coerce.

Local Definition Foldable__Identity_foldl
   : forall {b} {a}, (b -> a -> b) -> b -> Identity a -> b :=
  fun {b} {a} => GHC.Prim.coerce.

Local Definition Foldable__Identity_foldMap
   : forall {m} {a}, forall `{GHC.Base.Monoid m}, (a -> m) -> Identity a -> m :=
  fun {m} {a} `{GHC.Base.Monoid m} => GHC.Prim.coerce.

Local Definition Foldable__Identity_fold
   : forall {m}, forall `{GHC.Base.Monoid m}, Identity m -> m :=
  fun {m} `{GHC.Base.Monoid m} => Foldable__Identity_foldMap GHC.Base.id.

Program Instance Foldable__Identity : Data.Foldable.Foldable Identity :=
  fun _ k =>
    k {| Data.Foldable.fold__ := fun {m} `{GHC.Base.Monoid m} =>
           Foldable__Identity_fold ;
         Data.Foldable.foldMap__ := fun {m} {a} `{GHC.Base.Monoid m} =>
           Foldable__Identity_foldMap ;
         Data.Foldable.foldl__ := fun {b} {a} => Foldable__Identity_foldl ;
         Data.Foldable.foldl'__ := fun {b} {a} => Foldable__Identity_foldl' ;
         Data.Foldable.foldr__ := fun {a} {b} => Foldable__Identity_foldr ;
         Data.Foldable.foldr'__ := fun {a} {b} => Foldable__Identity_foldr' ;
         Data.Foldable.length__ := fun {a} => Foldable__Identity_length ;
         Data.Foldable.null__ := fun {a} => Foldable__Identity_null ;
         Data.Foldable.product__ := fun {a} `{GHC.Num.Num a} =>
           Foldable__Identity_product ;
         Data.Foldable.sum__ := fun {a} `{GHC.Num.Num a} => Foldable__Identity_sum ;
         Data.Foldable.toList__ := fun {a} => Foldable__Identity_toList |}.

Local Definition Functor__Identity_fmap
   : forall {a} {b}, (a -> b) -> Identity a -> Identity b :=
  fun {a} {b} => GHC.Prim.coerce.

Local Definition Functor__Identity_op_zlzd__
   : forall {a} {b}, a -> Identity b -> Identity a :=
  fun {a} {b} => Functor__Identity_fmap GHC.Base.∘ GHC.Base.const.

Program Instance Functor__Identity : GHC.Base.Functor Identity :=
  fun _ k =>
    k {| GHC.Base.fmap__ := fun {a} {b} => Functor__Identity_fmap ;
         GHC.Base.op_zlzd____ := fun {a} {b} => Functor__Identity_op_zlzd__ |}.

Local Definition Applicative__Identity_pure : forall {a}, a -> Identity a :=
  fun {a} => Mk_Identity.

Local Definition Applicative__Identity_op_zlztzg__
   : forall {a} {b}, Identity (a -> b) -> Identity a -> Identity b :=
  fun {a} {b} => GHC.Prim.coerce.

Local Definition Applicative__Identity_op_ztzg__
   : forall {a} {b}, Identity a -> Identity b -> Identity b :=
  fun {a} {b} =>
    fun a1 a2 => Applicative__Identity_op_zlztzg__ (GHC.Base.id GHC.Base.<$ a1) a2.

Local Definition Applicative__Identity_liftA2
   : forall {a} {b} {c},
     (a -> b -> c) -> Identity a -> Identity b -> Identity c :=
  fun {a} {b} {c} => GHC.Prim.coerce.

Program Instance Applicative__Identity : GHC.Base.Applicative Identity :=
  fun _ k =>
    k {| GHC.Base.liftA2__ := fun {a} {b} {c} => Applicative__Identity_liftA2 ;
         GHC.Base.op_zlztzg____ := fun {a} {b} => Applicative__Identity_op_zlztzg__ ;
         GHC.Base.op_ztzg____ := fun {a} {b} => Applicative__Identity_op_ztzg__ ;
         GHC.Base.pure__ := fun {a} => Applicative__Identity_pure |}.

Local Definition Monad__Identity_return_ : forall {a}, a -> Identity a :=
  fun {a} => GHC.Base.pure.

Local Definition Monad__Identity_op_zgzgze__
   : forall {a} {b}, Identity a -> (a -> Identity b) -> Identity b :=
  fun {a} {b} => fun m k => k (runIdentity m).

Local Definition Monad__Identity_op_zgzg__
   : forall {a} {b}, Identity a -> Identity b -> Identity b :=
  fun {a} {b} => fun m k => Monad__Identity_op_zgzgze__ m (fun arg_0__ => k).

Program Instance Monad__Identity : GHC.Base.Monad Identity :=
  fun _ k =>
    k {| GHC.Base.op_zgzg____ := fun {a} {b} => Monad__Identity_op_zgzg__ ;
         GHC.Base.op_zgzgze____ := fun {a} {b} => Monad__Identity_op_zgzgze__ ;
         GHC.Base.return___ := fun {a} => Monad__Identity_return_ |}.

(* Skipping instance MonadFix__Identity of class MonadFix *)

(* Skipping instance Storable__Identity of class Storable *)

(* Skipping instance RealFloat__Identity of class RealFloat *)

(* Skipping instance RealFrac__Identity of class RealFrac *)

(* Skipping instance Real__Identity of class Real *)

Local Definition Ord__Identity_min {inst_a} `{GHC.Base.Ord inst_a}
   : Identity inst_a -> Identity inst_a -> Identity inst_a :=
  GHC.Prim.coerce GHC.Base.min.

Local Definition Ord__Identity_max {inst_a} `{GHC.Base.Ord inst_a}
   : Identity inst_a -> Identity inst_a -> Identity inst_a :=
  GHC.Prim.coerce GHC.Base.max.

Local Definition Ord__Identity_compare {inst_a} `{GHC.Base.Ord inst_a}
   : Identity inst_a -> Identity inst_a -> comparison :=
  GHC.Prim.coerce GHC.Base.compare.

Local Definition Ord__Identity_op_zgze__ {inst_a} `{GHC.Base.Ord inst_a}
   : Identity inst_a -> Identity inst_a -> bool :=
  GHC.Prim.coerce _GHC.Base.>=_.

Local Definition Ord__Identity_op_zg__ {inst_a} `{GHC.Base.Ord inst_a}
   : Identity inst_a -> Identity inst_a -> bool :=
  GHC.Prim.coerce _GHC.Base.>_.

Local Definition Ord__Identity_op_zlze__ {inst_a} `{GHC.Base.Ord inst_a}
   : Identity inst_a -> Identity inst_a -> bool :=
  GHC.Prim.coerce _GHC.Base.<=_.

Local Definition Ord__Identity_op_zl__ {inst_a} `{GHC.Base.Ord inst_a}
   : Identity inst_a -> Identity inst_a -> bool :=
  GHC.Prim.coerce _GHC.Base.<_.

(* Translating `instance Num__Identity' failed: Could not find information for
   the class `GHC.Num.Num' when defining the instance
   `Data.Functor.Identity.Num__Identity' *)

Local Definition Monoid__Identity_mempty {inst_a} `{GHC.Base.Monoid inst_a}
   : Identity inst_a :=
  GHC.Prim.coerce GHC.Base.mempty.

Local Definition Monoid__Identity_mconcat {inst_a} `{GHC.Base.Monoid inst_a}
   : list (Identity inst_a) -> Identity inst_a :=
  GHC.Prim.coerce GHC.Base.mconcat.

Local Definition Monoid__Identity_mappend {inst_a} `{GHC.Base.Monoid inst_a}
   : Identity inst_a -> Identity inst_a -> Identity inst_a :=
  GHC.Prim.coerce GHC.Base.mappend.

Local Definition Semigroup__Identity_op_zlzlzgzg__ {inst_a} `{GHC.Base.Semigroup
  inst_a}
   : Identity inst_a -> Identity inst_a -> Identity inst_a :=
  GHC.Prim.coerce _GHC.Base.<<>>_.

Program Instance Semigroup__Identity {a} `{GHC.Base.Semigroup a}
   : GHC.Base.Semigroup (Identity a) :=
  fun _ k =>
    k {| GHC.Base.op_zlzlzgzg____ := Semigroup__Identity_op_zlzlzgzg__ |}.

Program Instance Monoid__Identity {a} `{GHC.Base.Monoid a}
   : GHC.Base.Monoid (Identity a) :=
  fun _ k =>
    k {| GHC.Base.mappend__ := Monoid__Identity_mappend ;
         GHC.Base.mconcat__ := Monoid__Identity_mconcat ;
         GHC.Base.mempty__ := Monoid__Identity_mempty |}.

(* Skipping instance Ix__Identity of class Ix *)

(* Skipping instance Integral__Identity of class Integral *)

(* Skipping instance Generic1__TYPE__Identity__LiftedRep of class Generic1 *)

(* Skipping instance Generic__Identity of class Generic *)

(* Skipping instance Fractional__Identity of class Fractional *)

(* Skipping instance Floating__Identity of class Floating *)

(* Skipping instance FiniteBits__Identity of class FiniteBits *)

Local Definition Eq___Identity_op_zsze__ {inst_a} `{GHC.Base.Eq_ inst_a}
   : Identity inst_a -> Identity inst_a -> bool :=
  GHC.Prim.coerce _GHC.Base./=_.

Local Definition Eq___Identity_op_zeze__ {inst_a} `{GHC.Base.Eq_ inst_a}
   : Identity inst_a -> Identity inst_a -> bool :=
  GHC.Prim.coerce _GHC.Base.==_.

Program Instance Eq___Identity {a} `{GHC.Base.Eq_ a}
   : GHC.Base.Eq_ (Identity a) :=
  fun _ k =>
    k {| GHC.Base.op_zeze____ := Eq___Identity_op_zeze__ ;
         GHC.Base.op_zsze____ := Eq___Identity_op_zsze__ |}.

Program Instance Ord__Identity {a} `{GHC.Base.Ord a}
   : GHC.Base.Ord (Identity a) :=
  fun _ k =>
    k {| GHC.Base.op_zl____ := Ord__Identity_op_zl__ ;
         GHC.Base.op_zlze____ := Ord__Identity_op_zlze__ ;
         GHC.Base.op_zg____ := Ord__Identity_op_zg__ ;
         GHC.Base.op_zgze____ := Ord__Identity_op_zgze__ ;
         GHC.Base.compare__ := Ord__Identity_compare ;
         GHC.Base.max__ := Ord__Identity_max ;
         GHC.Base.min__ := Ord__Identity_min |}.

(* Translating `instance Enum__Identity' failed: Could not find information for
   the class `GHC.Enum.Enum' when defining the instance
   `Data.Functor.Identity.Enum__Identity' *)

(* Translating `instance Bounded__Identity' failed: Could not find information
   for the class `GHC.Enum.Bounded' when defining the instance
   `Data.Functor.Identity.Bounded__Identity' *)

(* Skipping instance Bits__Identity of class Bits *)

(* External variables:
     bool comparison cons false list nil Data.Foldable.Foldable
     Data.Foldable.foldMap__ Data.Foldable.fold__ Data.Foldable.foldl'__
     Data.Foldable.foldl__ Data.Foldable.foldr'__ Data.Foldable.foldr__
     Data.Foldable.length__ Data.Foldable.null__ Data.Foldable.product__
     Data.Foldable.sum__ Data.Foldable.toList__ GHC.Base.Applicative GHC.Base.Eq_
     GHC.Base.Functor GHC.Base.Monad GHC.Base.Monoid GHC.Base.Ord GHC.Base.Semigroup
     GHC.Base.compare GHC.Base.compare__ GHC.Base.const GHC.Base.fmap__ GHC.Base.id
     GHC.Base.liftA2__ GHC.Base.mappend GHC.Base.mappend__ GHC.Base.max
     GHC.Base.max__ GHC.Base.mconcat GHC.Base.mconcat__ GHC.Base.mempty
     GHC.Base.mempty__ GHC.Base.min GHC.Base.min__ GHC.Base.op_z2218U__
     GHC.Base.op_zeze__ GHC.Base.op_zeze____ GHC.Base.op_zg__ GHC.Base.op_zg____
     GHC.Base.op_zgze__ GHC.Base.op_zgze____ GHC.Base.op_zgzg____
     GHC.Base.op_zgzgze____ GHC.Base.op_zl__ GHC.Base.op_zl____ GHC.Base.op_zlzd__
     GHC.Base.op_zlzd____ GHC.Base.op_zlze__ GHC.Base.op_zlze____
     GHC.Base.op_zlzlzgzg__ GHC.Base.op_zlzlzgzg____ GHC.Base.op_zlztzg____
     GHC.Base.op_zsze__ GHC.Base.op_zsze____ GHC.Base.op_ztzg____ GHC.Base.pure
     GHC.Base.pure__ GHC.Base.return___ GHC.Num.Int GHC.Num.Num GHC.Num.fromInteger
     GHC.Prim.coerce
*)
