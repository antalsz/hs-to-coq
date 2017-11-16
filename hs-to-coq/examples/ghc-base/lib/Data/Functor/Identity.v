(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Coq.Program.Wf.

(* Converted imports: *)

Require GHC.Base.
Require GHC.Prim.

(* Converted type declarations: *)

Inductive Identity a : Type := Mk_Identity : a -> Identity a.

Arguments Mk_Identity {_} _.

Definition runIdentity {a} (arg_0__ : Identity a) :=
  match arg_0__ with
    | Mk_Identity runIdentity => runIdentity
  end.
(* Midamble *)

Instance Unpeel_Identity a : Prim.Unpeel a (Identity a) :=
 Prim.Build_Unpeel _ _ Mk_Identity (fun arg => match arg with | Mk_Identity x => x end).
Instance Unpeel_CoIdentity a : Prim.Unpeel (Identity a) a :=
 Prim.Build_Unpeel _ _  (fun arg => match arg with | Mk_Identity x => x end) Mk_Identity.

(* Converted value declarations: *)

(* Translating `instance forall {a}, forall `{(GHC.Read.Read a)}, GHC.Read.Read
   (Identity a)' failed: OOPS! Cannot find information for class "GHC.Read.Read"
   unsupported *)

(* Translating `instance forall {a}, forall `{(GHC.Show.Show a)}, GHC.Show.Show
   (Identity a)' failed: OOPS! Cannot find information for class "GHC.Show.Show"
   unsupported *)

(* Translating `instance Data.Foldable.Foldable Identity' failed: OOPS! Cannot
   find information for class "Data.Foldable.Foldable" unsupported *)

Local Definition instance_GHC_Base_Functor_Identity_fmap : forall {a} {b},
                                                             (a -> b) -> Identity a -> Identity b :=
  fun {a} {b} => GHC.Prim.coerce.

Local Definition instance_GHC_Base_Functor_Identity_op_zlzd__ : forall {a} {b},
                                                                  a -> Identity b -> Identity a :=
  fun {a} {b} =>
    fun x => instance_GHC_Base_Functor_Identity_fmap (GHC.Base.const x).

Instance instance_GHC_Base_Functor_Identity : GHC.Base.Functor Identity := fun _
                                                                               k =>
    k (GHC.Base.Functor__Dict_Build Identity (fun {a} {b} =>
                                      instance_GHC_Base_Functor_Identity_op_zlzd__) (fun {a} {b} =>
                                      instance_GHC_Base_Functor_Identity_fmap)).

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

Instance instance_GHC_Base_Applicative_Identity : GHC.Base.Applicative
                                                  Identity := fun _ k =>
    k (GHC.Base.Applicative__Dict_Build Identity (fun {a} {b} =>
                                          instance_GHC_Base_Applicative_Identity_op_ztzg__) (fun {a} {b} =>
                                          instance_GHC_Base_Applicative_Identity_op_zlztzg__) (fun {a} =>
                                          instance_GHC_Base_Applicative_Identity_pure)).

Local Definition instance_GHC_Base_Monad_Identity_op_zgzg__ : forall {a} {b},
                                                                Identity a -> Identity b -> Identity b :=
  fun {a} {b} => GHC.Base.op_ztzg__.

Local Definition instance_GHC_Base_Monad_Identity_op_zgzgze__ : forall {a} {b},
                                                                  Identity a -> (a -> Identity b) -> Identity b :=
  fun {a} {b} =>
    fun arg_1__ arg_2__ =>
      match arg_1__ , arg_2__ with
        | m , k => k (runIdentity m)
      end.

Local Definition instance_GHC_Base_Monad_Identity_return_ : forall {a},
                                                              a -> Identity a :=
  fun {a} => GHC.Base.pure.

Instance instance_GHC_Base_Monad_Identity : GHC.Base.Monad Identity := fun _
                                                                           k =>
    k (GHC.Base.Monad__Dict_Build Identity (fun {a} {b} =>
                                    instance_GHC_Base_Monad_Identity_op_zgzg__) (fun {a} {b} =>
                                    instance_GHC_Base_Monad_Identity_op_zgzgze__) (fun {a} =>
                                    instance_GHC_Base_Monad_Identity_return_)).

(* Translating `instance Control.Monad.Fix.MonadFix Identity' failed: OOPS!
   Cannot find information for class "Control.Monad.Fix.MonadFix" unsupported *)

(* Translating `instance Control.Monad.Zip.MonadZip Identity' failed: OOPS!
   Cannot find information for class "Control.Monad.Zip.MonadZip" unsupported *)

(* Translating `instance Data.Traversable.Traversable Identity' failed: OOPS!
   Cannot find information for class "Data.Traversable.Traversable" unsupported *)

(* Translating `instance forall {a}, forall `{Foreign.Storable.Storable a},
   Foreign.Storable.Storable (Identity a)' failed: type applications unsupported *)

(* Translating `instance forall {a}, forall `{Data.Semigroup.Semigroup a},
   Data.Semigroup.Semigroup (Identity a)' failed: type applications unsupported *)

(* Translating `instance forall {a}, forall `{GHC.Float.RealFloat a},
   GHC.Float.RealFloat (Identity a)' failed: type applications unsupported *)

(* Translating `instance forall {a}, forall `{GHC.Real.RealFrac a},
   GHC.Real.RealFrac (Identity a)' failed: type applications unsupported *)

(* Translating `instance forall {a}, forall `{GHC.Real.Real a}, GHC.Real.Real
   (Identity a)' failed: type applications unsupported *)

(* Translating `instance forall {a}, forall `{GHC.Base.Ord a}, GHC.Base.Ord
   (Identity a)' failed: type applications unsupported *)

(* Translating `instance forall {a}, forall `{GHC.Num.Num a}, GHC.Num.Num
   (Identity a)' failed: type applications unsupported *)

(* Translating `instance forall {a}, forall `{GHC.Base.Monoid a},
   GHC.Base.Monoid (Identity a)' failed: type applications unsupported *)

(* Translating `instance forall {a}, forall `{GHC.Arr.Ix a}, GHC.Arr.Ix
   (Identity a)' failed: type applications unsupported *)

(* Translating `instance forall {a}, forall `{Data.String.IsString a},
   Data.String.IsString (Identity a)' failed: type applications unsupported *)

(* Translating `instance forall {a}, forall `{GHC.Real.Integral a},
   GHC.Real.Integral (Identity a)' failed: type applications unsupported *)

(* Translating `instance GHC.Generics.Generic1 Identity' failed: OOPS! Cannot
   find information for class "GHC.Generics.Generic1" unsupported *)

(* Translating `instance forall {a}, GHC.Generics.Generic (Identity a)' failed:
   OOPS! Cannot find information for class "GHC.Generics.Generic" unsupported *)

(* Translating `instance forall {a}, forall `{GHC.Real.Fractional a},
   GHC.Real.Fractional (Identity a)' failed: type applications unsupported *)

(* Translating `instance forall {a}, forall `{GHC.Float.Floating a},
   GHC.Float.Floating (Identity a)' failed: type applications unsupported *)

(* Translating `instance forall {a}, forall `{Data.Bits.FiniteBits a},
   Data.Bits.FiniteBits (Identity a)' failed: type applications unsupported *)

(* Translating `instance forall {a}, forall `{GHC.Base.Eq_ a}, GHC.Base.Eq_
   (Identity a)' failed: type applications unsupported *)

(* Translating `instance forall {a}, forall `{GHC.Enum.Enum a}, GHC.Enum.Enum
   (Identity a)' failed: type applications unsupported *)

(* Translating `instance forall {a}, forall `{Data.Data.Data a}, Data.Data.Data
   (Identity a)' failed: OOPS! Cannot find information for class "Data.Data.Data"
   unsupported *)

(* Translating `instance forall {a}, forall `{GHC.Enum.Bounded a},
   GHC.Enum.Bounded (Identity a)' failed: type applications unsupported *)

(* Translating `instance forall {a}, forall `{Data.Bits.Bits a}, Data.Bits.Bits
   (Identity a)' failed: type applications unsupported *)

(* Unbound variables:
     GHC.Base.Applicative GHC.Base.Applicative__Dict_Build GHC.Base.Functor
     GHC.Base.Functor__Dict_Build GHC.Base.Monad GHC.Base.Monad__Dict_Build
     GHC.Base.const GHC.Base.fmap GHC.Base.id GHC.Base.op_ztzg__ GHC.Base.pure
     GHC.Prim.coerce
*)
