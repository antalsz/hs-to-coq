(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Set Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Preamble *)


(* Converted imports: *)

Require Data.Bits.
Require Data.Foldable.
Require Foreign.Storable.
Require GHC.Arr.
Require GHC.Base.
Require GHC.Enum.
Require GHC.Float.
Require GHC.Generics.
Require GHC.Num.
Require GHC.Real.
Require GHC.Read.
Require GHC.Show.
Require GHC.Base.

(* Converted declarations: *)

(* Translating `instance forall `{GHC.Read.Read a}, GHC.Read.Read (Const a b)'
   failed: OOPS! Cannot construct types for this class def: Nothing unsupported *)

(* Translating `instance forall `{GHC.Show.Show a}, GHC.Show.Show (Const a b)'
   failed: OOPS! Cannot construct types for this class def: Nothing unsupported *)

(* Translating `instance Data.Foldable.Foldable (Const m)' failed: OOPS! Cannot
   construct types for this class def: Nothing unsupported *)

Inductive Const a (b:Type) : Type := Mk_Const : a -> Const a b.

Arguments Mk_Const {_} {_} _.

Definition getConst {a} {b} (arg_0__ : Const a b) :=
  match arg_0__ with
    | (Mk_Const getConst) => getConst
  end.

Local Definition instance_forall___GHC_Base_Monoid_m___GHC_Base_Applicative__Const_m__pure `{GHC.Base.Monoid
                                                                                                 m} : forall {a},
                                                                                                        a -> (Const m)
                                                                                                        a :=
  fun {a} => fun arg_1__ => Mk_Const GHC.Base.mempty.

Local Definition instance_forall___GHC_Base_Monoid_m___GHC_Base_Applicative__Const_m__op_zlztzg__ `{GHC.Base.Monoid m} :
  forall {a}{b}, (Const m) (a -> b) -> (Const m) a -> (Const m) b :=
  fun {a} {b} x y => match (x,y) with
                    (Mk_Const x1, Mk_Const x2) => Mk_Const (GHC.Base.mappend x1 x2)
                  end.

Local Definition instance_GHC_Base_Functor__Const_m__fmap : forall {m}{a} {b},
                                                                 (a -> b) -> (Const m) a -> (Const m) b :=
  fun {m}{a} {b} =>
    fun arg_5__ arg_6__ =>
      match arg_5__ , arg_6__ with
        | _ , (Mk_Const v) => Mk_Const v
      end.

Local Definition instance_GHC_Base_Functor__Const_m__op_zlzd__ : forall {m}{a}
                                                                           {b},
                                                                      b -> (Const m) a -> (Const m) b :=
  fun {m}{a} {b} =>
    fun x => instance_GHC_Base_Functor__Const_m__fmap (GHC.Base.const x).

Instance instance_GHC_Base_Functor__Const_m_ : !GHC.Base.Functor (Const
                                                                       m) := {
  fmap := fun {a} {b} => instance_GHC_Base_Functor__Const_m__fmap ;
  op_zlzd__ := fun {a} {b} => instance_GHC_Base_Functor__Const_m__op_zlzd__ }.



Local Definition instance_forall___GHC_Base_Monoid_m___GHC_Base_Applicative__Const_m__op_ztzg__ `{GHC.Base.Monoid
                                                                                                      m} : forall {a}
                                                                                                                  {b},
                                                                                                             (Const m)
                                                                                                             a -> (Const
                                                                                                             m)
                                                                                                             b -> (Const
                                                                                                             m) b :=
  fun {a} {b} =>
    fun x y =>
      instance_forall___GHC_Base_Monoid_m___GHC_Base_Applicative__Const_m__op_zlztzg__
      (GHC.Base.fmap (GHC.Base.const GHC.Base.id) x) y.

Local Definition instance_forall___GHC_Base_Monoid_m___GHC_Base_Applicative__Const_m__op_zlzt__ `{GHC.Base.Monoid
                                                                                                      m} : forall {a}
                                                                                                                  {b},
                                                                                                             (Const m)
                                                                                                             a -> (Const
                                                                                                             m)
                                                                                                             b -> (Const
                                                                                                             m) a :=
  fun {a} {b} =>
    fun x y =>
      instance_forall___GHC_Base_Monoid_m___GHC_Base_Applicative__Const_m__op_zlztzg__
      (GHC.Base.fmap GHC.Base.const x) y.

Instance instance_forall___GHC_Base_Monoid_m___GHC_Base_Applicative__Const_m_
  `{GHC.Base.Monoid m} : !GHC.Base.Applicative (Const m) := {
  op_zlzt__ := fun {a} {b} =>
    instance_forall___GHC_Base_Monoid_m___GHC_Base_Applicative__Const_m__op_zlzt__ ;
  op_zlztzg__ := fun {a} {b} =>
    instance_forall___GHC_Base_Monoid_m___GHC_Base_Applicative__Const_m__op_zlztzg__ ;
  op_ztzg__ := fun {a} {b} =>
    instance_forall___GHC_Base_Monoid_m___GHC_Base_Applicative__Const_m__op_ztzg__ ;
  pure := fun {a} =>
    instance_forall___GHC_Base_Monoid_m___GHC_Base_Applicative__Const_m__pure }.

(* Foldable, Read, Show derived *)

(* Unbound variables:
     Data.Foldable.Foldable GHC.Base.mappend GHC.Base.mempty GHC.Base.Applicative
     GHC.Base.Functor GHC.Base.Monoid GHC.Base.const GHC.Base.fmap
     GHC.Base.id GHC.Prim.coerce GHC.Read.Read GHC.Show.Show m
*)
