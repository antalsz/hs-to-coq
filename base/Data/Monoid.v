(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Coq.Program.Tactics.
Require Coq.Program.Wf.

(* Converted imports: *)

Require GHC.Base.
Require GHC.Prim.
Import GHC.Base.Notations.

(* Converted type declarations: *)

Inductive Last a : Type := | Mk_Last (getLast : option a) : Last a.

Inductive First a : Type := | Mk_First (getFirst : option a) : First a.

Arguments Mk_Last {_} _.

Arguments Mk_First {_} _.

Definition getLast {a} (arg_0__ : Last a) :=
  let 'Mk_Last getLast := arg_0__ in
  getLast.

Definition getFirst {a} (arg_0__ : First a) :=
  let 'Mk_First getFirst := arg_0__ in
  getFirst.

(* Converted value declarations: *)

Instance Unpeel_First a : GHC.Prim.Unpeel (First a) (option a) :=
  GHC.Prim.Build_Unpeel _ _ getFirst Mk_First.

Local Definition Eq___First_op_zeze__ {inst_a} `{GHC.Base.Eq_ inst_a}
   : First inst_a -> First inst_a -> bool :=
  GHC.Prim.coerce _GHC.Base.==_.

Local Definition Eq___First_op_zsze__ {inst_a} `{GHC.Base.Eq_ inst_a}
   : First inst_a -> First inst_a -> bool :=
  GHC.Prim.coerce _GHC.Base./=_.

Program Instance Eq___First {a} `{GHC.Base.Eq_ a} : GHC.Base.Eq_ (First a) :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zeze____ := Eq___First_op_zeze__ ;
           GHC.Base.op_zsze____ := Eq___First_op_zsze__ |}.

Local Definition Ord__First_op_zl__ {inst_a} `{GHC.Base.Ord inst_a}
   : First inst_a -> First inst_a -> bool :=
  GHC.Prim.coerce _GHC.Base.<_.

Local Definition Ord__First_op_zlze__ {inst_a} `{GHC.Base.Ord inst_a}
   : First inst_a -> First inst_a -> bool :=
  GHC.Prim.coerce _GHC.Base.<=_.

Local Definition Ord__First_op_zg__ {inst_a} `{GHC.Base.Ord inst_a}
   : First inst_a -> First inst_a -> bool :=
  GHC.Prim.coerce _GHC.Base.>_.

Local Definition Ord__First_op_zgze__ {inst_a} `{GHC.Base.Ord inst_a}
   : First inst_a -> First inst_a -> bool :=
  GHC.Prim.coerce _GHC.Base.>=_.

Local Definition Ord__First_compare {inst_a} `{GHC.Base.Ord inst_a}
   : First inst_a -> First inst_a -> comparison :=
  GHC.Prim.coerce GHC.Base.compare.

Local Definition Ord__First_max {inst_a} `{GHC.Base.Ord inst_a}
   : First inst_a -> First inst_a -> First inst_a :=
  GHC.Prim.coerce GHC.Base.max.

Local Definition Ord__First_min {inst_a} `{GHC.Base.Ord inst_a}
   : First inst_a -> First inst_a -> First inst_a :=
  GHC.Prim.coerce GHC.Base.min.

Program Instance Ord__First {a} `{GHC.Base.Ord a} : GHC.Base.Ord (First a) :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zl____ := Ord__First_op_zl__ ;
           GHC.Base.op_zlze____ := Ord__First_op_zlze__ ;
           GHC.Base.op_zg____ := Ord__First_op_zg__ ;
           GHC.Base.op_zgze____ := Ord__First_op_zgze__ ;
           GHC.Base.compare__ := Ord__First_compare ;
           GHC.Base.max__ := Ord__First_max ;
           GHC.Base.min__ := Ord__First_min |}.

(* Skipping all instances of class `GHC.Read.Read', including
   `Data.Monoid.Read__First' *)

(* Skipping all instances of class `GHC.Show.Show', including
   `Data.Monoid.Show__First' *)

(* Skipping all instances of class `GHC.Generics.Generic', including
   `Data.Monoid.Generic__First' *)

(* Skipping all instances of class `GHC.Generics.Generic1', including
   `Data.Monoid.Generic1__TYPE__First__LiftedRep' *)

Local Definition Functor__First_fmap
   : forall {a} {b}, (a -> b) -> First a -> First b :=
  fun {a} {b} => GHC.Prim.coerce GHC.Base.fmap.

Local Definition Functor__First_op_zlzd__
   : forall {a} {b}, a -> First b -> First a :=
  fun {a} {b} => GHC.Prim.coerce _GHC.Base.<$_.

Program Instance Functor__First : GHC.Base.Functor First :=
  fun _ k__ =>
    k__ {| GHC.Base.fmap__ := fun {a} {b} => Functor__First_fmap ;
           GHC.Base.op_zlzd____ := fun {a} {b} => Functor__First_op_zlzd__ |}.

Local Definition Applicative__First_liftA2
   : forall {a} {b} {c}, (a -> b -> c) -> First a -> First b -> First c :=
  fun {a} {b} {c} => GHC.Prim.coerce GHC.Base.liftA2.

Local Definition Applicative__First_op_zlztzg__
   : forall {a} {b}, First (a -> b) -> First a -> First b :=
  fun {a} {b} => GHC.Prim.coerce _GHC.Base.<*>_.

Local Definition Applicative__First_op_ztzg__
   : forall {a} {b}, First a -> First b -> First b :=
  fun {a} {b} => GHC.Prim.coerce _GHC.Base.*>_.

Local Definition Applicative__First_pure : forall {a}, a -> First a :=
  fun {a} => GHC.Prim.coerce GHC.Base.pure.

Program Instance Applicative__First : GHC.Base.Applicative First :=
  fun _ k__ =>
    k__ {| GHC.Base.liftA2__ := fun {a} {b} {c} => Applicative__First_liftA2 ;
           GHC.Base.op_zlztzg____ := fun {a} {b} => Applicative__First_op_zlztzg__ ;
           GHC.Base.op_ztzg____ := fun {a} {b} => Applicative__First_op_ztzg__ ;
           GHC.Base.pure__ := fun {a} => Applicative__First_pure |}.

Local Definition Monad__First_op_zgzg__
   : forall {a} {b}, First a -> First b -> First b :=
  fun {a} {b} => GHC.Prim.coerce _GHC.Base.>>_.

Local Definition Monad__First_op_zgzgze__
   : forall {a} {b}, First a -> (a -> First b) -> First b :=
  fun {a} {b} => GHC.Prim.coerce _GHC.Base.>>=_.

Local Definition Monad__First_return_ : forall {a}, a -> First a :=
  fun {a} => GHC.Prim.coerce GHC.Base.return_.

Program Instance Monad__First : GHC.Base.Monad First :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zgzg____ := fun {a} {b} => Monad__First_op_zgzg__ ;
           GHC.Base.op_zgzgze____ := fun {a} {b} => Monad__First_op_zgzgze__ ;
           GHC.Base.return___ := fun {a} => Monad__First_return_ |}.

Instance Unpeel_Last a : GHC.Prim.Unpeel (Last a) (option a) :=
  GHC.Prim.Build_Unpeel _ _ getLast Mk_Last.

Local Definition Eq___Last_op_zeze__ {inst_a} `{GHC.Base.Eq_ inst_a}
   : Last inst_a -> Last inst_a -> bool :=
  GHC.Prim.coerce _GHC.Base.==_.

Local Definition Eq___Last_op_zsze__ {inst_a} `{GHC.Base.Eq_ inst_a}
   : Last inst_a -> Last inst_a -> bool :=
  GHC.Prim.coerce _GHC.Base./=_.

Program Instance Eq___Last {a} `{GHC.Base.Eq_ a} : GHC.Base.Eq_ (Last a) :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zeze____ := Eq___Last_op_zeze__ ;
           GHC.Base.op_zsze____ := Eq___Last_op_zsze__ |}.

Local Definition Ord__Last_op_zl__ {inst_a} `{GHC.Base.Ord inst_a}
   : Last inst_a -> Last inst_a -> bool :=
  GHC.Prim.coerce _GHC.Base.<_.

Local Definition Ord__Last_op_zlze__ {inst_a} `{GHC.Base.Ord inst_a}
   : Last inst_a -> Last inst_a -> bool :=
  GHC.Prim.coerce _GHC.Base.<=_.

Local Definition Ord__Last_op_zg__ {inst_a} `{GHC.Base.Ord inst_a}
   : Last inst_a -> Last inst_a -> bool :=
  GHC.Prim.coerce _GHC.Base.>_.

Local Definition Ord__Last_op_zgze__ {inst_a} `{GHC.Base.Ord inst_a}
   : Last inst_a -> Last inst_a -> bool :=
  GHC.Prim.coerce _GHC.Base.>=_.

Local Definition Ord__Last_compare {inst_a} `{GHC.Base.Ord inst_a}
   : Last inst_a -> Last inst_a -> comparison :=
  GHC.Prim.coerce GHC.Base.compare.

Local Definition Ord__Last_max {inst_a} `{GHC.Base.Ord inst_a}
   : Last inst_a -> Last inst_a -> Last inst_a :=
  GHC.Prim.coerce GHC.Base.max.

Local Definition Ord__Last_min {inst_a} `{GHC.Base.Ord inst_a}
   : Last inst_a -> Last inst_a -> Last inst_a :=
  GHC.Prim.coerce GHC.Base.min.

Program Instance Ord__Last {a} `{GHC.Base.Ord a} : GHC.Base.Ord (Last a) :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zl____ := Ord__Last_op_zl__ ;
           GHC.Base.op_zlze____ := Ord__Last_op_zlze__ ;
           GHC.Base.op_zg____ := Ord__Last_op_zg__ ;
           GHC.Base.op_zgze____ := Ord__Last_op_zgze__ ;
           GHC.Base.compare__ := Ord__Last_compare ;
           GHC.Base.max__ := Ord__Last_max ;
           GHC.Base.min__ := Ord__Last_min |}.

(* Skipping all instances of class `GHC.Read.Read', including
   `Data.Monoid.Read__Last' *)

(* Skipping all instances of class `GHC.Show.Show', including
   `Data.Monoid.Show__Last' *)

(* Skipping all instances of class `GHC.Generics.Generic', including
   `Data.Monoid.Generic__Last' *)

(* Skipping all instances of class `GHC.Generics.Generic1', including
   `Data.Monoid.Generic1__TYPE__Last__LiftedRep' *)

Local Definition Functor__Last_fmap
   : forall {a} {b}, (a -> b) -> Last a -> Last b :=
  fun {a} {b} => GHC.Prim.coerce GHC.Base.fmap.

Local Definition Functor__Last_op_zlzd__
   : forall {a} {b}, a -> Last b -> Last a :=
  fun {a} {b} => GHC.Prim.coerce _GHC.Base.<$_.

Program Instance Functor__Last : GHC.Base.Functor Last :=
  fun _ k__ =>
    k__ {| GHC.Base.fmap__ := fun {a} {b} => Functor__Last_fmap ;
           GHC.Base.op_zlzd____ := fun {a} {b} => Functor__Last_op_zlzd__ |}.

Local Definition Applicative__Last_liftA2
   : forall {a} {b} {c}, (a -> b -> c) -> Last a -> Last b -> Last c :=
  fun {a} {b} {c} => GHC.Prim.coerce GHC.Base.liftA2.

Local Definition Applicative__Last_op_zlztzg__
   : forall {a} {b}, Last (a -> b) -> Last a -> Last b :=
  fun {a} {b} => GHC.Prim.coerce _GHC.Base.<*>_.

Local Definition Applicative__Last_op_ztzg__
   : forall {a} {b}, Last a -> Last b -> Last b :=
  fun {a} {b} => GHC.Prim.coerce _GHC.Base.*>_.

Local Definition Applicative__Last_pure : forall {a}, a -> Last a :=
  fun {a} => GHC.Prim.coerce GHC.Base.pure.

Program Instance Applicative__Last : GHC.Base.Applicative Last :=
  fun _ k__ =>
    k__ {| GHC.Base.liftA2__ := fun {a} {b} {c} => Applicative__Last_liftA2 ;
           GHC.Base.op_zlztzg____ := fun {a} {b} => Applicative__Last_op_zlztzg__ ;
           GHC.Base.op_ztzg____ := fun {a} {b} => Applicative__Last_op_ztzg__ ;
           GHC.Base.pure__ := fun {a} => Applicative__Last_pure |}.

Local Definition Monad__Last_op_zgzg__
   : forall {a} {b}, Last a -> Last b -> Last b :=
  fun {a} {b} => GHC.Prim.coerce _GHC.Base.>>_.

Local Definition Monad__Last_op_zgzgze__
   : forall {a} {b}, Last a -> (a -> Last b) -> Last b :=
  fun {a} {b} => GHC.Prim.coerce _GHC.Base.>>=_.

Local Definition Monad__Last_return_ : forall {a}, a -> Last a :=
  fun {a} => GHC.Prim.coerce GHC.Base.return_.

Program Instance Monad__Last : GHC.Base.Monad Last :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zgzg____ := fun {a} {b} => Monad__Last_op_zgzg__ ;
           GHC.Base.op_zgzgze____ := fun {a} {b} => Monad__Last_op_zgzgze__ ;
           GHC.Base.return___ := fun {a} => Monad__Last_return_ |}.

Local Definition Semigroup__First_op_zlzlzgzg__ {inst_a}
   : (First inst_a) -> (First inst_a) -> (First inst_a) :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | Mk_First None, b => b
    | a, _ => a
    end.

Program Instance Semigroup__First {a} : GHC.Base.Semigroup (First a) :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zlzlzgzg____ := Semigroup__First_op_zlzlzgzg__ |}.

Local Definition Monoid__First_mappend {inst_a}
   : (First inst_a) -> (First inst_a) -> (First inst_a) :=
  _GHC.Base.<<>>_.

Local Definition Monoid__First_mempty {inst_a} : (First inst_a) :=
  Mk_First None.

Local Definition Monoid__First_mconcat {inst_a}
   : list (First inst_a) -> (First inst_a) :=
  GHC.Base.foldr Monoid__First_mappend Monoid__First_mempty.

Program Instance Monoid__First {a} : GHC.Base.Monoid (First a) :=
  fun _ k__ =>
    k__ {| GHC.Base.mappend__ := Monoid__First_mappend ;
           GHC.Base.mconcat__ := Monoid__First_mconcat ;
           GHC.Base.mempty__ := Monoid__First_mempty |}.

Local Definition Semigroup__Last_op_zlzlzgzg__ {inst_a}
   : (Last inst_a) -> (Last inst_a) -> (Last inst_a) :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | a, Mk_Last None => a
    | _, b => b
    end.

Program Instance Semigroup__Last {a} : GHC.Base.Semigroup (Last a) :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zlzlzgzg____ := Semigroup__Last_op_zlzlzgzg__ |}.

Local Definition Monoid__Last_mappend {inst_a}
   : (Last inst_a) -> (Last inst_a) -> (Last inst_a) :=
  _GHC.Base.<<>>_.

Local Definition Monoid__Last_mempty {inst_a} : (Last inst_a) :=
  Mk_Last None.

Local Definition Monoid__Last_mconcat {inst_a}
   : list (Last inst_a) -> (Last inst_a) :=
  GHC.Base.foldr Monoid__Last_mappend Monoid__Last_mempty.

Program Instance Monoid__Last {a} : GHC.Base.Monoid (Last a) :=
  fun _ k__ =>
    k__ {| GHC.Base.mappend__ := Monoid__Last_mappend ;
           GHC.Base.mconcat__ := Monoid__Last_mconcat ;
           GHC.Base.mempty__ := Monoid__Last_mempty |}.

(* External variables:
     None bool comparison list option GHC.Base.Applicative GHC.Base.Eq_
     GHC.Base.Functor GHC.Base.Monad GHC.Base.Monoid GHC.Base.Ord GHC.Base.Semigroup
     GHC.Base.compare GHC.Base.compare__ GHC.Base.fmap GHC.Base.fmap__ GHC.Base.foldr
     GHC.Base.liftA2 GHC.Base.liftA2__ GHC.Base.mappend__ GHC.Base.max GHC.Base.max__
     GHC.Base.mconcat__ GHC.Base.mempty__ GHC.Base.min GHC.Base.min__
     GHC.Base.op_zeze__ GHC.Base.op_zeze____ GHC.Base.op_zg__ GHC.Base.op_zg____
     GHC.Base.op_zgze__ GHC.Base.op_zgze____ GHC.Base.op_zgzg__ GHC.Base.op_zgzg____
     GHC.Base.op_zgzgze__ GHC.Base.op_zgzgze____ GHC.Base.op_zl__ GHC.Base.op_zl____
     GHC.Base.op_zlzd__ GHC.Base.op_zlzd____ GHC.Base.op_zlze__ GHC.Base.op_zlze____
     GHC.Base.op_zlzlzgzg__ GHC.Base.op_zlzlzgzg____ GHC.Base.op_zlztzg__
     GHC.Base.op_zlztzg____ GHC.Base.op_zsze__ GHC.Base.op_zsze____
     GHC.Base.op_ztzg__ GHC.Base.op_ztzg____ GHC.Base.pure GHC.Base.pure__
     GHC.Base.return_ GHC.Base.return___ GHC.Prim.Build_Unpeel GHC.Prim.Unpeel
     GHC.Prim.coerce
*)
