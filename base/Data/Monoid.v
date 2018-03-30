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

Inductive Last a : Type := Mk_Last : option a -> Last a.

Inductive First a : Type := Mk_First : option a -> First a.

Arguments Mk_Last {_} _.

Arguments Mk_First {_} _.

Definition getLast {a} (arg_0__ : Last a) :=
  let 'Mk_Last getLast := arg_0__ in
  getLast.

Definition getFirst {a} (arg_1__ : First a) :=
  let 'Mk_First getFirst := arg_1__ in
  getFirst.
(* Converted value declarations: *)

Instance Unpeel_First a : GHC.Prim.Unpeel (First a) (option a) :=
  GHC.Prim.Build_Unpeel _ _ getFirst Mk_First.

Instance Unpeel_Last a : GHC.Prim.Unpeel (Last a) (option a) :=
  GHC.Prim.Build_Unpeel _ _ getLast Mk_Last.

(* Translating `instance Semigroup__Last' failed: OOPS! Cannot find information
   for class Qualified "GHC.Base" "Semigroup" unsupported *)

(* Translating `instance Monoid__Last' failed: missing Qualified "GHC.Base"
   "mappend" in fromList [(Qualified "GHC.Base" "mconcat",Qualified "Data.Monoid"
   "Monoid__Last_mconcat"),(Qualified "GHC.Base" "mempty",Qualified "Data.Monoid"
   "Monoid__Last_mempty")] unsupported *)

(* Translating `instance Semigroup__First' failed: OOPS! Cannot find information
   for class Qualified "GHC.Base" "Semigroup" unsupported *)

(* Translating `instance Monoid__First' failed: missing Qualified "GHC.Base"
   "mappend" in fromList [(Qualified "GHC.Base" "mconcat",Qualified "Data.Monoid"
   "Monoid__First_mconcat"),(Qualified "GHC.Base" "mempty",Qualified "Data.Monoid"
   "Monoid__First_mempty")] unsupported *)

Local Definition Monad__Last_op_zgzg__
   : forall {a} {b}, Last a -> Last b -> Last b :=
  fun {a} {b} => GHC.Prim.coerce _GHC.Base.>>_.

Local Definition Monad__Last_op_zgzgze__
   : forall {a} {b}, Last a -> (a -> Last b) -> Last b :=
  fun {a} {b} => GHC.Prim.coerce _GHC.Base.>>=_.

Local Definition Monad__Last_return_ : forall {a}, a -> Last a :=
  fun {a} => GHC.Prim.coerce GHC.Base.return_.

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

Local Definition Functor__Last_fmap
   : forall {a} {b}, (a -> b) -> Last a -> Last b :=
  fun {a} {b} => GHC.Prim.coerce GHC.Base.fmap.

Local Definition Functor__Last_op_zlzd__
   : forall {a} {b}, a -> Last b -> Last a :=
  fun {a} {b} => GHC.Prim.coerce _GHC.Base.<$_.

Program Instance Functor__Last : GHC.Base.Functor Last :=
  fun _ k =>
    k {| GHC.Base.op_zlzd____ := fun {a} {b} => Functor__Last_op_zlzd__ ;
         GHC.Base.fmap__ := fun {a} {b} => Functor__Last_fmap |}.

Program Instance Applicative__Last : GHC.Base.Applicative Last :=
  fun _ k =>
    k {| GHC.Base.op_ztzg____ := fun {a} {b} => Applicative__Last_op_ztzg__ ;
         GHC.Base.op_zlztzg____ := fun {a} {b} => Applicative__Last_op_zlztzg__ ;
         GHC.Base.liftA2__ := fun {a} {b} {c} => Applicative__Last_liftA2 ;
         GHC.Base.pure__ := fun {a} => Applicative__Last_pure |}.

Program Instance Monad__Last : GHC.Base.Monad Last :=
  fun _ k =>
    k {| GHC.Base.op_zgzg____ := fun {a} {b} => Monad__Last_op_zgzg__ ;
         GHC.Base.op_zgzgze____ := fun {a} {b} => Monad__Last_op_zgzgze__ ;
         GHC.Base.return___ := fun {a} => Monad__Last_return_ |}.

(* Translating `instance Generic1__TYPE__Last__LiftedRep' failed: OOPS! Cannot
   find information for class Qualified "GHC.Generics" "Generic1" unsupported *)

(* Translating `instance Generic__Last' failed: OOPS! Cannot find information
   for class Qualified "GHC.Generics" "Generic" unsupported *)

(* Skipping instance Show__Last *)

(* Skipping instance Read__Last *)

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

Local Definition Monad__First_op_zgzg__
   : forall {a} {b}, First a -> First b -> First b :=
  fun {a} {b} => GHC.Prim.coerce _GHC.Base.>>_.

Local Definition Monad__First_op_zgzgze__
   : forall {a} {b}, First a -> (a -> First b) -> First b :=
  fun {a} {b} => GHC.Prim.coerce _GHC.Base.>>=_.

Local Definition Monad__First_return_ : forall {a}, a -> First a :=
  fun {a} => GHC.Prim.coerce GHC.Base.return_.

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

Local Definition Functor__First_fmap
   : forall {a} {b}, (a -> b) -> First a -> First b :=
  fun {a} {b} => GHC.Prim.coerce GHC.Base.fmap.

Local Definition Functor__First_op_zlzd__
   : forall {a} {b}, a -> First b -> First a :=
  fun {a} {b} => GHC.Prim.coerce _GHC.Base.<$_.

Program Instance Functor__First : GHC.Base.Functor First :=
  fun _ k =>
    k {| GHC.Base.op_zlzd____ := fun {a} {b} => Functor__First_op_zlzd__ ;
         GHC.Base.fmap__ := fun {a} {b} => Functor__First_fmap |}.

Program Instance Applicative__First : GHC.Base.Applicative First :=
  fun _ k =>
    k {| GHC.Base.op_ztzg____ := fun {a} {b} => Applicative__First_op_ztzg__ ;
         GHC.Base.op_zlztzg____ := fun {a} {b} => Applicative__First_op_zlztzg__ ;
         GHC.Base.liftA2__ := fun {a} {b} {c} => Applicative__First_liftA2 ;
         GHC.Base.pure__ := fun {a} => Applicative__First_pure |}.

Program Instance Monad__First : GHC.Base.Monad First :=
  fun _ k =>
    k {| GHC.Base.op_zgzg____ := fun {a} {b} => Monad__First_op_zgzg__ ;
         GHC.Base.op_zgzgze____ := fun {a} {b} => Monad__First_op_zgzgze__ ;
         GHC.Base.return___ := fun {a} => Monad__First_return_ |}.

(* Translating `instance Generic1__TYPE__First__LiftedRep' failed: OOPS! Cannot
   find information for class Qualified "GHC.Generics" "Generic1" unsupported *)

(* Translating `instance Generic__First' failed: OOPS! Cannot find information
   for class Qualified "GHC.Generics" "Generic" unsupported *)

(* Skipping instance Show__First *)

(* Skipping instance Read__First *)

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

(* Unbound variables:
     bool comparison option GHC.Base.Applicative GHC.Base.Eq_ GHC.Base.Functor
     GHC.Base.Monad GHC.Base.Ord GHC.Base.compare GHC.Base.fmap GHC.Base.liftA2
     GHC.Base.max GHC.Base.min GHC.Base.op_zeze__ GHC.Base.op_zg__ GHC.Base.op_zgze__
     GHC.Base.op_zgzg__ GHC.Base.op_zgzgze__ GHC.Base.op_zl__ GHC.Base.op_zlzd__
     GHC.Base.op_zlze__ GHC.Base.op_zlztzg__ GHC.Base.op_zsze__ GHC.Base.op_ztzg__
     GHC.Base.pure GHC.Base.return_ GHC.Prim.Build_Unpeel GHC.Prim.Unpeel
     GHC.Prim.coerce
*)
