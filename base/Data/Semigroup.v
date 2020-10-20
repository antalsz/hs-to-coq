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
Require Data.Bifoldable.
Require Data.Bifunctor.
Require Data.Bitraversable.
Require Data.Foldable.
Require Data.Functor.
Require Data.Maybe.
Require Data.SemigroupInternal.
Require Data.Traversable.
Require GHC.Base.
Require GHC.Num.
Require GHC.Prim.
Import Data.Functor.Notations.
Import GHC.Base.Notations.
Import GHC.Num.Notations.

(* Converted type declarations: *)

Inductive WrappedMonoid m : Type
  := | WrapMonoid (unwrapMonoid : m) : WrappedMonoid m.

Inductive Option a : Type := | Mk_Option (getOption : option a) : Option a.

Inductive Min a : Type := | Mk_Min (getMin : a) : Min a.

Inductive Max a : Type := | Mk_Max (getMax : a) : Max a.

Inductive Last a : Type := | Mk_Last (getLast : a) : Last a.

Inductive First a : Type := | Mk_First (getFirst : a) : First a.

Inductive Arg a b : Type := | Mk_Arg : a -> b -> Arg a b.

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

Definition getOption {a} (arg_0__ : Option a) :=
  let 'Mk_Option getOption := arg_0__ in
  getOption.

Definition getMin {a} (arg_0__ : Min a) :=
  let 'Mk_Min getMin := arg_0__ in
  getMin.

Definition getMax {a} (arg_0__ : Max a) :=
  let 'Mk_Max getMax := arg_0__ in
  getMax.

Definition getLast {a} (arg_0__ : Last a) :=
  let 'Mk_Last getLast := arg_0__ in
  getLast.

Definition getFirst {a} (arg_0__ : First a) :=
  let 'Mk_First getFirst := arg_0__ in
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

(* Skipping all instances of class `GHC.Enum.Bounded', including
   `Data.Semigroup.Bounded__Min' *)

Instance Unpeel_Min a : GHC.Prim.Unpeel (Min a) a :=
  GHC.Prim.Build_Unpeel _ _ getMin Mk_Min.

Local Definition Eq___Min_op_zeze__ {inst_a} `{GHC.Base.Eq_ inst_a}
   : Min inst_a -> Min inst_a -> bool :=
  GHC.Prim.coerce _GHC.Base.==_.

Local Definition Eq___Min_op_zsze__ {inst_a} `{GHC.Base.Eq_ inst_a}
   : Min inst_a -> Min inst_a -> bool :=
  GHC.Prim.coerce _GHC.Base./=_.

Program Instance Eq___Min {a} `{GHC.Base.Eq_ a} : GHC.Base.Eq_ (Min a) :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zeze____ := Eq___Min_op_zeze__ ;
           GHC.Base.op_zsze____ := Eq___Min_op_zsze__ |}.

Local Definition Ord__Min_op_zl__ {inst_a} `{GHC.Base.Ord inst_a}
   : Min inst_a -> Min inst_a -> bool :=
  GHC.Prim.coerce _GHC.Base.<_.

Local Definition Ord__Min_op_zlze__ {inst_a} `{GHC.Base.Ord inst_a}
   : Min inst_a -> Min inst_a -> bool :=
  GHC.Prim.coerce _GHC.Base.<=_.

Local Definition Ord__Min_op_zg__ {inst_a} `{GHC.Base.Ord inst_a}
   : Min inst_a -> Min inst_a -> bool :=
  GHC.Prim.coerce _GHC.Base.>_.

Local Definition Ord__Min_op_zgze__ {inst_a} `{GHC.Base.Ord inst_a}
   : Min inst_a -> Min inst_a -> bool :=
  GHC.Prim.coerce _GHC.Base.>=_.

Local Definition Ord__Min_compare {inst_a} `{GHC.Base.Ord inst_a}
   : Min inst_a -> Min inst_a -> comparison :=
  GHC.Prim.coerce GHC.Base.compare.

Local Definition Ord__Min_max {inst_a} `{GHC.Base.Ord inst_a}
   : Min inst_a -> Min inst_a -> Min inst_a :=
  GHC.Prim.coerce GHC.Base.max.

Local Definition Ord__Min_min {inst_a} `{GHC.Base.Ord inst_a}
   : Min inst_a -> Min inst_a -> Min inst_a :=
  GHC.Prim.coerce GHC.Base.min.

Program Instance Ord__Min {a} `{GHC.Base.Ord a} : GHC.Base.Ord (Min a) :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zl____ := Ord__Min_op_zl__ ;
           GHC.Base.op_zlze____ := Ord__Min_op_zlze__ ;
           GHC.Base.op_zg____ := Ord__Min_op_zg__ ;
           GHC.Base.op_zgze____ := Ord__Min_op_zgze__ ;
           GHC.Base.compare__ := Ord__Min_compare ;
           GHC.Base.max__ := Ord__Min_max ;
           GHC.Base.min__ := Ord__Min_min |}.

(* Skipping all instances of class `GHC.Show.Show', including
   `Data.Semigroup.Show__Min' *)

(* Skipping all instances of class `GHC.Read.Read', including
   `Data.Semigroup.Read__Min' *)

(* Skipping all instances of class `Data.Data.Data', including
   `Data.Semigroup.Data__Min' *)

(* Skipping all instances of class `GHC.Generics.Generic', including
   `Data.Semigroup.Generic__Min' *)

(* Skipping all instances of class `GHC.Generics.Generic1', including
   `Data.Semigroup.Generic1__TYPE__Min__LiftedRep' *)

(* Skipping all instances of class `GHC.Enum.Bounded', including
   `Data.Semigroup.Bounded__Max' *)

Instance Unpeel_Max a : GHC.Prim.Unpeel (Max a) a :=
  GHC.Prim.Build_Unpeel _ _ getMax Mk_Max.

Local Definition Eq___Max_op_zeze__ {inst_a} `{GHC.Base.Eq_ inst_a}
   : Max inst_a -> Max inst_a -> bool :=
  GHC.Prim.coerce _GHC.Base.==_.

Local Definition Eq___Max_op_zsze__ {inst_a} `{GHC.Base.Eq_ inst_a}
   : Max inst_a -> Max inst_a -> bool :=
  GHC.Prim.coerce _GHC.Base./=_.

Program Instance Eq___Max {a} `{GHC.Base.Eq_ a} : GHC.Base.Eq_ (Max a) :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zeze____ := Eq___Max_op_zeze__ ;
           GHC.Base.op_zsze____ := Eq___Max_op_zsze__ |}.

Local Definition Ord__Max_op_zl__ {inst_a} `{GHC.Base.Ord inst_a}
   : Max inst_a -> Max inst_a -> bool :=
  GHC.Prim.coerce _GHC.Base.<_.

Local Definition Ord__Max_op_zlze__ {inst_a} `{GHC.Base.Ord inst_a}
   : Max inst_a -> Max inst_a -> bool :=
  GHC.Prim.coerce _GHC.Base.<=_.

Local Definition Ord__Max_op_zg__ {inst_a} `{GHC.Base.Ord inst_a}
   : Max inst_a -> Max inst_a -> bool :=
  GHC.Prim.coerce _GHC.Base.>_.

Local Definition Ord__Max_op_zgze__ {inst_a} `{GHC.Base.Ord inst_a}
   : Max inst_a -> Max inst_a -> bool :=
  GHC.Prim.coerce _GHC.Base.>=_.

Local Definition Ord__Max_compare {inst_a} `{GHC.Base.Ord inst_a}
   : Max inst_a -> Max inst_a -> comparison :=
  GHC.Prim.coerce GHC.Base.compare.

Local Definition Ord__Max_max {inst_a} `{GHC.Base.Ord inst_a}
   : Max inst_a -> Max inst_a -> Max inst_a :=
  GHC.Prim.coerce GHC.Base.max.

Local Definition Ord__Max_min {inst_a} `{GHC.Base.Ord inst_a}
   : Max inst_a -> Max inst_a -> Max inst_a :=
  GHC.Prim.coerce GHC.Base.min.

Program Instance Ord__Max {a} `{GHC.Base.Ord a} : GHC.Base.Ord (Max a) :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zl____ := Ord__Max_op_zl__ ;
           GHC.Base.op_zlze____ := Ord__Max_op_zlze__ ;
           GHC.Base.op_zg____ := Ord__Max_op_zg__ ;
           GHC.Base.op_zgze____ := Ord__Max_op_zgze__ ;
           GHC.Base.compare__ := Ord__Max_compare ;
           GHC.Base.max__ := Ord__Max_max ;
           GHC.Base.min__ := Ord__Max_min |}.

(* Skipping all instances of class `GHC.Show.Show', including
   `Data.Semigroup.Show__Max' *)

(* Skipping all instances of class `GHC.Read.Read', including
   `Data.Semigroup.Read__Max' *)

(* Skipping all instances of class `Data.Data.Data', including
   `Data.Semigroup.Data__Max' *)

(* Skipping all instances of class `GHC.Generics.Generic', including
   `Data.Semigroup.Generic__Max' *)

(* Skipping all instances of class `GHC.Generics.Generic1', including
   `Data.Semigroup.Generic1__TYPE__Max__LiftedRep' *)

(* Skipping all instances of class `GHC.Show.Show', including
   `Data.Semigroup.Show__Arg' *)

(* Skipping all instances of class `GHC.Read.Read', including
   `Data.Semigroup.Read__Arg' *)

(* Skipping all instances of class `Data.Data.Data', including
   `Data.Semigroup.Data__Arg' *)

(* Skipping all instances of class `GHC.Generics.Generic', including
   `Data.Semigroup.Generic__Arg' *)

(* Skipping all instances of class `GHC.Generics.Generic1', including
   `Data.Semigroup.Generic1__TYPE__Arg__LiftedRep' *)

(* Skipping all instances of class `GHC.Enum.Bounded', including
   `Data.Semigroup.Bounded__First' *)

Instance Unpeel_First a : GHC.Prim.Unpeel (First a) a :=
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

(* Skipping all instances of class `GHC.Show.Show', including
   `Data.Semigroup.Show__First' *)

(* Skipping all instances of class `GHC.Read.Read', including
   `Data.Semigroup.Read__First' *)

(* Skipping all instances of class `Data.Data.Data', including
   `Data.Semigroup.Data__First' *)

(* Skipping all instances of class `GHC.Generics.Generic', including
   `Data.Semigroup.Generic__First' *)

(* Skipping all instances of class `GHC.Generics.Generic1', including
   `Data.Semigroup.Generic1__TYPE__First__LiftedRep' *)

(* Skipping all instances of class `GHC.Enum.Bounded', including
   `Data.Semigroup.Bounded__Last' *)

Instance Unpeel_Last a : GHC.Prim.Unpeel (Last a) a :=
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

(* Skipping all instances of class `GHC.Show.Show', including
   `Data.Semigroup.Show__Last' *)

(* Skipping all instances of class `GHC.Read.Read', including
   `Data.Semigroup.Read__Last' *)

(* Skipping all instances of class `Data.Data.Data', including
   `Data.Semigroup.Data__Last' *)

(* Skipping all instances of class `GHC.Generics.Generic', including
   `Data.Semigroup.Generic__Last' *)

(* Skipping all instances of class `GHC.Generics.Generic1', including
   `Data.Semigroup.Generic1__TYPE__Last__LiftedRep' *)

(* Skipping all instances of class `GHC.Enum.Bounded', including
   `Data.Semigroup.Bounded__WrappedMonoid' *)

Instance Unpeel_WrappedMonoid a : GHC.Prim.Unpeel (WrappedMonoid a) a :=
  GHC.Prim.Build_Unpeel _ _ unwrapMonoid WrapMonoid.

Local Definition Eq___WrappedMonoid_op_zeze__ {inst_m} `{GHC.Base.Eq_ inst_m}
   : WrappedMonoid inst_m -> WrappedMonoid inst_m -> bool :=
  GHC.Prim.coerce _GHC.Base.==_.

Local Definition Eq___WrappedMonoid_op_zsze__ {inst_m} `{GHC.Base.Eq_ inst_m}
   : WrappedMonoid inst_m -> WrappedMonoid inst_m -> bool :=
  GHC.Prim.coerce _GHC.Base./=_.

Program Instance Eq___WrappedMonoid {m} `{GHC.Base.Eq_ m}
   : GHC.Base.Eq_ (WrappedMonoid m) :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zeze____ := Eq___WrappedMonoid_op_zeze__ ;
           GHC.Base.op_zsze____ := Eq___WrappedMonoid_op_zsze__ |}.

Local Definition Ord__WrappedMonoid_op_zl__ {inst_m} `{GHC.Base.Ord inst_m}
   : WrappedMonoid inst_m -> WrappedMonoid inst_m -> bool :=
  GHC.Prim.coerce _GHC.Base.<_.

Local Definition Ord__WrappedMonoid_op_zlze__ {inst_m} `{GHC.Base.Ord inst_m}
   : WrappedMonoid inst_m -> WrappedMonoid inst_m -> bool :=
  GHC.Prim.coerce _GHC.Base.<=_.

Local Definition Ord__WrappedMonoid_op_zg__ {inst_m} `{GHC.Base.Ord inst_m}
   : WrappedMonoid inst_m -> WrappedMonoid inst_m -> bool :=
  GHC.Prim.coerce _GHC.Base.>_.

Local Definition Ord__WrappedMonoid_op_zgze__ {inst_m} `{GHC.Base.Ord inst_m}
   : WrappedMonoid inst_m -> WrappedMonoid inst_m -> bool :=
  GHC.Prim.coerce _GHC.Base.>=_.

Local Definition Ord__WrappedMonoid_compare {inst_m} `{GHC.Base.Ord inst_m}
   : WrappedMonoid inst_m -> WrappedMonoid inst_m -> comparison :=
  GHC.Prim.coerce GHC.Base.compare.

Local Definition Ord__WrappedMonoid_max {inst_m} `{GHC.Base.Ord inst_m}
   : WrappedMonoid inst_m -> WrappedMonoid inst_m -> WrappedMonoid inst_m :=
  GHC.Prim.coerce GHC.Base.max.

Local Definition Ord__WrappedMonoid_min {inst_m} `{GHC.Base.Ord inst_m}
   : WrappedMonoid inst_m -> WrappedMonoid inst_m -> WrappedMonoid inst_m :=
  GHC.Prim.coerce GHC.Base.min.

Program Instance Ord__WrappedMonoid {m} `{GHC.Base.Ord m}
   : GHC.Base.Ord (WrappedMonoid m) :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zl____ := Ord__WrappedMonoid_op_zl__ ;
           GHC.Base.op_zlze____ := Ord__WrappedMonoid_op_zlze__ ;
           GHC.Base.op_zg____ := Ord__WrappedMonoid_op_zg__ ;
           GHC.Base.op_zgze____ := Ord__WrappedMonoid_op_zgze__ ;
           GHC.Base.compare__ := Ord__WrappedMonoid_compare ;
           GHC.Base.max__ := Ord__WrappedMonoid_max ;
           GHC.Base.min__ := Ord__WrappedMonoid_min |}.

(* Skipping all instances of class `GHC.Show.Show', including
   `Data.Semigroup.Show__WrappedMonoid' *)

(* Skipping all instances of class `GHC.Read.Read', including
   `Data.Semigroup.Read__WrappedMonoid' *)

(* Skipping all instances of class `Data.Data.Data', including
   `Data.Semigroup.Data__WrappedMonoid' *)

(* Skipping all instances of class `GHC.Generics.Generic', including
   `Data.Semigroup.Generic__WrappedMonoid' *)

(* Skipping all instances of class `GHC.Generics.Generic1', including
   `Data.Semigroup.Generic1__TYPE__WrappedMonoid__LiftedRep' *)

Instance Unpeel_Option a : GHC.Prim.Unpeel (Option a) (option a) :=
  GHC.Prim.Build_Unpeel _ _ getOption Mk_Option.

Local Definition Eq___Option_op_zeze__ {inst_a} `{GHC.Base.Eq_ inst_a}
   : Option inst_a -> Option inst_a -> bool :=
  GHC.Prim.coerce _GHC.Base.==_.

Local Definition Eq___Option_op_zsze__ {inst_a} `{GHC.Base.Eq_ inst_a}
   : Option inst_a -> Option inst_a -> bool :=
  GHC.Prim.coerce _GHC.Base./=_.

Program Instance Eq___Option {a} `{GHC.Base.Eq_ a} : GHC.Base.Eq_ (Option a) :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zeze____ := Eq___Option_op_zeze__ ;
           GHC.Base.op_zsze____ := Eq___Option_op_zsze__ |}.

Local Definition Ord__Option_op_zl__ {inst_a} `{GHC.Base.Ord inst_a}
   : Option inst_a -> Option inst_a -> bool :=
  GHC.Prim.coerce _GHC.Base.<_.

Local Definition Ord__Option_op_zlze__ {inst_a} `{GHC.Base.Ord inst_a}
   : Option inst_a -> Option inst_a -> bool :=
  GHC.Prim.coerce _GHC.Base.<=_.

Local Definition Ord__Option_op_zg__ {inst_a} `{GHC.Base.Ord inst_a}
   : Option inst_a -> Option inst_a -> bool :=
  GHC.Prim.coerce _GHC.Base.>_.

Local Definition Ord__Option_op_zgze__ {inst_a} `{GHC.Base.Ord inst_a}
   : Option inst_a -> Option inst_a -> bool :=
  GHC.Prim.coerce _GHC.Base.>=_.

Local Definition Ord__Option_compare {inst_a} `{GHC.Base.Ord inst_a}
   : Option inst_a -> Option inst_a -> comparison :=
  GHC.Prim.coerce GHC.Base.compare.

Local Definition Ord__Option_max {inst_a} `{GHC.Base.Ord inst_a}
   : Option inst_a -> Option inst_a -> Option inst_a :=
  GHC.Prim.coerce GHC.Base.max.

Local Definition Ord__Option_min {inst_a} `{GHC.Base.Ord inst_a}
   : Option inst_a -> Option inst_a -> Option inst_a :=
  GHC.Prim.coerce GHC.Base.min.

Program Instance Ord__Option {a} `{GHC.Base.Ord a} : GHC.Base.Ord (Option a) :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zl____ := Ord__Option_op_zl__ ;
           GHC.Base.op_zlze____ := Ord__Option_op_zlze__ ;
           GHC.Base.op_zg____ := Ord__Option_op_zg__ ;
           GHC.Base.op_zgze____ := Ord__Option_op_zgze__ ;
           GHC.Base.compare__ := Ord__Option_compare ;
           GHC.Base.max__ := Ord__Option_max ;
           GHC.Base.min__ := Ord__Option_min |}.

(* Skipping all instances of class `GHC.Show.Show', including
   `Data.Semigroup.Show__Option' *)

(* Skipping all instances of class `GHC.Read.Read', including
   `Data.Semigroup.Read__Option' *)

(* Skipping all instances of class `Data.Data.Data', including
   `Data.Semigroup.Data__Option' *)

(* Skipping all instances of class `GHC.Generics.Generic', including
   `Data.Semigroup.Generic__Option' *)

(* Skipping all instances of class `GHC.Generics.Generic1', including
   `Data.Semigroup.Generic1__TYPE__Option__LiftedRep' *)

(* Skipping all instances of class `GHC.Enum.Enum', including
   `Data.Semigroup.Enum__Min' *)

Local Definition Semigroup__Min_op_zlzlzgzg__ {inst_a} `{_
   : GHC.Base.Ord inst_a}
   : Min inst_a -> Min inst_a -> Min inst_a :=
  GHC.Prim.coerce (@GHC.Base.min inst_a _ _).

Program Instance Semigroup__Min {a} `{GHC.Base.Ord a}
   : GHC.Base.Semigroup (Min a) :=
  fun _ k__ => k__ {| GHC.Base.op_zlzlzgzg____ := Semigroup__Min_op_zlzlzgzg__ |}.

(* Skipping instance `Data.Semigroup.Monoid__Min' of class `GHC.Base.Monoid' *)

Local Definition Functor__Min_fmap
   : forall {a} {b}, (a -> b) -> Min a -> Min b :=
  fun {a} {b} =>
    fun arg_0__ arg_1__ =>
      match arg_0__, arg_1__ with
      | f, Mk_Min x => Mk_Min (f x)
      end.

Local Definition Functor__Min_op_zlzd__ : forall {a} {b}, a -> Min b -> Min a :=
  fun {a} {b} => Functor__Min_fmap GHC.Base.∘ GHC.Base.const.

Program Instance Functor__Min : GHC.Base.Functor Min :=
  fun _ k__ =>
    k__ {| GHC.Base.fmap__ := fun {a} {b} => Functor__Min_fmap ;
           GHC.Base.op_zlzd____ := fun {a} {b} => Functor__Min_op_zlzd__ |}.

Local Definition Foldable__Min_foldMap
   : forall {m} {a}, forall `{GHC.Base.Monoid m}, (a -> m) -> Min a -> m :=
  fun {m} {a} `{GHC.Base.Monoid m} =>
    fun arg_0__ arg_1__ => match arg_0__, arg_1__ with | f, Mk_Min a => f a end.

Local Definition Foldable__Min_fold
   : forall {m}, forall `{GHC.Base.Monoid m}, Min m -> m :=
  fun {m} `{GHC.Base.Monoid m} => Foldable__Min_foldMap GHC.Base.id.

Local Definition Foldable__Min_foldl
   : forall {b} {a}, (b -> a -> b) -> b -> Min a -> b :=
  fun {b} {a} =>
    fun f z t =>
      Data.SemigroupInternal.appEndo (Data.SemigroupInternal.getDual
                                      (Foldable__Min_foldMap (Data.SemigroupInternal.Mk_Dual GHC.Base.∘
                                                              (Data.SemigroupInternal.Mk_Endo GHC.Base.∘
                                                               GHC.Base.flip f)) t)) z.

Local Definition Foldable__Min_foldr
   : forall {a} {b}, (a -> b -> b) -> b -> Min a -> b :=
  fun {a} {b} =>
    fun f z t =>
      Data.SemigroupInternal.appEndo (Foldable__Min_foldMap
                                      (Coq.Program.Basics.compose Data.SemigroupInternal.Mk_Endo f) t) z.

Local Definition Foldable__Min_foldl'
   : forall {b} {a}, (b -> a -> b) -> b -> Min a -> b :=
  fun {b} {a} =>
    fun f z0 xs =>
      let f' := fun x k z => k (f z x) in Foldable__Min_foldr f' GHC.Base.id xs z0.

Local Definition Foldable__Min_foldr'
   : forall {a} {b}, (a -> b -> b) -> b -> Min a -> b :=
  fun {a} {b} =>
    fun f z0 xs =>
      let f' := fun k x z => k (f x z) in Foldable__Min_foldl f' GHC.Base.id xs z0.

Local Definition Foldable__Min_length : forall {a}, Min a -> GHC.Num.Int :=
  fun {a} =>
    Foldable__Min_foldl' (fun arg_0__ arg_1__ =>
                            match arg_0__, arg_1__ with
                            | c, _ => c GHC.Num.+ #1
                            end) #0.

Local Definition Foldable__Min_null : forall {a}, Min a -> bool :=
  fun {a} => Foldable__Min_foldr (fun arg_0__ arg_1__ => false) true.

Local Definition Foldable__Min_product
   : forall {a}, forall `{GHC.Num.Num a}, Min a -> a :=
  fun {a} `{GHC.Num.Num a} =>
    Coq.Program.Basics.compose Data.SemigroupInternal.getProduct
                               (Foldable__Min_foldMap Data.SemigroupInternal.Mk_Product).

Local Definition Foldable__Min_sum
   : forall {a}, forall `{GHC.Num.Num a}, Min a -> a :=
  fun {a} `{GHC.Num.Num a} =>
    Coq.Program.Basics.compose Data.SemigroupInternal.getSum (Foldable__Min_foldMap
                                Data.SemigroupInternal.Mk_Sum).

Local Definition Foldable__Min_toList : forall {a}, Min a -> list a :=
  fun {a} =>
    fun t => GHC.Base.build' (fun _ => (fun c n => Foldable__Min_foldr c n t)).

Program Instance Foldable__Min : Data.Foldable.Foldable Min :=
  fun _ k__ =>
    k__ {| Data.Foldable.fold__ := fun {m} `{GHC.Base.Monoid m} =>
             Foldable__Min_fold ;
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

Local Definition Traversable__Min_mapM
   : forall {m} {a} {b},
     forall `{GHC.Base.Monad m}, (a -> m b) -> Min a -> m (Min b) :=
  fun {m} {a} {b} `{GHC.Base.Monad m} => Traversable__Min_traverse.

Local Definition Traversable__Min_sequenceA
   : forall {f} {a}, forall `{GHC.Base.Applicative f}, Min (f a) -> f (Min a) :=
  fun {f} {a} `{GHC.Base.Applicative f} => Traversable__Min_traverse GHC.Base.id.

Local Definition Traversable__Min_sequence
   : forall {m} {a}, forall `{GHC.Base.Monad m}, Min (m a) -> m (Min a) :=
  fun {m} {a} `{GHC.Base.Monad m} => Traversable__Min_sequenceA.

Program Instance Traversable__Min : Data.Traversable.Traversable Min :=
  fun _ k__ =>
    k__ {| Data.Traversable.mapM__ := fun {m} {a} {b} `{GHC.Base.Monad m} =>
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
  fun _ k__ =>
    k__ {| GHC.Base.liftA2__ := fun {a} {b} {c} => Applicative__Min_liftA2 ;
           GHC.Base.op_zlztzg____ := fun {a} {b} => Applicative__Min_op_zlztzg__ ;
           GHC.Base.op_ztzg____ := fun {a} {b} => Applicative__Min_op_ztzg__ ;
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
  fun _ k__ =>
    k__ {| GHC.Base.op_zgzg____ := fun {a} {b} => Monad__Min_op_zgzg__ ;
           GHC.Base.op_zgzgze____ := fun {a} {b} => Monad__Min_op_zgzgze__ ;
           GHC.Base.return___ := fun {a} => Monad__Min_return_ |}.

(* Skipping all instances of class `Control.Monad.Fix.MonadFix', including
   `Data.Semigroup.MonadFix__Min' *)

(* Skipping all instances of class `GHC.Num.Num', including
   `Data.Semigroup.Num__Min' *)

(* Skipping all instances of class `GHC.Enum.Enum', including
   `Data.Semigroup.Enum__Max' *)

Local Definition Semigroup__Max_op_zlzlzgzg__ {inst_a} `{_
   : GHC.Base.Ord inst_a}
   : Max inst_a -> Max inst_a -> Max inst_a :=
  GHC.Prim.coerce (@GHC.Base.max inst_a _ _).

Program Instance Semigroup__Max {a} `{GHC.Base.Ord a}
   : GHC.Base.Semigroup (Max a) :=
  fun _ k__ => k__ {| GHC.Base.op_zlzlzgzg____ := Semigroup__Max_op_zlzlzgzg__ |}.

(* Skipping instance `Data.Semigroup.Monoid__Max' of class `GHC.Base.Monoid' *)

Local Definition Functor__Max_fmap
   : forall {a} {b}, (a -> b) -> Max a -> Max b :=
  fun {a} {b} =>
    fun arg_0__ arg_1__ =>
      match arg_0__, arg_1__ with
      | f, Mk_Max x => Mk_Max (f x)
      end.

Local Definition Functor__Max_op_zlzd__ : forall {a} {b}, a -> Max b -> Max a :=
  fun {a} {b} => Functor__Max_fmap GHC.Base.∘ GHC.Base.const.

Program Instance Functor__Max : GHC.Base.Functor Max :=
  fun _ k__ =>
    k__ {| GHC.Base.fmap__ := fun {a} {b} => Functor__Max_fmap ;
           GHC.Base.op_zlzd____ := fun {a} {b} => Functor__Max_op_zlzd__ |}.

Local Definition Foldable__Max_foldMap
   : forall {m} {a}, forall `{GHC.Base.Monoid m}, (a -> m) -> Max a -> m :=
  fun {m} {a} `{GHC.Base.Monoid m} =>
    fun arg_0__ arg_1__ => match arg_0__, arg_1__ with | f, Mk_Max a => f a end.

Local Definition Foldable__Max_fold
   : forall {m}, forall `{GHC.Base.Monoid m}, Max m -> m :=
  fun {m} `{GHC.Base.Monoid m} => Foldable__Max_foldMap GHC.Base.id.

Local Definition Foldable__Max_foldl
   : forall {b} {a}, (b -> a -> b) -> b -> Max a -> b :=
  fun {b} {a} =>
    fun f z t =>
      Data.SemigroupInternal.appEndo (Data.SemigroupInternal.getDual
                                      (Foldable__Max_foldMap (Data.SemigroupInternal.Mk_Dual GHC.Base.∘
                                                              (Data.SemigroupInternal.Mk_Endo GHC.Base.∘
                                                               GHC.Base.flip f)) t)) z.

Local Definition Foldable__Max_foldr
   : forall {a} {b}, (a -> b -> b) -> b -> Max a -> b :=
  fun {a} {b} =>
    fun f z t =>
      Data.SemigroupInternal.appEndo (Foldable__Max_foldMap
                                      (Coq.Program.Basics.compose Data.SemigroupInternal.Mk_Endo f) t) z.

Local Definition Foldable__Max_foldl'
   : forall {b} {a}, (b -> a -> b) -> b -> Max a -> b :=
  fun {b} {a} =>
    fun f z0 xs =>
      let f' := fun x k z => k (f z x) in Foldable__Max_foldr f' GHC.Base.id xs z0.

Local Definition Foldable__Max_foldr'
   : forall {a} {b}, (a -> b -> b) -> b -> Max a -> b :=
  fun {a} {b} =>
    fun f z0 xs =>
      let f' := fun k x z => k (f x z) in Foldable__Max_foldl f' GHC.Base.id xs z0.

Local Definition Foldable__Max_length : forall {a}, Max a -> GHC.Num.Int :=
  fun {a} =>
    Foldable__Max_foldl' (fun arg_0__ arg_1__ =>
                            match arg_0__, arg_1__ with
                            | c, _ => c GHC.Num.+ #1
                            end) #0.

Local Definition Foldable__Max_null : forall {a}, Max a -> bool :=
  fun {a} => Foldable__Max_foldr (fun arg_0__ arg_1__ => false) true.

Local Definition Foldable__Max_product
   : forall {a}, forall `{GHC.Num.Num a}, Max a -> a :=
  fun {a} `{GHC.Num.Num a} =>
    Coq.Program.Basics.compose Data.SemigroupInternal.getProduct
                               (Foldable__Max_foldMap Data.SemigroupInternal.Mk_Product).

Local Definition Foldable__Max_sum
   : forall {a}, forall `{GHC.Num.Num a}, Max a -> a :=
  fun {a} `{GHC.Num.Num a} =>
    Coq.Program.Basics.compose Data.SemigroupInternal.getSum (Foldable__Max_foldMap
                                Data.SemigroupInternal.Mk_Sum).

Local Definition Foldable__Max_toList : forall {a}, Max a -> list a :=
  fun {a} =>
    fun t => GHC.Base.build' (fun _ => (fun c n => Foldable__Max_foldr c n t)).

Program Instance Foldable__Max : Data.Foldable.Foldable Max :=
  fun _ k__ =>
    k__ {| Data.Foldable.fold__ := fun {m} `{GHC.Base.Monoid m} =>
             Foldable__Max_fold ;
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

Local Definition Traversable__Max_mapM
   : forall {m} {a} {b},
     forall `{GHC.Base.Monad m}, (a -> m b) -> Max a -> m (Max b) :=
  fun {m} {a} {b} `{GHC.Base.Monad m} => Traversable__Max_traverse.

Local Definition Traversable__Max_sequenceA
   : forall {f} {a}, forall `{GHC.Base.Applicative f}, Max (f a) -> f (Max a) :=
  fun {f} {a} `{GHC.Base.Applicative f} => Traversable__Max_traverse GHC.Base.id.

Local Definition Traversable__Max_sequence
   : forall {m} {a}, forall `{GHC.Base.Monad m}, Max (m a) -> m (Max a) :=
  fun {m} {a} `{GHC.Base.Monad m} => Traversable__Max_sequenceA.

Program Instance Traversable__Max : Data.Traversable.Traversable Max :=
  fun _ k__ =>
    k__ {| Data.Traversable.mapM__ := fun {m} {a} {b} `{GHC.Base.Monad m} =>
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
  fun _ k__ =>
    k__ {| GHC.Base.liftA2__ := fun {a} {b} {c} => Applicative__Max_liftA2 ;
           GHC.Base.op_zlztzg____ := fun {a} {b} => Applicative__Max_op_zlztzg__ ;
           GHC.Base.op_ztzg____ := fun {a} {b} => Applicative__Max_op_ztzg__ ;
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
  fun _ k__ =>
    k__ {| GHC.Base.op_zgzg____ := fun {a} {b} => Monad__Max_op_zgzg__ ;
           GHC.Base.op_zgzgze____ := fun {a} {b} => Monad__Max_op_zgzgze__ ;
           GHC.Base.return___ := fun {a} => Monad__Max_return_ |}.

(* Skipping all instances of class `Control.Monad.Fix.MonadFix', including
   `Data.Semigroup.MonadFix__Max' *)

(* Skipping all instances of class `GHC.Num.Num', including
   `Data.Semigroup.Num__Max' *)

Local Definition Functor__Arg_fmap {inst_a}
   : forall {a} {b}, (a -> b) -> (Arg inst_a) a -> (Arg inst_a) b :=
  fun {a} {b} =>
    fun arg_0__ arg_1__ =>
      match arg_0__, arg_1__ with
      | f, Mk_Arg x a => Mk_Arg x (f a)
      end.

Local Definition Functor__Arg_op_zlzd__ {inst_a}
   : forall {a} {b}, a -> (Arg inst_a) b -> (Arg inst_a) a :=
  fun {a} {b} => Functor__Arg_fmap GHC.Base.∘ GHC.Base.const.

Program Instance Functor__Arg {a} : GHC.Base.Functor (Arg a) :=
  fun _ k__ =>
    k__ {| GHC.Base.fmap__ := fun {a} {b} => Functor__Arg_fmap ;
           GHC.Base.op_zlzd____ := fun {a} {b} => Functor__Arg_op_zlzd__ |}.

Local Definition Foldable__Arg_foldMap {inst_a}
   : forall {m} {a},
     forall `{GHC.Base.Monoid m}, (a -> m) -> (Arg inst_a) a -> m :=
  fun {m} {a} `{GHC.Base.Monoid m} =>
    fun arg_0__ arg_1__ => match arg_0__, arg_1__ with | f, Mk_Arg _ a => f a end.

Local Definition Foldable__Arg_fold {inst_a}
   : forall {m}, forall `{GHC.Base.Monoid m}, (Arg inst_a) m -> m :=
  fun {m} `{GHC.Base.Monoid m} => Foldable__Arg_foldMap GHC.Base.id.

Local Definition Foldable__Arg_foldl {inst_a}
   : forall {b} {a}, (b -> a -> b) -> b -> (Arg inst_a) a -> b :=
  fun {b} {a} =>
    fun f z t =>
      Data.SemigroupInternal.appEndo (Data.SemigroupInternal.getDual
                                      (Foldable__Arg_foldMap (Data.SemigroupInternal.Mk_Dual GHC.Base.∘
                                                              (Data.SemigroupInternal.Mk_Endo GHC.Base.∘
                                                               GHC.Base.flip f)) t)) z.

Local Definition Foldable__Arg_foldr {inst_a}
   : forall {a} {b}, (a -> b -> b) -> b -> (Arg inst_a) a -> b :=
  fun {a} {b} =>
    fun f z t =>
      Data.SemigroupInternal.appEndo (Foldable__Arg_foldMap
                                      (Coq.Program.Basics.compose Data.SemigroupInternal.Mk_Endo f) t) z.

Local Definition Foldable__Arg_foldl' {inst_a}
   : forall {b} {a}, (b -> a -> b) -> b -> (Arg inst_a) a -> b :=
  fun {b} {a} =>
    fun f z0 xs =>
      let f' := fun x k z => k (f z x) in Foldable__Arg_foldr f' GHC.Base.id xs z0.

Local Definition Foldable__Arg_foldr' {inst_a}
   : forall {a} {b}, (a -> b -> b) -> b -> (Arg inst_a) a -> b :=
  fun {a} {b} =>
    fun f z0 xs =>
      let f' := fun k x z => k (f x z) in Foldable__Arg_foldl f' GHC.Base.id xs z0.

Local Definition Foldable__Arg_length {inst_a}
   : forall {a}, (Arg inst_a) a -> GHC.Num.Int :=
  fun {a} =>
    Foldable__Arg_foldl' (fun arg_0__ arg_1__ =>
                            match arg_0__, arg_1__ with
                            | c, _ => c GHC.Num.+ #1
                            end) #0.

Local Definition Foldable__Arg_null {inst_a}
   : forall {a}, (Arg inst_a) a -> bool :=
  fun {a} => Foldable__Arg_foldr (fun arg_0__ arg_1__ => false) true.

Local Definition Foldable__Arg_product {inst_a}
   : forall {a}, forall `{GHC.Num.Num a}, (Arg inst_a) a -> a :=
  fun {a} `{GHC.Num.Num a} =>
    Coq.Program.Basics.compose Data.SemigroupInternal.getProduct
                               (Foldable__Arg_foldMap Data.SemigroupInternal.Mk_Product).

Local Definition Foldable__Arg_sum {inst_a}
   : forall {a}, forall `{GHC.Num.Num a}, (Arg inst_a) a -> a :=
  fun {a} `{GHC.Num.Num a} =>
    Coq.Program.Basics.compose Data.SemigroupInternal.getSum (Foldable__Arg_foldMap
                                Data.SemigroupInternal.Mk_Sum).

Local Definition Foldable__Arg_toList {inst_a}
   : forall {a}, (Arg inst_a) a -> list a :=
  fun {a} =>
    fun t => GHC.Base.build' (fun _ => (fun c n => Foldable__Arg_foldr c n t)).

Program Instance Foldable__Arg {a} : Data.Foldable.Foldable (Arg a) :=
  fun _ k__ =>
    k__ {| Data.Foldable.fold__ := fun {m} `{GHC.Base.Monoid m} =>
             Foldable__Arg_fold ;
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

Local Definition Traversable__Arg_mapM {inst_a}
   : forall {m} {a} {b},
     forall `{GHC.Base.Monad m},
     (a -> m b) -> (Arg inst_a) a -> m ((Arg inst_a) b) :=
  fun {m} {a} {b} `{GHC.Base.Monad m} => Traversable__Arg_traverse.

Local Definition Traversable__Arg_sequenceA {inst_a}
   : forall {f} {a},
     forall `{GHC.Base.Applicative f}, (Arg inst_a) (f a) -> f ((Arg inst_a) a) :=
  fun {f} {a} `{GHC.Base.Applicative f} => Traversable__Arg_traverse GHC.Base.id.

Local Definition Traversable__Arg_sequence {inst_a}
   : forall {m} {a},
     forall `{GHC.Base.Monad m}, (Arg inst_a) (m a) -> m ((Arg inst_a) a) :=
  fun {m} {a} `{GHC.Base.Monad m} => Traversable__Arg_sequenceA.

Program Instance Traversable__Arg {a} : Data.Traversable.Traversable (Arg a) :=
  fun _ k__ =>
    k__ {| Data.Traversable.mapM__ := fun {m} {a} {b} `{GHC.Base.Monad m} =>
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
  fun _ k__ =>
    k__ {| GHC.Base.op_zeze____ := Eq___Arg_op_zeze__ ;
           GHC.Base.op_zsze____ := Eq___Arg_op_zsze__ |}.

(* Skipping instance `Data.Semigroup.Ord__Arg' of class `GHC.Base.Ord' *)

Local Definition Bifunctor__Arg_bimap
   : forall {a} {b} {c} {d}, (a -> b) -> (c -> d) -> Arg a c -> Arg b d :=
  fun {a} {b} {c} {d} =>
    fun arg_0__ arg_1__ arg_2__ =>
      match arg_0__, arg_1__, arg_2__ with
      | f, g, Mk_Arg a b => Mk_Arg (f a) (g b)
      end.

Local Definition Bifunctor__Arg_first
   : forall {a} {b} {c}, (a -> b) -> Arg a c -> Arg b c :=
  fun {a} {b} {c} => fun f => Bifunctor__Arg_bimap f GHC.Base.id.

Local Definition Bifunctor__Arg_second
   : forall {b} {c} {a}, (b -> c) -> Arg a b -> Arg a c :=
  fun {b} {c} {a} => Bifunctor__Arg_bimap GHC.Base.id.

Program Instance Bifunctor__Arg : Data.Bifunctor.Bifunctor Arg :=
  fun _ k__ =>
    k__ {| Data.Bifunctor.bimap__ := fun {a} {b} {c} {d} => Bifunctor__Arg_bimap ;
           Data.Bifunctor.first__ := fun {a} {b} {c} => Bifunctor__Arg_first ;
           Data.Bifunctor.second__ := fun {b} {c} {a} => Bifunctor__Arg_second |}.

Local Definition Bifoldable__Arg_bifoldMap
   : forall {m} {a} {b},
     forall `{GHC.Base.Monoid m}, (a -> m) -> (b -> m) -> Arg a b -> m :=
  fun {m} {a} {b} `{GHC.Base.Monoid m} =>
    fun arg_0__ arg_1__ arg_2__ =>
      match arg_0__, arg_1__, arg_2__ with
      | f, g, Mk_Arg a b => f a GHC.Base.<<>> g b
      end.

Local Definition Bifoldable__Arg_bifold
   : forall {m}, forall `{GHC.Base.Monoid m}, Arg m m -> m :=
  fun {m} `{GHC.Base.Monoid m} =>
    Bifoldable__Arg_bifoldMap GHC.Base.id GHC.Base.id.

Local Definition Bifoldable__Arg_bifoldl
   : forall {c} {a} {b}, (c -> a -> c) -> (c -> b -> c) -> c -> Arg a b -> c :=
  fun {c} {a} {b} =>
    fun f g z t =>
      Data.SemigroupInternal.appEndo (Data.SemigroupInternal.getDual
                                      (Bifoldable__Arg_bifoldMap (Data.SemigroupInternal.Mk_Dual GHC.Base.∘
                                                                  (Data.SemigroupInternal.Mk_Endo GHC.Base.∘
                                                                   GHC.Base.flip f)) (Data.SemigroupInternal.Mk_Dual
                                                                                      GHC.Base.∘
                                                                                      (Data.SemigroupInternal.Mk_Endo
                                                                                       GHC.Base.∘
                                                                                       GHC.Base.flip g)) t)) z.

Local Definition Bifoldable__Arg_bifoldr
   : forall {a} {c} {b}, (a -> c -> c) -> (b -> c -> c) -> c -> Arg a b -> c :=
  fun {a} {c} {b} =>
    fun f g z t =>
      Data.SemigroupInternal.appEndo (Bifoldable__Arg_bifoldMap
                                      (Coq.Program.Basics.compose Data.SemigroupInternal.Mk_Endo f)
                                      (Coq.Program.Basics.compose Data.SemigroupInternal.Mk_Endo g) t) z.

Program Instance Bifoldable__Arg : Data.Bifoldable.Bifoldable Arg :=
  fun _ k__ =>
    k__ {| Data.Bifoldable.bifold__ := fun {m} `{GHC.Base.Monoid m} =>
             Bifoldable__Arg_bifold ;
           Data.Bifoldable.bifoldMap__ := fun {m} {a} {b} `{GHC.Base.Monoid m} =>
             Bifoldable__Arg_bifoldMap ;
           Data.Bifoldable.bifoldl__ := fun {c} {a} {b} => Bifoldable__Arg_bifoldl ;
           Data.Bifoldable.bifoldr__ := fun {a} {c} {b} => Bifoldable__Arg_bifoldr |}.

Local Definition Bitraversable__Arg_bitraverse
   : forall {f} {a} {c} {b} {d},
     forall `{GHC.Base.Applicative f},
     (a -> f c) -> (b -> f d) -> Arg a b -> f (Arg c d) :=
  fun {f} {a} {c} {b} {d} `{GHC.Base.Applicative f} =>
    fun arg_0__ arg_1__ arg_2__ =>
      match arg_0__, arg_1__, arg_2__ with
      | f, g, Mk_Arg a b => (Mk_Arg Data.Functor.<$> f a) GHC.Base.<*> g b
      end.

Program Instance Bitraversable__Arg : Data.Bitraversable.Bitraversable Arg :=
  fun _ k__ =>
    k__ {| Data.Bitraversable.bitraverse__ := fun {f}
           {a}
           {c}
           {b}
           {d}
           `{GHC.Base.Applicative f} =>
             Bitraversable__Arg_bitraverse |}.

(* Skipping all instances of class `GHC.Enum.Enum', including
   `Data.Semigroup.Enum__First' *)

Local Definition Semigroup__First_op_zlzlzgzg__ {inst_a}
   : (First inst_a) -> (First inst_a) -> (First inst_a) :=
  fun arg_0__ arg_1__ => match arg_0__, arg_1__ with | a, _ => a end.

Program Instance Semigroup__First {a} : GHC.Base.Semigroup (First a) :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zlzlzgzg____ := Semigroup__First_op_zlzlzgzg__ |}.

Local Definition Functor__First_fmap
   : forall {a} {b}, (a -> b) -> First a -> First b :=
  fun {a} {b} =>
    fun arg_0__ arg_1__ =>
      match arg_0__, arg_1__ with
      | f, Mk_First x => Mk_First (f x)
      end.

Local Definition Functor__First_op_zlzd__
   : forall {a} {b}, a -> First b -> First a :=
  fun {a} {b} => Functor__First_fmap GHC.Base.∘ GHC.Base.const.

Program Instance Functor__First : GHC.Base.Functor First :=
  fun _ k__ =>
    k__ {| GHC.Base.fmap__ := fun {a} {b} => Functor__First_fmap ;
           GHC.Base.op_zlzd____ := fun {a} {b} => Functor__First_op_zlzd__ |}.

Local Definition Foldable__First_foldMap
   : forall {m} {a}, forall `{GHC.Base.Monoid m}, (a -> m) -> First a -> m :=
  fun {m} {a} `{GHC.Base.Monoid m} =>
    fun arg_0__ arg_1__ => match arg_0__, arg_1__ with | f, Mk_First a => f a end.

Local Definition Foldable__First_fold
   : forall {m}, forall `{GHC.Base.Monoid m}, First m -> m :=
  fun {m} `{GHC.Base.Monoid m} => Foldable__First_foldMap GHC.Base.id.

Local Definition Foldable__First_foldl
   : forall {b} {a}, (b -> a -> b) -> b -> First a -> b :=
  fun {b} {a} =>
    fun f z t =>
      Data.SemigroupInternal.appEndo (Data.SemigroupInternal.getDual
                                      (Foldable__First_foldMap (Data.SemigroupInternal.Mk_Dual GHC.Base.∘
                                                                (Data.SemigroupInternal.Mk_Endo GHC.Base.∘
                                                                 GHC.Base.flip f)) t)) z.

Local Definition Foldable__First_foldr
   : forall {a} {b}, (a -> b -> b) -> b -> First a -> b :=
  fun {a} {b} =>
    fun f z t =>
      Data.SemigroupInternal.appEndo (Foldable__First_foldMap
                                      (Coq.Program.Basics.compose Data.SemigroupInternal.Mk_Endo f) t) z.

Local Definition Foldable__First_foldl'
   : forall {b} {a}, (b -> a -> b) -> b -> First a -> b :=
  fun {b} {a} =>
    fun f z0 xs =>
      let f' := fun x k z => k (f z x) in Foldable__First_foldr f' GHC.Base.id xs z0.

Local Definition Foldable__First_foldr'
   : forall {a} {b}, (a -> b -> b) -> b -> First a -> b :=
  fun {a} {b} =>
    fun f z0 xs =>
      let f' := fun k x z => k (f x z) in Foldable__First_foldl f' GHC.Base.id xs z0.

Local Definition Foldable__First_length : forall {a}, First a -> GHC.Num.Int :=
  fun {a} =>
    Foldable__First_foldl' (fun arg_0__ arg_1__ =>
                              match arg_0__, arg_1__ with
                              | c, _ => c GHC.Num.+ #1
                              end) #0.

Local Definition Foldable__First_null : forall {a}, First a -> bool :=
  fun {a} => Foldable__First_foldr (fun arg_0__ arg_1__ => false) true.

Local Definition Foldable__First_product
   : forall {a}, forall `{GHC.Num.Num a}, First a -> a :=
  fun {a} `{GHC.Num.Num a} =>
    Coq.Program.Basics.compose Data.SemigroupInternal.getProduct
                               (Foldable__First_foldMap Data.SemigroupInternal.Mk_Product).

Local Definition Foldable__First_sum
   : forall {a}, forall `{GHC.Num.Num a}, First a -> a :=
  fun {a} `{GHC.Num.Num a} =>
    Coq.Program.Basics.compose Data.SemigroupInternal.getSum
                               (Foldable__First_foldMap Data.SemigroupInternal.Mk_Sum).

Local Definition Foldable__First_toList : forall {a}, First a -> list a :=
  fun {a} =>
    fun t => GHC.Base.build' (fun _ => (fun c n => Foldable__First_foldr c n t)).

Program Instance Foldable__First : Data.Foldable.Foldable First :=
  fun _ k__ =>
    k__ {| Data.Foldable.fold__ := fun {m} `{GHC.Base.Monoid m} =>
             Foldable__First_fold ;
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

Local Definition Traversable__First_mapM
   : forall {m} {a} {b},
     forall `{GHC.Base.Monad m}, (a -> m b) -> First a -> m (First b) :=
  fun {m} {a} {b} `{GHC.Base.Monad m} => Traversable__First_traverse.

Local Definition Traversable__First_sequenceA
   : forall {f} {a},
     forall `{GHC.Base.Applicative f}, First (f a) -> f (First a) :=
  fun {f} {a} `{GHC.Base.Applicative f} =>
    Traversable__First_traverse GHC.Base.id.

Local Definition Traversable__First_sequence
   : forall {m} {a}, forall `{GHC.Base.Monad m}, First (m a) -> m (First a) :=
  fun {m} {a} `{GHC.Base.Monad m} => Traversable__First_sequenceA.

Program Instance Traversable__First : Data.Traversable.Traversable First :=
  fun _ k__ =>
    k__ {| Data.Traversable.mapM__ := fun {m} {a} {b} `{GHC.Base.Monad m} =>
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
  fun _ k__ =>
    k__ {| GHC.Base.liftA2__ := fun {a} {b} {c} => Applicative__First_liftA2 ;
           GHC.Base.op_zlztzg____ := fun {a} {b} => Applicative__First_op_zlztzg__ ;
           GHC.Base.op_ztzg____ := fun {a} {b} => Applicative__First_op_ztzg__ ;
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
  fun _ k__ =>
    k__ {| GHC.Base.op_zgzg____ := fun {a} {b} => Monad__First_op_zgzg__ ;
           GHC.Base.op_zgzgze____ := fun {a} {b} => Monad__First_op_zgzgze__ ;
           GHC.Base.return___ := fun {a} => Monad__First_return_ |}.

(* Skipping all instances of class `Control.Monad.Fix.MonadFix', including
   `Data.Semigroup.MonadFix__First' *)

(* Skipping all instances of class `GHC.Enum.Enum', including
   `Data.Semigroup.Enum__Last' *)

Local Definition Semigroup__Last_op_zlzlzgzg__ {inst_a}
   : (Last inst_a) -> (Last inst_a) -> (Last inst_a) :=
  fun arg_0__ arg_1__ => match arg_0__, arg_1__ with | _, b => b end.

Program Instance Semigroup__Last {a} : GHC.Base.Semigroup (Last a) :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zlzlzgzg____ := Semigroup__Last_op_zlzlzgzg__ |}.

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
  fun _ k__ =>
    k__ {| GHC.Base.fmap__ := fun {a} {b} => Functor__Last_fmap ;
           GHC.Base.op_zlzd____ := fun {a} {b} => Functor__Last_op_zlzd__ |}.

Local Definition Foldable__Last_foldMap
   : forall {m} {a}, forall `{GHC.Base.Monoid m}, (a -> m) -> Last a -> m :=
  fun {m} {a} `{GHC.Base.Monoid m} =>
    fun arg_0__ arg_1__ => match arg_0__, arg_1__ with | f, Mk_Last a => f a end.

Local Definition Foldable__Last_fold
   : forall {m}, forall `{GHC.Base.Monoid m}, Last m -> m :=
  fun {m} `{GHC.Base.Monoid m} => Foldable__Last_foldMap GHC.Base.id.

Local Definition Foldable__Last_foldl
   : forall {b} {a}, (b -> a -> b) -> b -> Last a -> b :=
  fun {b} {a} =>
    fun f z t =>
      Data.SemigroupInternal.appEndo (Data.SemigroupInternal.getDual
                                      (Foldable__Last_foldMap (Data.SemigroupInternal.Mk_Dual GHC.Base.∘
                                                               (Data.SemigroupInternal.Mk_Endo GHC.Base.∘
                                                                GHC.Base.flip f)) t)) z.

Local Definition Foldable__Last_foldr
   : forall {a} {b}, (a -> b -> b) -> b -> Last a -> b :=
  fun {a} {b} =>
    fun f z t =>
      Data.SemigroupInternal.appEndo (Foldable__Last_foldMap
                                      (Coq.Program.Basics.compose Data.SemigroupInternal.Mk_Endo f) t) z.

Local Definition Foldable__Last_foldl'
   : forall {b} {a}, (b -> a -> b) -> b -> Last a -> b :=
  fun {b} {a} =>
    fun f z0 xs =>
      let f' := fun x k z => k (f z x) in Foldable__Last_foldr f' GHC.Base.id xs z0.

Local Definition Foldable__Last_foldr'
   : forall {a} {b}, (a -> b -> b) -> b -> Last a -> b :=
  fun {a} {b} =>
    fun f z0 xs =>
      let f' := fun k x z => k (f x z) in Foldable__Last_foldl f' GHC.Base.id xs z0.

Local Definition Foldable__Last_length : forall {a}, Last a -> GHC.Num.Int :=
  fun {a} =>
    Foldable__Last_foldl' (fun arg_0__ arg_1__ =>
                             match arg_0__, arg_1__ with
                             | c, _ => c GHC.Num.+ #1
                             end) #0.

Local Definition Foldable__Last_null : forall {a}, Last a -> bool :=
  fun {a} => Foldable__Last_foldr (fun arg_0__ arg_1__ => false) true.

Local Definition Foldable__Last_product
   : forall {a}, forall `{GHC.Num.Num a}, Last a -> a :=
  fun {a} `{GHC.Num.Num a} =>
    Coq.Program.Basics.compose Data.SemigroupInternal.getProduct
                               (Foldable__Last_foldMap Data.SemigroupInternal.Mk_Product).

Local Definition Foldable__Last_sum
   : forall {a}, forall `{GHC.Num.Num a}, Last a -> a :=
  fun {a} `{GHC.Num.Num a} =>
    Coq.Program.Basics.compose Data.SemigroupInternal.getSum (Foldable__Last_foldMap
                                Data.SemigroupInternal.Mk_Sum).

Local Definition Foldable__Last_toList : forall {a}, Last a -> list a :=
  fun {a} =>
    fun t => GHC.Base.build' (fun _ => (fun c n => Foldable__Last_foldr c n t)).

Program Instance Foldable__Last : Data.Foldable.Foldable Last :=
  fun _ k__ =>
    k__ {| Data.Foldable.fold__ := fun {m} `{GHC.Base.Monoid m} =>
             Foldable__Last_fold ;
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

Local Definition Traversable__Last_mapM
   : forall {m} {a} {b},
     forall `{GHC.Base.Monad m}, (a -> m b) -> Last a -> m (Last b) :=
  fun {m} {a} {b} `{GHC.Base.Monad m} => Traversable__Last_traverse.

Local Definition Traversable__Last_sequenceA
   : forall {f} {a}, forall `{GHC.Base.Applicative f}, Last (f a) -> f (Last a) :=
  fun {f} {a} `{GHC.Base.Applicative f} => Traversable__Last_traverse GHC.Base.id.

Local Definition Traversable__Last_sequence
   : forall {m} {a}, forall `{GHC.Base.Monad m}, Last (m a) -> m (Last a) :=
  fun {m} {a} `{GHC.Base.Monad m} => Traversable__Last_sequenceA.

Program Instance Traversable__Last : Data.Traversable.Traversable Last :=
  fun _ k__ =>
    k__ {| Data.Traversable.mapM__ := fun {m} {a} {b} `{GHC.Base.Monad m} =>
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
  fun _ k__ =>
    k__ {| GHC.Base.liftA2__ := fun {a} {b} {c} => Applicative__Last_liftA2 ;
           GHC.Base.op_zlztzg____ := fun {a} {b} => Applicative__Last_op_zlztzg__ ;
           GHC.Base.op_ztzg____ := fun {a} {b} => Applicative__Last_op_ztzg__ ;
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
  fun _ k__ =>
    k__ {| GHC.Base.op_zgzg____ := fun {a} {b} => Monad__Last_op_zgzg__ ;
           GHC.Base.op_zgzgze____ := fun {a} {b} => Monad__Last_op_zgzgze__ ;
           GHC.Base.return___ := fun {a} => Monad__Last_return_ |}.

(* Skipping all instances of class `Control.Monad.Fix.MonadFix', including
   `Data.Semigroup.MonadFix__Last' *)

Local Definition Semigroup__WrappedMonoid_op_zlzlzgzg__ {inst_m} `{_
   : GHC.Base.Monoid inst_m}
   : WrappedMonoid inst_m -> WrappedMonoid inst_m -> WrappedMonoid inst_m :=
  GHC.Prim.coerce (@GHC.Base.mappend inst_m _ _).

Program Instance Semigroup__WrappedMonoid {m} `{GHC.Base.Monoid m}
   : GHC.Base.Semigroup (WrappedMonoid m) :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zlzlzgzg____ := Semigroup__WrappedMonoid_op_zlzlzgzg__ |}.

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
  fun _ k__ =>
    k__ {| GHC.Base.mappend__ := Monoid__WrappedMonoid_mappend ;
           GHC.Base.mconcat__ := Monoid__WrappedMonoid_mconcat ;
           GHC.Base.mempty__ := Monoid__WrappedMonoid_mempty |}.

(* Skipping all instances of class `GHC.Enum.Enum', including
   `Data.Semigroup.Enum__WrappedMonoid' *)

Local Definition Functor__Option_fmap
   : forall {a} {b}, (a -> b) -> Option a -> Option b :=
  fun {a} {b} =>
    fun arg_0__ arg_1__ =>
      match arg_0__, arg_1__ with
      | f, Mk_Option a => Mk_Option (GHC.Base.fmap f a)
      end.

Local Definition Functor__Option_op_zlzd__
   : forall {a} {b}, a -> Option b -> Option a :=
  fun {a} {b} => Functor__Option_fmap GHC.Base.∘ GHC.Base.const.

Program Instance Functor__Option : GHC.Base.Functor Option :=
  fun _ k__ =>
    k__ {| GHC.Base.fmap__ := fun {a} {b} => Functor__Option_fmap ;
           GHC.Base.op_zlzd____ := fun {a} {b} => Functor__Option_op_zlzd__ |}.

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
  fun _ k__ =>
    k__ {| GHC.Base.liftA2__ := fun {a} {b} {c} => Applicative__Option_liftA2 ;
           GHC.Base.op_zlztzg____ := fun {a} {b} => Applicative__Option_op_zlztzg__ ;
           GHC.Base.op_ztzg____ := fun {a} {b} => Applicative__Option_op_ztzg__ ;
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
  fun _ k__ =>
    k__ {| GHC.Base.op_zgzg____ := fun {a} {b} => Monad__Option_op_zgzg__ ;
           GHC.Base.op_zgzgze____ := fun {a} {b} => Monad__Option_op_zgzgze__ ;
           GHC.Base.return___ := fun {a} => Monad__Option_return_ |}.

(* Skipping all instances of class `GHC.Base.Alternative', including
   `Data.Semigroup.Alternative__Option' *)

(* Skipping all instances of class `GHC.Base.MonadPlus', including
   `Data.Semigroup.MonadPlus__Option' *)

(* Skipping all instances of class `Control.Monad.Fix.MonadFix', including
   `Data.Semigroup.MonadFix__Option' *)

Local Definition Foldable__Option_foldMap
   : forall {m} {a}, forall `{GHC.Base.Monoid m}, (a -> m) -> Option a -> m :=
  fun {m} {a} `{GHC.Base.Monoid m} =>
    fun arg_0__ arg_1__ =>
      match arg_0__, arg_1__ with
      | f, Mk_Option (Some m) => f m
      | _, Mk_Option None => GHC.Base.mempty
      end.

Local Definition Foldable__Option_fold
   : forall {m}, forall `{GHC.Base.Monoid m}, Option m -> m :=
  fun {m} `{GHC.Base.Monoid m} => Foldable__Option_foldMap GHC.Base.id.

Local Definition Foldable__Option_foldl
   : forall {b} {a}, (b -> a -> b) -> b -> Option a -> b :=
  fun {b} {a} =>
    fun f z t =>
      Data.SemigroupInternal.appEndo (Data.SemigroupInternal.getDual
                                      (Foldable__Option_foldMap (Data.SemigroupInternal.Mk_Dual GHC.Base.∘
                                                                 (Data.SemigroupInternal.Mk_Endo GHC.Base.∘
                                                                  GHC.Base.flip f)) t)) z.

Local Definition Foldable__Option_foldr
   : forall {a} {b}, (a -> b -> b) -> b -> Option a -> b :=
  fun {a} {b} =>
    fun f z t =>
      Data.SemigroupInternal.appEndo (Foldable__Option_foldMap
                                      (Coq.Program.Basics.compose Data.SemigroupInternal.Mk_Endo f) t) z.

Local Definition Foldable__Option_foldl'
   : forall {b} {a}, (b -> a -> b) -> b -> Option a -> b :=
  fun {b} {a} =>
    fun f z0 xs =>
      let f' := fun x k z => k (f z x) in Foldable__Option_foldr f' GHC.Base.id xs z0.

Local Definition Foldable__Option_foldr'
   : forall {a} {b}, (a -> b -> b) -> b -> Option a -> b :=
  fun {a} {b} =>
    fun f z0 xs =>
      let f' := fun k x z => k (f x z) in Foldable__Option_foldl f' GHC.Base.id xs z0.

Local Definition Foldable__Option_length
   : forall {a}, Option a -> GHC.Num.Int :=
  fun {a} =>
    Foldable__Option_foldl' (fun arg_0__ arg_1__ =>
                               match arg_0__, arg_1__ with
                               | c, _ => c GHC.Num.+ #1
                               end) #0.

Local Definition Foldable__Option_null : forall {a}, Option a -> bool :=
  fun {a} => Foldable__Option_foldr (fun arg_0__ arg_1__ => false) true.

Local Definition Foldable__Option_product
   : forall {a}, forall `{GHC.Num.Num a}, Option a -> a :=
  fun {a} `{GHC.Num.Num a} =>
    Coq.Program.Basics.compose Data.SemigroupInternal.getProduct
                               (Foldable__Option_foldMap Data.SemigroupInternal.Mk_Product).

Local Definition Foldable__Option_sum
   : forall {a}, forall `{GHC.Num.Num a}, Option a -> a :=
  fun {a} `{GHC.Num.Num a} =>
    Coq.Program.Basics.compose Data.SemigroupInternal.getSum
                               (Foldable__Option_foldMap Data.SemigroupInternal.Mk_Sum).

Local Definition Foldable__Option_toList : forall {a}, Option a -> list a :=
  fun {a} =>
    fun t => GHC.Base.build' (fun _ => (fun c n => Foldable__Option_foldr c n t)).

Program Instance Foldable__Option : Data.Foldable.Foldable Option :=
  fun _ k__ =>
    k__ {| Data.Foldable.fold__ := fun {m} `{GHC.Base.Monoid m} =>
             Foldable__Option_fold ;
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

Local Definition Traversable__Option_mapM
   : forall {m} {a} {b},
     forall `{GHC.Base.Monad m}, (a -> m b) -> Option a -> m (Option b) :=
  fun {m} {a} {b} `{GHC.Base.Monad m} => Traversable__Option_traverse.

Local Definition Traversable__Option_sequenceA
   : forall {f} {a},
     forall `{GHC.Base.Applicative f}, Option (f a) -> f (Option a) :=
  fun {f} {a} `{GHC.Base.Applicative f} =>
    Traversable__Option_traverse GHC.Base.id.

Local Definition Traversable__Option_sequence
   : forall {m} {a}, forall `{GHC.Base.Monad m}, Option (m a) -> m (Option a) :=
  fun {m} {a} `{GHC.Base.Monad m} => Traversable__Option_sequenceA.

Program Instance Traversable__Option : Data.Traversable.Traversable Option :=
  fun _ k__ =>
    k__ {| Data.Traversable.mapM__ := fun {m} {a} {b} `{GHC.Base.Monad m} =>
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
  fun _ k__ =>
    k__ {| GHC.Base.op_zlzlzgzg____ := Semigroup__Option_op_zlzlzgzg__ |}.

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
  fun _ k__ =>
    k__ {| GHC.Base.mappend__ := Monoid__Option_mappend ;
           GHC.Base.mconcat__ := Monoid__Option_mconcat ;
           GHC.Base.mempty__ := Monoid__Option_mempty |}.

(* Skipping definition `Data.Semigroup.cycle1' *)

Definition diff {m} `{GHC.Base.Semigroup m}
   : m -> Data.SemigroupInternal.Endo m :=
  Data.SemigroupInternal.Mk_Endo GHC.Base.∘ _GHC.Base.<<>>_.

(* Skipping definition `Data.Semigroup.mtimesDefault' *)

Definition destruct_option {b} {a} : b -> (a -> b) -> Option a -> b :=
  fun arg_0__ arg_1__ arg_2__ =>
    match arg_0__, arg_1__, arg_2__ with
    | n, j, Mk_Option m => Data.Maybe.maybe n j m
    end.

(* External variables:
     None Some bool comparison false list negb option true Coq.Program.Basics.compose
     Data.Bifoldable.Bifoldable Data.Bifoldable.bifoldMap__ Data.Bifoldable.bifold__
     Data.Bifoldable.bifoldl__ Data.Bifoldable.bifoldr__ Data.Bifunctor.Bifunctor
     Data.Bifunctor.bimap__ Data.Bifunctor.first__ Data.Bifunctor.second__
     Data.Bitraversable.Bitraversable Data.Bitraversable.bitraverse__
     Data.Foldable.Foldable Data.Foldable.foldMap__ Data.Foldable.fold__
     Data.Foldable.foldl'__ Data.Foldable.foldl__ Data.Foldable.foldr'__
     Data.Foldable.foldr__ Data.Foldable.length__ Data.Foldable.null__
     Data.Foldable.product__ Data.Foldable.sum__ Data.Foldable.toList__
     Data.Functor.op_zlzdzg__ Data.Maybe.maybe Data.SemigroupInternal.Endo
     Data.SemigroupInternal.Mk_Dual Data.SemigroupInternal.Mk_Endo
     Data.SemigroupInternal.Mk_Product Data.SemigroupInternal.Mk_Sum
     Data.SemigroupInternal.appEndo Data.SemigroupInternal.getDual
     Data.SemigroupInternal.getProduct Data.SemigroupInternal.getSum
     Data.Traversable.Traversable Data.Traversable.mapM__
     Data.Traversable.sequenceA__ Data.Traversable.sequence__
     Data.Traversable.traverse__ GHC.Base.Applicative GHC.Base.Eq_ GHC.Base.Functor
     GHC.Base.Monad GHC.Base.Monoid GHC.Base.Ord GHC.Base.Semigroup GHC.Base.build'
     GHC.Base.compare GHC.Base.compare__ GHC.Base.const GHC.Base.flip GHC.Base.fmap
     GHC.Base.fmap__ GHC.Base.foldr GHC.Base.id GHC.Base.liftA2 GHC.Base.liftA2__
     GHC.Base.mappend GHC.Base.mappend__ GHC.Base.max GHC.Base.max__
     GHC.Base.mconcat__ GHC.Base.mempty GHC.Base.mempty__ GHC.Base.min GHC.Base.min__
     GHC.Base.op_z2218U__ GHC.Base.op_zeze__ GHC.Base.op_zeze____ GHC.Base.op_zg__
     GHC.Base.op_zg____ GHC.Base.op_zgze__ GHC.Base.op_zgze____ GHC.Base.op_zgzg____
     GHC.Base.op_zgzgze____ GHC.Base.op_zl__ GHC.Base.op_zl____ GHC.Base.op_zlzd____
     GHC.Base.op_zlze__ GHC.Base.op_zlze____ GHC.Base.op_zlzlzgzg__
     GHC.Base.op_zlzlzgzg____ GHC.Base.op_zlztzg__ GHC.Base.op_zlztzg____
     GHC.Base.op_zsze__ GHC.Base.op_zsze____ GHC.Base.op_ztzg__ GHC.Base.op_ztzg____
     GHC.Base.pure GHC.Base.pure__ GHC.Base.return___ GHC.Num.Int GHC.Num.Num
     GHC.Num.fromInteger GHC.Num.op_zp__ GHC.Prim.Build_Unpeel GHC.Prim.Unpeel
     GHC.Prim.coerce
*)
