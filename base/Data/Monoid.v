(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Coq.Program.Tactics.
Require Coq.Program.Wf.

(* Preamble *)

Require Import GHC.Base.
(*
Definition op_zlzg__ {m} `{GHC.Base.Monoid m} : m -> m -> m :=
  GHC.Base.mappend.

Infix "<>" := (op_zlzg__) (at level 70).

Notation "'_<>_'" := (op_zlzg__).
*)

(* WE do these by hand because they are defined in GHC using Data.Coerce. *)

(*
Inductive All : Type := Mk_All : bool -> All.
Definition getAll (arg_7__ : All) :=
  match arg_7__ with
    | (Mk_All getAll) => getAll
  end.

Definition mappend_All : All -> All -> All :=
  fun x y => match x,y with
          | Mk_All b1, Mk_All b2 => Mk_All (b1 && b2)
          end.
Definition mempty_All : All := Mk_All true.

Instance instance_GHC_Base_Monoid_All :
  GHC.Base.Monoid All := fun _ k => k {|
   mappend__ := mappend_All;
   mempty__  := mempty_All;
   mconcat__ := foldr mappend_All mempty_All;
|}.


Inductive Any : Type := Mk_Any : bool -> Any.
Definition getAny (arg_7__ : Any) :=
  match arg_7__ with
    | (Mk_Any getAny) => getAny
  end.

Definition mappend_Any : Any -> Any -> Any :=
  fun x y => match x,y with
          | Mk_Any b1, Mk_Any b2 => Mk_Any (b1 || b2)
          end.
Definition mempty_Any : Any := Mk_Any false.

Instance instance_GHC_Base_Monoid_Any :
  GHC.Base.Monoid Any := fun _ k => k {|
   mappend__ := mappend_Any;
   mempty__  := mempty_Any;
   mconcat__ := foldr mappend_Any mempty_Any;
|}.


Inductive First a : Type := Mk_First : option a -> First a.
Arguments Mk_First {_}.

Definition getFirst {a} (arg_3__ : First a) :=
  match arg_3__ with
    | (Mk_First getFirst) => getFirst
  end.

Definition mempty_First {a} : First a := Mk_First None.
Definition mappend_First {a} (x: First a) (y :First a) : First a :=
  match x , y with
    | Mk_First None, _ => y
    | _ , _ => x
  end.
Instance instance_GHC_Base_Monoid__First_a_ {a} :
  GHC.Base.Monoid (First a) := fun _ k => k
 {| mappend__ := mappend_First;
    mempty__  := mempty_First;
    mconcat__ := foldr mappend_First mempty_First |}.

Inductive Last a : Type := Mk_Last : option a -> Last a.
Arguments Mk_Last {_}.

Definition getLast {a} (arg_2__ : Last a) :=
  match arg_2__ with
    | (Mk_Last getLast) => getLast
  end.
Definition mempty_Last {a} : Last a := Mk_Last None.
Definition mappend_Last {a} (x: Last a) (y :Last a) : Last a :=
  match x , y with
    | _ , Mk_Last None => y
    | _ , _ => x
  end.

Instance instance_GHC_Base_Monoid__Last_a_ {a} :
  GHC.Base.Monoid (Last a) := fun _ k => k
 {| mappend__ := mappend_Last;
    mempty__  := mempty_Last;
    mconcat__ := foldr mappend_Last mempty_Last |}.


Inductive Product a : Type := Mk_Product : a -> Product a.
Arguments Mk_Product {_}.

Definition getProduct {a} (arg_1__ : Product a) :=
  match arg_1__ with
    | (Mk_Product getProduct) => getProduct
  end.

Definition mempty_Product {a} `{Num a} : Product a := Mk_Product #1.
Definition mappend_Product {a} `{Num a} (x: Product a) (y :Product a)  : Product a :=
  match x , y with
    | Mk_Product i , Mk_Product j => Mk_Product (i * j)
  end.
Instance instance_GHC_Base_Monoid__Product_a_ {a} `{Num a}:
  GHC.Base.Monoid (Product a) := fun _ k => k
 {| mappend__ := mappend_Product;
    mempty__  := mempty_Product;
    mconcat__ := foldr mappend_Product mempty_Product |}.

Instance instance_GHC_Base_Functor__Product_ : GHC.Base.Functor Product :=
  fun _ k => k {|
    fmap__      := fun _ _ f y => match y with | Mk_Product j => Mk_Product (f j) end;
    op_zlzd____ := fun _ _ x y => match y with | Mk_Product j => Mk_Product x end;
    |}.

Inductive Sum a : Type := Mk_Sum : a -> Sum a.
Arguments Mk_Sum {_}.

Definition getSum {a} (arg_1__ : Sum a) :=
  match arg_1__ with
    | (Mk_Sum getSum) => getSum
  end.

Definition mempty_Sum {a} `{Num a} : Sum a := Mk_Sum #0.
Definition mappend_Sum {a} `{Num a} (x: Sum a) (y :Sum a)  : Sum a :=
  match x , y with
    | Mk_Sum i , Mk_Sum j => Mk_Sum (i + j)
  end.
Instance instance_GHC_Base_Monoid__Sum_a_ {a} `{Num a}:
  GHC.Base.Monoid (Sum a) := fun _ k => k
 {| mappend__ := mappend_Sum;
    mempty__  := mempty_Sum;
    mconcat__ := foldr mappend_Sum mempty_Sum |}.

Instance instance_GHC_Base_Functor__Sum_ : GHC.Base.Functor Sum :=
  fun _ k => k {|
    fmap__      := fun _ _ f y => match y with | Mk_Sum j => Mk_Sum (f j) end;
    op_zlzd____ := fun _ _ x y => match y with | Mk_Sum j => Mk_Sum x end;
    |}.
*)
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
(* Midamble *)

Definition op_zlzg__ {m} `{GHC.Base.Monoid m} : m -> m -> m :=
  GHC.Base.mappend.

Infix "<>" := (op_zlzg__) (at level 70).
Notation "'_<>_'" := (op_zlzg__).


Definition mempty_Sum {a} `{Num a} : Sum a := Mk_Sum #0.
Definition mappend_Sum {a} `{Num a} (x: Sum a) (y :Sum a)  : Sum a :=
  match x , y with
    | Mk_Sum i , Mk_Sum j => Mk_Sum (i + j)
  end.
Instance instance_GHC_Base_Monoid__Sum_a_ {a} `{Num a}:
  GHC.Base.Monoid (Sum a) := fun _ k => k
 {| mappend__ := mappend_Sum;
    mempty__  := mempty_Sum;
    mconcat__ := foldr mappend_Sum mempty_Sum |}.


Definition mempty_Product {a} `{Num a} : Product a := Mk_Product #1.
Definition mappend_Product {a} `{Num a} (x: Product a) (y :Product a)  : Product a :=
  match x , y with
    | Mk_Product i , Mk_Product j => Mk_Product (i * j)
  end.
Instance instance_GHC_Base_Monoid__Product_a_ {a} `{Num a}:
  GHC.Base.Monoid (Product a) := fun _ k => k
 {| mappend__ := mappend_Product;
    mempty__  := mempty_Product;
    mconcat__ := foldr mappend_Product mempty_Product |}.

Instance Unpeel_Alt (f:Type->Type) a : Unpeel (Alt f a) (f a) :=
    Build_Unpeel _ _ getAlt Mk_Alt.


Local Definition instance_forall___GHC_Base_Eq___f_a____GHC_Base_Eq___Alt_f_a__op_zeze__
                                                                                         {inst_f} {inst_a}
                                                                                         `{GHC.Base.Eq_ (inst_f inst_a)}
    : Alt inst_f inst_a -> Alt inst_f inst_a -> bool :=
  GHC.Prim.coerce GHC.Base.op_zeze__.

Local Definition instance_forall___GHC_Base_Eq___f_a____GHC_Base_Eq___Alt_f_a__op_zsze__
                                                                                         {inst_f} {inst_a}
                                                                                         `{GHC.Base.Eq_ (inst_f inst_a)}
    : Alt inst_f inst_a -> Alt inst_f inst_a -> bool :=
  GHC.Prim.coerce GHC.Base.op_zsze__.

Instance instance_forall___GHC_Base_Eq___f_a____GHC_Base_Eq___Alt_f_a_  {f}
                                                                       {a} `{GHC.Base.Eq_ (f a)} : GHC.Base.Eq_ (Alt f
                                                                                                                a) :=
  fun _ k =>
    k (GHC.Base.Eq___Dict_Build (Alt f a)
                                instance_forall___GHC_Base_Eq___f_a____GHC_Base_Eq___Alt_f_a__op_zeze__
                                instance_forall___GHC_Base_Eq___f_a____GHC_Base_Eq___Alt_f_a__op_zsze__).


Local Definition instance_forall___GHC_Base_Ord__f_a____GHC_Base_Ord__Alt_f_a__compare
                                                                                       {inst_f} {inst_a} `{GHC.Base.Ord
                                                                                       (inst_f inst_a)} : Alt inst_f
                                                                                                          inst_a -> Alt
                                                                                                          inst_f
                                                                                                          inst_a -> comparison :=
  GHC.Prim.coerce GHC.Base.compare.

Local Definition instance_forall___GHC_Base_Ord__f_a____GHC_Base_Ord__Alt_f_a__max                                                                                   {inst_f} {inst_a} `{GHC.Base.Ord
                                                                                   (inst_f inst_a)} : Alt inst_f
                                                                                                      inst_a -> Alt
                                                                                                      inst_f
                                                                                                      inst_a -> Alt
                                                                                                      inst_f inst_a :=
  GHC.Prim.coerce GHC.Base.max.

Local Definition instance_forall___GHC_Base_Ord__f_a____GHC_Base_Ord__Alt_f_a__min                                                                                    {inst_f} {inst_a} `{GHC.Base.Ord
                                                                                   (inst_f inst_a)} : Alt inst_f
                                                                                                      inst_a -> Alt
                                                                                                      inst_f
                                                                                                      inst_a -> Alt
                                                                                                      inst_f inst_a :=
  GHC.Prim.coerce GHC.Base.min.

Local Definition instance_forall___GHC_Base_Ord__f_a____GHC_Base_Ord__Alt_f_a__op_zg__
                                                                                       {inst_f} {inst_a} `{GHC.Base.Ord
                                                                                       (inst_f inst_a)} : Alt inst_f
                                                                                                          inst_a -> Alt
                                                                                                          inst_f
                                                                                                          inst_a -> bool :=
  GHC.Prim.coerce GHC.Base.op_zg__.

Local Definition instance_forall___GHC_Base_Ord__f_a____GHC_Base_Ord__Alt_f_a__op_zgze__
                                                                                         {inst_f} {inst_a}
                                                                                         `{GHC.Base.Ord (inst_f inst_a)}
    : Alt inst_f inst_a -> Alt inst_f inst_a -> bool :=
  GHC.Prim.coerce GHC.Base.op_zgze__.

Local Definition instance_forall___GHC_Base_Ord__f_a____GHC_Base_Ord__Alt_f_a__op_zl__
                                                                                       {inst_f} {inst_a} `{GHC.Base.Ord
                                                                                       (inst_f inst_a)} : Alt inst_f
                                                                                                          inst_a -> Alt
                                                                                                          inst_f
                                                                                                          inst_a -> bool :=
  GHC.Prim.coerce GHC.Base.op_zl__.

Local Definition instance_forall___GHC_Base_Ord__f_a____GHC_Base_Ord__Alt_f_a__op_zlze__
                                                                                         {inst_f} {inst_a}
                                                                                         `{GHC.Base.Ord (inst_f inst_a)}
    : Alt inst_f inst_a -> Alt inst_f inst_a -> bool :=
  GHC.Prim.coerce GHC.Base.op_zlze__.

Instance instance_forall___GHC_Base_Ord__f_a____GHC_Base_Ord__Alt_f_a_  {f}
                                                                       {a} `{GHC.Base.Ord (f a)} : GHC.Base.Ord (Alt f
                                                                                                                a) :=
  fun _ k =>
    k (GHC.Base.Ord__Dict_Build (Alt f a)
                                instance_forall___GHC_Base_Ord__f_a____GHC_Base_Ord__Alt_f_a__op_zl__
                                instance_forall___GHC_Base_Ord__f_a____GHC_Base_Ord__Alt_f_a__op_zlze__
                                instance_forall___GHC_Base_Ord__f_a____GHC_Base_Ord__Alt_f_a__op_zg__
                                instance_forall___GHC_Base_Ord__f_a____GHC_Base_Ord__Alt_f_a__op_zgze__
                                instance_forall___GHC_Base_Ord__f_a____GHC_Base_Ord__Alt_f_a__compare
                                instance_forall___GHC_Base_Ord__f_a____GHC_Base_Ord__Alt_f_a__max
                                instance_forall___GHC_Base_Ord__f_a____GHC_Base_Ord__Alt_f_a__min).
(* Converted value declarations: *)

Instance Unpeel_Dual a : Unpeel (Dual a) a := Build_Unpeel _ _ getDual Mk_Dual.

Instance Unpeel_Sum a : Unpeel (Sum a) a := Build_Unpeel _ _ getSum Mk_Sum.

Instance Unpeel_Product a : Unpeel (Product a) a :=
  Build_Unpeel _ _ getProduct Mk_Product.

Instance Unpeel_First a : Unpeel (First a) (option a) :=
  Build_Unpeel _ _ getFirst Mk_First.

Instance Unpeel_Last a : Unpeel (Last a) (option a) :=
  Build_Unpeel _ _ getLast Mk_Last.

Instance Unpeel_Endo a : Unpeel (Endo a) (a -> a) :=
  Build_Unpeel _ _ appEndo Mk_Endo.

Instance Unpeel_Any : Unpeel Any bool := Build_Unpeel _ _ getAny Mk_Any.

Instance Unpeel_All : Unpeel All bool := Build_Unpeel _ _ getAll Mk_All.

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

Program Instance Monad__Last : GHC.Base.Monad Last :=
  fun _ k =>
    k {| GHC.Base.op_zgzg____ := fun {a} {b} => Monad__Last_op_zgzg__ ;
         GHC.Base.op_zgzgze____ := fun {a} {b} => Monad__Last_op_zgzgze__ ;
         GHC.Base.return___ := fun {a} => Monad__Last_return_ |}.

(* Translating `instance Applicative__Last' failed: Cannot find sig for
   Qualified "GHC.Base" "liftA2" unsupported *)

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

Program Instance Monad__First : GHC.Base.Monad First :=
  fun _ k =>
    k {| GHC.Base.op_zgzg____ := fun {a} {b} => Monad__First_op_zgzg__ ;
         GHC.Base.op_zgzgze____ := fun {a} {b} => Monad__First_op_zgzgze__ ;
         GHC.Base.return___ := fun {a} => Monad__First_return_ |}.

(* Translating `instance Applicative__First' failed: Cannot find sig for
   Qualified "GHC.Base" "liftA2" unsupported *)

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
     All Any Build_Unpeel Dual Endo Mk_All Mk_Any Mk_Dual Mk_Endo Mk_Product Mk_Sum
     Product Sum Unpeel appEndo bool comparison getAll getAny getDual getProduct
     getSum option GHC.Base.Eq_ GHC.Base.Functor GHC.Base.Monad GHC.Base.Ord
     GHC.Base.compare GHC.Base.fmap GHC.Base.max GHC.Base.min GHC.Base.op_zeze__
     GHC.Base.op_zg__ GHC.Base.op_zgze__ GHC.Base.op_zgzg__ GHC.Base.op_zgzgze__
     GHC.Base.op_zl__ GHC.Base.op_zlzd__ GHC.Base.op_zlze__ GHC.Base.op_zsze__
     GHC.Base.return_ GHC.Prim.coerce
*)
