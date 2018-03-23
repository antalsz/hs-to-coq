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

Inductive Sum a : Type := Mk_Sum : a -> Sum a.

Inductive Product a : Type := Mk_Product : a -> Product a.

Inductive Last a : Type := Mk_Last : option a -> Last a.

Inductive First a : Type := Mk_First : option a -> First a.

Inductive Endo a : Type := Mk_Endo : (a -> a) -> Endo a.

Inductive Dual a : Type := Mk_Dual : a -> Dual a.

Inductive Any : Type := Mk_Any : bool -> Any.

Inductive Alt (f : Type -> Type) a : Type := Mk_Alt : f a -> Alt f a.

Inductive All : Type := Mk_All : bool -> All.

Arguments Mk_Sum {_} _.

Arguments Mk_Product {_} _.

Arguments Mk_Last {_} _.

Arguments Mk_First {_} _.

Arguments Mk_Endo {_} _.

Arguments Mk_Dual {_} _.

Arguments Mk_Alt {_} {_} _.

Definition getSum {a} (arg_0__ : Sum a) :=
  let 'Mk_Sum getSum := arg_0__ in
  getSum.

Definition getProduct {a} (arg_1__ : Product a) :=
  let 'Mk_Product getProduct := arg_1__ in
  getProduct.

Definition getLast {a} (arg_2__ : Last a) :=
  let 'Mk_Last getLast := arg_2__ in
  getLast.

Definition getFirst {a} (arg_3__ : First a) :=
  let 'Mk_First getFirst := arg_3__ in
  getFirst.

Definition appEndo {a} (arg_4__ : Endo a) :=
  let 'Mk_Endo appEndo := arg_4__ in
  appEndo.

Definition getDual {a} (arg_5__ : Dual a) :=
  let 'Mk_Dual getDual := arg_5__ in
  getDual.

Definition getAny (arg_6__ : Any) :=
  let 'Mk_Any getAny := arg_6__ in
  getAny.

Definition getAlt {f : Type -> Type} {a} (arg_7__ : Alt f a) :=
  let 'Mk_Alt getAlt := arg_7__ in
  getAlt.

Definition getAll (arg_8__ : All) :=
  let 'Mk_All getAll := arg_8__ in
  getAll.
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

Local Definition Monoid__Dual_mappend {inst_a} `{GHC.Base.Monoid inst_a}
   : (Dual inst_a) -> (Dual inst_a) -> (Dual inst_a) :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | Mk_Dual x, Mk_Dual y => Mk_Dual (GHC.Base.mappend y x)
    end.

Local Definition Monoid__Dual_mempty {inst_a} `{GHC.Base.Monoid inst_a}
   : (Dual inst_a) :=
  Mk_Dual GHC.Base.mempty.

Local Definition Monoid__Dual_mconcat {inst_a} `{GHC.Base.Monoid inst_a}
   : list (Dual inst_a) -> (Dual inst_a) :=
  GHC.Base.foldr Monoid__Dual_mappend Monoid__Dual_mempty.

Program Instance Monoid__Dual {a} `{GHC.Base.Monoid a}
   : GHC.Base.Monoid (Dual a) :=
  fun _ k =>
    k {| GHC.Base.mappend__ := Monoid__Dual_mappend ;
         GHC.Base.mconcat__ := Monoid__Dual_mconcat ;
         GHC.Base.mempty__ := Monoid__Dual_mempty |}.

Local Definition Functor__Dual_fmap
   : forall {a} {b}, (a -> b) -> Dual a -> Dual b :=
  fun {a} {b} => GHC.Prim.coerce.

Local Definition Functor__Dual_op_zlzd__
   : forall {a} {b}, a -> Dual b -> Dual a :=
  fun {a} {b} => fun x => Functor__Dual_fmap (GHC.Base.const x).

Program Instance Functor__Dual : GHC.Base.Functor Dual :=
  fun _ k =>
    k {| GHC.Base.op_zlzd____ := fun {a} {b} => Functor__Dual_op_zlzd__ ;
         GHC.Base.fmap__ := fun {a} {b} => Functor__Dual_fmap |}.

Local Definition Applicative__Dual_op_zlztzg__
   : forall {a} {b}, Dual (a -> b) -> Dual a -> Dual b :=
  fun {a} {b} => GHC.Prim.coerce.

Local Definition Applicative__Dual_op_ztzg__
   : forall {a} {b}, Dual a -> Dual b -> Dual b :=
  fun {a} {b} =>
    fun x y =>
      Applicative__Dual_op_zlztzg__ (GHC.Base.fmap (GHC.Base.const GHC.Base.id) x) y.

Local Definition Applicative__Dual_pure : forall {a}, a -> Dual a :=
  fun {a} => Mk_Dual.

Program Instance Applicative__Dual : GHC.Base.Applicative Dual :=
  fun _ k =>
    k {| GHC.Base.op_ztzg____ := fun {a} {b} => Applicative__Dual_op_ztzg__ ;
         GHC.Base.op_zlztzg____ := fun {a} {b} => Applicative__Dual_op_zlztzg__ ;
         GHC.Base.pure__ := fun {a} => Applicative__Dual_pure |}.

Local Definition Monad__Dual_op_zgzg__
   : forall {a} {b}, Dual a -> Dual b -> Dual b :=
  fun {a} {b} => _GHC.Base.*>_.

Local Definition Monad__Dual_op_zgzgze__
   : forall {a} {b}, Dual a -> (a -> Dual b) -> Dual b :=
  fun {a} {b} => fun m k => k (getDual m).

Local Definition Monad__Dual_return_ : forall {a}, a -> Dual a :=
  fun {a} => GHC.Base.pure.

Program Instance Monad__Dual : GHC.Base.Monad Dual :=
  fun _ k =>
    k {| GHC.Base.op_zgzg____ := fun {a} {b} => Monad__Dual_op_zgzg__ ;
         GHC.Base.op_zgzgze____ := fun {a} {b} => Monad__Dual_op_zgzgze__ ;
         GHC.Base.return___ := fun {a} => Monad__Dual_return_ |}.

Local Definition Monoid__Endo_mappend {inst_a}
   : (Endo inst_a) -> (Endo inst_a) -> (Endo inst_a) :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | Mk_Endo f, Mk_Endo g => Mk_Endo (f GHC.Base.∘ g)
    end.

Local Definition Monoid__Endo_mempty {inst_a} : (Endo inst_a) :=
  Mk_Endo GHC.Base.id.

Local Definition Monoid__Endo_mconcat {inst_a}
   : list (Endo inst_a) -> (Endo inst_a) :=
  GHC.Base.foldr Monoid__Endo_mappend Monoid__Endo_mempty.

Program Instance Monoid__Endo {a} : GHC.Base.Monoid (Endo a) :=
  fun _ k =>
    k {| GHC.Base.mappend__ := Monoid__Endo_mappend ;
         GHC.Base.mconcat__ := Monoid__Endo_mconcat ;
         GHC.Base.mempty__ := Monoid__Endo_mempty |}.

Local Definition Monoid__All_mappend : All -> All -> All :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | Mk_All x, Mk_All y => Mk_All (andb x y)
    end.

Local Definition Monoid__All_mempty : All :=
  Mk_All true.

Local Definition Monoid__All_mconcat : list All -> All :=
  GHC.Base.foldr Monoid__All_mappend Monoid__All_mempty.

Program Instance Monoid__All : GHC.Base.Monoid All :=
  fun _ k =>
    k {| GHC.Base.mappend__ := Monoid__All_mappend ;
         GHC.Base.mconcat__ := Monoid__All_mconcat ;
         GHC.Base.mempty__ := Monoid__All_mempty |}.

Local Definition Monoid__Any_mappend : Any -> Any -> Any :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | Mk_Any x, Mk_Any y => Mk_Any (orb x y)
    end.

Local Definition Monoid__Any_mempty : Any :=
  Mk_Any false.

Local Definition Monoid__Any_mconcat : list Any -> Any :=
  GHC.Base.foldr Monoid__Any_mappend Monoid__Any_mempty.

Program Instance Monoid__Any : GHC.Base.Monoid Any :=
  fun _ k =>
    k {| GHC.Base.mappend__ := Monoid__Any_mappend ;
         GHC.Base.mconcat__ := Monoid__Any_mconcat ;
         GHC.Base.mempty__ := Monoid__Any_mempty |}.

(* Skipping instance Monoid__Sum *)

Local Definition Functor__Sum_fmap
   : forall {a} {b}, (a -> b) -> Sum a -> Sum b :=
  fun {a} {b} => GHC.Prim.coerce.

Local Definition Functor__Sum_op_zlzd__ : forall {a} {b}, a -> Sum b -> Sum a :=
  fun {a} {b} => fun x => Functor__Sum_fmap (GHC.Base.const x).

Program Instance Functor__Sum : GHC.Base.Functor Sum :=
  fun _ k =>
    k {| GHC.Base.op_zlzd____ := fun {a} {b} => Functor__Sum_op_zlzd__ ;
         GHC.Base.fmap__ := fun {a} {b} => Functor__Sum_fmap |}.

Local Definition Applicative__Sum_op_zlztzg__
   : forall {a} {b}, Sum (a -> b) -> Sum a -> Sum b :=
  fun {a} {b} => GHC.Prim.coerce.

Local Definition Applicative__Sum_op_ztzg__
   : forall {a} {b}, Sum a -> Sum b -> Sum b :=
  fun {a} {b} =>
    fun x y =>
      Applicative__Sum_op_zlztzg__ (GHC.Base.fmap (GHC.Base.const GHC.Base.id) x) y.

Local Definition Applicative__Sum_pure : forall {a}, a -> Sum a :=
  fun {a} => Mk_Sum.

Program Instance Applicative__Sum : GHC.Base.Applicative Sum :=
  fun _ k =>
    k {| GHC.Base.op_ztzg____ := fun {a} {b} => Applicative__Sum_op_ztzg__ ;
         GHC.Base.op_zlztzg____ := fun {a} {b} => Applicative__Sum_op_zlztzg__ ;
         GHC.Base.pure__ := fun {a} => Applicative__Sum_pure |}.

Local Definition Monad__Sum_op_zgzg__
   : forall {a} {b}, Sum a -> Sum b -> Sum b :=
  fun {a} {b} => _GHC.Base.*>_.

Local Definition Monad__Sum_op_zgzgze__
   : forall {a} {b}, Sum a -> (a -> Sum b) -> Sum b :=
  fun {a} {b} => fun m k => k (getSum m).

Local Definition Monad__Sum_return_ : forall {a}, a -> Sum a :=
  fun {a} => GHC.Base.pure.

Program Instance Monad__Sum : GHC.Base.Monad Sum :=
  fun _ k =>
    k {| GHC.Base.op_zgzg____ := fun {a} {b} => Monad__Sum_op_zgzg__ ;
         GHC.Base.op_zgzgze____ := fun {a} {b} => Monad__Sum_op_zgzgze__ ;
         GHC.Base.return___ := fun {a} => Monad__Sum_return_ |}.

(* Skipping instance Monoid__Product *)

Local Definition Functor__Product_fmap
   : forall {a} {b}, (a -> b) -> Product a -> Product b :=
  fun {a} {b} => GHC.Prim.coerce.

Local Definition Functor__Product_op_zlzd__
   : forall {a} {b}, a -> Product b -> Product a :=
  fun {a} {b} => fun x => Functor__Product_fmap (GHC.Base.const x).

Program Instance Functor__Product : GHC.Base.Functor Product :=
  fun _ k =>
    k {| GHC.Base.op_zlzd____ := fun {a} {b} => Functor__Product_op_zlzd__ ;
         GHC.Base.fmap__ := fun {a} {b} => Functor__Product_fmap |}.

Local Definition Applicative__Product_op_zlztzg__
   : forall {a} {b}, Product (a -> b) -> Product a -> Product b :=
  fun {a} {b} => GHC.Prim.coerce.

Local Definition Applicative__Product_op_ztzg__
   : forall {a} {b}, Product a -> Product b -> Product b :=
  fun {a} {b} =>
    fun x y =>
      Applicative__Product_op_zlztzg__ (GHC.Base.fmap (GHC.Base.const GHC.Base.id) x)
                                       y.

Local Definition Applicative__Product_pure : forall {a}, a -> Product a :=
  fun {a} => Mk_Product.

Program Instance Applicative__Product : GHC.Base.Applicative Product :=
  fun _ k =>
    k {| GHC.Base.op_ztzg____ := fun {a} {b} => Applicative__Product_op_ztzg__ ;
         GHC.Base.op_zlztzg____ := fun {a} {b} => Applicative__Product_op_zlztzg__ ;
         GHC.Base.pure__ := fun {a} => Applicative__Product_pure |}.

Local Definition Monad__Product_op_zgzg__
   : forall {a} {b}, Product a -> Product b -> Product b :=
  fun {a} {b} => _GHC.Base.*>_.

Local Definition Monad__Product_op_zgzgze__
   : forall {a} {b}, Product a -> (a -> Product b) -> Product b :=
  fun {a} {b} => fun m k => k (getProduct m).

Local Definition Monad__Product_return_ : forall {a}, a -> Product a :=
  fun {a} => GHC.Base.pure.

Program Instance Monad__Product : GHC.Base.Monad Product :=
  fun _ k =>
    k {| GHC.Base.op_zgzg____ := fun {a} {b} => Monad__Product_op_zgzg__ ;
         GHC.Base.op_zgzgze____ := fun {a} {b} => Monad__Product_op_zgzgze__ ;
         GHC.Base.return___ := fun {a} => Monad__Product_return_ |}.

Local Definition Monoid__First_mappend {inst_a}
   : (First inst_a) -> (First inst_a) -> (First inst_a) :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | Mk_First None, r => r
    | l, _ => l
    end.

Local Definition Monoid__First_mempty {inst_a} : (First inst_a) :=
  Mk_First None.

Local Definition Monoid__First_mconcat {inst_a}
   : list (First inst_a) -> (First inst_a) :=
  GHC.Base.foldr Monoid__First_mappend Monoid__First_mempty.

Program Instance Monoid__First {a} : GHC.Base.Monoid (First a) :=
  fun _ k =>
    k {| GHC.Base.mappend__ := Monoid__First_mappend ;
         GHC.Base.mconcat__ := Monoid__First_mconcat ;
         GHC.Base.mempty__ := Monoid__First_mempty |}.

Local Definition Monoid__Last_mappend {inst_a}
   : (Last inst_a) -> (Last inst_a) -> (Last inst_a) :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | l, Mk_Last None => l
    | _, r => r
    end.

Local Definition Monoid__Last_mempty {inst_a} : (Last inst_a) :=
  Mk_Last None.

Local Definition Monoid__Last_mconcat {inst_a}
   : list (Last inst_a) -> (Last inst_a) :=
  GHC.Base.foldr Monoid__Last_mappend Monoid__Last_mempty.

Program Instance Monoid__Last {a} : GHC.Base.Monoid (Last a) :=
  fun _ k =>
    k {| GHC.Base.mappend__ := Monoid__Last_mappend ;
         GHC.Base.mconcat__ := Monoid__Last_mconcat ;
         GHC.Base.mempty__ := Monoid__Last_mempty |}.

Local Definition Monoid__Alt_mappend {inst_f} {inst_a} `{_
   : GHC.Base.Alternative inst_f}
   : Alt inst_f inst_a -> Alt inst_f inst_a -> Alt inst_f inst_a :=
  GHC.Prim.coerce _GHC.Base.<|>_.

Local Definition Monoid__Alt_mempty {inst_f} {inst_a} `{GHC.Base.Alternative
  inst_f}
   : (Alt inst_f inst_a) :=
  Mk_Alt GHC.Base.empty.

Local Definition Monoid__Alt_mconcat {inst_f} {inst_a} `{GHC.Base.Alternative
  inst_f}
   : list (Alt inst_f inst_a) -> (Alt inst_f inst_a) :=
  GHC.Base.foldr Monoid__Alt_mappend Monoid__Alt_mempty.

Program Instance Monoid__Alt {f} {a} `{GHC.Base.Alternative f}
   : GHC.Base.Monoid (Alt f a) :=
  fun _ k =>
    k {| GHC.Base.mappend__ := Monoid__Alt_mappend ;
         GHC.Base.mconcat__ := Monoid__Alt_mconcat ;
         GHC.Base.mempty__ := Monoid__Alt_mempty |}.

Local Definition Functor__Alt_fmap {inst_f} `{GHC.Base.Functor inst_f}
   : forall {a} {b}, (a -> b) -> Alt inst_f a -> Alt inst_f b :=
  fun {a} {b} => GHC.Prim.coerce GHC.Base.fmap.

Local Definition Functor__Alt_op_zlzd__ {inst_f} `{GHC.Base.Functor inst_f}
   : forall {a} {b}, a -> Alt inst_f b -> Alt inst_f a :=
  fun {a} {b} => GHC.Prim.coerce _GHC.Base.<$_.

Program Instance Functor__Alt {f} `{GHC.Base.Functor f}
   : GHC.Base.Functor (Alt f) :=
  fun _ k =>
    k {| GHC.Base.op_zlzd____ := fun {a} {b} => Functor__Alt_op_zlzd__ ;
         GHC.Base.fmap__ := fun {a} {b} => Functor__Alt_fmap |}.

(* Translating `instance Alternative__Alt' failed: OOPS! Cannot find information
   for class Qualified "GHC.Base" "Alternative" unsupported *)

Local Definition Applicative__Alt_op_zlztzg__ {inst_f} `{GHC.Base.Applicative
  inst_f}
   : forall {a} {b}, Alt inst_f (a -> b) -> Alt inst_f a -> Alt inst_f b :=
  fun {a} {b} => GHC.Prim.coerce _GHC.Base.<*>_.

Local Definition Applicative__Alt_op_ztzg__ {inst_f} `{GHC.Base.Applicative
  inst_f}
   : forall {a} {b}, Alt inst_f a -> Alt inst_f b -> Alt inst_f b :=
  fun {a} {b} => GHC.Prim.coerce _GHC.Base.*>_.

Local Definition Applicative__Alt_pure {inst_f} `{GHC.Base.Applicative inst_f}
   : forall {a}, a -> Alt inst_f a :=
  fun {a} => GHC.Prim.coerce GHC.Base.pure.

Program Instance Applicative__Alt {f} `{GHC.Base.Applicative f}
   : GHC.Base.Applicative (Alt f) :=
  fun _ k =>
    k {| GHC.Base.op_ztzg____ := fun {a} {b} => Applicative__Alt_op_ztzg__ ;
         GHC.Base.op_zlztzg____ := fun {a} {b} => Applicative__Alt_op_zlztzg__ ;
         GHC.Base.pure__ := fun {a} => Applicative__Alt_pure |}.

(* Translating `instance MonadPlus__Alt' failed: OOPS! Cannot find information
   for class Qualified "GHC.Base" "MonadPlus" unsupported *)

Local Definition Monad__Alt_op_zgzg__ {inst_f} `{GHC.Base.Monad inst_f}
   : forall {a} {b}, Alt inst_f a -> Alt inst_f b -> Alt inst_f b :=
  fun {a} {b} => GHC.Prim.coerce _GHC.Base.>>_.

Local Definition Monad__Alt_op_zgzgze__ {inst_f} `{GHC.Base.Monad inst_f}
   : forall {a} {b}, Alt inst_f a -> (a -> Alt inst_f b) -> Alt inst_f b :=
  fun {a} {b} => GHC.Prim.coerce _GHC.Base.>>=_.

Local Definition Monad__Alt_return_ {inst_f} `{GHC.Base.Monad inst_f}
   : forall {a}, a -> Alt inst_f a :=
  fun {a} => GHC.Prim.coerce GHC.Base.return_.

Program Instance Monad__Alt {f} `{GHC.Base.Monad f} : GHC.Base.Monad (Alt f) :=
  fun _ k =>
    k {| GHC.Base.op_zgzg____ := fun {a} {b} => Monad__Alt_op_zgzg__ ;
         GHC.Base.op_zgzgze____ := fun {a} {b} => Monad__Alt_op_zgzgze__ ;
         GHC.Base.return___ := fun {a} => Monad__Alt_return_ |}.

(* Translating `instance Enum__Alt' failed: OOPS! Cannot find information for
   class Qualified "GHC.Enum" "Enum" unsupported *)

(* Translating `instance Num__Alt' failed: OOPS! Cannot find information for
   class Qualified "GHC.Num" "Num" unsupported *)

(* Skipping instance Ord__Alt *)

(* Skipping instance Eq___Alt *)

(* Skipping instance Show__Alt *)

(* Skipping instance Read__Alt *)

(* Translating `instance Generic1__Alt' failed: OOPS! Cannot find information
   for class Qualified "GHC.Generics" "Generic1" unsupported *)

(* Translating `instance Generic__Alt' failed: OOPS! Cannot find information for
   class Qualified "GHC.Generics" "Generic" unsupported *)

Local Definition Monad__Last_op_zgzg__
   : forall {a} {b}, Last a -> Last b -> Last b :=
  fun {a} {b} => GHC.Prim.coerce _GHC.Base.>>_.

Local Definition Monad__Last_op_zgzgze__
   : forall {a} {b}, Last a -> (a -> Last b) -> Last b :=
  fun {a} {b} => GHC.Prim.coerce _GHC.Base.>>=_.

Local Definition Monad__Last_return_ : forall {a}, a -> Last a :=
  fun {a} => GHC.Prim.coerce GHC.Base.return_.

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
         GHC.Base.pure__ := fun {a} => Applicative__Last_pure |}.

Program Instance Monad__Last : GHC.Base.Monad Last :=
  fun _ k =>
    k {| GHC.Base.op_zgzg____ := fun {a} {b} => Monad__Last_op_zgzg__ ;
         GHC.Base.op_zgzgze____ := fun {a} {b} => Monad__Last_op_zgzgze__ ;
         GHC.Base.return___ := fun {a} => Monad__Last_return_ |}.

(* Translating `instance Generic1__Last' failed: OOPS! Cannot find information
   for class Qualified "GHC.Generics" "Generic1" unsupported *)

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
         GHC.Base.pure__ := fun {a} => Applicative__First_pure |}.

Program Instance Monad__First : GHC.Base.Monad First :=
  fun _ k =>
    k {| GHC.Base.op_zgzg____ := fun {a} {b} => Monad__First_op_zgzg__ ;
         GHC.Base.op_zgzgze____ := fun {a} {b} => Monad__First_op_zgzgze__ ;
         GHC.Base.return___ := fun {a} => Monad__First_return_ |}.

(* Translating `instance Generic1__First' failed: OOPS! Cannot find information
   for class Qualified "GHC.Generics" "Generic1" unsupported *)

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

(* Translating `instance Num__Product' failed: OOPS! Cannot find information for
   class Qualified "GHC.Num" "Num" unsupported *)

(* Translating `instance Generic1__Product' failed: OOPS! Cannot find
   information for class Qualified "GHC.Generics" "Generic1" unsupported *)

(* Translating `instance Generic__Product' failed: OOPS! Cannot find information
   for class Qualified "GHC.Generics" "Generic" unsupported *)

(* Translating `instance Bounded__Product' failed: OOPS! Cannot find information
   for class Qualified "GHC.Enum" "Bounded" unsupported *)

(* Skipping instance Show__Product *)

(* Skipping instance Read__Product *)

Local Definition Ord__Product_compare {inst_a} `{GHC.Base.Ord inst_a}
   : Product inst_a -> Product inst_a -> comparison :=
  GHC.Prim.coerce GHC.Base.compare.

Local Definition Ord__Product_max {inst_a} `{GHC.Base.Ord inst_a}
   : Product inst_a -> Product inst_a -> Product inst_a :=
  GHC.Prim.coerce GHC.Base.max.

Local Definition Ord__Product_min {inst_a} `{GHC.Base.Ord inst_a}
   : Product inst_a -> Product inst_a -> Product inst_a :=
  GHC.Prim.coerce GHC.Base.min.

Local Definition Ord__Product_op_zg__ {inst_a} `{GHC.Base.Ord inst_a}
   : Product inst_a -> Product inst_a -> bool :=
  GHC.Prim.coerce _GHC.Base.>_.

Local Definition Ord__Product_op_zgze__ {inst_a} `{GHC.Base.Ord inst_a}
   : Product inst_a -> Product inst_a -> bool :=
  GHC.Prim.coerce _GHC.Base.>=_.

Local Definition Ord__Product_op_zl__ {inst_a} `{GHC.Base.Ord inst_a}
   : Product inst_a -> Product inst_a -> bool :=
  GHC.Prim.coerce _GHC.Base.<_.

Local Definition Ord__Product_op_zlze__ {inst_a} `{GHC.Base.Ord inst_a}
   : Product inst_a -> Product inst_a -> bool :=
  GHC.Prim.coerce _GHC.Base.<=_.

Local Definition Eq___Product_op_zeze__ {inst_a} `{GHC.Base.Eq_ inst_a}
   : Product inst_a -> Product inst_a -> bool :=
  GHC.Prim.coerce _GHC.Base.==_.

Local Definition Eq___Product_op_zsze__ {inst_a} `{GHC.Base.Eq_ inst_a}
   : Product inst_a -> Product inst_a -> bool :=
  GHC.Prim.coerce _GHC.Base./=_.

Program Instance Eq___Product {a} `{GHC.Base.Eq_ a}
   : GHC.Base.Eq_ (Product a) :=
  fun _ k =>
    k {| GHC.Base.op_zeze____ := Eq___Product_op_zeze__ ;
         GHC.Base.op_zsze____ := Eq___Product_op_zsze__ |}.

Program Instance Ord__Product {a} `{GHC.Base.Ord a}
   : GHC.Base.Ord (Product a) :=
  fun _ k =>
    k {| GHC.Base.op_zl____ := Ord__Product_op_zl__ ;
         GHC.Base.op_zlze____ := Ord__Product_op_zlze__ ;
         GHC.Base.op_zg____ := Ord__Product_op_zg__ ;
         GHC.Base.op_zgze____ := Ord__Product_op_zgze__ ;
         GHC.Base.compare__ := Ord__Product_compare ;
         GHC.Base.max__ := Ord__Product_max ;
         GHC.Base.min__ := Ord__Product_min |}.

(* Translating `instance Num__Sum' failed: OOPS! Cannot find information for
   class Qualified "GHC.Num" "Num" unsupported *)

(* Translating `instance Generic1__Sum' failed: OOPS! Cannot find information
   for class Qualified "GHC.Generics" "Generic1" unsupported *)

(* Translating `instance Generic__Sum' failed: OOPS! Cannot find information for
   class Qualified "GHC.Generics" "Generic" unsupported *)

(* Translating `instance Bounded__Sum' failed: OOPS! Cannot find information for
   class Qualified "GHC.Enum" "Bounded" unsupported *)

(* Skipping instance Show__Sum *)

(* Skipping instance Read__Sum *)

Local Definition Ord__Sum_compare {inst_a} `{GHC.Base.Ord inst_a}
   : Sum inst_a -> Sum inst_a -> comparison :=
  GHC.Prim.coerce GHC.Base.compare.

Local Definition Ord__Sum_max {inst_a} `{GHC.Base.Ord inst_a}
   : Sum inst_a -> Sum inst_a -> Sum inst_a :=
  GHC.Prim.coerce GHC.Base.max.

Local Definition Ord__Sum_min {inst_a} `{GHC.Base.Ord inst_a}
   : Sum inst_a -> Sum inst_a -> Sum inst_a :=
  GHC.Prim.coerce GHC.Base.min.

Local Definition Ord__Sum_op_zg__ {inst_a} `{GHC.Base.Ord inst_a}
   : Sum inst_a -> Sum inst_a -> bool :=
  GHC.Prim.coerce _GHC.Base.>_.

Local Definition Ord__Sum_op_zgze__ {inst_a} `{GHC.Base.Ord inst_a}
   : Sum inst_a -> Sum inst_a -> bool :=
  GHC.Prim.coerce _GHC.Base.>=_.

Local Definition Ord__Sum_op_zl__ {inst_a} `{GHC.Base.Ord inst_a}
   : Sum inst_a -> Sum inst_a -> bool :=
  GHC.Prim.coerce _GHC.Base.<_.

Local Definition Ord__Sum_op_zlze__ {inst_a} `{GHC.Base.Ord inst_a}
   : Sum inst_a -> Sum inst_a -> bool :=
  GHC.Prim.coerce _GHC.Base.<=_.

Local Definition Eq___Sum_op_zeze__ {inst_a} `{GHC.Base.Eq_ inst_a}
   : Sum inst_a -> Sum inst_a -> bool :=
  GHC.Prim.coerce _GHC.Base.==_.

Local Definition Eq___Sum_op_zsze__ {inst_a} `{GHC.Base.Eq_ inst_a}
   : Sum inst_a -> Sum inst_a -> bool :=
  GHC.Prim.coerce _GHC.Base./=_.

Program Instance Eq___Sum {a} `{GHC.Base.Eq_ a} : GHC.Base.Eq_ (Sum a) :=
  fun _ k =>
    k {| GHC.Base.op_zeze____ := Eq___Sum_op_zeze__ ;
         GHC.Base.op_zsze____ := Eq___Sum_op_zsze__ |}.

Program Instance Ord__Sum {a} `{GHC.Base.Ord a} : GHC.Base.Ord (Sum a) :=
  fun _ k =>
    k {| GHC.Base.op_zl____ := Ord__Sum_op_zl__ ;
         GHC.Base.op_zlze____ := Ord__Sum_op_zlze__ ;
         GHC.Base.op_zg____ := Ord__Sum_op_zg__ ;
         GHC.Base.op_zgze____ := Ord__Sum_op_zgze__ ;
         GHC.Base.compare__ := Ord__Sum_compare ;
         GHC.Base.max__ := Ord__Sum_max ;
         GHC.Base.min__ := Ord__Sum_min |}.

(* Translating `instance Generic__Any' failed: OOPS! Cannot find information for
   class Qualified "GHC.Generics" "Generic" unsupported *)

(* Translating `instance Bounded__Any' failed: OOPS! Cannot find information for
   class Qualified "GHC.Enum" "Bounded" unsupported *)

(* Skipping instance Show__Any *)

(* Skipping instance Read__Any *)

Local Definition Ord__Any_compare : Any -> Any -> comparison :=
  GHC.Prim.coerce GHC.Base.compare.

Local Definition Ord__Any_max : Any -> Any -> Any :=
  GHC.Prim.coerce GHC.Base.max.

Local Definition Ord__Any_min : Any -> Any -> Any :=
  GHC.Prim.coerce GHC.Base.min.

Local Definition Ord__Any_op_zg__ : Any -> Any -> bool :=
  GHC.Prim.coerce _GHC.Base.>_.

Local Definition Ord__Any_op_zgze__ : Any -> Any -> bool :=
  GHC.Prim.coerce _GHC.Base.>=_.

Local Definition Ord__Any_op_zl__ : Any -> Any -> bool :=
  GHC.Prim.coerce _GHC.Base.<_.

Local Definition Ord__Any_op_zlze__ : Any -> Any -> bool :=
  GHC.Prim.coerce _GHC.Base.<=_.

Local Definition Eq___Any_op_zeze__ : Any -> Any -> bool :=
  GHC.Prim.coerce _GHC.Base.==_.

Local Definition Eq___Any_op_zsze__ : Any -> Any -> bool :=
  GHC.Prim.coerce _GHC.Base./=_.

Program Instance Eq___Any : GHC.Base.Eq_ Any :=
  fun _ k =>
    k {| GHC.Base.op_zeze____ := Eq___Any_op_zeze__ ;
         GHC.Base.op_zsze____ := Eq___Any_op_zsze__ |}.

Program Instance Ord__Any : GHC.Base.Ord Any :=
  fun _ k =>
    k {| GHC.Base.op_zl____ := Ord__Any_op_zl__ ;
         GHC.Base.op_zlze____ := Ord__Any_op_zlze__ ;
         GHC.Base.op_zg____ := Ord__Any_op_zg__ ;
         GHC.Base.op_zgze____ := Ord__Any_op_zgze__ ;
         GHC.Base.compare__ := Ord__Any_compare ;
         GHC.Base.max__ := Ord__Any_max ;
         GHC.Base.min__ := Ord__Any_min |}.

(* Translating `instance Generic__All' failed: OOPS! Cannot find information for
   class Qualified "GHC.Generics" "Generic" unsupported *)

(* Translating `instance Bounded__All' failed: OOPS! Cannot find information for
   class Qualified "GHC.Enum" "Bounded" unsupported *)

(* Skipping instance Show__All *)

(* Skipping instance Read__All *)

Local Definition Ord__All_compare : All -> All -> comparison :=
  GHC.Prim.coerce GHC.Base.compare.

Local Definition Ord__All_max : All -> All -> All :=
  GHC.Prim.coerce GHC.Base.max.

Local Definition Ord__All_min : All -> All -> All :=
  GHC.Prim.coerce GHC.Base.min.

Local Definition Ord__All_op_zg__ : All -> All -> bool :=
  GHC.Prim.coerce _GHC.Base.>_.

Local Definition Ord__All_op_zgze__ : All -> All -> bool :=
  GHC.Prim.coerce _GHC.Base.>=_.

Local Definition Ord__All_op_zl__ : All -> All -> bool :=
  GHC.Prim.coerce _GHC.Base.<_.

Local Definition Ord__All_op_zlze__ : All -> All -> bool :=
  GHC.Prim.coerce _GHC.Base.<=_.

Local Definition Eq___All_op_zeze__ : All -> All -> bool :=
  GHC.Prim.coerce _GHC.Base.==_.

Local Definition Eq___All_op_zsze__ : All -> All -> bool :=
  GHC.Prim.coerce _GHC.Base./=_.

Program Instance Eq___All : GHC.Base.Eq_ All :=
  fun _ k =>
    k {| GHC.Base.op_zeze____ := Eq___All_op_zeze__ ;
         GHC.Base.op_zsze____ := Eq___All_op_zsze__ |}.

Program Instance Ord__All : GHC.Base.Ord All :=
  fun _ k =>
    k {| GHC.Base.op_zl____ := Ord__All_op_zl__ ;
         GHC.Base.op_zlze____ := Ord__All_op_zlze__ ;
         GHC.Base.op_zg____ := Ord__All_op_zg__ ;
         GHC.Base.op_zgze____ := Ord__All_op_zgze__ ;
         GHC.Base.compare__ := Ord__All_compare ;
         GHC.Base.max__ := Ord__All_max ;
         GHC.Base.min__ := Ord__All_min |}.

(* Translating `instance Generic__Endo' failed: OOPS! Cannot find information
   for class Qualified "GHC.Generics" "Generic" unsupported *)

(* Translating `instance Generic1__Dual' failed: OOPS! Cannot find information
   for class Qualified "GHC.Generics" "Generic1" unsupported *)

(* Translating `instance Generic__Dual' failed: OOPS! Cannot find information
   for class Qualified "GHC.Generics" "Generic" unsupported *)

(* Translating `instance Bounded__Dual' failed: OOPS! Cannot find information
   for class Qualified "GHC.Enum" "Bounded" unsupported *)

(* Skipping instance Show__Dual *)

(* Skipping instance Read__Dual *)

Local Definition Ord__Dual_compare {inst_a} `{GHC.Base.Ord inst_a}
   : Dual inst_a -> Dual inst_a -> comparison :=
  GHC.Prim.coerce GHC.Base.compare.

Local Definition Ord__Dual_max {inst_a} `{GHC.Base.Ord inst_a}
   : Dual inst_a -> Dual inst_a -> Dual inst_a :=
  GHC.Prim.coerce GHC.Base.max.

Local Definition Ord__Dual_min {inst_a} `{GHC.Base.Ord inst_a}
   : Dual inst_a -> Dual inst_a -> Dual inst_a :=
  GHC.Prim.coerce GHC.Base.min.

Local Definition Ord__Dual_op_zg__ {inst_a} `{GHC.Base.Ord inst_a}
   : Dual inst_a -> Dual inst_a -> bool :=
  GHC.Prim.coerce _GHC.Base.>_.

Local Definition Ord__Dual_op_zgze__ {inst_a} `{GHC.Base.Ord inst_a}
   : Dual inst_a -> Dual inst_a -> bool :=
  GHC.Prim.coerce _GHC.Base.>=_.

Local Definition Ord__Dual_op_zl__ {inst_a} `{GHC.Base.Ord inst_a}
   : Dual inst_a -> Dual inst_a -> bool :=
  GHC.Prim.coerce _GHC.Base.<_.

Local Definition Ord__Dual_op_zlze__ {inst_a} `{GHC.Base.Ord inst_a}
   : Dual inst_a -> Dual inst_a -> bool :=
  GHC.Prim.coerce _GHC.Base.<=_.

Local Definition Eq___Dual_op_zeze__ {inst_a} `{GHC.Base.Eq_ inst_a}
   : Dual inst_a -> Dual inst_a -> bool :=
  GHC.Prim.coerce _GHC.Base.==_.

Local Definition Eq___Dual_op_zsze__ {inst_a} `{GHC.Base.Eq_ inst_a}
   : Dual inst_a -> Dual inst_a -> bool :=
  GHC.Prim.coerce _GHC.Base./=_.

Program Instance Eq___Dual {a} `{GHC.Base.Eq_ a} : GHC.Base.Eq_ (Dual a) :=
  fun _ k =>
    k {| GHC.Base.op_zeze____ := Eq___Dual_op_zeze__ ;
         GHC.Base.op_zsze____ := Eq___Dual_op_zsze__ |}.

Program Instance Ord__Dual {a} `{GHC.Base.Ord a} : GHC.Base.Ord (Dual a) :=
  fun _ k =>
    k {| GHC.Base.op_zl____ := Ord__Dual_op_zl__ ;
         GHC.Base.op_zlze____ := Ord__Dual_op_zlze__ ;
         GHC.Base.op_zg____ := Ord__Dual_op_zg__ ;
         GHC.Base.op_zgze____ := Ord__Dual_op_zgze__ ;
         GHC.Base.compare__ := Ord__Dual_compare ;
         GHC.Base.max__ := Ord__Dual_max ;
         GHC.Base.min__ := Ord__Dual_min |}.

(* Unbound variables:
     Build_Unpeel None Type Unpeel andb bool comparison false list option orb true
     GHC.Base.Alternative GHC.Base.Applicative GHC.Base.Eq_ GHC.Base.Functor
     GHC.Base.Monad GHC.Base.Monoid GHC.Base.Ord GHC.Base.compare GHC.Base.const
     GHC.Base.empty GHC.Base.fmap GHC.Base.foldr GHC.Base.id GHC.Base.mappend
     GHC.Base.max GHC.Base.mempty GHC.Base.min GHC.Base.op_z2218U__
     GHC.Base.op_zeze__ GHC.Base.op_zg__ GHC.Base.op_zgze__ GHC.Base.op_zgzg__
     GHC.Base.op_zgzgze__ GHC.Base.op_zl__ GHC.Base.op_zlzbzg__ GHC.Base.op_zlzd__
     GHC.Base.op_zlze__ GHC.Base.op_zlztzg__ GHC.Base.op_zsze__ GHC.Base.op_ztzg__
     GHC.Base.pure GHC.Base.return_ GHC.Prim.coerce
*)
