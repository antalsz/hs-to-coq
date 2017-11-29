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
  match arg_0__ with
    | Mk_Sum getSum => getSum
  end.

Definition getProduct {a} (arg_1__ : Product a) :=
  match arg_1__ with
    | Mk_Product getProduct => getProduct
  end.

Definition getLast {a} (arg_2__ : Last a) :=
  match arg_2__ with
    | Mk_Last getLast => getLast
  end.

Definition getFirst {a} (arg_3__ : First a) :=
  match arg_3__ with
    | Mk_First getFirst => getFirst
  end.

Definition appEndo {a} (arg_4__ : Endo a) :=
  match arg_4__ with
    | Mk_Endo appEndo => appEndo
  end.

Definition getDual {a} (arg_5__ : Dual a) :=
  match arg_5__ with
    | Mk_Dual getDual => getDual
  end.

Definition getAny (arg_6__ : Any) :=
  match arg_6__ with
    | Mk_Any getAny => getAny
  end.

Definition getAlt {f : Type -> Type} {a} (arg_7__ : Alt f a) :=
  match arg_7__ with
    | Mk_Alt getAlt => getAlt
  end.

Definition getAll (arg_8__ : All) :=
  match arg_8__ with
    | Mk_All getAll => getAll
  end.
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

Instance Unpeel_Product a : Unpeel (Product a) a := Build_Unpeel _ _ getProduct
                                                                 Mk_Product.

Instance Unpeel_First a : Unpeel (First a) (option a) := Build_Unpeel _ _
                                                                      getFirst Mk_First.

Instance Unpeel_Last a : Unpeel (Last a) (option a) := Build_Unpeel _ _ getLast
                                                                    Mk_Last.

Instance Unpeel_Endo a : Unpeel (Endo a) (a -> a) := Build_Unpeel _ _ appEndo
                                                                  Mk_Endo.

Instance Unpeel_Any : Unpeel Any bool := Build_Unpeel _ _ getAny Mk_Any.

Instance Unpeel_All : Unpeel All bool := Build_Unpeel _ _ getAll Mk_All.

Local Definition instance_forall___GHC_Base_Monoid_a___GHC_Base_Monoid__Data_Monoid_Dual_a__mappend {inst_a}
                                                                                                    `{GHC.Base.Monoid
                                                                                                    inst_a} : (Dual
                                                                                                              inst_a) -> (Dual
                                                                                                              inst_a) -> (Dual
                                                                                                              inst_a) :=
  fun arg_192__ arg_193__ =>
    match arg_192__ , arg_193__ with
      | Mk_Dual x , Mk_Dual y => Mk_Dual (GHC.Base.mappend y x)
    end.

Local Definition instance_forall___GHC_Base_Monoid_a___GHC_Base_Monoid__Data_Monoid_Dual_a__mempty {inst_a}
                                                                                                   `{GHC.Base.Monoid
                                                                                                   inst_a} : (Dual
                                                                                                             inst_a) :=
  Mk_Dual GHC.Base.mempty.

Local Definition instance_forall___GHC_Base_Monoid_a___GHC_Base_Monoid__Data_Monoid_Dual_a__mconcat {inst_a}
                                                                                                    `{GHC.Base.Monoid
                                                                                                    inst_a} : list (Dual
                                                                                                                   inst_a) -> (Dual
                                                                                                              inst_a) :=
  GHC.Base.foldr
  instance_forall___GHC_Base_Monoid_a___GHC_Base_Monoid__Data_Monoid_Dual_a__mappend
  instance_forall___GHC_Base_Monoid_a___GHC_Base_Monoid__Data_Monoid_Dual_a__mempty.

Program Instance instance_forall___GHC_Base_Monoid_a___GHC_Base_Monoid__Data_Monoid_Dual_a_ {a}
                                                                                            `{GHC.Base.Monoid a}
  : GHC.Base.Monoid (Dual a) := fun _ k =>
    k
    {|GHC.Base.mappend__ := instance_forall___GHC_Base_Monoid_a___GHC_Base_Monoid__Data_Monoid_Dual_a__mappend ;
    GHC.Base.mconcat__ := instance_forall___GHC_Base_Monoid_a___GHC_Base_Monoid__Data_Monoid_Dual_a__mconcat ;
    GHC.Base.mempty__ := instance_forall___GHC_Base_Monoid_a___GHC_Base_Monoid__Data_Monoid_Dual_a__mempty |}.

Local Definition instance_GHC_Base_Functor_Data_Monoid_Dual_fmap : forall {a}
                                                                          {b},
                                                                     (a -> b) -> Dual a -> Dual b :=
  fun {a} {b} => GHC.Prim.coerce.

Local Definition instance_GHC_Base_Functor_Data_Monoid_Dual_op_zlzd__
    : forall {a} {b}, a -> Dual b -> Dual a :=
  fun {a} {b} =>
    fun x => instance_GHC_Base_Functor_Data_Monoid_Dual_fmap (GHC.Base.const x).

Program Instance instance_GHC_Base_Functor_Data_Monoid_Dual : GHC.Base.Functor
                                                              Dual := fun _ k =>
    k {|GHC.Base.op_zlzd____ := fun {a} {b} =>
        instance_GHC_Base_Functor_Data_Monoid_Dual_op_zlzd__ ;
      GHC.Base.fmap__ := fun {a} {b} =>
        instance_GHC_Base_Functor_Data_Monoid_Dual_fmap |}.

Local Definition instance_GHC_Base_Applicative_Data_Monoid_Dual_op_zlztzg__
    : forall {a} {b}, Dual (a -> b) -> Dual a -> Dual b :=
  fun {a} {b} => GHC.Prim.coerce.

Local Definition instance_GHC_Base_Applicative_Data_Monoid_Dual_op_ztzg__
    : forall {a} {b}, Dual a -> Dual b -> Dual b :=
  fun {a} {b} =>
    fun x y =>
      instance_GHC_Base_Applicative_Data_Monoid_Dual_op_zlztzg__ (GHC.Base.fmap
                                                                 (GHC.Base.const GHC.Base.id) x) y.

Local Definition instance_GHC_Base_Applicative_Data_Monoid_Dual_pure
    : forall {a}, a -> Dual a :=
  fun {a} => Mk_Dual.

Program Instance instance_GHC_Base_Applicative_Data_Monoid_Dual
  : GHC.Base.Applicative Dual := fun _ k =>
    k {|GHC.Base.op_ztzg____ := fun {a} {b} =>
        instance_GHC_Base_Applicative_Data_Monoid_Dual_op_ztzg__ ;
      GHC.Base.op_zlztzg____ := fun {a} {b} =>
        instance_GHC_Base_Applicative_Data_Monoid_Dual_op_zlztzg__ ;
      GHC.Base.pure__ := fun {a} =>
        instance_GHC_Base_Applicative_Data_Monoid_Dual_pure |}.

Local Definition instance_GHC_Base_Monad_Data_Monoid_Dual_op_zgzg__ : forall {a}
                                                                             {b},
                                                                        Dual a -> Dual b -> Dual b :=
  fun {a} {b} => GHC.Base.op_ztzg__.

Local Definition instance_GHC_Base_Monad_Data_Monoid_Dual_op_zgzgze__
    : forall {a} {b}, Dual a -> (a -> Dual b) -> Dual b :=
  fun {a} {b} => fun m k => k (getDual m).

Local Definition instance_GHC_Base_Monad_Data_Monoid_Dual_return_ : forall {a},
                                                                      a -> Dual a :=
  fun {a} => GHC.Base.pure.

Program Instance instance_GHC_Base_Monad_Data_Monoid_Dual : GHC.Base.Monad
                                                            Dual := fun _ k =>
    k {|GHC.Base.op_zgzg____ := fun {a} {b} =>
        instance_GHC_Base_Monad_Data_Monoid_Dual_op_zgzg__ ;
      GHC.Base.op_zgzgze____ := fun {a} {b} =>
        instance_GHC_Base_Monad_Data_Monoid_Dual_op_zgzgze__ ;
      GHC.Base.return___ := fun {a} =>
        instance_GHC_Base_Monad_Data_Monoid_Dual_return_ |}.

Local Definition instance_GHC_Base_Monoid__Data_Monoid_Endo_a__mappend {inst_a}
    : (Endo inst_a) -> (Endo inst_a) -> (Endo inst_a) :=
  fun arg_186__ arg_187__ =>
    match arg_186__ , arg_187__ with
      | Mk_Endo f , Mk_Endo g => Mk_Endo (GHC.Base.op_z2218U__ f g)
    end.

Local Definition instance_GHC_Base_Monoid__Data_Monoid_Endo_a__mempty {inst_a}
    : (Endo inst_a) :=
  Mk_Endo GHC.Base.id.

Local Definition instance_GHC_Base_Monoid__Data_Monoid_Endo_a__mconcat {inst_a}
    : list (Endo inst_a) -> (Endo inst_a) :=
  GHC.Base.foldr instance_GHC_Base_Monoid__Data_Monoid_Endo_a__mappend
                 instance_GHC_Base_Monoid__Data_Monoid_Endo_a__mempty.

Program Instance instance_GHC_Base_Monoid__Data_Monoid_Endo_a_ {a}
  : GHC.Base.Monoid (Endo a) := fun _ k =>
    k
    {|GHC.Base.mappend__ := instance_GHC_Base_Monoid__Data_Monoid_Endo_a__mappend ;
    GHC.Base.mconcat__ := instance_GHC_Base_Monoid__Data_Monoid_Endo_a__mconcat ;
    GHC.Base.mempty__ := instance_GHC_Base_Monoid__Data_Monoid_Endo_a__mempty |}.

Local Definition instance_GHC_Base_Monoid_Data_Monoid_All_mappend
    : All -> All -> All :=
  fun arg_181__ arg_182__ =>
    match arg_181__ , arg_182__ with
      | Mk_All x , Mk_All y => Mk_All (andb x y)
    end.

Local Definition instance_GHC_Base_Monoid_Data_Monoid_All_mempty : All :=
  Mk_All true.

Local Definition instance_GHC_Base_Monoid_Data_Monoid_All_mconcat : list
                                                                    All -> All :=
  GHC.Base.foldr instance_GHC_Base_Monoid_Data_Monoid_All_mappend
                 instance_GHC_Base_Monoid_Data_Monoid_All_mempty.

Program Instance instance_GHC_Base_Monoid_Data_Monoid_All : GHC.Base.Monoid
                                                            All := fun _ k =>
    k {|GHC.Base.mappend__ := instance_GHC_Base_Monoid_Data_Monoid_All_mappend ;
      GHC.Base.mconcat__ := instance_GHC_Base_Monoid_Data_Monoid_All_mconcat ;
      GHC.Base.mempty__ := instance_GHC_Base_Monoid_Data_Monoid_All_mempty |}.

Local Definition instance_GHC_Base_Monoid_Data_Monoid_Any_mappend
    : Any -> Any -> Any :=
  fun arg_176__ arg_177__ =>
    match arg_176__ , arg_177__ with
      | Mk_Any x , Mk_Any y => Mk_Any (orb x y)
    end.

Local Definition instance_GHC_Base_Monoid_Data_Monoid_Any_mempty : Any :=
  Mk_Any false.

Local Definition instance_GHC_Base_Monoid_Data_Monoid_Any_mconcat : list
                                                                    Any -> Any :=
  GHC.Base.foldr instance_GHC_Base_Monoid_Data_Monoid_Any_mappend
                 instance_GHC_Base_Monoid_Data_Monoid_Any_mempty.

Program Instance instance_GHC_Base_Monoid_Data_Monoid_Any : GHC.Base.Monoid
                                                            Any := fun _ k =>
    k {|GHC.Base.mappend__ := instance_GHC_Base_Monoid_Data_Monoid_Any_mappend ;
      GHC.Base.mconcat__ := instance_GHC_Base_Monoid_Data_Monoid_Any_mconcat ;
      GHC.Base.mempty__ := instance_GHC_Base_Monoid_Data_Monoid_Any_mempty |}.

(* Skipping instance
   instance_forall___GHC_Num_Num_a___GHC_Base_Monoid__Data_Monoid_Sum_a_ *)

Local Definition instance_GHC_Base_Functor_Data_Monoid_Sum_fmap : forall {a}
                                                                         {b},
                                                                    (a -> b) -> Sum a -> Sum b :=
  fun {a} {b} => GHC.Prim.coerce.

Local Definition instance_GHC_Base_Functor_Data_Monoid_Sum_op_zlzd__
    : forall {a} {b}, a -> Sum b -> Sum a :=
  fun {a} {b} =>
    fun x => instance_GHC_Base_Functor_Data_Monoid_Sum_fmap (GHC.Base.const x).

Program Instance instance_GHC_Base_Functor_Data_Monoid_Sum : GHC.Base.Functor
                                                             Sum := fun _ k =>
    k {|GHC.Base.op_zlzd____ := fun {a} {b} =>
        instance_GHC_Base_Functor_Data_Monoid_Sum_op_zlzd__ ;
      GHC.Base.fmap__ := fun {a} {b} =>
        instance_GHC_Base_Functor_Data_Monoid_Sum_fmap |}.

Local Definition instance_GHC_Base_Applicative_Data_Monoid_Sum_op_zlztzg__
    : forall {a} {b}, Sum (a -> b) -> Sum a -> Sum b :=
  fun {a} {b} => GHC.Prim.coerce.

Local Definition instance_GHC_Base_Applicative_Data_Monoid_Sum_op_ztzg__
    : forall {a} {b}, Sum a -> Sum b -> Sum b :=
  fun {a} {b} =>
    fun x y =>
      instance_GHC_Base_Applicative_Data_Monoid_Sum_op_zlztzg__ (GHC.Base.fmap
                                                                (GHC.Base.const GHC.Base.id) x) y.

Local Definition instance_GHC_Base_Applicative_Data_Monoid_Sum_pure
    : forall {a}, a -> Sum a :=
  fun {a} => Mk_Sum.

Program Instance instance_GHC_Base_Applicative_Data_Monoid_Sum
  : GHC.Base.Applicative Sum := fun _ k =>
    k {|GHC.Base.op_ztzg____ := fun {a} {b} =>
        instance_GHC_Base_Applicative_Data_Monoid_Sum_op_ztzg__ ;
      GHC.Base.op_zlztzg____ := fun {a} {b} =>
        instance_GHC_Base_Applicative_Data_Monoid_Sum_op_zlztzg__ ;
      GHC.Base.pure__ := fun {a} =>
        instance_GHC_Base_Applicative_Data_Monoid_Sum_pure |}.

Local Definition instance_GHC_Base_Monad_Data_Monoid_Sum_op_zgzg__ : forall {a}
                                                                            {b},
                                                                       Sum a -> Sum b -> Sum b :=
  fun {a} {b} => GHC.Base.op_ztzg__.

Local Definition instance_GHC_Base_Monad_Data_Monoid_Sum_op_zgzgze__
    : forall {a} {b}, Sum a -> (a -> Sum b) -> Sum b :=
  fun {a} {b} => fun m k => k (getSum m).

Local Definition instance_GHC_Base_Monad_Data_Monoid_Sum_return_ : forall {a},
                                                                     a -> Sum a :=
  fun {a} => GHC.Base.pure.

Program Instance instance_GHC_Base_Monad_Data_Monoid_Sum : GHC.Base.Monad Sum :=
  fun _ k =>
    k {|GHC.Base.op_zgzg____ := fun {a} {b} =>
        instance_GHC_Base_Monad_Data_Monoid_Sum_op_zgzg__ ;
      GHC.Base.op_zgzgze____ := fun {a} {b} =>
        instance_GHC_Base_Monad_Data_Monoid_Sum_op_zgzgze__ ;
      GHC.Base.return___ := fun {a} =>
        instance_GHC_Base_Monad_Data_Monoid_Sum_return_ |}.

(* Skipping instance
   instance_forall___GHC_Num_Num_a___GHC_Base_Monoid__Data_Monoid_Product_a_ *)

Local Definition instance_GHC_Base_Functor_Data_Monoid_Product_fmap : forall {a}
                                                                             {b},
                                                                        (a -> b) -> Product a -> Product b :=
  fun {a} {b} => GHC.Prim.coerce.

Local Definition instance_GHC_Base_Functor_Data_Monoid_Product_op_zlzd__
    : forall {a} {b}, a -> Product b -> Product a :=
  fun {a} {b} =>
    fun x => instance_GHC_Base_Functor_Data_Monoid_Product_fmap (GHC.Base.const x).

Program Instance instance_GHC_Base_Functor_Data_Monoid_Product
  : GHC.Base.Functor Product := fun _ k =>
    k {|GHC.Base.op_zlzd____ := fun {a} {b} =>
        instance_GHC_Base_Functor_Data_Monoid_Product_op_zlzd__ ;
      GHC.Base.fmap__ := fun {a} {b} =>
        instance_GHC_Base_Functor_Data_Monoid_Product_fmap |}.

Local Definition instance_GHC_Base_Applicative_Data_Monoid_Product_op_zlztzg__
    : forall {a} {b}, Product (a -> b) -> Product a -> Product b :=
  fun {a} {b} => GHC.Prim.coerce.

Local Definition instance_GHC_Base_Applicative_Data_Monoid_Product_op_ztzg__
    : forall {a} {b}, Product a -> Product b -> Product b :=
  fun {a} {b} =>
    fun x y =>
      instance_GHC_Base_Applicative_Data_Monoid_Product_op_zlztzg__ (GHC.Base.fmap
                                                                    (GHC.Base.const GHC.Base.id) x) y.

Local Definition instance_GHC_Base_Applicative_Data_Monoid_Product_pure
    : forall {a}, a -> Product a :=
  fun {a} => Mk_Product.

Program Instance instance_GHC_Base_Applicative_Data_Monoid_Product
  : GHC.Base.Applicative Product := fun _ k =>
    k {|GHC.Base.op_ztzg____ := fun {a} {b} =>
        instance_GHC_Base_Applicative_Data_Monoid_Product_op_ztzg__ ;
      GHC.Base.op_zlztzg____ := fun {a} {b} =>
        instance_GHC_Base_Applicative_Data_Monoid_Product_op_zlztzg__ ;
      GHC.Base.pure__ := fun {a} =>
        instance_GHC_Base_Applicative_Data_Monoid_Product_pure |}.

Local Definition instance_GHC_Base_Monad_Data_Monoid_Product_op_zgzg__
    : forall {a} {b}, Product a -> Product b -> Product b :=
  fun {a} {b} => GHC.Base.op_ztzg__.

Local Definition instance_GHC_Base_Monad_Data_Monoid_Product_op_zgzgze__
    : forall {a} {b}, Product a -> (a -> Product b) -> Product b :=
  fun {a} {b} => fun m k => k (getProduct m).

Local Definition instance_GHC_Base_Monad_Data_Monoid_Product_return_
    : forall {a}, a -> Product a :=
  fun {a} => GHC.Base.pure.

Program Instance instance_GHC_Base_Monad_Data_Monoid_Product : GHC.Base.Monad
                                                               Product := fun _ k =>
    k {|GHC.Base.op_zgzg____ := fun {a} {b} =>
        instance_GHC_Base_Monad_Data_Monoid_Product_op_zgzg__ ;
      GHC.Base.op_zgzgze____ := fun {a} {b} =>
        instance_GHC_Base_Monad_Data_Monoid_Product_op_zgzgze__ ;
      GHC.Base.return___ := fun {a} =>
        instance_GHC_Base_Monad_Data_Monoid_Product_return_ |}.

Local Definition instance_GHC_Base_Monoid__Data_Monoid_First_a__mappend {inst_a}
    : (First inst_a) -> (First inst_a) -> (First inst_a) :=
  fun arg_166__ arg_167__ =>
    match arg_166__ , arg_167__ with
      | Mk_First None , r => r
      | l , _ => l
    end.

Local Definition instance_GHC_Base_Monoid__Data_Monoid_First_a__mempty {inst_a}
    : (First inst_a) :=
  Mk_First None.

Local Definition instance_GHC_Base_Monoid__Data_Monoid_First_a__mconcat {inst_a}
    : list (First inst_a) -> (First inst_a) :=
  GHC.Base.foldr instance_GHC_Base_Monoid__Data_Monoid_First_a__mappend
                 instance_GHC_Base_Monoid__Data_Monoid_First_a__mempty.

Program Instance instance_GHC_Base_Monoid__Data_Monoid_First_a_ {a}
  : GHC.Base.Monoid (First a) := fun _ k =>
    k
    {|GHC.Base.mappend__ := instance_GHC_Base_Monoid__Data_Monoid_First_a__mappend ;
    GHC.Base.mconcat__ := instance_GHC_Base_Monoid__Data_Monoid_First_a__mconcat ;
    GHC.Base.mempty__ := instance_GHC_Base_Monoid__Data_Monoid_First_a__mempty |}.

Local Definition instance_GHC_Base_Monoid__Data_Monoid_Last_a__mappend {inst_a}
    : (Last inst_a) -> (Last inst_a) -> (Last inst_a) :=
  fun arg_162__ arg_163__ =>
    match arg_162__ , arg_163__ with
      | l , Mk_Last None => l
      | _ , r => r
    end.

Local Definition instance_GHC_Base_Monoid__Data_Monoid_Last_a__mempty {inst_a}
    : (Last inst_a) :=
  Mk_Last None.

Local Definition instance_GHC_Base_Monoid__Data_Monoid_Last_a__mconcat {inst_a}
    : list (Last inst_a) -> (Last inst_a) :=
  GHC.Base.foldr instance_GHC_Base_Monoid__Data_Monoid_Last_a__mappend
                 instance_GHC_Base_Monoid__Data_Monoid_Last_a__mempty.

Program Instance instance_GHC_Base_Monoid__Data_Monoid_Last_a_ {a}
  : GHC.Base.Monoid (Last a) := fun _ k =>
    k
    {|GHC.Base.mappend__ := instance_GHC_Base_Monoid__Data_Monoid_Last_a__mappend ;
    GHC.Base.mconcat__ := instance_GHC_Base_Monoid__Data_Monoid_Last_a__mconcat ;
    GHC.Base.mempty__ := instance_GHC_Base_Monoid__Data_Monoid_Last_a__mempty |}.

Local Definition instance_forall___GHC_Base_Alternative_f___GHC_Base_Monoid__Data_Monoid_Alt_f_a__mappend {inst_f}
                                                                                                          {inst_a} `{_
                                                                                                            : GHC.Base.Alternative
                                                                                                              inst_f}
    : Alt inst_f inst_a -> Alt inst_f inst_a -> Alt inst_f inst_a :=
  GHC.Prim.coerce GHC.Base.op_zlzbzg__.

Local Definition instance_forall___GHC_Base_Alternative_f___GHC_Base_Monoid__Data_Monoid_Alt_f_a__mempty {inst_f}
                                                                                                         {inst_a}
                                                                                                         `{GHC.Base.Alternative
                                                                                                         inst_f} : (Alt
                                                                                                                   inst_f
                                                                                                                   inst_a) :=
  Mk_Alt GHC.Base.empty.

Local Definition instance_forall___GHC_Base_Alternative_f___GHC_Base_Monoid__Data_Monoid_Alt_f_a__mconcat {inst_f}
                                                                                                          {inst_a}
                                                                                                          `{GHC.Base.Alternative
                                                                                                          inst_f} : list
                                                                                                                    (Alt
                                                                                                                    inst_f
                                                                                                                    inst_a) -> (Alt
                                                                                                                    inst_f
                                                                                                                    inst_a) :=
  GHC.Base.foldr
  instance_forall___GHC_Base_Alternative_f___GHC_Base_Monoid__Data_Monoid_Alt_f_a__mappend
  instance_forall___GHC_Base_Alternative_f___GHC_Base_Monoid__Data_Monoid_Alt_f_a__mempty.

Program Instance instance_forall___GHC_Base_Alternative_f___GHC_Base_Monoid__Data_Monoid_Alt_f_a_ {f}
                                                                                                  {a}
                                                                                                  `{GHC.Base.Alternative
                                                                                                  f} : GHC.Base.Monoid
                                                                                                       (Alt f a) :=
  fun _ k =>
    k
    {|GHC.Base.mappend__ := instance_forall___GHC_Base_Alternative_f___GHC_Base_Monoid__Data_Monoid_Alt_f_a__mappend ;
    GHC.Base.mconcat__ := instance_forall___GHC_Base_Alternative_f___GHC_Base_Monoid__Data_Monoid_Alt_f_a__mconcat ;
    GHC.Base.mempty__ := instance_forall___GHC_Base_Alternative_f___GHC_Base_Monoid__Data_Monoid_Alt_f_a__mempty |}.

Local Definition instance_forall___GHC_Base_Functor_f___GHC_Base_Functor__Data_Monoid_Alt_f__fmap {inst_f}
                                                                                                  `{GHC.Base.Functor
                                                                                                  inst_f} : forall {a}
                                                                                                                   {b},
                                                                                                              (a -> b) -> Alt
                                                                                                              inst_f
                                                                                                              a -> Alt
                                                                                                              inst_f
                                                                                                              b :=
  fun {a} {b} => GHC.Prim.coerce GHC.Base.fmap.

Local Definition instance_forall___GHC_Base_Functor_f___GHC_Base_Functor__Data_Monoid_Alt_f__op_zlzd__ {inst_f}
                                                                                                       `{GHC.Base.Functor
                                                                                                       inst_f}
    : forall {a} {b}, a -> Alt inst_f b -> Alt inst_f a :=
  fun {a} {b} => GHC.Prim.coerce GHC.Base.op_zlzd__.

Program Instance instance_forall___GHC_Base_Functor_f___GHC_Base_Functor__Data_Monoid_Alt_f_ {f}
                                                                                             `{GHC.Base.Functor f}
  : GHC.Base.Functor (Alt f) := fun _ k =>
    k {|GHC.Base.op_zlzd____ := fun {a} {b} =>
        instance_forall___GHC_Base_Functor_f___GHC_Base_Functor__Data_Monoid_Alt_f__op_zlzd__ ;
      GHC.Base.fmap__ := fun {a} {b} =>
        instance_forall___GHC_Base_Functor_f___GHC_Base_Functor__Data_Monoid_Alt_f__fmap |}.

(* Translating `instance forall {f}, forall `{GHC.Base.Alternative f},
   GHC.Base.Alternative (Data.Monoid.Alt f)' failed: OOPS! Cannot find information
   for class Qualified_ "GHC.Base" "Alternative" unsupported *)

Local Definition instance_forall___GHC_Base_Applicative_f___GHC_Base_Applicative__Data_Monoid_Alt_f__op_zlztzg__ {inst_f}
                                                                                                                 `{GHC.Base.Applicative
                                                                                                                 inst_f}
    : forall {a} {b}, Alt inst_f (a -> b) -> Alt inst_f a -> Alt inst_f b :=
  fun {a} {b} => GHC.Prim.coerce GHC.Base.op_zlztzg__.

Local Definition instance_forall___GHC_Base_Applicative_f___GHC_Base_Applicative__Data_Monoid_Alt_f__op_ztzg__ {inst_f}
                                                                                                               `{GHC.Base.Applicative
                                                                                                               inst_f}
    : forall {a} {b}, Alt inst_f a -> Alt inst_f b -> Alt inst_f b :=
  fun {a} {b} => GHC.Prim.coerce GHC.Base.op_ztzg__.

Local Definition instance_forall___GHC_Base_Applicative_f___GHC_Base_Applicative__Data_Monoid_Alt_f__pure {inst_f}
                                                                                                          `{GHC.Base.Applicative
                                                                                                          inst_f}
    : forall {a}, a -> Alt inst_f a :=
  fun {a} => GHC.Prim.coerce GHC.Base.pure.

Program Instance instance_forall___GHC_Base_Applicative_f___GHC_Base_Applicative__Data_Monoid_Alt_f_ {f}
                                                                                                     `{GHC.Base.Applicative
                                                                                                     f}
  : GHC.Base.Applicative (Alt f) := fun _ k =>
    k {|GHC.Base.op_ztzg____ := fun {a} {b} =>
        instance_forall___GHC_Base_Applicative_f___GHC_Base_Applicative__Data_Monoid_Alt_f__op_ztzg__ ;
      GHC.Base.op_zlztzg____ := fun {a} {b} =>
        instance_forall___GHC_Base_Applicative_f___GHC_Base_Applicative__Data_Monoid_Alt_f__op_zlztzg__ ;
      GHC.Base.pure__ := fun {a} =>
        instance_forall___GHC_Base_Applicative_f___GHC_Base_Applicative__Data_Monoid_Alt_f__pure |}.

(* Translating `instance forall {f}, forall `{GHC.Base.MonadPlus f},
   GHC.Base.MonadPlus (Data.Monoid.Alt f)' failed: OOPS! Cannot find information
   for class Qualified_ "GHC.Base" "MonadPlus" unsupported *)

Local Definition instance_forall___GHC_Base_Monad_f___GHC_Base_Monad__Data_Monoid_Alt_f__op_zgzg__ {inst_f}
                                                                                                   `{GHC.Base.Monad
                                                                                                   inst_f} : forall {a}
                                                                                                                    {b},
                                                                                                               Alt
                                                                                                               inst_f
                                                                                                               a -> Alt
                                                                                                               inst_f
                                                                                                               b -> Alt
                                                                                                               inst_f
                                                                                                               b :=
  fun {a} {b} => GHC.Prim.coerce GHC.Base.op_zgzg__.

Local Definition instance_forall___GHC_Base_Monad_f___GHC_Base_Monad__Data_Monoid_Alt_f__op_zgzgze__ {inst_f}
                                                                                                     `{GHC.Base.Monad
                                                                                                     inst_f}
    : forall {a} {b}, Alt inst_f a -> (a -> Alt inst_f b) -> Alt inst_f b :=
  fun {a} {b} => GHC.Prim.coerce GHC.Base.op_zgzgze__.

Local Definition instance_forall___GHC_Base_Monad_f___GHC_Base_Monad__Data_Monoid_Alt_f__return_ {inst_f}
                                                                                                 `{GHC.Base.Monad
                                                                                                 inst_f} : forall {a},
                                                                                                             a -> Alt
                                                                                                             inst_f a :=
  fun {a} => GHC.Prim.coerce GHC.Base.return_.

Program Instance instance_forall___GHC_Base_Monad_f___GHC_Base_Monad__Data_Monoid_Alt_f_ {f}
                                                                                         `{GHC.Base.Monad f}
  : GHC.Base.Monad (Alt f) := fun _ k =>
    k {|GHC.Base.op_zgzg____ := fun {a} {b} =>
        instance_forall___GHC_Base_Monad_f___GHC_Base_Monad__Data_Monoid_Alt_f__op_zgzg__ ;
      GHC.Base.op_zgzgze____ := fun {a} {b} =>
        instance_forall___GHC_Base_Monad_f___GHC_Base_Monad__Data_Monoid_Alt_f__op_zgzgze__ ;
      GHC.Base.return___ := fun {a} =>
        instance_forall___GHC_Base_Monad_f___GHC_Base_Monad__Data_Monoid_Alt_f__return_ |}.

(* Translating `instance forall {k} {f} {a}, forall `{GHC.Enum.Enum (f a)},
   GHC.Enum.Enum (Data.Monoid.Alt f a)' failed: OOPS! Cannot find information for
   class Qualified_ "GHC.Enum" "Enum" unsupported *)

(* Translating `instance forall {k} {f} {a}, forall `{GHC.Num.Num (f a)},
   GHC.Num.Num (Data.Monoid.Alt f a)' failed: OOPS! Cannot find information for
   class Qualified_ "GHC.Num" "Num" unsupported *)

(* Skipping instance
   instance_forall___GHC_Base_Ord__f_a____GHC_Base_Ord__Data_Monoid_Alt_f_a_ *)

(* Skipping instance
   instance_forall___GHC_Base_Eq___f_a____GHC_Base_Eq___Data_Monoid_Alt_f_a_ *)

(* Skipping instance
   instance_forall___GHC_Show_Show__f_a____GHC_Show_Show__Data_Monoid_Alt_f_a_ *)

(* Skipping instance
   instance_forall___GHC_Read_Read__f_a____GHC_Read_Read__Data_Monoid_Alt_f_a_ *)

(* Translating `instance forall {f}, GHC.Generics.Generic1 (Data.Monoid.Alt f)'
   failed: OOPS! Cannot find information for class Qualified_ "GHC.Generics"
   "Generic1" unsupported *)

(* Translating `instance forall {k} {f} {a}, GHC.Generics.Generic
   (Data.Monoid.Alt f a)' failed: OOPS! Cannot find information for class
   Qualified_ "GHC.Generics" "Generic" unsupported *)

Local Definition instance_GHC_Base_Monad_Data_Monoid_Last_op_zgzg__ : forall {a}
                                                                             {b},
                                                                        Last a -> Last b -> Last b :=
  fun {a} {b} => GHC.Prim.coerce GHC.Base.op_zgzg__.

Local Definition instance_GHC_Base_Monad_Data_Monoid_Last_op_zgzgze__
    : forall {a} {b}, Last a -> (a -> Last b) -> Last b :=
  fun {a} {b} => GHC.Prim.coerce GHC.Base.op_zgzgze__.

Local Definition instance_GHC_Base_Monad_Data_Monoid_Last_return_ : forall {a},
                                                                      a -> Last a :=
  fun {a} => GHC.Prim.coerce GHC.Base.return_.

Local Definition instance_GHC_Base_Applicative_Data_Monoid_Last_op_zlztzg__
    : forall {a} {b}, Last (a -> b) -> Last a -> Last b :=
  fun {a} {b} => GHC.Prim.coerce GHC.Base.op_zlztzg__.

Local Definition instance_GHC_Base_Applicative_Data_Monoid_Last_op_ztzg__
    : forall {a} {b}, Last a -> Last b -> Last b :=
  fun {a} {b} => GHC.Prim.coerce GHC.Base.op_ztzg__.

Local Definition instance_GHC_Base_Applicative_Data_Monoid_Last_pure
    : forall {a}, a -> Last a :=
  fun {a} => GHC.Prim.coerce GHC.Base.pure.

Local Definition instance_GHC_Base_Functor_Data_Monoid_Last_fmap : forall {a}
                                                                          {b},
                                                                     (a -> b) -> Last a -> Last b :=
  fun {a} {b} => GHC.Prim.coerce GHC.Base.fmap.

Local Definition instance_GHC_Base_Functor_Data_Monoid_Last_op_zlzd__
    : forall {a} {b}, a -> Last b -> Last a :=
  fun {a} {b} => GHC.Prim.coerce GHC.Base.op_zlzd__.

Program Instance instance_GHC_Base_Functor_Data_Monoid_Last : GHC.Base.Functor
                                                              Last := fun _ k =>
    k {|GHC.Base.op_zlzd____ := fun {a} {b} =>
        instance_GHC_Base_Functor_Data_Monoid_Last_op_zlzd__ ;
      GHC.Base.fmap__ := fun {a} {b} =>
        instance_GHC_Base_Functor_Data_Monoid_Last_fmap |}.

Program Instance instance_GHC_Base_Applicative_Data_Monoid_Last
  : GHC.Base.Applicative Last := fun _ k =>
    k {|GHC.Base.op_ztzg____ := fun {a} {b} =>
        instance_GHC_Base_Applicative_Data_Monoid_Last_op_ztzg__ ;
      GHC.Base.op_zlztzg____ := fun {a} {b} =>
        instance_GHC_Base_Applicative_Data_Monoid_Last_op_zlztzg__ ;
      GHC.Base.pure__ := fun {a} =>
        instance_GHC_Base_Applicative_Data_Monoid_Last_pure |}.

Program Instance instance_GHC_Base_Monad_Data_Monoid_Last : GHC.Base.Monad
                                                            Last := fun _ k =>
    k {|GHC.Base.op_zgzg____ := fun {a} {b} =>
        instance_GHC_Base_Monad_Data_Monoid_Last_op_zgzg__ ;
      GHC.Base.op_zgzgze____ := fun {a} {b} =>
        instance_GHC_Base_Monad_Data_Monoid_Last_op_zgzgze__ ;
      GHC.Base.return___ := fun {a} =>
        instance_GHC_Base_Monad_Data_Monoid_Last_return_ |}.

(* Translating `instance GHC.Generics.Generic1 Data.Monoid.Last' failed: OOPS!
   Cannot find information for class Qualified_ "GHC.Generics" "Generic1"
   unsupported *)

(* Translating `instance forall {a}, GHC.Generics.Generic (Data.Monoid.Last a)'
   failed: OOPS! Cannot find information for class Qualified_ "GHC.Generics"
   "Generic" unsupported *)

(* Skipping instance
   instance_forall___GHC_Show_Show_a___GHC_Show_Show__Data_Monoid_Last_a_ *)

(* Skipping instance
   instance_forall___GHC_Read_Read_a___GHC_Read_Read__Data_Monoid_Last_a_ *)

Local Definition instance_forall___GHC_Base_Ord_a___GHC_Base_Ord__Data_Monoid_Last_a__compare {inst_a}
                                                                                              `{GHC.Base.Ord inst_a}
    : Last inst_a -> Last inst_a -> comparison :=
  GHC.Prim.coerce GHC.Base.compare.

Local Definition instance_forall___GHC_Base_Ord_a___GHC_Base_Ord__Data_Monoid_Last_a__max {inst_a}
                                                                                          `{GHC.Base.Ord inst_a} : Last
                                                                                                                   inst_a -> Last
                                                                                                                   inst_a -> Last
                                                                                                                   inst_a :=
  GHC.Prim.coerce GHC.Base.max.

Local Definition instance_forall___GHC_Base_Ord_a___GHC_Base_Ord__Data_Monoid_Last_a__min {inst_a}
                                                                                          `{GHC.Base.Ord inst_a} : Last
                                                                                                                   inst_a -> Last
                                                                                                                   inst_a -> Last
                                                                                                                   inst_a :=
  GHC.Prim.coerce GHC.Base.min.

Local Definition instance_forall___GHC_Base_Ord_a___GHC_Base_Ord__Data_Monoid_Last_a__op_zg__ {inst_a}
                                                                                              `{GHC.Base.Ord inst_a}
    : Last inst_a -> Last inst_a -> bool :=
  GHC.Prim.coerce GHC.Base.op_zg__.

Local Definition instance_forall___GHC_Base_Ord_a___GHC_Base_Ord__Data_Monoid_Last_a__op_zgze__ {inst_a}
                                                                                                `{GHC.Base.Ord inst_a}
    : Last inst_a -> Last inst_a -> bool :=
  GHC.Prim.coerce GHC.Base.op_zgze__.

Local Definition instance_forall___GHC_Base_Ord_a___GHC_Base_Ord__Data_Monoid_Last_a__op_zl__ {inst_a}
                                                                                              `{GHC.Base.Ord inst_a}
    : Last inst_a -> Last inst_a -> bool :=
  GHC.Prim.coerce GHC.Base.op_zl__.

Local Definition instance_forall___GHC_Base_Ord_a___GHC_Base_Ord__Data_Monoid_Last_a__op_zlze__ {inst_a}
                                                                                                `{GHC.Base.Ord inst_a}
    : Last inst_a -> Last inst_a -> bool :=
  GHC.Prim.coerce GHC.Base.op_zlze__.

Local Definition instance_forall___GHC_Base_Eq__a___GHC_Base_Eq___Data_Monoid_Last_a__op_zeze__ {inst_a}
                                                                                                `{GHC.Base.Eq_ inst_a}
    : Last inst_a -> Last inst_a -> bool :=
  GHC.Prim.coerce GHC.Base.op_zeze__.

Local Definition instance_forall___GHC_Base_Eq__a___GHC_Base_Eq___Data_Monoid_Last_a__op_zsze__ {inst_a}
                                                                                                `{GHC.Base.Eq_ inst_a}
    : Last inst_a -> Last inst_a -> bool :=
  GHC.Prim.coerce GHC.Base.op_zsze__.

Program Instance instance_forall___GHC_Base_Eq__a___GHC_Base_Eq___Data_Monoid_Last_a_ {a}
                                                                                      `{GHC.Base.Eq_ a} : GHC.Base.Eq_
                                                                                                          (Last a) :=
  fun _ k =>
    k
    {|GHC.Base.op_zeze____ := instance_forall___GHC_Base_Eq__a___GHC_Base_Eq___Data_Monoid_Last_a__op_zeze__ ;
    GHC.Base.op_zsze____ := instance_forall___GHC_Base_Eq__a___GHC_Base_Eq___Data_Monoid_Last_a__op_zsze__ |}.

Program Instance instance_forall___GHC_Base_Ord_a___GHC_Base_Ord__Data_Monoid_Last_a_ {a}
                                                                                      `{GHC.Base.Ord a} : GHC.Base.Ord
                                                                                                          (Last a) :=
  fun _ k =>
    k
    {|GHC.Base.op_zl____ := instance_forall___GHC_Base_Ord_a___GHC_Base_Ord__Data_Monoid_Last_a__op_zl__ ;
    GHC.Base.op_zlze____ := instance_forall___GHC_Base_Ord_a___GHC_Base_Ord__Data_Monoid_Last_a__op_zlze__ ;
    GHC.Base.op_zg____ := instance_forall___GHC_Base_Ord_a___GHC_Base_Ord__Data_Monoid_Last_a__op_zg__ ;
    GHC.Base.op_zgze____ := instance_forall___GHC_Base_Ord_a___GHC_Base_Ord__Data_Monoid_Last_a__op_zgze__ ;
    GHC.Base.compare__ := instance_forall___GHC_Base_Ord_a___GHC_Base_Ord__Data_Monoid_Last_a__compare ;
    GHC.Base.max__ := instance_forall___GHC_Base_Ord_a___GHC_Base_Ord__Data_Monoid_Last_a__max ;
    GHC.Base.min__ := instance_forall___GHC_Base_Ord_a___GHC_Base_Ord__Data_Monoid_Last_a__min |}.

Local Definition instance_GHC_Base_Monad_Data_Monoid_First_op_zgzg__
    : forall {a} {b}, First a -> First b -> First b :=
  fun {a} {b} => GHC.Prim.coerce GHC.Base.op_zgzg__.

Local Definition instance_GHC_Base_Monad_Data_Monoid_First_op_zgzgze__
    : forall {a} {b}, First a -> (a -> First b) -> First b :=
  fun {a} {b} => GHC.Prim.coerce GHC.Base.op_zgzgze__.

Local Definition instance_GHC_Base_Monad_Data_Monoid_First_return_ : forall {a},
                                                                       a -> First a :=
  fun {a} => GHC.Prim.coerce GHC.Base.return_.

Local Definition instance_GHC_Base_Applicative_Data_Monoid_First_op_zlztzg__
    : forall {a} {b}, First (a -> b) -> First a -> First b :=
  fun {a} {b} => GHC.Prim.coerce GHC.Base.op_zlztzg__.

Local Definition instance_GHC_Base_Applicative_Data_Monoid_First_op_ztzg__
    : forall {a} {b}, First a -> First b -> First b :=
  fun {a} {b} => GHC.Prim.coerce GHC.Base.op_ztzg__.

Local Definition instance_GHC_Base_Applicative_Data_Monoid_First_pure
    : forall {a}, a -> First a :=
  fun {a} => GHC.Prim.coerce GHC.Base.pure.

Local Definition instance_GHC_Base_Functor_Data_Monoid_First_fmap : forall {a}
                                                                           {b},
                                                                      (a -> b) -> First a -> First b :=
  fun {a} {b} => GHC.Prim.coerce GHC.Base.fmap.

Local Definition instance_GHC_Base_Functor_Data_Monoid_First_op_zlzd__
    : forall {a} {b}, a -> First b -> First a :=
  fun {a} {b} => GHC.Prim.coerce GHC.Base.op_zlzd__.

Program Instance instance_GHC_Base_Functor_Data_Monoid_First : GHC.Base.Functor
                                                               First := fun _ k =>
    k {|GHC.Base.op_zlzd____ := fun {a} {b} =>
        instance_GHC_Base_Functor_Data_Monoid_First_op_zlzd__ ;
      GHC.Base.fmap__ := fun {a} {b} =>
        instance_GHC_Base_Functor_Data_Monoid_First_fmap |}.

Program Instance instance_GHC_Base_Applicative_Data_Monoid_First
  : GHC.Base.Applicative First := fun _ k =>
    k {|GHC.Base.op_ztzg____ := fun {a} {b} =>
        instance_GHC_Base_Applicative_Data_Monoid_First_op_ztzg__ ;
      GHC.Base.op_zlztzg____ := fun {a} {b} =>
        instance_GHC_Base_Applicative_Data_Monoid_First_op_zlztzg__ ;
      GHC.Base.pure__ := fun {a} =>
        instance_GHC_Base_Applicative_Data_Monoid_First_pure |}.

Program Instance instance_GHC_Base_Monad_Data_Monoid_First : GHC.Base.Monad
                                                             First := fun _ k =>
    k {|GHC.Base.op_zgzg____ := fun {a} {b} =>
        instance_GHC_Base_Monad_Data_Monoid_First_op_zgzg__ ;
      GHC.Base.op_zgzgze____ := fun {a} {b} =>
        instance_GHC_Base_Monad_Data_Monoid_First_op_zgzgze__ ;
      GHC.Base.return___ := fun {a} =>
        instance_GHC_Base_Monad_Data_Monoid_First_return_ |}.

(* Translating `instance GHC.Generics.Generic1 Data.Monoid.First' failed: OOPS!
   Cannot find information for class Qualified_ "GHC.Generics" "Generic1"
   unsupported *)

(* Translating `instance forall {a}, GHC.Generics.Generic (Data.Monoid.First a)'
   failed: OOPS! Cannot find information for class Qualified_ "GHC.Generics"
   "Generic" unsupported *)

(* Skipping instance
   instance_forall___GHC_Show_Show_a___GHC_Show_Show__Data_Monoid_First_a_ *)

(* Skipping instance
   instance_forall___GHC_Read_Read_a___GHC_Read_Read__Data_Monoid_First_a_ *)

Local Definition instance_forall___GHC_Base_Ord_a___GHC_Base_Ord__Data_Monoid_First_a__compare {inst_a}
                                                                                               `{GHC.Base.Ord inst_a}
    : First inst_a -> First inst_a -> comparison :=
  GHC.Prim.coerce GHC.Base.compare.

Local Definition instance_forall___GHC_Base_Ord_a___GHC_Base_Ord__Data_Monoid_First_a__max {inst_a}
                                                                                           `{GHC.Base.Ord inst_a}
    : First inst_a -> First inst_a -> First inst_a :=
  GHC.Prim.coerce GHC.Base.max.

Local Definition instance_forall___GHC_Base_Ord_a___GHC_Base_Ord__Data_Monoid_First_a__min {inst_a}
                                                                                           `{GHC.Base.Ord inst_a}
    : First inst_a -> First inst_a -> First inst_a :=
  GHC.Prim.coerce GHC.Base.min.

Local Definition instance_forall___GHC_Base_Ord_a___GHC_Base_Ord__Data_Monoid_First_a__op_zg__ {inst_a}
                                                                                               `{GHC.Base.Ord inst_a}
    : First inst_a -> First inst_a -> bool :=
  GHC.Prim.coerce GHC.Base.op_zg__.

Local Definition instance_forall___GHC_Base_Ord_a___GHC_Base_Ord__Data_Monoid_First_a__op_zgze__ {inst_a}
                                                                                                 `{GHC.Base.Ord inst_a}
    : First inst_a -> First inst_a -> bool :=
  GHC.Prim.coerce GHC.Base.op_zgze__.

Local Definition instance_forall___GHC_Base_Ord_a___GHC_Base_Ord__Data_Monoid_First_a__op_zl__ {inst_a}
                                                                                               `{GHC.Base.Ord inst_a}
    : First inst_a -> First inst_a -> bool :=
  GHC.Prim.coerce GHC.Base.op_zl__.

Local Definition instance_forall___GHC_Base_Ord_a___GHC_Base_Ord__Data_Monoid_First_a__op_zlze__ {inst_a}
                                                                                                 `{GHC.Base.Ord inst_a}
    : First inst_a -> First inst_a -> bool :=
  GHC.Prim.coerce GHC.Base.op_zlze__.

Local Definition instance_forall___GHC_Base_Eq__a___GHC_Base_Eq___Data_Monoid_First_a__op_zeze__ {inst_a}
                                                                                                 `{GHC.Base.Eq_ inst_a}
    : First inst_a -> First inst_a -> bool :=
  GHC.Prim.coerce GHC.Base.op_zeze__.

Local Definition instance_forall___GHC_Base_Eq__a___GHC_Base_Eq___Data_Monoid_First_a__op_zsze__ {inst_a}
                                                                                                 `{GHC.Base.Eq_ inst_a}
    : First inst_a -> First inst_a -> bool :=
  GHC.Prim.coerce GHC.Base.op_zsze__.

Program Instance instance_forall___GHC_Base_Eq__a___GHC_Base_Eq___Data_Monoid_First_a_ {a}
                                                                                       `{GHC.Base.Eq_ a} : GHC.Base.Eq_
                                                                                                           (First a) :=
  fun _ k =>
    k
    {|GHC.Base.op_zeze____ := instance_forall___GHC_Base_Eq__a___GHC_Base_Eq___Data_Monoid_First_a__op_zeze__ ;
    GHC.Base.op_zsze____ := instance_forall___GHC_Base_Eq__a___GHC_Base_Eq___Data_Monoid_First_a__op_zsze__ |}.

Program Instance instance_forall___GHC_Base_Ord_a___GHC_Base_Ord__Data_Monoid_First_a_ {a}
                                                                                       `{GHC.Base.Ord a} : GHC.Base.Ord
                                                                                                           (First a) :=
  fun _ k =>
    k
    {|GHC.Base.op_zl____ := instance_forall___GHC_Base_Ord_a___GHC_Base_Ord__Data_Monoid_First_a__op_zl__ ;
    GHC.Base.op_zlze____ := instance_forall___GHC_Base_Ord_a___GHC_Base_Ord__Data_Monoid_First_a__op_zlze__ ;
    GHC.Base.op_zg____ := instance_forall___GHC_Base_Ord_a___GHC_Base_Ord__Data_Monoid_First_a__op_zg__ ;
    GHC.Base.op_zgze____ := instance_forall___GHC_Base_Ord_a___GHC_Base_Ord__Data_Monoid_First_a__op_zgze__ ;
    GHC.Base.compare__ := instance_forall___GHC_Base_Ord_a___GHC_Base_Ord__Data_Monoid_First_a__compare ;
    GHC.Base.max__ := instance_forall___GHC_Base_Ord_a___GHC_Base_Ord__Data_Monoid_First_a__max ;
    GHC.Base.min__ := instance_forall___GHC_Base_Ord_a___GHC_Base_Ord__Data_Monoid_First_a__min |}.

(* Translating `instance forall {a}, forall `{GHC.Num.Num a}, GHC.Num.Num
   (Data.Monoid.Product a)' failed: OOPS! Cannot find information for class
   Qualified_ "GHC.Num" "Num" unsupported *)

(* Translating `instance GHC.Generics.Generic1 Data.Monoid.Product' failed:
   OOPS! Cannot find information for class Qualified_ "GHC.Generics" "Generic1"
   unsupported *)

(* Translating `instance forall {a}, GHC.Generics.Generic (Data.Monoid.Product
   a)' failed: OOPS! Cannot find information for class Qualified_ "GHC.Generics"
   "Generic" unsupported *)

(* Translating `instance forall {a}, forall `{GHC.Enum.Bounded a},
   GHC.Enum.Bounded (Data.Monoid.Product a)' failed: OOPS! Cannot find information
   for class Qualified_ "GHC.Enum" "Bounded" unsupported *)

(* Skipping instance
   instance_forall___GHC_Show_Show_a___GHC_Show_Show__Data_Monoid_Product_a_ *)

(* Skipping instance
   instance_forall___GHC_Read_Read_a___GHC_Read_Read__Data_Monoid_Product_a_ *)

Local Definition instance_forall___GHC_Base_Ord_a___GHC_Base_Ord__Data_Monoid_Product_a__compare {inst_a}
                                                                                                 `{GHC.Base.Ord inst_a}
    : Product inst_a -> Product inst_a -> comparison :=
  GHC.Prim.coerce GHC.Base.compare.

Local Definition instance_forall___GHC_Base_Ord_a___GHC_Base_Ord__Data_Monoid_Product_a__max {inst_a}
                                                                                             `{GHC.Base.Ord inst_a}
    : Product inst_a -> Product inst_a -> Product inst_a :=
  GHC.Prim.coerce GHC.Base.max.

Local Definition instance_forall___GHC_Base_Ord_a___GHC_Base_Ord__Data_Monoid_Product_a__min {inst_a}
                                                                                             `{GHC.Base.Ord inst_a}
    : Product inst_a -> Product inst_a -> Product inst_a :=
  GHC.Prim.coerce GHC.Base.min.

Local Definition instance_forall___GHC_Base_Ord_a___GHC_Base_Ord__Data_Monoid_Product_a__op_zg__ {inst_a}
                                                                                                 `{GHC.Base.Ord inst_a}
    : Product inst_a -> Product inst_a -> bool :=
  GHC.Prim.coerce GHC.Base.op_zg__.

Local Definition instance_forall___GHC_Base_Ord_a___GHC_Base_Ord__Data_Monoid_Product_a__op_zgze__ {inst_a}
                                                                                                   `{GHC.Base.Ord
                                                                                                   inst_a} : Product
                                                                                                             inst_a -> Product
                                                                                                             inst_a -> bool :=
  GHC.Prim.coerce GHC.Base.op_zgze__.

Local Definition instance_forall___GHC_Base_Ord_a___GHC_Base_Ord__Data_Monoid_Product_a__op_zl__ {inst_a}
                                                                                                 `{GHC.Base.Ord inst_a}
    : Product inst_a -> Product inst_a -> bool :=
  GHC.Prim.coerce GHC.Base.op_zl__.

Local Definition instance_forall___GHC_Base_Ord_a___GHC_Base_Ord__Data_Monoid_Product_a__op_zlze__ {inst_a}
                                                                                                   `{GHC.Base.Ord
                                                                                                   inst_a} : Product
                                                                                                             inst_a -> Product
                                                                                                             inst_a -> bool :=
  GHC.Prim.coerce GHC.Base.op_zlze__.

Local Definition instance_forall___GHC_Base_Eq__a___GHC_Base_Eq___Data_Monoid_Product_a__op_zeze__ {inst_a}
                                                                                                   `{GHC.Base.Eq_
                                                                                                   inst_a} : Product
                                                                                                             inst_a -> Product
                                                                                                             inst_a -> bool :=
  GHC.Prim.coerce GHC.Base.op_zeze__.

Local Definition instance_forall___GHC_Base_Eq__a___GHC_Base_Eq___Data_Monoid_Product_a__op_zsze__ {inst_a}
                                                                                                   `{GHC.Base.Eq_
                                                                                                   inst_a} : Product
                                                                                                             inst_a -> Product
                                                                                                             inst_a -> bool :=
  GHC.Prim.coerce GHC.Base.op_zsze__.

Program Instance instance_forall___GHC_Base_Eq__a___GHC_Base_Eq___Data_Monoid_Product_a_ {a}
                                                                                         `{GHC.Base.Eq_ a}
  : GHC.Base.Eq_ (Product a) := fun _ k =>
    k
    {|GHC.Base.op_zeze____ := instance_forall___GHC_Base_Eq__a___GHC_Base_Eq___Data_Monoid_Product_a__op_zeze__ ;
    GHC.Base.op_zsze____ := instance_forall___GHC_Base_Eq__a___GHC_Base_Eq___Data_Monoid_Product_a__op_zsze__ |}.

Program Instance instance_forall___GHC_Base_Ord_a___GHC_Base_Ord__Data_Monoid_Product_a_ {a}
                                                                                         `{GHC.Base.Ord a}
  : GHC.Base.Ord (Product a) := fun _ k =>
    k
    {|GHC.Base.op_zl____ := instance_forall___GHC_Base_Ord_a___GHC_Base_Ord__Data_Monoid_Product_a__op_zl__ ;
    GHC.Base.op_zlze____ := instance_forall___GHC_Base_Ord_a___GHC_Base_Ord__Data_Monoid_Product_a__op_zlze__ ;
    GHC.Base.op_zg____ := instance_forall___GHC_Base_Ord_a___GHC_Base_Ord__Data_Monoid_Product_a__op_zg__ ;
    GHC.Base.op_zgze____ := instance_forall___GHC_Base_Ord_a___GHC_Base_Ord__Data_Monoid_Product_a__op_zgze__ ;
    GHC.Base.compare__ := instance_forall___GHC_Base_Ord_a___GHC_Base_Ord__Data_Monoid_Product_a__compare ;
    GHC.Base.max__ := instance_forall___GHC_Base_Ord_a___GHC_Base_Ord__Data_Monoid_Product_a__max ;
    GHC.Base.min__ := instance_forall___GHC_Base_Ord_a___GHC_Base_Ord__Data_Monoid_Product_a__min |}.

(* Translating `instance forall {a}, forall `{GHC.Num.Num a}, GHC.Num.Num
   (Data.Monoid.Sum a)' failed: OOPS! Cannot find information for class Qualified_
   "GHC.Num" "Num" unsupported *)

(* Translating `instance GHC.Generics.Generic1 Data.Monoid.Sum' failed: OOPS!
   Cannot find information for class Qualified_ "GHC.Generics" "Generic1"
   unsupported *)

(* Translating `instance forall {a}, GHC.Generics.Generic (Data.Monoid.Sum a)'
   failed: OOPS! Cannot find information for class Qualified_ "GHC.Generics"
   "Generic" unsupported *)

(* Translating `instance forall {a}, forall `{GHC.Enum.Bounded a},
   GHC.Enum.Bounded (Data.Monoid.Sum a)' failed: OOPS! Cannot find information for
   class Qualified_ "GHC.Enum" "Bounded" unsupported *)

(* Skipping instance
   instance_forall___GHC_Show_Show_a___GHC_Show_Show__Data_Monoid_Sum_a_ *)

(* Skipping instance
   instance_forall___GHC_Read_Read_a___GHC_Read_Read__Data_Monoid_Sum_a_ *)

Local Definition instance_forall___GHC_Base_Ord_a___GHC_Base_Ord__Data_Monoid_Sum_a__compare {inst_a}
                                                                                             `{GHC.Base.Ord inst_a}
    : Sum inst_a -> Sum inst_a -> comparison :=
  GHC.Prim.coerce GHC.Base.compare.

Local Definition instance_forall___GHC_Base_Ord_a___GHC_Base_Ord__Data_Monoid_Sum_a__max {inst_a}
                                                                                         `{GHC.Base.Ord inst_a} : Sum
                                                                                                                  inst_a -> Sum
                                                                                                                  inst_a -> Sum
                                                                                                                  inst_a :=
  GHC.Prim.coerce GHC.Base.max.

Local Definition instance_forall___GHC_Base_Ord_a___GHC_Base_Ord__Data_Monoid_Sum_a__min {inst_a}
                                                                                         `{GHC.Base.Ord inst_a} : Sum
                                                                                                                  inst_a -> Sum
                                                                                                                  inst_a -> Sum
                                                                                                                  inst_a :=
  GHC.Prim.coerce GHC.Base.min.

Local Definition instance_forall___GHC_Base_Ord_a___GHC_Base_Ord__Data_Monoid_Sum_a__op_zg__ {inst_a}
                                                                                             `{GHC.Base.Ord inst_a}
    : Sum inst_a -> Sum inst_a -> bool :=
  GHC.Prim.coerce GHC.Base.op_zg__.

Local Definition instance_forall___GHC_Base_Ord_a___GHC_Base_Ord__Data_Monoid_Sum_a__op_zgze__ {inst_a}
                                                                                               `{GHC.Base.Ord inst_a}
    : Sum inst_a -> Sum inst_a -> bool :=
  GHC.Prim.coerce GHC.Base.op_zgze__.

Local Definition instance_forall___GHC_Base_Ord_a___GHC_Base_Ord__Data_Monoid_Sum_a__op_zl__ {inst_a}
                                                                                             `{GHC.Base.Ord inst_a}
    : Sum inst_a -> Sum inst_a -> bool :=
  GHC.Prim.coerce GHC.Base.op_zl__.

Local Definition instance_forall___GHC_Base_Ord_a___GHC_Base_Ord__Data_Monoid_Sum_a__op_zlze__ {inst_a}
                                                                                               `{GHC.Base.Ord inst_a}
    : Sum inst_a -> Sum inst_a -> bool :=
  GHC.Prim.coerce GHC.Base.op_zlze__.

Local Definition instance_forall___GHC_Base_Eq__a___GHC_Base_Eq___Data_Monoid_Sum_a__op_zeze__ {inst_a}
                                                                                               `{GHC.Base.Eq_ inst_a}
    : Sum inst_a -> Sum inst_a -> bool :=
  GHC.Prim.coerce GHC.Base.op_zeze__.

Local Definition instance_forall___GHC_Base_Eq__a___GHC_Base_Eq___Data_Monoid_Sum_a__op_zsze__ {inst_a}
                                                                                               `{GHC.Base.Eq_ inst_a}
    : Sum inst_a -> Sum inst_a -> bool :=
  GHC.Prim.coerce GHC.Base.op_zsze__.

Program Instance instance_forall___GHC_Base_Eq__a___GHC_Base_Eq___Data_Monoid_Sum_a_ {a}
                                                                                     `{GHC.Base.Eq_ a} : GHC.Base.Eq_
                                                                                                         (Sum a) :=
  fun _ k =>
    k
    {|GHC.Base.op_zeze____ := instance_forall___GHC_Base_Eq__a___GHC_Base_Eq___Data_Monoid_Sum_a__op_zeze__ ;
    GHC.Base.op_zsze____ := instance_forall___GHC_Base_Eq__a___GHC_Base_Eq___Data_Monoid_Sum_a__op_zsze__ |}.

Program Instance instance_forall___GHC_Base_Ord_a___GHC_Base_Ord__Data_Monoid_Sum_a_ {a}
                                                                                     `{GHC.Base.Ord a} : GHC.Base.Ord
                                                                                                         (Sum a) :=
  fun _ k =>
    k
    {|GHC.Base.op_zl____ := instance_forall___GHC_Base_Ord_a___GHC_Base_Ord__Data_Monoid_Sum_a__op_zl__ ;
    GHC.Base.op_zlze____ := instance_forall___GHC_Base_Ord_a___GHC_Base_Ord__Data_Monoid_Sum_a__op_zlze__ ;
    GHC.Base.op_zg____ := instance_forall___GHC_Base_Ord_a___GHC_Base_Ord__Data_Monoid_Sum_a__op_zg__ ;
    GHC.Base.op_zgze____ := instance_forall___GHC_Base_Ord_a___GHC_Base_Ord__Data_Monoid_Sum_a__op_zgze__ ;
    GHC.Base.compare__ := instance_forall___GHC_Base_Ord_a___GHC_Base_Ord__Data_Monoid_Sum_a__compare ;
    GHC.Base.max__ := instance_forall___GHC_Base_Ord_a___GHC_Base_Ord__Data_Monoid_Sum_a__max ;
    GHC.Base.min__ := instance_forall___GHC_Base_Ord_a___GHC_Base_Ord__Data_Monoid_Sum_a__min |}.

(* Translating `instance GHC.Generics.Generic Data.Monoid.Any' failed: OOPS!
   Cannot find information for class Qualified_ "GHC.Generics" "Generic"
   unsupported *)

(* Translating `instance GHC.Enum.Bounded Data.Monoid.Any' failed: OOPS! Cannot
   find information for class Qualified_ "GHC.Enum" "Bounded" unsupported *)

(* Skipping instance instance_GHC_Show_Show_Data_Monoid_Any *)

(* Skipping instance instance_GHC_Read_Read_Data_Monoid_Any *)

Local Definition instance_GHC_Base_Ord_Data_Monoid_Any_compare
    : Any -> Any -> comparison :=
  GHC.Prim.coerce GHC.Base.compare.

Local Definition instance_GHC_Base_Ord_Data_Monoid_Any_max
    : Any -> Any -> Any :=
  GHC.Prim.coerce GHC.Base.max.

Local Definition instance_GHC_Base_Ord_Data_Monoid_Any_min
    : Any -> Any -> Any :=
  GHC.Prim.coerce GHC.Base.min.

Local Definition instance_GHC_Base_Ord_Data_Monoid_Any_op_zg__
    : Any -> Any -> bool :=
  GHC.Prim.coerce GHC.Base.op_zg__.

Local Definition instance_GHC_Base_Ord_Data_Monoid_Any_op_zgze__
    : Any -> Any -> bool :=
  GHC.Prim.coerce GHC.Base.op_zgze__.

Local Definition instance_GHC_Base_Ord_Data_Monoid_Any_op_zl__
    : Any -> Any -> bool :=
  GHC.Prim.coerce GHC.Base.op_zl__.

Local Definition instance_GHC_Base_Ord_Data_Monoid_Any_op_zlze__
    : Any -> Any -> bool :=
  GHC.Prim.coerce GHC.Base.op_zlze__.

Local Definition instance_GHC_Base_Eq__Data_Monoid_Any_op_zeze__
    : Any -> Any -> bool :=
  GHC.Prim.coerce GHC.Base.op_zeze__.

Local Definition instance_GHC_Base_Eq__Data_Monoid_Any_op_zsze__
    : Any -> Any -> bool :=
  GHC.Prim.coerce GHC.Base.op_zsze__.

Program Instance instance_GHC_Base_Eq__Data_Monoid_Any : GHC.Base.Eq_ Any :=
  fun _ k =>
    k {|GHC.Base.op_zeze____ := instance_GHC_Base_Eq__Data_Monoid_Any_op_zeze__ ;
      GHC.Base.op_zsze____ := instance_GHC_Base_Eq__Data_Monoid_Any_op_zsze__ |}.

Program Instance instance_GHC_Base_Ord_Data_Monoid_Any : GHC.Base.Ord Any :=
  fun _ k =>
    k {|GHC.Base.op_zl____ := instance_GHC_Base_Ord_Data_Monoid_Any_op_zl__ ;
      GHC.Base.op_zlze____ := instance_GHC_Base_Ord_Data_Monoid_Any_op_zlze__ ;
      GHC.Base.op_zg____ := instance_GHC_Base_Ord_Data_Monoid_Any_op_zg__ ;
      GHC.Base.op_zgze____ := instance_GHC_Base_Ord_Data_Monoid_Any_op_zgze__ ;
      GHC.Base.compare__ := instance_GHC_Base_Ord_Data_Monoid_Any_compare ;
      GHC.Base.max__ := instance_GHC_Base_Ord_Data_Monoid_Any_max ;
      GHC.Base.min__ := instance_GHC_Base_Ord_Data_Monoid_Any_min |}.

(* Translating `instance GHC.Generics.Generic Data.Monoid.All' failed: OOPS!
   Cannot find information for class Qualified_ "GHC.Generics" "Generic"
   unsupported *)

(* Translating `instance GHC.Enum.Bounded Data.Monoid.All' failed: OOPS! Cannot
   find information for class Qualified_ "GHC.Enum" "Bounded" unsupported *)

(* Skipping instance instance_GHC_Show_Show_Data_Monoid_All *)

(* Skipping instance instance_GHC_Read_Read_Data_Monoid_All *)

Local Definition instance_GHC_Base_Ord_Data_Monoid_All_compare
    : All -> All -> comparison :=
  GHC.Prim.coerce GHC.Base.compare.

Local Definition instance_GHC_Base_Ord_Data_Monoid_All_max
    : All -> All -> All :=
  GHC.Prim.coerce GHC.Base.max.

Local Definition instance_GHC_Base_Ord_Data_Monoid_All_min
    : All -> All -> All :=
  GHC.Prim.coerce GHC.Base.min.

Local Definition instance_GHC_Base_Ord_Data_Monoid_All_op_zg__
    : All -> All -> bool :=
  GHC.Prim.coerce GHC.Base.op_zg__.

Local Definition instance_GHC_Base_Ord_Data_Monoid_All_op_zgze__
    : All -> All -> bool :=
  GHC.Prim.coerce GHC.Base.op_zgze__.

Local Definition instance_GHC_Base_Ord_Data_Monoid_All_op_zl__
    : All -> All -> bool :=
  GHC.Prim.coerce GHC.Base.op_zl__.

Local Definition instance_GHC_Base_Ord_Data_Monoid_All_op_zlze__
    : All -> All -> bool :=
  GHC.Prim.coerce GHC.Base.op_zlze__.

Local Definition instance_GHC_Base_Eq__Data_Monoid_All_op_zeze__
    : All -> All -> bool :=
  GHC.Prim.coerce GHC.Base.op_zeze__.

Local Definition instance_GHC_Base_Eq__Data_Monoid_All_op_zsze__
    : All -> All -> bool :=
  GHC.Prim.coerce GHC.Base.op_zsze__.

Program Instance instance_GHC_Base_Eq__Data_Monoid_All : GHC.Base.Eq_ All :=
  fun _ k =>
    k {|GHC.Base.op_zeze____ := instance_GHC_Base_Eq__Data_Monoid_All_op_zeze__ ;
      GHC.Base.op_zsze____ := instance_GHC_Base_Eq__Data_Monoid_All_op_zsze__ |}.

Program Instance instance_GHC_Base_Ord_Data_Monoid_All : GHC.Base.Ord All :=
  fun _ k =>
    k {|GHC.Base.op_zl____ := instance_GHC_Base_Ord_Data_Monoid_All_op_zl__ ;
      GHC.Base.op_zlze____ := instance_GHC_Base_Ord_Data_Monoid_All_op_zlze__ ;
      GHC.Base.op_zg____ := instance_GHC_Base_Ord_Data_Monoid_All_op_zg__ ;
      GHC.Base.op_zgze____ := instance_GHC_Base_Ord_Data_Monoid_All_op_zgze__ ;
      GHC.Base.compare__ := instance_GHC_Base_Ord_Data_Monoid_All_compare ;
      GHC.Base.max__ := instance_GHC_Base_Ord_Data_Monoid_All_max ;
      GHC.Base.min__ := instance_GHC_Base_Ord_Data_Monoid_All_min |}.

(* Translating `instance forall {a}, GHC.Generics.Generic (Data.Monoid.Endo a)'
   failed: OOPS! Cannot find information for class Qualified_ "GHC.Generics"
   "Generic" unsupported *)

(* Translating `instance GHC.Generics.Generic1 Data.Monoid.Dual' failed: OOPS!
   Cannot find information for class Qualified_ "GHC.Generics" "Generic1"
   unsupported *)

(* Translating `instance forall {a}, GHC.Generics.Generic (Data.Monoid.Dual a)'
   failed: OOPS! Cannot find information for class Qualified_ "GHC.Generics"
   "Generic" unsupported *)

(* Translating `instance forall {a}, forall `{GHC.Enum.Bounded a},
   GHC.Enum.Bounded (Data.Monoid.Dual a)' failed: OOPS! Cannot find information for
   class Qualified_ "GHC.Enum" "Bounded" unsupported *)

(* Skipping instance
   instance_forall___GHC_Show_Show_a___GHC_Show_Show__Data_Monoid_Dual_a_ *)

(* Skipping instance
   instance_forall___GHC_Read_Read_a___GHC_Read_Read__Data_Monoid_Dual_a_ *)

Local Definition instance_forall___GHC_Base_Ord_a___GHC_Base_Ord__Data_Monoid_Dual_a__compare {inst_a}
                                                                                              `{GHC.Base.Ord inst_a}
    : Dual inst_a -> Dual inst_a -> comparison :=
  GHC.Prim.coerce GHC.Base.compare.

Local Definition instance_forall___GHC_Base_Ord_a___GHC_Base_Ord__Data_Monoid_Dual_a__max {inst_a}
                                                                                          `{GHC.Base.Ord inst_a} : Dual
                                                                                                                   inst_a -> Dual
                                                                                                                   inst_a -> Dual
                                                                                                                   inst_a :=
  GHC.Prim.coerce GHC.Base.max.

Local Definition instance_forall___GHC_Base_Ord_a___GHC_Base_Ord__Data_Monoid_Dual_a__min {inst_a}
                                                                                          `{GHC.Base.Ord inst_a} : Dual
                                                                                                                   inst_a -> Dual
                                                                                                                   inst_a -> Dual
                                                                                                                   inst_a :=
  GHC.Prim.coerce GHC.Base.min.

Local Definition instance_forall___GHC_Base_Ord_a___GHC_Base_Ord__Data_Monoid_Dual_a__op_zg__ {inst_a}
                                                                                              `{GHC.Base.Ord inst_a}
    : Dual inst_a -> Dual inst_a -> bool :=
  GHC.Prim.coerce GHC.Base.op_zg__.

Local Definition instance_forall___GHC_Base_Ord_a___GHC_Base_Ord__Data_Monoid_Dual_a__op_zgze__ {inst_a}
                                                                                                `{GHC.Base.Ord inst_a}
    : Dual inst_a -> Dual inst_a -> bool :=
  GHC.Prim.coerce GHC.Base.op_zgze__.

Local Definition instance_forall___GHC_Base_Ord_a___GHC_Base_Ord__Data_Monoid_Dual_a__op_zl__ {inst_a}
                                                                                              `{GHC.Base.Ord inst_a}
    : Dual inst_a -> Dual inst_a -> bool :=
  GHC.Prim.coerce GHC.Base.op_zl__.

Local Definition instance_forall___GHC_Base_Ord_a___GHC_Base_Ord__Data_Monoid_Dual_a__op_zlze__ {inst_a}
                                                                                                `{GHC.Base.Ord inst_a}
    : Dual inst_a -> Dual inst_a -> bool :=
  GHC.Prim.coerce GHC.Base.op_zlze__.

Local Definition instance_forall___GHC_Base_Eq__a___GHC_Base_Eq___Data_Monoid_Dual_a__op_zeze__ {inst_a}
                                                                                                `{GHC.Base.Eq_ inst_a}
    : Dual inst_a -> Dual inst_a -> bool :=
  GHC.Prim.coerce GHC.Base.op_zeze__.

Local Definition instance_forall___GHC_Base_Eq__a___GHC_Base_Eq___Data_Monoid_Dual_a__op_zsze__ {inst_a}
                                                                                                `{GHC.Base.Eq_ inst_a}
    : Dual inst_a -> Dual inst_a -> bool :=
  GHC.Prim.coerce GHC.Base.op_zsze__.

Program Instance instance_forall___GHC_Base_Eq__a___GHC_Base_Eq___Data_Monoid_Dual_a_ {a}
                                                                                      `{GHC.Base.Eq_ a} : GHC.Base.Eq_
                                                                                                          (Dual a) :=
  fun _ k =>
    k
    {|GHC.Base.op_zeze____ := instance_forall___GHC_Base_Eq__a___GHC_Base_Eq___Data_Monoid_Dual_a__op_zeze__ ;
    GHC.Base.op_zsze____ := instance_forall___GHC_Base_Eq__a___GHC_Base_Eq___Data_Monoid_Dual_a__op_zsze__ |}.

Program Instance instance_forall___GHC_Base_Ord_a___GHC_Base_Ord__Data_Monoid_Dual_a_ {a}
                                                                                      `{GHC.Base.Ord a} : GHC.Base.Ord
                                                                                                          (Dual a) :=
  fun _ k =>
    k
    {|GHC.Base.op_zl____ := instance_forall___GHC_Base_Ord_a___GHC_Base_Ord__Data_Monoid_Dual_a__op_zl__ ;
    GHC.Base.op_zlze____ := instance_forall___GHC_Base_Ord_a___GHC_Base_Ord__Data_Monoid_Dual_a__op_zlze__ ;
    GHC.Base.op_zg____ := instance_forall___GHC_Base_Ord_a___GHC_Base_Ord__Data_Monoid_Dual_a__op_zg__ ;
    GHC.Base.op_zgze____ := instance_forall___GHC_Base_Ord_a___GHC_Base_Ord__Data_Monoid_Dual_a__op_zgze__ ;
    GHC.Base.compare__ := instance_forall___GHC_Base_Ord_a___GHC_Base_Ord__Data_Monoid_Dual_a__compare ;
    GHC.Base.max__ := instance_forall___GHC_Base_Ord_a___GHC_Base_Ord__Data_Monoid_Dual_a__max ;
    GHC.Base.min__ := instance_forall___GHC_Base_Ord_a___GHC_Base_Ord__Data_Monoid_Dual_a__min |}.

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
