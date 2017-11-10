(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Coq.Program.Wf.

(* Preamble *)

Require Import GHC.Base.

(* WE do these by hand because they are defined in GHC using Data.Coerce. *)

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

(* Converted imports: *)

Require Coq.Program.Basics.
Require GHC.Base.
Require GHC.Prim.

(* Converted type declarations: *)

Inductive Endo a : Type := Mk_Endo : (a -> a) -> Endo a.

Inductive Dual a : Type := Mk_Dual : a -> Dual a.

Inductive Alt (f : Type -> Type) a : Type := Mk_Alt : f a -> Alt f a.

Arguments Mk_Endo {_} _.

Arguments Mk_Dual {_} _.

Definition appEndo {a} (arg_0__ : Endo a) :=
  match arg_0__ with
    | Mk_Endo appEndo => appEndo
  end.

Definition getDual {a} (arg_1__ : Dual a) :=
  match arg_1__ with
    | Mk_Dual getDual => getDual
  end.
(* Converted value declarations: *)

Instance Unpeel_Dual a : Unpeel (Dual a) a := Build_Unpeel _ _ getDual Mk_Dual.

Local Definition instance_forall___GHC_Base_Monoid_a___GHC_Base_Monoid__Dual_a__mappend {inst_a}
                                                                                        `{GHC.Base.Monoid inst_a}
    : (Dual inst_a) -> (Dual inst_a) -> (Dual inst_a) :=
  fun arg_92__ arg_93__ =>
    match arg_92__ , arg_93__ with
      | Mk_Dual x , Mk_Dual y => Mk_Dual (GHC.Base.mappend y x)
    end.

Local Definition instance_forall___GHC_Base_Monoid_a___GHC_Base_Monoid__Dual_a__mempty {inst_a}
                                                                                       `{GHC.Base.Monoid inst_a} : (Dual
                                                                                                                   inst_a) :=
  Mk_Dual GHC.Base.mempty.

Local Definition instance_forall___GHC_Base_Monoid_a___GHC_Base_Monoid__Dual_a__mconcat {inst_a}
                                                                                        `{GHC.Base.Monoid inst_a} : list
                                                                                                                    (Dual
                                                                                                                    inst_a) -> (Dual
                                                                                                                    inst_a) :=
  GHC.Base.foldr
  instance_forall___GHC_Base_Monoid_a___GHC_Base_Monoid__Dual_a__mappend
  instance_forall___GHC_Base_Monoid_a___GHC_Base_Monoid__Dual_a__mempty.

Instance instance_forall___GHC_Base_Monoid_a___GHC_Base_Monoid__Dual_a_ {a}
                                                                        `{GHC.Base.Monoid a} : GHC.Base.Monoid (Dual
                                                                                                               a) :=
  fun _ k =>
    k (GHC.Base.Monoid__Dict_Build (Dual a)
                                   instance_forall___GHC_Base_Monoid_a___GHC_Base_Monoid__Dual_a__mappend
                                   instance_forall___GHC_Base_Monoid_a___GHC_Base_Monoid__Dual_a__mconcat
                                   instance_forall___GHC_Base_Monoid_a___GHC_Base_Monoid__Dual_a__mempty).

Local Definition instance_GHC_Base_Functor_Dual_fmap : forall {a} {b},
                                                         (a -> b) -> Dual a -> Dual b :=
  fun {a} {b} => GHC.Prim.coerce.

Local Definition instance_GHC_Base_Functor_Dual_op_zlzd__ : forall {a} {b},
                                                              a -> Dual b -> Dual a :=
  fun {a} {b} => fun x => instance_GHC_Base_Functor_Dual_fmap (GHC.Base.const x).

Instance instance_GHC_Base_Functor_Dual : GHC.Base.Functor Dual := fun _ k =>
    k (GHC.Base.Functor__Dict_Build Dual (fun {a} {b} =>
                                      instance_GHC_Base_Functor_Dual_op_zlzd__) (fun {a} {b} =>
                                      instance_GHC_Base_Functor_Dual_fmap)).

Local Definition instance_GHC_Base_Applicative_Dual_op_zlztzg__ : forall {a}
                                                                         {b},
                                                                    Dual (a -> b) -> Dual a -> Dual b :=
  fun {a} {b} => GHC.Prim.coerce.

Local Definition instance_GHC_Base_Applicative_Dual_op_ztzg__ : forall {a} {b},
                                                                  Dual a -> Dual b -> Dual b :=
  fun {a} {b} =>
    fun x y =>
      instance_GHC_Base_Applicative_Dual_op_zlztzg__ (GHC.Base.fmap (GHC.Base.const
                                                                    GHC.Base.id) x) y.

Local Definition instance_GHC_Base_Applicative_Dual_pure : forall {a},
                                                             a -> Dual a :=
  fun {a} => Mk_Dual.

Instance instance_GHC_Base_Applicative_Dual : GHC.Base.Applicative Dual := fun _
                                                                               k =>
    k (GHC.Base.Applicative__Dict_Build Dual (fun {a} {b} =>
                                          instance_GHC_Base_Applicative_Dual_op_ztzg__) (fun {a} {b} =>
                                          instance_GHC_Base_Applicative_Dual_op_zlztzg__) (fun {a} =>
                                          instance_GHC_Base_Applicative_Dual_pure)).

(* Skipping instance instance_GHC_Base_Monad_Dual *)

Local Definition instance_GHC_Base_Monoid__Endo_a__mappend {inst_a} : (Endo
                                                                      inst_a) -> (Endo inst_a) -> (Endo inst_a) :=
  fun arg_83__ arg_84__ =>
    match arg_83__ , arg_84__ with
      | Mk_Endo f , Mk_Endo g => Mk_Endo (Coq.Program.Basics.compose f g)
    end.

Local Definition instance_GHC_Base_Monoid__Endo_a__mempty {inst_a} : (Endo
                                                                     inst_a) :=
  Mk_Endo GHC.Base.id.

Local Definition instance_GHC_Base_Monoid__Endo_a__mconcat {inst_a} : list (Endo
                                                                           inst_a) -> (Endo inst_a) :=
  GHC.Base.foldr instance_GHC_Base_Monoid__Endo_a__mappend
                 instance_GHC_Base_Monoid__Endo_a__mempty.

Instance instance_GHC_Base_Monoid__Endo_a_ {a} : GHC.Base.Monoid (Endo a) :=
  fun _ k =>
    k (GHC.Base.Monoid__Dict_Build (Endo a)
                                   instance_GHC_Base_Monoid__Endo_a__mappend
                                   instance_GHC_Base_Monoid__Endo_a__mconcat
                                   instance_GHC_Base_Monoid__Endo_a__mempty).

(* Skipping instance instance_GHC_Base_Monoid_All *)

(* Skipping instance instance_GHC_Base_Monoid_Any *)

(* Skipping instance
   instance_forall___GHC_Num_Num_a___GHC_Base_Monoid__Sum_a_ *)

(* Skipping instance instance_GHC_Base_Functor_Sum *)

(* Skipping instance instance_GHC_Base_Applicative_Sum *)

(* Skipping instance instance_GHC_Base_Monad_Sum *)

(* Skipping instance
   instance_forall___GHC_Num_Num_a___GHC_Base_Monoid__Product_a_ *)

(* Skipping instance instance_GHC_Base_Functor_Product *)

(* Skipping instance instance_GHC_Base_Applicative_Product *)

(* Skipping instance instance_GHC_Base_Monad_Product *)

(* Skipping instance instance_GHC_Base_Monoid__First_a_ *)

(* Skipping instance instance_GHC_Base_Monoid__Last_a_ *)

(* Skipping instance
   instance_forall___GHC_Base_Alternative_f___GHC_Base_Monoid__Alt_f_a_ *)

(* Translating `instance forall {f}, forall `{GHC.Base.Functor f},
   GHC.Base.Functor (Alt f)' failed: type applications unsupported *)

(* Translating `instance forall {f}, forall `{GHC.Base.Alternative f},
   GHC.Base.Alternative (Alt f)' failed: type applications unsupported *)

(* Translating `instance forall {f}, forall `{GHC.Base.Applicative f},
   GHC.Base.Applicative (Alt f)' failed: type applications unsupported *)

(* Translating `instance forall {f}, forall `{GHC.Base.MonadPlus f},
   GHC.Base.MonadPlus (Alt f)' failed: type applications unsupported *)

(* Translating `instance forall {f}, forall `{GHC.Base.Monad f}, GHC.Base.Monad
   (Alt f)' failed: type applications unsupported *)

(* Translating `instance forall {k} {f} {a}, forall `{GHC.Enum.Enum (f a)},
   GHC.Enum.Enum (Alt f a)' failed: type applications unsupported *)

(* Translating `instance forall {k} {f} {a}, forall `{GHC.Num.Num (f a)},
   GHC.Num.Num (Alt f a)' failed: type applications unsupported *)

(* Translating `instance forall {k} {f} {a}, forall `{GHC.Base.Ord (f a)},
   GHC.Base.Ord (Alt f a)' failed: type applications unsupported *)

(* Translating `instance forall {k} {f} {a}, forall `{GHC.Base.Eq_ (f a)},
   GHC.Base.Eq_ (Alt f a)' failed: type applications unsupported *)

(* Skipping instance
   instance_forall___GHC_Show_Show__f_a____GHC_Show_Show__Alt_f_a_ *)

(* Skipping instance
   instance_forall___GHC_Read_Read__f_a____GHC_Read_Read__Alt_f_a_ *)

(* Translating `instance forall {f}, GHC.Generics.Generic1 (Alt f)' failed:
   OOPS! Cannot find information for class "GHC.Generics.Generic1" unsupported *)

(* Translating `instance forall {k} {f} {a}, GHC.Generics.Generic (Alt f a)'
   failed: OOPS! Cannot find information for class "GHC.Generics.Generic"
   unsupported *)

(* Translating `instance GHC.Base.Monad Last' failed: type applications
   unsupported *)

(* Translating `instance GHC.Base.Applicative Last' failed: type applications
   unsupported *)

(* Translating `instance GHC.Base.Functor Last' failed: type applications
   unsupported *)

(* Translating `instance GHC.Generics.Generic1 Last' failed: OOPS! Cannot find
   information for class "GHC.Generics.Generic1" unsupported *)

(* Translating `instance forall {a}, GHC.Generics.Generic (Last a)' failed:
   OOPS! Cannot find information for class "GHC.Generics.Generic" unsupported *)

(* Skipping instance
   instance_forall___GHC_Show_Show_a___GHC_Show_Show__Last_a_ *)

(* Skipping instance
   instance_forall___GHC_Read_Read_a___GHC_Read_Read__Last_a_ *)

(* Translating `instance forall {a}, forall `{GHC.Base.Ord a}, GHC.Base.Ord
   (Last a)' failed: type applications unsupported *)

(* Translating `instance forall {a}, forall `{GHC.Base.Eq_ a}, GHC.Base.Eq_
   (Last a)' failed: type applications unsupported *)

(* Translating `instance GHC.Base.Monad First' failed: type applications
   unsupported *)

(* Translating `instance GHC.Base.Applicative First' failed: type applications
   unsupported *)

(* Translating `instance GHC.Base.Functor First' failed: type applications
   unsupported *)

(* Translating `instance GHC.Generics.Generic1 First' failed: OOPS! Cannot find
   information for class "GHC.Generics.Generic1" unsupported *)

(* Translating `instance forall {a}, GHC.Generics.Generic (First a)' failed:
   OOPS! Cannot find information for class "GHC.Generics.Generic" unsupported *)

(* Skipping instance
   instance_forall___GHC_Show_Show_a___GHC_Show_Show__First_a_ *)

(* Skipping instance
   instance_forall___GHC_Read_Read_a___GHC_Read_Read__First_a_ *)

(* Translating `instance forall {a}, forall `{GHC.Base.Ord a}, GHC.Base.Ord
   (First a)' failed: type applications unsupported *)

(* Translating `instance forall {a}, forall `{GHC.Base.Eq_ a}, GHC.Base.Eq_
   (First a)' failed: type applications unsupported *)

(* Translating `instance forall {a}, forall `{GHC.Num.Num a}, GHC.Num.Num
   (Product a)' failed: type applications unsupported *)

(* Translating `instance GHC.Generics.Generic1 Product' failed: OOPS! Cannot
   find information for class "GHC.Generics.Generic1" unsupported *)

(* Translating `instance forall {a}, GHC.Generics.Generic (Product a)' failed:
   OOPS! Cannot find information for class "GHC.Generics.Generic" unsupported *)

(* Translating `instance forall {a}, forall `{GHC.Enum.Bounded a},
   GHC.Enum.Bounded (Product a)' failed: type applications unsupported *)

(* Skipping instance
   instance_forall___GHC_Show_Show_a___GHC_Show_Show__Product_a_ *)

(* Skipping instance
   instance_forall___GHC_Read_Read_a___GHC_Read_Read__Product_a_ *)

(* Translating `instance forall {a}, forall `{GHC.Base.Ord a}, GHC.Base.Ord
   (Product a)' failed: type applications unsupported *)

(* Translating `instance forall {a}, forall `{GHC.Base.Eq_ a}, GHC.Base.Eq_
   (Product a)' failed: type applications unsupported *)

(* Translating `instance forall {a}, forall `{GHC.Num.Num a}, GHC.Num.Num (Sum
   a)' failed: type applications unsupported *)

(* Translating `instance GHC.Generics.Generic1 Sum' failed: OOPS! Cannot find
   information for class "GHC.Generics.Generic1" unsupported *)

(* Translating `instance forall {a}, GHC.Generics.Generic (Sum a)' failed: OOPS!
   Cannot find information for class "GHC.Generics.Generic" unsupported *)

(* Translating `instance forall {a}, forall `{GHC.Enum.Bounded a},
   GHC.Enum.Bounded (Sum a)' failed: type applications unsupported *)

(* Skipping instance
   instance_forall___GHC_Show_Show_a___GHC_Show_Show__Sum_a_ *)

(* Skipping instance
   instance_forall___GHC_Read_Read_a___GHC_Read_Read__Sum_a_ *)

(* Translating `instance forall {a}, forall `{GHC.Base.Ord a}, GHC.Base.Ord (Sum
   a)' failed: type applications unsupported *)

(* Translating `instance forall {a}, forall `{GHC.Base.Eq_ a}, GHC.Base.Eq_ (Sum
   a)' failed: type applications unsupported *)

(* Translating `instance GHC.Generics.Generic Any' failed: OOPS! Cannot find
   information for class "GHC.Generics.Generic" unsupported *)

(* Translating `instance GHC.Enum.Bounded Any' failed: type applications
   unsupported *)

(* Skipping instance instance_GHC_Show_Show_Any *)

(* Skipping instance instance_GHC_Read_Read_Any *)

(* Translating `instance GHC.Base.Ord Any' failed: type applications
   unsupported *)

(* Translating `instance GHC.Base.Eq_ Any' failed: type applications
   unsupported *)

(* Translating `instance GHC.Generics.Generic All' failed: OOPS! Cannot find
   information for class "GHC.Generics.Generic" unsupported *)

(* Translating `instance GHC.Enum.Bounded All' failed: type applications
   unsupported *)

(* Skipping instance instance_GHC_Show_Show_All *)

(* Skipping instance instance_GHC_Read_Read_All *)

(* Translating `instance GHC.Base.Ord All' failed: type applications
   unsupported *)

(* Translating `instance GHC.Base.Eq_ All' failed: type applications
   unsupported *)

(* Translating `instance forall {a}, GHC.Generics.Generic (Endo a)' failed:
   OOPS! Cannot find information for class "GHC.Generics.Generic" unsupported *)

(* Translating `instance GHC.Generics.Generic1 Dual' failed: OOPS! Cannot find
   information for class "GHC.Generics.Generic1" unsupported *)

(* Translating `instance forall {a}, GHC.Generics.Generic (Dual a)' failed:
   OOPS! Cannot find information for class "GHC.Generics.Generic" unsupported *)

(* Translating `instance forall {a}, forall `{GHC.Enum.Bounded a},
   GHC.Enum.Bounded (Dual a)' failed: type applications unsupported *)

(* Skipping instance
   instance_forall___GHC_Show_Show_a___GHC_Show_Show__Dual_a_ *)

(* Skipping instance
   instance_forall___GHC_Read_Read_a___GHC_Read_Read__Dual_a_ *)

(* Translating `instance forall {a}, forall `{GHC.Base.Ord a}, GHC.Base.Ord
   (Dual a)' failed: type applications unsupported *)

(* Translating `instance forall {a}, forall `{GHC.Base.Eq_ a}, GHC.Base.Eq_
   (Dual a)' failed: type applications unsupported *)

(* Unbound variables:
     Build_Unpeel Coq.Program.Basics.compose GHC.Base.Applicative
     GHC.Base.Applicative__Dict_Build GHC.Base.Functor GHC.Base.Functor__Dict_Build
     GHC.Base.Monoid GHC.Base.Monoid__Dict_Build GHC.Base.const GHC.Base.fmap
     GHC.Base.foldr GHC.Base.id GHC.Base.mappend GHC.Base.mempty GHC.Prim.coerce Type
     Unpeel list
*)
