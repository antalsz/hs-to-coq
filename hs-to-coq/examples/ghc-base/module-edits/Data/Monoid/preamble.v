Require Import GHC.Base.

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

Instance instance_GHC_Base_Monoid_All : !GHC.Base.Monoid All := {
   mappend := mappend_All;
   mempty  := mempty_All;
   mconcat := foldr mappend_All mempty_All;
}.


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

Instance instance_GHC_Base_Monoid_Any : !GHC.Base.Monoid Any := {
   mappend := mappend_Any;
   mempty  := mempty_Any;
   mconcat := foldr mappend_Any mempty_Any;
}.


Inductive First a : Type := Mk_First : option a -> First a.

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
Instance instance_GHC_Base_Monoid__First_a_ : !GHC.Base.Monoid (First a) :=
 { mappend := mappend_First;
   mempty  := mempty_First;
   mconcat := foldr mappend_First mempty_First }.

Inductive Last a : Type := Mk_Last : option a -> Last a.

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
Instance instance_GHC_Base_Monoid__Last_a_ : !GHC.Base.Monoid (Last a) :=
 { mappend := mappend_Last;
   mempty  := mempty_Last;
   mconcat := foldr mappend_Last mempty_Last }.



Inductive Product a : Type := Mk_Product : a -> Product a.

Definition getProduct {a} (arg_1__ : Product a) :=
  match arg_1__ with
    | (Mk_Product getProduct) => getProduct
  end.

Definition mempty_Product {a} `{Num a} : Product a := Mk_Product #1.
Definition mappend_Product {a} `{Num a} (x: Product a) (y :Product a)  : Product a :=
  match x , y with
    | Mk_Product i , Mk_Product j => Mk_Product (i * j)
  end.
Instance instance_GHC_Base_Monoid__Product_a_ {a} `{Num a}: !GHC.Base.Monoid (Product a) :=
 { mappend := mappend_Product;
   mempty  := mempty_Product;
   mconcat := foldr mappend_Product mempty_Product }.

Inductive Sum a : Type := Mk_Sum : a -> Sum a.

Definition getSum {a} (arg_1__ : Sum a) :=
  match arg_1__ with
    | (Mk_Sum getSum) => getSum
  end.

Definition mempty_Sum {a} `{Num a} : Sum a := Mk_Sum #0.
Definition mappend_Sum {a} `{Num a} (x: Sum a) (y :Sum a)  : Sum a :=
  match x , y with
    | Mk_Sum i , Mk_Sum j => Mk_Sum (i + j)
  end.
Instance instance_GHC_Base_Monoid__Sum_a_ {a} `{Num a}: !GHC.Base.Monoid (Sum a) :=
 { mappend := mappend_Sum;
   mempty  := mempty_Sum;
   mconcat := foldr mappend_Sum mempty_Sum }.