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
