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