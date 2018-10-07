Instance Unpeel_Alt (f:Type->Type) a : GHC.Prim.Unpeel (Alt f a) (f a) :=
    GHC.Prim.Build_Unpeel _ _ getAlt Mk_Alt.

(*
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
*)
