(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Converted imports: *)

Require Coq.Program.Basics.
Require GHC.Base.
Require GHC.Prim.

(* Converted declarations: *)

(* Skipping instance instance_GHC_Base_Monad_Dual *)

<<<<<<< HEAD
(* Skipping instance instance_GHC_Base_Monoid_All *)

(* Skipping instance instance_GHC_Base_Monoid_Any *)

(* Skipping instance
   instance_forall___GHC_Num_Num_a___GHC_Base_Monoid__Sum_a_ *)

(* Skipping instance instance_GHC_Base_Functor_Sum *)

(* Skipping instance instance_GHC_Base_Applicative_Sum *)
=======
(* Skipping instance
   instance_forall___GHC_Num_Num_a___GHC_Base_Monoid__Sum_a_ *)
>>>>>>> Data.Monoid: Now preamble free

(* Skipping instance instance_GHC_Base_Monad_Sum *)

(* Skipping instance
   instance_forall___GHC_Num_Num_a___GHC_Base_Monoid__Product_a_ *)
<<<<<<< HEAD

(* Skipping instance instance_GHC_Base_Functor_Product *)

(* Skipping instance instance_GHC_Base_Applicative_Product *)

(* Skipping instance instance_GHC_Base_Monad_Product *)

(* Skipping instance instance_GHC_Base_Monoid__First_a_ *)

(* Skipping instance instance_GHC_Base_Monoid__Last_a_ *)

=======

(* Skipping instance instance_GHC_Base_Monad_Product *)

>>>>>>> Data.Monoid: Now preamble free
(* Skipping instance
   instance_forall___GHC_Base_Alternative_f___GHC_Base_Monoid__Alt_f_a_ *)

(* Skipping instance
   instance_forall___GHC_Base_Functor_f___GHC_Base_Functor__Alt_f_ *)

(* Translating `instance forall {f}, forall `{GHC.Base.Alternative f},
   GHC.Base.Alternative (Alt f)' failed: OOPS! Cannot find information for class
   "GHC.Base.Alternative" unsupported *)

(* Skipping instance
   instance_forall___GHC_Base_Applicative_f___GHC_Base_Applicative__Alt_f_ *)

(* Translating `instance forall {f}, forall `{GHC.Base.MonadPlus f},
   GHC.Base.MonadPlus (Alt f)' failed: OOPS! Cannot find information for class
   "GHC.Base.MonadPlus" unsupported *)

(* Skipping instance
   instance_forall___GHC_Base_Monad_f___GHC_Base_Monad__Alt_f_ *)

(* Translating `instance forall {k} {f} {a}, forall `{GHC.Enum.Enum (f a)},
   GHC.Enum.Enum (Alt f a)' failed: OOPS! Cannot find information for class
   "GHC.Enum.Enum" unsupported *)

(* Translating `instance forall {k} {f} {a}, forall `{GHC.Num.Num (f a)},
   GHC.Num.Num (Alt f a)' failed: OOPS! Cannot find information for class
   "GHC.Num.Num" unsupported *)

(* Skipping instance
   instance_forall___GHC_Base_Ord__f_a____GHC_Base_Ord__Alt_f_a_ *)

(* Skipping instance
   instance_forall___GHC_Base_Eq___f_a____GHC_Base_Eq___Alt_f_a_ *)

(* Skipping instance
   instance_forall___GHC_Show_Show__f_a____GHC_Show_Show__Alt_f_a_ *)

(* Skipping instance
   instance_forall___GHC_Read_Read__f_a____GHC_Read_Read__Alt_f_a_ *)

(* Translating `instance forall {f}, GHC.Generics.Generic1 (Alt f)' failed:
   OOPS! Cannot find information for class "GHC.Generics.Generic1" unsupported *)

(* Translating `instance forall {k} {f} {a}, GHC.Generics.Generic (Alt f a)'
   failed: OOPS! Cannot find information for class "GHC.Generics.Generic"
   unsupported *)

(* Skipping instance instance_GHC_Base_Monad_Last *)

(* Skipping instance instance_GHC_Base_Applicative_Last *)

(* Skipping instance instance_GHC_Base_Functor_Last *)

(* Translating `instance GHC.Generics.Generic1 Last' failed: OOPS! Cannot find
   information for class "GHC.Generics.Generic1" unsupported *)

(* Translating `instance forall {a}, GHC.Generics.Generic (Last a)' failed:
   OOPS! Cannot find information for class "GHC.Generics.Generic" unsupported *)

(* Skipping instance
   instance_forall___GHC_Show_Show_a___GHC_Show_Show__Last_a_ *)

(* Skipping instance
   instance_forall___GHC_Read_Read_a___GHC_Read_Read__Last_a_ *)

(* Skipping instance instance_forall___GHC_Base_Ord_a___GHC_Base_Ord__Last_a_ *)

(* Skipping instance instance_forall___GHC_Base_Eq__a___GHC_Base_Eq___Last_a_ *)

(* Skipping instance instance_GHC_Base_Monad_First *)

(* Skipping instance instance_GHC_Base_Applicative_First *)

(* Skipping instance instance_GHC_Base_Functor_First *)

(* Translating `instance GHC.Generics.Generic1 First' failed: OOPS! Cannot find
   information for class "GHC.Generics.Generic1" unsupported *)

(* Translating `instance forall {a}, GHC.Generics.Generic (First a)' failed:
   OOPS! Cannot find information for class "GHC.Generics.Generic" unsupported *)

(* Skipping instance
   instance_forall___GHC_Show_Show_a___GHC_Show_Show__First_a_ *)

(* Skipping instance
   instance_forall___GHC_Read_Read_a___GHC_Read_Read__First_a_ *)

(* Skipping instance
   instance_forall___GHC_Base_Ord_a___GHC_Base_Ord__First_a_ *)

(* Skipping instance
   instance_forall___GHC_Base_Eq__a___GHC_Base_Eq___First_a_ *)

(* Translating `instance forall {a}, forall `{GHC.Num.Num a}, GHC.Num.Num
   (Product a)' failed: OOPS! Cannot find information for class "GHC.Num.Num"
   unsupported *)

(* Translating `instance GHC.Generics.Generic1 Product' failed: OOPS! Cannot
   find information for class "GHC.Generics.Generic1" unsupported *)

(* Translating `instance forall {a}, GHC.Generics.Generic (Product a)' failed:
   OOPS! Cannot find information for class "GHC.Generics.Generic" unsupported *)

(* Translating `instance forall {a}, forall `{GHC.Enum.Bounded a},
   GHC.Enum.Bounded (Product a)' failed: OOPS! Cannot find information for class
   "GHC.Enum.Bounded" unsupported *)

(* Skipping instance
   instance_forall___GHC_Show_Show_a___GHC_Show_Show__Product_a_ *)

(* Skipping instance
   instance_forall___GHC_Read_Read_a___GHC_Read_Read__Product_a_ *)

(* Skipping instance
   instance_forall___GHC_Base_Ord_a___GHC_Base_Ord__Product_a_ *)

(* Skipping instance
   instance_forall___GHC_Base_Eq__a___GHC_Base_Eq___Product_a_ *)

(* Translating `instance forall {a}, forall `{GHC.Num.Num a}, GHC.Num.Num (Sum
   a)' failed: OOPS! Cannot find information for class "GHC.Num.Num" unsupported *)

(* Translating `instance GHC.Generics.Generic1 Sum' failed: OOPS! Cannot find
   information for class "GHC.Generics.Generic1" unsupported *)

(* Translating `instance forall {a}, GHC.Generics.Generic (Sum a)' failed: OOPS!
   Cannot find information for class "GHC.Generics.Generic" unsupported *)

(* Translating `instance forall {a}, forall `{GHC.Enum.Bounded a},
   GHC.Enum.Bounded (Sum a)' failed: OOPS! Cannot find information for class
   "GHC.Enum.Bounded" unsupported *)

(* Skipping instance
   instance_forall___GHC_Show_Show_a___GHC_Show_Show__Sum_a_ *)

(* Skipping instance
   instance_forall___GHC_Read_Read_a___GHC_Read_Read__Sum_a_ *)

(* Skipping instance instance_forall___GHC_Base_Ord_a___GHC_Base_Ord__Sum_a_ *)

(* Skipping instance instance_forall___GHC_Base_Eq__a___GHC_Base_Eq___Sum_a_ *)

(* Translating `instance GHC.Generics.Generic Any' failed: OOPS! Cannot find
   information for class "GHC.Generics.Generic" unsupported *)

(* Translating `instance GHC.Enum.Bounded Any' failed: OOPS! Cannot find
   information for class "GHC.Enum.Bounded" unsupported *)

(* Skipping instance instance_GHC_Show_Show_Any *)

(* Skipping instance instance_GHC_Read_Read_Any *)

(* Translating `instance GHC.Generics.Generic All' failed: OOPS! Cannot find
   information for class "GHC.Generics.Generic" unsupported *)

(* Translating `instance GHC.Enum.Bounded All' failed: OOPS! Cannot find
   information for class "GHC.Enum.Bounded" unsupported *)

(* Skipping instance instance_GHC_Show_Show_All *)

(* Skipping instance instance_GHC_Read_Read_All *)

(* Translating `instance forall {a}, GHC.Generics.Generic (Endo a)' failed:
   OOPS! Cannot find information for class "GHC.Generics.Generic" unsupported *)

(* Translating `instance GHC.Generics.Generic1 Dual' failed: OOPS! Cannot find
   information for class "GHC.Generics.Generic1" unsupported *)

(* Translating `instance forall {a}, GHC.Generics.Generic (Dual a)' failed:
   OOPS! Cannot find information for class "GHC.Generics.Generic" unsupported *)

(* Translating `instance forall {a}, forall `{GHC.Enum.Bounded a},
   GHC.Enum.Bounded (Dual a)' failed: OOPS! Cannot find information for class
   "GHC.Enum.Bounded" unsupported *)

(* Skipping instance
   instance_forall___GHC_Show_Show_a___GHC_Show_Show__Dual_a_ *)

(* Skipping instance
   instance_forall___GHC_Read_Read_a___GHC_Read_Read__Dual_a_ *)

(* Skipping instance instance_forall___GHC_Base_Ord_a___GHC_Base_Ord__Dual_a_ *)

(* Skipping instance instance_forall___GHC_Base_Eq__a___GHC_Base_Eq___Dual_a_ *)

Inductive All : Type := Mk_All : bool -> All.

Definition getAll (arg_7__ : All) :=
  match arg_7__ with
    | Mk_All getAll => getAll
  end.

Local Definition instance_GHC_Base_Monoid_All_mempty : All :=
  Mk_All true.

Local Definition instance_GHC_Base_Monoid_All_mappend : All -> All -> All :=
  fun arg_186__ arg_187__ =>
    match arg_186__ , arg_187__ with
      | Mk_All x , Mk_All y => Mk_All (andb x y)
    end.

Local Definition instance_GHC_Base_Monoid_All_mconcat : list All -> All :=
  GHC.Base.foldr instance_GHC_Base_Monoid_All_mappend
                 instance_GHC_Base_Monoid_All_mempty.

Instance instance_GHC_Base_Monoid_All : GHC.Base.Monoid All := {
  mappend := instance_GHC_Base_Monoid_All_mappend ;
  mconcat := instance_GHC_Base_Monoid_All_mconcat ;
  mempty := instance_GHC_Base_Monoid_All_mempty }.

Instance Unpeel_All : GHC.Prim.Unpeel All bool := GHC.Prim.Build_Unpeel _ _
                                                                        getAll Mk_All.

Local Definition instance_GHC_Base_Eq__All_op_zsze__ : All -> All -> bool :=
  (@GHC.Prim.coerce (bool -> bool -> bool) (All -> All -> bool) _)
  GHC.Base.op_zsze__.

Local Definition instance_GHC_Base_Eq__All_op_zeze__ : All -> All -> bool :=
  (@GHC.Prim.coerce (bool -> bool -> bool) (All -> All -> bool) _)
  GHC.Base.op_zeze__.

Instance instance_GHC_Base_Eq__All : GHC.Base.Eq_ All := {
  op_zeze__ := instance_GHC_Base_Eq__All_op_zeze__ ;
  op_zsze__ := instance_GHC_Base_Eq__All_op_zsze__ }.

Local Definition instance_GHC_Base_Ord_All_op_zlze__ : All -> All -> bool :=
  (@GHC.Prim.coerce (bool -> bool -> bool) (All -> All -> bool) _)
  GHC.Base.op_zlze__.

Local Definition instance_GHC_Base_Ord_All_op_zl__ : All -> All -> bool :=
  (@GHC.Prim.coerce (bool -> bool -> bool) (All -> All -> bool) _)
  GHC.Base.op_zl__.

Local Definition instance_GHC_Base_Ord_All_op_zgze__ : All -> All -> bool :=
  (@GHC.Prim.coerce (bool -> bool -> bool) (All -> All -> bool) _)
  GHC.Base.op_zgze__.

Local Definition instance_GHC_Base_Ord_All_op_zg__ : All -> All -> bool :=
  (@GHC.Prim.coerce (bool -> bool -> bool) (All -> All -> bool) _)
  GHC.Base.op_zg__.

Local Definition instance_GHC_Base_Ord_All_min : All -> All -> All :=
  (@GHC.Prim.coerce (bool -> bool -> bool) (All -> All -> All) _) GHC.Base.min.

Local Definition instance_GHC_Base_Ord_All_max : All -> All -> All :=
  (@GHC.Prim.coerce (bool -> bool -> bool) (All -> All -> All) _) GHC.Base.max.

Local Definition instance_GHC_Base_Ord_All_compare : All -> All -> comparison :=
  (@GHC.Prim.coerce (bool -> bool -> comparison) (All -> All -> comparison) _)
  GHC.Base.compare.

Instance instance_GHC_Base_Ord_All : GHC.Base.Ord All := {
  compare := instance_GHC_Base_Ord_All_compare ;
  max := instance_GHC_Base_Ord_All_max ;
  min := instance_GHC_Base_Ord_All_min ;
  op_zg__ := instance_GHC_Base_Ord_All_op_zg__ ;
  op_zgze__ := instance_GHC_Base_Ord_All_op_zgze__ ;
  op_zl__ := instance_GHC_Base_Ord_All_op_zl__ ;
  op_zlze__ := instance_GHC_Base_Ord_All_op_zlze__ }.

Inductive Alt (f : Type -> Type) a : Type := Mk_Alt : f a -> Alt f a.

Inductive Any : Type := Mk_Any : bool -> Any.

Definition getAny (arg_6__ : Any) :=
  match arg_6__ with
    | Mk_Any getAny => getAny
  end.

Local Definition instance_GHC_Base_Monoid_Any_mempty : Any :=
  Mk_Any false.

Local Definition instance_GHC_Base_Monoid_Any_mappend : Any -> Any -> Any :=
  fun arg_181__ arg_182__ =>
    match arg_181__ , arg_182__ with
      | Mk_Any x , Mk_Any y => Mk_Any (orb x y)
    end.

Local Definition instance_GHC_Base_Monoid_Any_mconcat : list Any -> Any :=
  GHC.Base.foldr instance_GHC_Base_Monoid_Any_mappend
                 instance_GHC_Base_Monoid_Any_mempty.

Instance instance_GHC_Base_Monoid_Any : GHC.Base.Monoid Any := {
  mappend := instance_GHC_Base_Monoid_Any_mappend ;
  mconcat := instance_GHC_Base_Monoid_Any_mconcat ;
  mempty := instance_GHC_Base_Monoid_Any_mempty }.

Instance Unpeel_Any : GHC.Prim.Unpeel Any bool := GHC.Prim.Build_Unpeel _ _
                                                                        getAny Mk_Any.

Local Definition instance_GHC_Base_Eq__Any_op_zsze__ : Any -> Any -> bool :=
  (@GHC.Prim.coerce (bool -> bool -> bool) (Any -> Any -> bool) _)
  GHC.Base.op_zsze__.

Local Definition instance_GHC_Base_Eq__Any_op_zeze__ : Any -> Any -> bool :=
  (@GHC.Prim.coerce (bool -> bool -> bool) (Any -> Any -> bool) _)
  GHC.Base.op_zeze__.

Instance instance_GHC_Base_Eq__Any : GHC.Base.Eq_ Any := {
  op_zeze__ := instance_GHC_Base_Eq__Any_op_zeze__ ;
  op_zsze__ := instance_GHC_Base_Eq__Any_op_zsze__ }.

Local Definition instance_GHC_Base_Ord_Any_op_zlze__ : Any -> Any -> bool :=
  (@GHC.Prim.coerce (bool -> bool -> bool) (Any -> Any -> bool) _)
  GHC.Base.op_zlze__.

Local Definition instance_GHC_Base_Ord_Any_op_zl__ : Any -> Any -> bool :=
  (@GHC.Prim.coerce (bool -> bool -> bool) (Any -> Any -> bool) _)
  GHC.Base.op_zl__.

Local Definition instance_GHC_Base_Ord_Any_op_zgze__ : Any -> Any -> bool :=
  (@GHC.Prim.coerce (bool -> bool -> bool) (Any -> Any -> bool) _)
  GHC.Base.op_zgze__.

Local Definition instance_GHC_Base_Ord_Any_op_zg__ : Any -> Any -> bool :=
  (@GHC.Prim.coerce (bool -> bool -> bool) (Any -> Any -> bool) _)
  GHC.Base.op_zg__.

Local Definition instance_GHC_Base_Ord_Any_min : Any -> Any -> Any :=
  (@GHC.Prim.coerce (bool -> bool -> bool) (Any -> Any -> Any) _) GHC.Base.min.

Local Definition instance_GHC_Base_Ord_Any_max : Any -> Any -> Any :=
  (@GHC.Prim.coerce (bool -> bool -> bool) (Any -> Any -> Any) _) GHC.Base.max.

Local Definition instance_GHC_Base_Ord_Any_compare : Any -> Any -> comparison :=
  (@GHC.Prim.coerce (bool -> bool -> comparison) (Any -> Any -> comparison) _)
  GHC.Base.compare.

Instance instance_GHC_Base_Ord_Any : GHC.Base.Ord Any := {
  compare := instance_GHC_Base_Ord_Any_compare ;
  max := instance_GHC_Base_Ord_Any_max ;
  min := instance_GHC_Base_Ord_Any_min ;
  op_zg__ := instance_GHC_Base_Ord_Any_op_zg__ ;
  op_zgze__ := instance_GHC_Base_Ord_Any_op_zgze__ ;
  op_zl__ := instance_GHC_Base_Ord_Any_op_zl__ ;
  op_zlze__ := instance_GHC_Base_Ord_Any_op_zlze__ }.

Inductive Dual a : Type := Mk_Dual : a -> Dual a.

Arguments Mk_Dual {_} _.

Definition getDual {a} (arg_5__ : Dual a) :=
  match arg_5__ with
    | Mk_Dual getDual => getDual
  end.

Local Definition instance_GHC_Base_Applicative_Dual_pure : forall {a},
                                                             a -> Dual a :=
  fun {a} => Mk_Dual.

Local Definition instance_forall___GHC_Base_Monoid_a___GHC_Base_Monoid__Dual_a__mempty {inst_a}
                                                                                       `{GHC.Base.Monoid inst_a} : (Dual
                                                                                                                   inst_a) :=
  Mk_Dual GHC.Base.mempty.

Local Definition instance_forall___GHC_Base_Monoid_a___GHC_Base_Monoid__Dual_a__mappend {inst_a}
                                                                                        `{GHC.Base.Monoid inst_a}
    : (Dual inst_a) -> (Dual inst_a) -> (Dual inst_a) :=
<<<<<<< HEAD
  fun arg_92__ arg_93__ =>
    match arg_92__ , arg_93__ with
=======
  fun arg_200__ arg_201__ =>
    match arg_200__ , arg_201__ with
>>>>>>> Data.Monoid: Now preamble free
      | Mk_Dual x , Mk_Dual y => Mk_Dual (GHC.Base.mappend y x)
    end.

Local Definition instance_forall___GHC_Base_Monoid_a___GHC_Base_Monoid__Dual_a__mconcat {inst_a}
                                                                                        `{GHC.Base.Monoid inst_a} : list
                                                                                                                    (Dual
                                                                                                                    inst_a) -> (Dual
                                                                                                                    inst_a) :=
  GHC.Base.foldr
  instance_forall___GHC_Base_Monoid_a___GHC_Base_Monoid__Dual_a__mappend
  instance_forall___GHC_Base_Monoid_a___GHC_Base_Monoid__Dual_a__mempty.

Instance instance_forall___GHC_Base_Monoid_a___GHC_Base_Monoid__Dual_a_
  : forall {a}, forall `{GHC.Base.Monoid a}, GHC.Base.Monoid (Dual a) := {
  mappend := instance_forall___GHC_Base_Monoid_a___GHC_Base_Monoid__Dual_a__mappend ;
  mconcat := instance_forall___GHC_Base_Monoid_a___GHC_Base_Monoid__Dual_a__mconcat ;
  mempty := instance_forall___GHC_Base_Monoid_a___GHC_Base_Monoid__Dual_a__mempty }.

<<<<<<< HEAD
Instance Unpeel_Dual a : Unpeel (Dual a) a := Build_Unpeel _ _ getDual Mk_Dual.
=======
Instance Unpeel_Dual a : GHC.Prim.Unpeel (Dual a) a := GHC.Prim.Build_Unpeel _ _
                                                                             getDual Mk_Dual.
>>>>>>> Data.Monoid: Now preamble free

Local Definition instance_GHC_Base_Applicative_Dual_op_zlztzg__ : forall {a}
                                                                         {b},
                                                                    Dual (a -> b) -> Dual a -> Dual b :=
  fun {a} {b} => GHC.Prim.coerce.

Local Definition instance_GHC_Base_Functor_Dual_fmap : forall {a} {b},
                                                         (a -> b) -> Dual a -> Dual b :=
  fun {a} {b} => GHC.Prim.coerce.

Local Definition instance_GHC_Base_Functor_Dual_op_zlzd__ : forall {a} {b},
                                                              b -> Dual a -> Dual b :=
  fun {a} {b} => fun x => instance_GHC_Base_Functor_Dual_fmap (GHC.Base.const x).

Instance instance_GHC_Base_Functor_Dual : GHC.Base.Functor Dual := {
  fmap := fun {a} {b} => instance_GHC_Base_Functor_Dual_fmap ;
  op_zlzd__ := fun {a} {b} => instance_GHC_Base_Functor_Dual_op_zlzd__ }.

Local Definition instance_GHC_Base_Applicative_Dual_op_ztzg__ : forall {a} {b},
                                                                  Dual a -> Dual b -> Dual b :=
  fun {a} {b} =>
    fun x y =>
      instance_GHC_Base_Applicative_Dual_op_zlztzg__ (GHC.Base.fmap (GHC.Base.const
                                                                    GHC.Base.id) x) y.

Instance instance_GHC_Base_Applicative_Dual : GHC.Base.Applicative Dual := {
  op_zlztzg__ := fun {a} {b} => instance_GHC_Base_Applicative_Dual_op_zlztzg__ ;
  op_ztzg__ := fun {a} {b} => instance_GHC_Base_Applicative_Dual_op_ztzg__ ;
  pure := fun {a} => instance_GHC_Base_Applicative_Dual_pure }.

Inductive Endo a : Type := Mk_Endo : (a -> a) -> Endo a.

Arguments Mk_Endo {_} _.

Definition appEndo {a} (arg_4__ : Endo a) :=
  match arg_4__ with
    | Mk_Endo appEndo => appEndo
  end.

Local Definition instance_GHC_Base_Monoid__Endo_a__mempty {inst_a} : (Endo
                                                                     inst_a) :=
  Mk_Endo GHC.Base.id.

Local Definition instance_GHC_Base_Monoid__Endo_a__mappend {inst_a} : (Endo
                                                                      inst_a) -> (Endo inst_a) -> (Endo inst_a) :=
<<<<<<< HEAD
  fun arg_83__ arg_84__ =>
    match arg_83__ , arg_84__ with
=======
  fun arg_191__ arg_192__ =>
    match arg_191__ , arg_192__ with
>>>>>>> Data.Monoid: Now preamble free
      | Mk_Endo f , Mk_Endo g => Mk_Endo (Coq.Program.Basics.compose f g)
    end.

Local Definition instance_GHC_Base_Monoid__Endo_a__mconcat {inst_a} : list (Endo
                                                                           inst_a) -> (Endo inst_a) :=
  GHC.Base.foldr instance_GHC_Base_Monoid__Endo_a__mappend
                 instance_GHC_Base_Monoid__Endo_a__mempty.

Instance instance_GHC_Base_Monoid__Endo_a_ : forall {a},
                                               GHC.Base.Monoid (Endo a) := {
  mappend := instance_GHC_Base_Monoid__Endo_a__mappend ;
  mconcat := instance_GHC_Base_Monoid__Endo_a__mconcat ;
  mempty := instance_GHC_Base_Monoid__Endo_a__mempty }.

<<<<<<< HEAD
(* Unbound variables:
     Build_Unpeel Coq.Program.Basics.compose GHC.Base.Applicative GHC.Base.Functor
     GHC.Base.Monoid GHC.Base.const GHC.Base.fmap GHC.Base.foldr GHC.Base.id
     GHC.Base.mappend GHC.Base.mempty GHC.Prim.coerce Type Unpeel list
=======
Inductive First a : Type := Mk_First : option a -> First a.

Arguments Mk_First {_} _.

Definition getFirst {a} (arg_3__ : First a) :=
  match arg_3__ with
    | Mk_First getFirst => getFirst
  end.

Local Definition instance_GHC_Base_Monoid__First_a__mempty {inst_a} : (First
                                                                      inst_a) :=
  Mk_First None.

Local Definition instance_GHC_Base_Monoid__First_a__mappend {inst_a} : (First
                                                                       inst_a) -> (First inst_a) -> (First inst_a) :=
  fun arg_165__ arg_166__ =>
    match arg_165__ , arg_166__ with
      | Mk_First None , r => r
      | l , _ => l
    end.

Local Definition instance_GHC_Base_Monoid__First_a__mconcat {inst_a} : list
                                                                       (First inst_a) -> (First inst_a) :=
  GHC.Base.foldr instance_GHC_Base_Monoid__First_a__mappend
                 instance_GHC_Base_Monoid__First_a__mempty.

Instance instance_GHC_Base_Monoid__First_a_ : forall {a},
                                                GHC.Base.Monoid (First a) := {
  mappend := instance_GHC_Base_Monoid__First_a__mappend ;
  mconcat := instance_GHC_Base_Monoid__First_a__mconcat ;
  mempty := instance_GHC_Base_Monoid__First_a__mempty }.

Inductive Last a : Type := Mk_Last : option a -> Last a.

Arguments Mk_Last {_} _.

Definition getLast {a} (arg_2__ : Last a) :=
  match arg_2__ with
    | Mk_Last getLast => getLast
  end.

Local Definition instance_GHC_Base_Monoid__Last_a__mempty {inst_a} : (Last
                                                                     inst_a) :=
  Mk_Last None.

Local Definition instance_GHC_Base_Monoid__Last_a__mappend {inst_a} : (Last
                                                                      inst_a) -> (Last inst_a) -> (Last inst_a) :=
  fun arg_161__ arg_162__ =>
    match arg_161__ , arg_162__ with
      | l , Mk_Last None => l
      | _ , r => r
    end.

Local Definition instance_GHC_Base_Monoid__Last_a__mconcat {inst_a} : list (Last
                                                                           inst_a) -> (Last inst_a) :=
  GHC.Base.foldr instance_GHC_Base_Monoid__Last_a__mappend
                 instance_GHC_Base_Monoid__Last_a__mempty.

Instance instance_GHC_Base_Monoid__Last_a_ : forall {a},
                                               GHC.Base.Monoid (Last a) := {
  mappend := instance_GHC_Base_Monoid__Last_a__mappend ;
  mconcat := instance_GHC_Base_Monoid__Last_a__mconcat ;
  mempty := instance_GHC_Base_Monoid__Last_a__mempty }.

Instance Unpeel_Last a : GHC.Prim.Unpeel (Last a) (option a) :=
  GHC.Prim.Build_Unpeel _ _ getLast Mk_Last.

Inductive Product a : Type := Mk_Product : a -> Product a.

Arguments Mk_Product {_} _.

Definition getProduct {a} (arg_1__ : Product a) :=
  match arg_1__ with
    | Mk_Product getProduct => getProduct
  end.

Local Definition instance_GHC_Base_Applicative_Product_pure : forall {a},
                                                                a -> Product a :=
  fun {a} => Mk_Product.

Instance Unpeel_Product a : GHC.Prim.Unpeel (Product a) a :=
  GHC.Prim.Build_Unpeel _ _ getProduct Mk_Product.

Local Definition instance_GHC_Base_Applicative_Product_op_zlztzg__ : forall {a}
                                                                            {b},
                                                                       Product (a -> b) -> Product a -> Product b :=
  fun {a} {b} => GHC.Prim.coerce.

Local Definition instance_GHC_Base_Functor_Product_fmap : forall {a} {b},
                                                            (a -> b) -> Product a -> Product b :=
  fun {a} {b} => GHC.Prim.coerce.

Local Definition instance_GHC_Base_Functor_Product_op_zlzd__ : forall {a} {b},
                                                                 b -> Product a -> Product b :=
  fun {a} {b} =>
    fun x => instance_GHC_Base_Functor_Product_fmap (GHC.Base.const x).

Instance instance_GHC_Base_Functor_Product : GHC.Base.Functor Product := {
  fmap := fun {a} {b} => instance_GHC_Base_Functor_Product_fmap ;
  op_zlzd__ := fun {a} {b} => instance_GHC_Base_Functor_Product_op_zlzd__ }.

Local Definition instance_GHC_Base_Applicative_Product_op_ztzg__ : forall {a}
                                                                          {b},
                                                                     Product a -> Product b -> Product b :=
  fun {a} {b} =>
    fun x y =>
      instance_GHC_Base_Applicative_Product_op_zlztzg__ (GHC.Base.fmap (GHC.Base.const
                                                                       GHC.Base.id) x) y.

Instance instance_GHC_Base_Applicative_Product : GHC.Base.Applicative Product :=
  {
  op_zlztzg__ := fun {a} {b} =>
    instance_GHC_Base_Applicative_Product_op_zlztzg__ ;
  op_ztzg__ := fun {a} {b} => instance_GHC_Base_Applicative_Product_op_ztzg__ ;
  pure := fun {a} => instance_GHC_Base_Applicative_Product_pure }.

Inductive Sum a : Type := Mk_Sum : a -> Sum a.

Arguments Mk_Sum {_} _.

Definition getSum {a} (arg_0__ : Sum a) :=
  match arg_0__ with
    | Mk_Sum getSum => getSum
  end.

Local Definition instance_GHC_Base_Applicative_Sum_pure : forall {a},
                                                            a -> Sum a :=
  fun {a} => Mk_Sum.

Instance Unpeel_Sum a : GHC.Prim.Unpeel (Sum a) a := GHC.Prim.Build_Unpeel _ _
                                                                           getSum Mk_Sum.

Local Definition instance_GHC_Base_Applicative_Sum_op_zlztzg__ : forall {a} {b},
                                                                   Sum (a -> b) -> Sum a -> Sum b :=
  fun {a} {b} => GHC.Prim.coerce.

Local Definition instance_GHC_Base_Functor_Sum_fmap : forall {a} {b},
                                                        (a -> b) -> Sum a -> Sum b :=
  fun {a} {b} => GHC.Prim.coerce.

Local Definition instance_GHC_Base_Functor_Sum_op_zlzd__ : forall {a} {b},
                                                             b -> Sum a -> Sum b :=
  fun {a} {b} => fun x => instance_GHC_Base_Functor_Sum_fmap (GHC.Base.const x).

Instance instance_GHC_Base_Functor_Sum : GHC.Base.Functor Sum := {
  fmap := fun {a} {b} => instance_GHC_Base_Functor_Sum_fmap ;
  op_zlzd__ := fun {a} {b} => instance_GHC_Base_Functor_Sum_op_zlzd__ }.

Local Definition instance_GHC_Base_Applicative_Sum_op_ztzg__ : forall {a} {b},
                                                                 Sum a -> Sum b -> Sum b :=
  fun {a} {b} =>
    fun x y =>
      instance_GHC_Base_Applicative_Sum_op_zlztzg__ (GHC.Base.fmap (GHC.Base.const
                                                                   GHC.Base.id) x) y.

Instance instance_GHC_Base_Applicative_Sum : GHC.Base.Applicative Sum := {
  op_zlztzg__ := fun {a} {b} => instance_GHC_Base_Applicative_Sum_op_zlztzg__ ;
  op_ztzg__ := fun {a} {b} => instance_GHC_Base_Applicative_Sum_op_ztzg__ ;
  pure := fun {a} => instance_GHC_Base_Applicative_Sum_pure }.

(* Unbound variables:
     Coq.Program.Basics.compose GHC.Base.Applicative GHC.Base.Eq_ GHC.Base.Functor
     GHC.Base.Monoid GHC.Base.Ord GHC.Base.compare GHC.Base.const GHC.Base.fmap
     GHC.Base.foldr GHC.Base.id GHC.Base.mappend GHC.Base.max GHC.Base.mempty
     GHC.Base.min GHC.Base.op_zeze__ GHC.Base.op_zg__ GHC.Base.op_zgze__
     GHC.Base.op_zl__ GHC.Base.op_zlze__ GHC.Base.op_zsze__ GHC.Prim.Build_Unpeel
     GHC.Prim.Unpeel GHC.Prim.coerce None Type andb bool comparison false list option
     orb true
>>>>>>> Data.Monoid: Now preamble free
*)
