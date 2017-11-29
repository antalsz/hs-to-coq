(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Coq.Program.Tactics.
Require Coq.Program.Wf.

(* Converted imports: *)

Require Data.Either.
Require Data.Functor.Const.
Require Data.Functor.Identity.
Require Data.Proxy.
Require GHC.Base.
Require GHC.Tuple.

(* Converted type declarations: *)

Record Eq2__Dict f := Eq2__Dict_Build {
  liftEq2__ : forall {a} {b} {c} {d},
    (a -> b -> bool) -> (c -> d -> bool) -> f a c -> f b d -> bool }.

Definition Eq2 f :=
  forall r, (Eq2__Dict f -> r) -> r.

Existing Class Eq2.

Definition liftEq2 `{g : Eq2 f} : forall {a} {b} {c} {d},
                                    (a -> b -> bool) -> (c -> d -> bool) -> f a c -> f b d -> bool :=
  g _ (liftEq2__ f).

Record Ord2__Dict f := Ord2__Dict_Build {
  liftCompare2__ : forall {a} {b} {c} {d},
    (a -> b -> comparison) -> (c -> d -> comparison) -> f a c -> f b
    d -> comparison }.

Definition Ord2 f `{(Eq2 f)} :=
  forall r, (Ord2__Dict f -> r) -> r.

Existing Class Ord2.

Definition liftCompare2 `{g : Ord2 f} : forall {a} {b} {c} {d},
                                          (a -> b -> comparison) -> (c -> d -> comparison) -> f a c -> f b
                                          d -> comparison :=
  g _ (liftCompare2__ f).

Record Eq1__Dict f := Eq1__Dict_Build {
  liftEq__ : forall {a} {b}, (a -> b -> bool) -> f a -> f b -> bool }.

Definition Eq1 f :=
  forall r, (Eq1__Dict f -> r) -> r.

Existing Class Eq1.

Definition liftEq `{g : Eq1 f} : forall {a} {b},
                                   (a -> b -> bool) -> f a -> f b -> bool :=
  g _ (liftEq__ f).

Record Ord1__Dict f := Ord1__Dict_Build {
  liftCompare__ : forall {a} {b},
    (a -> b -> comparison) -> f a -> f b -> comparison }.

Definition Ord1 f `{(Eq1 f)} :=
  forall r, (Ord1__Dict f -> r) -> r.

Existing Class Ord1.

Definition liftCompare `{g : Ord1 f} : forall {a} {b},
                                         (a -> b -> comparison) -> f a -> f b -> comparison :=
  g _ (liftCompare__ f).
(* Converted value declarations: *)

Local Definition instance_Data_Functor_Classes_Eq1_option_liftEq : forall {a}
                                                                          {b},
                                                                     (a -> b -> bool) -> option a -> option b -> bool :=
  fun {a} {b} =>
    fun arg_79__ arg_80__ arg_81__ =>
      match arg_79__ , arg_80__ , arg_81__ with
        | _ , None , None => true
        | _ , None , Some _ => false
        | _ , Some _ , None => false
        | eq , Some x , Some y => eq x y
      end.

Program Instance instance_Data_Functor_Classes_Eq1_option : Eq1 option := fun _
                                                                              k =>
    k {|liftEq__ := fun {a} {b} =>
        instance_Data_Functor_Classes_Eq1_option_liftEq |}.

Local Definition instance_Data_Functor_Classes_Ord1_option_liftCompare
    : forall {a} {b},
        (a -> b -> comparison) -> option a -> option b -> comparison :=
  fun {a} {b} =>
    fun arg_74__ arg_75__ arg_76__ =>
      match arg_74__ , arg_75__ , arg_76__ with
        | _ , None , None => Eq
        | _ , None , Some _ => Lt
        | _ , Some _ , None => Gt
        | comp , Some x , Some y => comp x y
      end.

Program Instance instance_Data_Functor_Classes_Ord1_option : Ord1 option :=
  fun _ k =>
    k {|liftCompare__ := fun {a} {b} =>
        instance_Data_Functor_Classes_Ord1_option_liftCompare |}.

(* Translating `instance Data.Functor.Classes.Read1 option' failed: OOPS! Cannot
   find information for class Qualified_ "Data.Functor.Classes" "Read1"
   unsupported *)

(* Translating `instance Data.Functor.Classes.Show1 option' failed: OOPS! Cannot
   find information for class Qualified_ "Data.Functor.Classes" "Show1"
   unsupported *)

Local Definition instance_Data_Functor_Classes_Eq1_list_liftEq : forall {a} {b},
                                                                   (a -> b -> bool) -> list a -> list b -> bool :=
  fun {a} {b} =>
    fix liftEq arg_69__ arg_70__ arg_71__
          := match arg_69__ , arg_70__ , arg_71__ with
               | _ , nil , nil => true
               | _ , nil , cons _ _ => false
               | _ , cons _ _ , nil => false
               | eq , cons x xs , cons y ys => andb (eq x y) (liftEq eq xs ys)
             end.

Program Instance instance_Data_Functor_Classes_Eq1_list : Eq1 list := fun _ k =>
    k {|liftEq__ := fun {a} {b} => instance_Data_Functor_Classes_Eq1_list_liftEq |}.

Local Definition instance_Data_Functor_Classes_Ord1_list_liftCompare
    : forall {a} {b}, (a -> b -> comparison) -> list a -> list b -> comparison :=
  fun {a} {b} =>
    fix liftCompare arg_64__ arg_65__ arg_66__
          := match arg_64__ , arg_65__ , arg_66__ with
               | _ , nil , nil => Eq
               | _ , nil , cons _ _ => Lt
               | _ , cons _ _ , nil => Gt
               | comp , cons x xs , cons y ys => GHC.Base.mappend (comp x y) (liftCompare comp
                                                                  xs ys)
             end.

Program Instance instance_Data_Functor_Classes_Ord1_list : Ord1 list := fun _
                                                                            k =>
    k {|liftCompare__ := fun {a} {b} =>
        instance_Data_Functor_Classes_Ord1_list_liftCompare |}.

(* Translating `instance Data.Functor.Classes.Read1 list' failed: OOPS! Cannot
   find information for class Qualified_ "Data.Functor.Classes" "Read1"
   unsupported *)

(* Translating `instance Data.Functor.Classes.Show1 list' failed: OOPS! Cannot
   find information for class Qualified_ "Data.Functor.Classes" "Show1"
   unsupported *)

Local Definition instance_Data_Functor_Classes_Eq2_GHC_Tuple_pair_type_liftEq2
    : forall {a} {b} {c} {d},
        (a -> b -> bool) -> (c -> d -> bool) -> GHC.Tuple.pair_type a
        c -> GHC.Tuple.pair_type b d -> bool :=
  fun {a} {b} {c} {d} =>
    fun arg_58__ arg_59__ arg_60__ arg_61__ =>
      match arg_58__ , arg_59__ , arg_60__ , arg_61__ with
        | e1 , e2 , pair x1 y1 , pair x2 y2 => andb (e1 x1 x2) (e2 y1 y2)
      end.

Program Instance instance_Data_Functor_Classes_Eq2_GHC_Tuple_pair_type : Eq2
                                                                         GHC.Tuple.pair_type := fun _ k =>
    k {|liftEq2__ := fun {a} {b} {c} {d} =>
        instance_Data_Functor_Classes_Eq2_GHC_Tuple_pair_type_liftEq2 |}.

Local Definition instance_Data_Functor_Classes_Ord2_GHC_Tuple_pair_type_liftCompare2
    : forall {a} {b} {c} {d},
        (a -> b -> comparison) -> (c -> d -> comparison) -> GHC.Tuple.pair_type a
        c -> GHC.Tuple.pair_type b d -> comparison :=
  fun {a} {b} {c} {d} =>
    fun arg_52__ arg_53__ arg_54__ arg_55__ =>
      match arg_52__ , arg_53__ , arg_54__ , arg_55__ with
        | comp1 , comp2 , pair x1 y1 , pair x2 y2 => GHC.Base.mappend (comp1 x1 x2)
                                                                      (comp2 y1 y2)
      end.

Program Instance instance_Data_Functor_Classes_Ord2_GHC_Tuple_pair_type : Ord2
                                                                          GHC.Tuple.pair_type := fun _ k =>
    k {|liftCompare2__ := fun {a} {b} {c} {d} =>
        instance_Data_Functor_Classes_Ord2_GHC_Tuple_pair_type_liftCompare2 |}.

(* Translating `instance Data.Functor.Classes.Read2 GHC.Tuple.pair_type' failed:
   OOPS! Cannot find information for class Qualified_ "Data.Functor.Classes"
   "Read2" unsupported *)

(* Translating `instance Data.Functor.Classes.Show2 GHC.Tuple.pair_type' failed:
   OOPS! Cannot find information for class Qualified_ "Data.Functor.Classes"
   "Show2" unsupported *)

Local Definition instance_forall____GHC_Base_Eq__a____Data_Functor_Classes_Eq1__GHC_Tuple_pair_type_a__liftEq {inst_a}
                                                                                                              `{(GHC.Base.Eq_
                                                                                                              inst_a)}
    : forall {a} {b},
        (a -> b -> bool) -> (GHC.Tuple.pair_type inst_a) a -> (GHC.Tuple.pair_type
        inst_a) b -> bool :=
  fun {a} {b} => liftEq2 GHC.Base.op_zeze__.

Program Instance instance_forall____GHC_Base_Eq__a____Data_Functor_Classes_Eq1__GHC_Tuple_pair_type_a_ {a}
                                                                                                       `{(GHC.Base.Eq_
                                                                                                       a)} : Eq1
                                                                                                             (GHC.Tuple.pair_type
                                                                                                             a) := fun _
                                                                                                                       k =>
    k {|liftEq__ := fun {a} {b} =>
        instance_forall____GHC_Base_Eq__a____Data_Functor_Classes_Eq1__GHC_Tuple_pair_type_a__liftEq |}.

Local Definition instance_forall____GHC_Base_Ord_a____Data_Functor_Classes_Ord1__GHC_Tuple_pair_type_a__liftCompare {inst_a}
                                                                                                                    `{(GHC.Base.Ord
                                                                                                                    inst_a)}
    : forall {a} {b},
        (a -> b -> comparison) -> (GHC.Tuple.pair_type inst_a) a -> (GHC.Tuple.pair_type
        inst_a) b -> comparison :=
  fun {a} {b} => liftCompare2 GHC.Base.compare.

Program Instance instance_forall____GHC_Base_Ord_a____Data_Functor_Classes_Ord1__GHC_Tuple_pair_type_a_ {a}
                                                                                                        `{(GHC.Base.Ord
                                                                                                        a)} : Ord1
                                                                                                              (GHC.Tuple.pair_type
                                                                                                              a) :=
  fun _ k =>
    k {|liftCompare__ := fun {a} {b} =>
        instance_forall____GHC_Base_Ord_a____Data_Functor_Classes_Ord1__GHC_Tuple_pair_type_a__liftCompare |}.

(* Translating `instance forall {a}, forall `{(GHC.Read.Read a)},
   Data.Functor.Classes.Read1 (GHC.Tuple.pair_type a)' failed: OOPS! Cannot find
   information for class Qualified_ "Data.Functor.Classes" "Read1" unsupported *)

(* Translating `instance forall {a}, forall `{(GHC.Show.Show a)},
   Data.Functor.Classes.Show1 (GHC.Tuple.pair_type a)' failed: OOPS! Cannot find
   information for class Qualified_ "Data.Functor.Classes" "Show1" unsupported *)

Local Definition instance_Data_Functor_Classes_Eq2_Data_Either_Either_liftEq2
    : forall {a} {b} {c} {d},
        (a -> b -> bool) -> (c -> d -> bool) -> Data.Either.Either a
        c -> Data.Either.Either b d -> bool :=
  fun {a} {b} {c} {d} =>
    fun arg_43__ arg_44__ arg_45__ arg_46__ =>
      match arg_43__ , arg_44__ , arg_45__ , arg_46__ with
        | e1 , _ , Data.Either.Mk_Left x , Data.Either.Mk_Left y => e1 x y
        | _ , _ , Data.Either.Mk_Left _ , Data.Either.Mk_Right _ => false
        | _ , _ , Data.Either.Mk_Right _ , Data.Either.Mk_Left _ => false
        | _ , e2 , Data.Either.Mk_Right x , Data.Either.Mk_Right y => e2 x y
      end.

Program Instance instance_Data_Functor_Classes_Eq2_Data_Either_Either : Eq2
                                                                        Data.Either.Either := fun _ k =>
    k {|liftEq2__ := fun {a} {b} {c} {d} =>
        instance_Data_Functor_Classes_Eq2_Data_Either_Either_liftEq2 |}.

Local Definition instance_Data_Functor_Classes_Ord2_Data_Either_Either_liftCompare2
    : forall {a} {b} {c} {d},
        (a -> b -> comparison) -> (c -> d -> comparison) -> Data.Either.Either a
        c -> Data.Either.Either b d -> comparison :=
  fun {a} {b} {c} {d} =>
    fun arg_36__ arg_37__ arg_38__ arg_39__ =>
      match arg_36__ , arg_37__ , arg_38__ , arg_39__ with
        | comp1 , _ , Data.Either.Mk_Left x , Data.Either.Mk_Left y => comp1 x y
        | _ , _ , Data.Either.Mk_Left _ , Data.Either.Mk_Right _ => Lt
        | _ , _ , Data.Either.Mk_Right _ , Data.Either.Mk_Left _ => Gt
        | _ , comp2 , Data.Either.Mk_Right x , Data.Either.Mk_Right y => comp2 x y
      end.

Program Instance instance_Data_Functor_Classes_Ord2_Data_Either_Either : Ord2
                                                                         Data.Either.Either := fun _ k =>
    k {|liftCompare2__ := fun {a} {b} {c} {d} =>
        instance_Data_Functor_Classes_Ord2_Data_Either_Either_liftCompare2 |}.

(* Translating `instance Data.Functor.Classes.Read2 Data.Either.Either' failed:
   OOPS! Cannot find information for class Qualified_ "Data.Functor.Classes"
   "Read2" unsupported *)

(* Translating `instance Data.Functor.Classes.Show2 Data.Either.Either' failed:
   OOPS! Cannot find information for class Qualified_ "Data.Functor.Classes"
   "Show2" unsupported *)

Local Definition instance_forall____GHC_Base_Eq__a____Data_Functor_Classes_Eq1__Data_Either_Either_a__liftEq {inst_a}
                                                                                                             `{(GHC.Base.Eq_
                                                                                                             inst_a)}
    : forall {a} {b},
        (a -> b -> bool) -> (Data.Either.Either inst_a) a -> (Data.Either.Either inst_a)
        b -> bool :=
  fun {a} {b} => liftEq2 GHC.Base.op_zeze__.

Program Instance instance_forall____GHC_Base_Eq__a____Data_Functor_Classes_Eq1__Data_Either_Either_a_ {a}
                                                                                                      `{(GHC.Base.Eq_
                                                                                                      a)} : Eq1
                                                                                                            (Data.Either.Either
                                                                                                            a) := fun _
                                                                                                                      k =>
    k {|liftEq__ := fun {a} {b} =>
        instance_forall____GHC_Base_Eq__a____Data_Functor_Classes_Eq1__Data_Either_Either_a__liftEq |}.

Local Definition instance_forall____GHC_Base_Ord_a____Data_Functor_Classes_Ord1__Data_Either_Either_a__liftCompare {inst_a}
                                                                                                                   `{(GHC.Base.Ord
                                                                                                                   inst_a)}
    : forall {a} {b},
        (a -> b -> comparison) -> (Data.Either.Either inst_a) a -> (Data.Either.Either
        inst_a) b -> comparison :=
  fun {a} {b} => liftCompare2 GHC.Base.compare.

Program Instance instance_forall____GHC_Base_Ord_a____Data_Functor_Classes_Ord1__Data_Either_Either_a_ {a}
                                                                                                       `{(GHC.Base.Ord
                                                                                                       a)} : Ord1
                                                                                                             (Data.Either.Either
                                                                                                             a) := fun _
                                                                                                                       k =>
    k {|liftCompare__ := fun {a} {b} =>
        instance_forall____GHC_Base_Ord_a____Data_Functor_Classes_Ord1__Data_Either_Either_a__liftCompare |}.

(* Translating `instance forall {a}, forall `{(GHC.Read.Read a)},
   Data.Functor.Classes.Read1 (Data.Either.Either a)' failed: OOPS! Cannot find
   information for class Qualified_ "Data.Functor.Classes" "Read1" unsupported *)

(* Translating `instance forall {a}, forall `{(GHC.Show.Show a)},
   Data.Functor.Classes.Show1 (Data.Either.Either a)' failed: OOPS! Cannot find
   information for class Qualified_ "Data.Functor.Classes" "Show1" unsupported *)

Local Definition instance_Data_Functor_Classes_Eq1_Data_Functor_Identity_Identity_liftEq
    : forall {a} {b},
        (a -> b -> bool) -> Data.Functor.Identity.Identity
        a -> Data.Functor.Identity.Identity b -> bool :=
  fun {a} {b} =>
    fun arg_29__ arg_30__ arg_31__ =>
      match arg_29__ , arg_30__ , arg_31__ with
        | eq , Data.Functor.Identity.Mk_Identity x , Data.Functor.Identity.Mk_Identity
          y => eq x y
      end.

Program Instance instance_Data_Functor_Classes_Eq1_Data_Functor_Identity_Identity
  : Eq1 Data.Functor.Identity.Identity := fun _ k =>
    k {|liftEq__ := fun {a} {b} =>
        instance_Data_Functor_Classes_Eq1_Data_Functor_Identity_Identity_liftEq |}.

Local Definition instance_Data_Functor_Classes_Ord1_Data_Functor_Identity_Identity_liftCompare
    : forall {a} {b},
        (a -> b -> comparison) -> Data.Functor.Identity.Identity
        a -> Data.Functor.Identity.Identity b -> comparison :=
  fun {a} {b} =>
    fun arg_24__ arg_25__ arg_26__ =>
      match arg_24__ , arg_25__ , arg_26__ with
        | comp , Data.Functor.Identity.Mk_Identity x , Data.Functor.Identity.Mk_Identity
          y => comp x y
      end.

Program Instance instance_Data_Functor_Classes_Ord1_Data_Functor_Identity_Identity
  : Ord1 Data.Functor.Identity.Identity := fun _ k =>
    k {|liftCompare__ := fun {a} {b} =>
        instance_Data_Functor_Classes_Ord1_Data_Functor_Identity_Identity_liftCompare |}.

(* Translating `instance Data.Functor.Classes.Read1
   Data.Functor.Identity.Identity' failed: OOPS! Cannot find information for class
   Qualified_ "Data.Functor.Classes" "Read1" unsupported *)

(* Translating `instance Data.Functor.Classes.Show1
   Data.Functor.Identity.Identity' failed: OOPS! Cannot find information for class
   Qualified_ "Data.Functor.Classes" "Show1" unsupported *)

Local Definition instance_Data_Functor_Classes_Eq2_Data_Functor_Const_Const_liftEq2
    : forall {a} {b} {c} {d},
        (a -> b -> bool) -> (c -> d -> bool) -> Data.Functor.Const.Const a
        c -> Data.Functor.Const.Const b d -> bool :=
  fun {a} {b} {c} {d} =>
    fun arg_18__ arg_19__ arg_20__ arg_21__ =>
      match arg_18__ , arg_19__ , arg_20__ , arg_21__ with
        | eq , _ , Data.Functor.Const.Mk_Const x , Data.Functor.Const.Mk_Const y => eq x
                                                                                    y
      end.

Program Instance instance_Data_Functor_Classes_Eq2_Data_Functor_Const_Const
  : Eq2 Data.Functor.Const.Const := fun _ k =>
    k {|liftEq2__ := fun {a} {b} {c} {d} =>
        instance_Data_Functor_Classes_Eq2_Data_Functor_Const_Const_liftEq2 |}.

Local Definition instance_Data_Functor_Classes_Ord2_Data_Functor_Const_Const_liftCompare2
    : forall {a} {b} {c} {d},
        (a -> b -> comparison) -> (c -> d -> comparison) -> Data.Functor.Const.Const a
        c -> Data.Functor.Const.Const b d -> comparison :=
  fun {a} {b} {c} {d} =>
    fun arg_12__ arg_13__ arg_14__ arg_15__ =>
      match arg_12__ , arg_13__ , arg_14__ , arg_15__ with
        | comp , _ , Data.Functor.Const.Mk_Const x , Data.Functor.Const.Mk_Const y =>
          comp x y
      end.

Program Instance instance_Data_Functor_Classes_Ord2_Data_Functor_Const_Const
  : Ord2 Data.Functor.Const.Const := fun _ k =>
    k {|liftCompare2__ := fun {a} {b} {c} {d} =>
        instance_Data_Functor_Classes_Ord2_Data_Functor_Const_Const_liftCompare2 |}.

(* Translating `instance Data.Functor.Classes.Read2 Data.Functor.Const.Const'
   failed: OOPS! Cannot find information for class Qualified_
   "Data.Functor.Classes" "Read2" unsupported *)

(* Translating `instance Data.Functor.Classes.Show2 Data.Functor.Const.Const'
   failed: OOPS! Cannot find information for class Qualified_
   "Data.Functor.Classes" "Show2" unsupported *)

Local Definition instance_forall____GHC_Base_Eq__a____Data_Functor_Classes_Eq1__Data_Functor_Const_Const_a__liftEq {inst_a}
                                                                                                                   `{(GHC.Base.Eq_
                                                                                                                   inst_a)}
    : forall {a} {b},
        (a -> b -> bool) -> (Data.Functor.Const.Const inst_a)
        a -> (Data.Functor.Const.Const inst_a) b -> bool :=
  fun {a} {b} => liftEq2 GHC.Base.op_zeze__.

Program Instance instance_forall____GHC_Base_Eq__a____Data_Functor_Classes_Eq1__Data_Functor_Const_Const_a_ {a}
                                                                                                            `{(GHC.Base.Eq_
                                                                                                            a)} : Eq1
                                                                                                                  (Data.Functor.Const.Const
                                                                                                                  a) :=
  fun _ k =>
    k {|liftEq__ := fun {a} {b} =>
        instance_forall____GHC_Base_Eq__a____Data_Functor_Classes_Eq1__Data_Functor_Const_Const_a__liftEq |}.

Local Definition instance_forall____GHC_Base_Ord_a____Data_Functor_Classes_Ord1__Data_Functor_Const_Const_a__liftCompare {inst_a}
                                                                                                                         `{(GHC.Base.Ord
                                                                                                                         inst_a)}
    : forall {a} {b},
        (a -> b -> comparison) -> (Data.Functor.Const.Const inst_a)
        a -> (Data.Functor.Const.Const inst_a) b -> comparison :=
  fun {a} {b} => liftCompare2 GHC.Base.compare.

Program Instance instance_forall____GHC_Base_Ord_a____Data_Functor_Classes_Ord1__Data_Functor_Const_Const_a_ {a}
                                                                                                             `{(GHC.Base.Ord
                                                                                                             a)} : Ord1
                                                                                                                   (Data.Functor.Const.Const
                                                                                                                   a) :=
  fun _ k =>
    k {|liftCompare__ := fun {a} {b} =>
        instance_forall____GHC_Base_Ord_a____Data_Functor_Classes_Ord1__Data_Functor_Const_Const_a__liftCompare |}.

(* Translating `instance forall {a}, forall `{(GHC.Read.Read a)},
   Data.Functor.Classes.Read1 (Data.Functor.Const.Const a)' failed: OOPS! Cannot
   find information for class Qualified_ "Data.Functor.Classes" "Read1"
   unsupported *)

(* Translating `instance forall {a}, forall `{(GHC.Show.Show a)},
   Data.Functor.Classes.Show1 (Data.Functor.Const.Const a)' failed: OOPS! Cannot
   find information for class Qualified_ "Data.Functor.Classes" "Show1"
   unsupported *)

Local Definition instance_Data_Functor_Classes_Eq1_Data_Proxy_Proxy_liftEq
    : forall {a} {b},
        (a -> b -> bool) -> Data.Proxy.Proxy a -> Data.Proxy.Proxy b -> bool :=
  fun {a} {b} => fun arg_7__ arg_8__ arg_9__ => true.

Program Instance instance_Data_Functor_Classes_Eq1_Data_Proxy_Proxy : Eq1
                                                                      Data.Proxy.Proxy := fun _ k =>
    k {|liftEq__ := fun {a} {b} =>
        instance_Data_Functor_Classes_Eq1_Data_Proxy_Proxy_liftEq |}.

Local Definition instance_Data_Functor_Classes_Ord1_Data_Proxy_Proxy_liftCompare
    : forall {a} {b},
        (a -> b -> comparison) -> Data.Proxy.Proxy a -> Data.Proxy.Proxy
        b -> comparison :=
  fun {a} {b} => fun arg_4__ arg_5__ arg_6__ => Eq.

Program Instance instance_Data_Functor_Classes_Ord1_Data_Proxy_Proxy : Ord1
                                                                       Data.Proxy.Proxy := fun _ k =>
    k {|liftCompare__ := fun {a} {b} =>
        instance_Data_Functor_Classes_Ord1_Data_Proxy_Proxy_liftCompare |}.

(* Translating `instance Data.Functor.Classes.Show1 Data.Proxy.Proxy' failed:
   OOPS! Cannot find information for class Qualified_ "Data.Functor.Classes"
   "Show1" unsupported *)

(* Translating `instance Data.Functor.Classes.Read1 Data.Proxy.Proxy' failed:
   OOPS! Cannot find information for class Qualified_ "Data.Functor.Classes"
   "Read1" unsupported *)

Definition compare1 {f} {a} `{Ord1 f} `{GHC.Base.Ord a} : f a -> f
                                                          a -> comparison :=
  liftCompare GHC.Base.compare.

Definition compare2 {f} {a} {b} `{Ord2 f} `{GHC.Base.Ord a} `{GHC.Base.Ord b}
    : f a b -> f a b -> comparison :=
  liftCompare2 GHC.Base.compare GHC.Base.compare.

Definition eq1 {f} {a} `{Eq1 f} `{GHC.Base.Eq_ a} : f a -> f a -> bool :=
  liftEq GHC.Base.op_zeze__.

Definition eq2 {f} {a} {b} `{Eq2 f} `{GHC.Base.Eq_ a} `{GHC.Base.Eq_ b} : f a
                                                                          b -> f a b -> bool :=
  liftEq2 GHC.Base.op_zeze__ GHC.Base.op_zeze__.

(* Unbound variables:
     Eq Gt Lt Some andb bool comparison cons false list option pair true
     Data.Either.Either Data.Either.Mk_Left Data.Either.Mk_Right
     Data.Functor.Const.Const Data.Functor.Const.Mk_Const
     Data.Functor.Identity.Identity Data.Functor.Identity.Mk_Identity
     Data.Proxy.Proxy GHC.Base.Eq_ GHC.Base.Ord GHC.Base.compare GHC.Base.mappend
     GHC.Base.op_zeze__ GHC.Tuple.pair_type
*)
