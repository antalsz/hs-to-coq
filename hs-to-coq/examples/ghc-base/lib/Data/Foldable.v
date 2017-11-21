(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Coq.Program.Wf.

(* Preamble *)

Require Import Data.Monoid.
(* Converted imports: *)

Require Coq.Program.Basics.
Require Data.Either.
Require Data.Monoid.
Require Data.Proxy.
Require GHC.Base.
Require GHC.List.
Require GHC.Num.
Require GHC.Tuple.

(* Converted type declarations: *)

Inductive Min a : Type := Mk_Min : option a -> Min a.

Inductive Max a : Type := Mk_Max : option a -> Max a.

Record Foldable__Dict t := Foldable__Dict_Build {
  elem__ : forall {a}, forall `{GHC.Base.Eq_ a}, a -> t a -> bool ;
  fold__ : forall {m}, forall `{GHC.Base.Monoid m}, t m -> m ;
  foldMap__ : forall {m} {a}, forall `{GHC.Base.Monoid m}, (a -> m) -> t a -> m ;
  foldl__ : forall {b} {a}, (b -> a -> b) -> b -> t a -> b ;
  foldl'__ : forall {b} {a}, (b -> a -> b) -> b -> t a -> b ;
  foldr__ : forall {a} {b}, (a -> b -> b) -> b -> t a -> b ;
  foldr'__ : forall {a} {b}, (a -> b -> b) -> b -> t a -> b ;
  length__ : forall {a}, t a -> GHC.Num.Int ;
  null__ : forall {a}, t a -> bool ;
  product__ : forall {a}, forall `{GHC.Num.Num a}, t a -> a ;
  sum__ : forall {a}, forall `{GHC.Num.Num a}, t a -> a ;
  toList__ : forall {a}, t a -> list a }.

Definition Foldable t :=
  forall r, (Foldable__Dict t -> r) -> r.

Existing Class Foldable.

Definition elem `{g : Foldable t} : forall {a},
                                      forall `{GHC.Base.Eq_ a}, a -> t a -> bool :=
  g _ (elem__ t).

Definition fold `{g : Foldable t} : forall {m},
                                      forall `{GHC.Base.Monoid m}, t m -> m :=
  g _ (fold__ t).

Definition foldMap `{g : Foldable t} : forall {m} {a},
                                         forall `{GHC.Base.Monoid m}, (a -> m) -> t a -> m :=
  g _ (foldMap__ t).

Definition foldl `{g : Foldable t} : forall {b} {a},
                                       (b -> a -> b) -> b -> t a -> b :=
  g _ (foldl__ t).

Definition foldl' `{g : Foldable t} : forall {b} {a},
                                        (b -> a -> b) -> b -> t a -> b :=
  g _ (foldl'__ t).

Definition foldr `{g : Foldable t} : forall {a} {b},
                                       (a -> b -> b) -> b -> t a -> b :=
  g _ (foldr__ t).

Definition foldr' `{g : Foldable t} : forall {a} {b},
                                        (a -> b -> b) -> b -> t a -> b :=
  g _ (foldr'__ t).

Definition length `{g : Foldable t} : forall {a}, t a -> GHC.Num.Int :=
  g _ (length__ t).

Definition null `{g : Foldable t} : forall {a}, t a -> bool :=
  g _ (null__ t).

Definition product `{g : Foldable t} : forall {a},
                                         forall `{GHC.Num.Num a}, t a -> a :=
  g _ (product__ t).

Definition sum `{g : Foldable t} : forall {a},
                                     forall `{GHC.Num.Num a}, t a -> a :=
  g _ (sum__ t).

Definition toList `{g : Foldable t} : forall {a}, t a -> list a :=
  g _ (toList__ t).

Arguments Mk_Min {_} _.

Arguments Mk_Max {_} _.

Definition getMin {a} (arg_77__ : Min a) :=
  match arg_77__ with
    | Mk_Min getMin => getMin
  end.

Definition getMax {a} (arg_78__ : Max a) :=
  match arg_78__ with
    | Mk_Max getMax => getMax
  end.
(* Midamble *)

Definition default_foldable {f:Type -> Type}
  (foldMap : forall {m} {a}, forall `{GHC.Base.Monoid m}, (a -> m) -> f a -> m)
  (foldr : forall {a} {b}, (a -> b -> b) -> b -> f a -> b):=
  let foldl : forall {b} {a}, (b -> a -> b) -> b -> f a -> b :=
      (fun {b} {a} =>
         fun f  z t => Data.Monoid.appEndo
                    (Data.Monoid.getDual
                       (foldMap (Coq.Program.Basics.compose
                                   Data.Monoid.Mk_Dual
                                   (Coq.Program.Basics.compose
                                      Data.Monoid.Mk_Endo
                                      (GHC.Base.flip f))) t)) z)
  in
  let foldl' : forall {b} {a}, (b -> a -> b) -> b -> f a -> b :=
      (fun {b} {a} =>
         fun f  z0  xs =>
           let f' :=  fun  x  k  z => GHC.Base.op_zdzn__ k (f z x)
           in foldr f' GHC.Base.id xs z0)
  in
  Foldable__Dict_Build
    f
    (fun {a} `{GHC.Base.Eq_ a} =>
       Coq.Program.Basics.compose
         (fun p => Coq.Program.Basics.compose
                  Data.Monoid.getAny
                  (foldMap (fun x => Data.Monoid.Mk_Any (p x))))
         GHC.Base.op_zeze__ )
    (* fold *)
    (fun {m} `{GHC.Base.Monoid m} => foldMap GHC.Base.id)
    (* foldMap *)
    (fun {m}{a} `{GHC.Base.Monoid m} => foldMap)
    (* foldl *)
    foldl
    (* foldl' *)
    foldl'
    (* foldr  *)
    (fun {a}{b} => foldr)
    (* foldr' *)
    (fun {a} {b} f z0 xs =>
       let f' := fun k  x  z => GHC.Base.op_zdzn__ k (f x z)
       in
       foldl _ _ f' GHC.Base.id xs z0)
    (* length *)
    (fun {a} => foldl' _ _ (fun c  _ => GHC.Num.op_zp__ c (GHC.Num.fromInteger 1))
                    (GHC.Num.fromInteger 0))
    (* null *)
    (fun {a} => foldr (fun arg_61__ arg_62__ => false) true)
    (* product *)
    (fun {a} `{GHC.Num.Num a} =>
       Coq.Program.Basics.compose Data.Monoid.getProduct
                                  (foldMap Data.Monoid.Mk_Product))
    (* sum *)
    (fun  {a} `{GHC.Num.Num a} =>
       Coq.Program.Basics.compose Data.Monoid.getSum
                                  (foldMap Data.Monoid.Mk_Sum))
    (* toList *)
    (fun {a} => fun t => GHC.Base.build (fun c n => foldr c n t)).

Definition default_foldable_foldMap {f : Type -> Type}
  (foldMap : forall {m} {a}, forall `{GHC.Base.Monoid m}, (a -> m) -> f a -> m)
 :=
  let foldr : forall {a} {b}, (a -> b -> b) -> b -> f a -> b :=
  fun {a} {b} f z t =>
    Data.Monoid.appEndo
      (foldMap
         (Coq.Program.Basics.compose Data.Monoid.Mk_Endo f) t) z
  in
  default_foldable (fun {m}{a}`{GHC.Base.Monoid m} => foldMap) foldr.

Definition default_foldable_foldr (f : Type -> Type)
  (foldr : forall {a} {b}, (a -> b -> b) -> b -> f a -> b) :=
  let foldMap :  forall {m} {a} `{GHC.Base.Monoid m}, (a -> m) -> f a -> m :=
  fun {m} {a} `{GHC.Base.Monoid m} =>
    fun f => foldr
            (Coq.Program.Basics.compose GHC.Base.mappend
                                        f) GHC.Base.mempty
  in
  default_foldable foldMap (fun {a} {b} => foldr).

(* Converted value declarations: *)

Local Definition instance_Foldable_option_foldl : forall {b} {a},
                                                    (b -> a -> b) -> b -> option a -> b :=
  fun {b} {a} =>
    fun arg_449__ arg_450__ arg_451__ =>
      match arg_449__ , arg_450__ , arg_451__ with
        | _ , z , None => z
        | f , z , Some x => f z x
      end.

Local Definition instance_Foldable_option_foldr' : forall {a} {b},
                                                     (a -> b -> b) -> b -> option a -> b :=
  fun {a} {b} =>
    fun arg_9__ arg_10__ arg_11__ =>
      match arg_9__ , arg_10__ , arg_11__ with
        | f , z0 , xs => let f' :=
                           fun arg_12__ arg_13__ arg_14__ =>
                             match arg_12__ , arg_13__ , arg_14__ with
                               | k , x , z => GHC.Base.op_zdzn__ k (f x z)
                             end in
                         instance_Foldable_option_foldl f' GHC.Base.id xs z0
      end.

Local Definition instance_Foldable_option_foldr : forall {a} {b},
                                                    (a -> b -> b) -> b -> option a -> b :=
  fun {a} {b} =>
    fun arg_444__ arg_445__ arg_446__ =>
      match arg_444__ , arg_445__ , arg_446__ with
        | _ , z , None => z
        | f , z , Some x => f x z
      end.

Local Definition instance_Foldable_option_null : forall {a}, option a -> bool :=
  fun {a} => instance_Foldable_option_foldr (fun arg_61__ arg_62__ => false) true.

Local Definition instance_Foldable_option_toList : forall {a},
                                                     option a -> list a :=
  fun {a} =>
    fun arg_54__ =>
      match arg_54__ with
        | t => GHC.Base.build (fun arg_55__ arg_56__ =>
                                match arg_55__ , arg_56__ with
                                  | c , n => instance_Foldable_option_foldr c n t
                                end)
      end.

Local Definition instance_Foldable_option_foldl' : forall {b} {a},
                                                     (b -> a -> b) -> b -> option a -> b :=
  fun {b} {a} =>
    fun arg_24__ arg_25__ arg_26__ =>
      match arg_24__ , arg_25__ , arg_26__ with
        | f , z0 , xs => let f' :=
                           fun arg_27__ arg_28__ arg_29__ =>
                             match arg_27__ , arg_28__ , arg_29__ with
                               | x , k , z => GHC.Base.op_zdzn__ k (f z x)
                             end in
                         instance_Foldable_option_foldr f' GHC.Base.id xs z0
      end.

Local Definition instance_Foldable_option_length : forall {a},
                                                     option a -> GHC.Num.Int :=
  fun {a} =>
    instance_Foldable_option_foldl' (fun arg_64__ arg_65__ =>
                                      match arg_64__ , arg_65__ with
                                        | c , _ => GHC.Num.op_zp__ c (GHC.Num.fromInteger 1)
                                      end) (GHC.Num.fromInteger 0).

Local Definition instance_Foldable_option_foldMap : forall {m} {a},
                                                      forall `{GHC.Base.Monoid m}, (a -> m) -> option a -> m :=
  fun {m} {a} `{GHC.Base.Monoid m} =>
    fun arg_1__ =>
      match arg_1__ with
        | f => instance_Foldable_option_foldr (Coq.Program.Basics.compose
                                              GHC.Base.mappend f) GHC.Base.mempty
      end.

Local Definition instance_Foldable_option_fold : forall {m},
                                                   forall `{GHC.Base.Monoid m}, option m -> m :=
  fun {m} `{GHC.Base.Monoid m} => instance_Foldable_option_foldMap GHC.Base.id.

Local Definition instance_Foldable_option_elem : forall {a},
                                                   forall `{GHC.Base.Eq_ a}, a -> option a -> bool :=
  fun {a} `{GHC.Base.Eq_ a} =>
    Coq.Program.Basics.compose (fun arg_69__ =>
                                 match arg_69__ with
                                   | p => Coq.Program.Basics.compose getAny (instance_Foldable_option_foldMap
                                                                     (Coq.Program.Basics.compose Data.Monoid.Mk_Any p))
                                 end) GHC.Base.op_zeze__.

Local Definition instance_Foldable_list_elem : forall {a},
                                                 forall `{GHC.Base.Eq_ a}, a -> list a -> bool :=
  fun {a} `{GHC.Base.Eq_ a} => GHC.List.elem.

Local Definition instance_Foldable_list_foldl : forall {b} {a},
                                                  (b -> a -> b) -> b -> list a -> b :=
  fun {b} {a} => GHC.Base.foldl.

Local Definition instance_Foldable_list_foldr' : forall {a} {b},
                                                   (a -> b -> b) -> b -> list a -> b :=
  fun {a} {b} =>
    fun arg_9__ arg_10__ arg_11__ =>
      match arg_9__ , arg_10__ , arg_11__ with
        | f , z0 , xs => let f' :=
                           fun arg_12__ arg_13__ arg_14__ =>
                             match arg_12__ , arg_13__ , arg_14__ with
                               | k , x , z => GHC.Base.op_zdzn__ k (f x z)
                             end in
                         instance_Foldable_list_foldl f' GHC.Base.id xs z0
      end.

Local Definition instance_Foldable_list_foldl' : forall {b} {a},
                                                   (b -> a -> b) -> b -> list a -> b :=
  fun {b} {a} => GHC.Base.foldl'.

Local Definition instance_Foldable_list_foldr : forall {a} {b},
                                                  (a -> b -> b) -> b -> list a -> b :=
  fun {a} {b} => GHC.Base.foldr.

Local Definition instance_Foldable_list_foldMap : forall {m} {a},
                                                    forall `{GHC.Base.Monoid m}, (a -> m) -> list a -> m :=
  fun {m} {a} `{GHC.Base.Monoid m} =>
    fun arg_1__ =>
      match arg_1__ with
        | f => instance_Foldable_list_foldr (Coq.Program.Basics.compose GHC.Base.mappend
                                                                        f) GHC.Base.mempty
      end.

Local Definition instance_Foldable_list_fold : forall {m},
                                                 forall `{GHC.Base.Monoid m}, list m -> m :=
  fun {m} `{GHC.Base.Monoid m} => instance_Foldable_list_foldMap GHC.Base.id.

Local Definition instance_Foldable_list_length : forall {a},
                                                   list a -> GHC.Num.Int :=
  fun {a} => GHC.List.length.

Local Definition instance_Foldable_list_null : forall {a}, list a -> bool :=
  fun {a} => GHC.List.null.

Local Definition instance_Foldable_list_product : forall {a},
                                                    forall `{GHC.Num.Num a}, list a -> a :=
  fun {a} `{GHC.Num.Num a} => GHC.List.product.

Local Definition instance_Foldable_list_sum : forall {a},
                                                forall `{GHC.Num.Num a}, list a -> a :=
  fun {a} `{GHC.Num.Num a} => GHC.List.sum.

Local Definition instance_Foldable_list_toList : forall {a}, list a -> list a :=
  fun {a} => GHC.Base.id.

Instance instance_Foldable_list : Foldable list := fun _ k =>
    k (Foldable__Dict_Build list (fun {a} `{GHC.Base.Eq_ a} =>
                              instance_Foldable_list_elem) (fun {m} `{GHC.Base.Monoid m} =>
                              instance_Foldable_list_fold) (fun {m} {a} `{GHC.Base.Monoid m} =>
                              instance_Foldable_list_foldMap) (fun {b} {a} => instance_Foldable_list_foldl)
                            (fun {b} {a} => instance_Foldable_list_foldl') (fun {a} {b} =>
                              instance_Foldable_list_foldr) (fun {a} {b} => instance_Foldable_list_foldr')
                            (fun {a} => instance_Foldable_list_length) (fun {a} =>
                              instance_Foldable_list_null) (fun {a} `{GHC.Num.Num a} =>
                              instance_Foldable_list_product) (fun {a} `{GHC.Num.Num a} =>
                              instance_Foldable_list_sum) (fun {a} => instance_Foldable_list_toList)).

Local Definition instance_Foldable__Data_Either_Either_a__foldMap {inst_a}
    : forall {m} {a},
        forall `{GHC.Base.Monoid m}, (a -> m) -> (Data.Either.Either inst_a) a -> m :=
  fun {m} {a} `{GHC.Base.Monoid m} =>
    fun arg_431__ arg_432__ =>
      match arg_431__ , arg_432__ with
        | _ , Data.Either.Mk_Left _ => GHC.Base.mempty
        | f , Data.Either.Mk_Right y => f y
      end.

Local Definition instance_Foldable__Data_Either_Either_a__foldl {inst_a}
    : forall {b} {a}, (b -> a -> b) -> b -> (Data.Either.Either inst_a) a -> b :=
  fun {b} {a} =>
    fun arg_19__ arg_20__ arg_21__ =>
      match arg_19__ , arg_20__ , arg_21__ with
        | f , z , t => appEndo (getDual
                               (instance_Foldable__Data_Either_Either_a__foldMap (Coq.Program.Basics.compose
                                                                                 Data.Monoid.Mk_Dual
                                                                                 (Coq.Program.Basics.compose
                                                                                 Data.Monoid.Mk_Endo (GHC.Base.flip f)))
                               t)) z
      end.

Local Definition instance_Foldable__Data_Either_Either_a__foldr' {inst_a}
    : forall {a} {b}, (a -> b -> b) -> b -> (Data.Either.Either inst_a) a -> b :=
  fun {a} {b} =>
    fun arg_9__ arg_10__ arg_11__ =>
      match arg_9__ , arg_10__ , arg_11__ with
        | f , z0 , xs => let f' :=
                           fun arg_12__ arg_13__ arg_14__ =>
                             match arg_12__ , arg_13__ , arg_14__ with
                               | k , x , z => GHC.Base.op_zdzn__ k (f x z)
                             end in
                         instance_Foldable__Data_Either_Either_a__foldl f' GHC.Base.id xs z0
      end.

Local Definition instance_Foldable__Data_Either_Either_a__fold {inst_a}
    : forall {m}, forall `{GHC.Base.Monoid m}, (Data.Either.Either inst_a) m -> m :=
  fun {m} `{GHC.Base.Monoid m} =>
    instance_Foldable__Data_Either_Either_a__foldMap GHC.Base.id.

Local Definition instance_Foldable__Data_Either_Either_a__elem {inst_a}
    : forall {a},
        forall `{GHC.Base.Eq_ a}, a -> (Data.Either.Either inst_a) a -> bool :=
  fun {a} `{GHC.Base.Eq_ a} =>
    Coq.Program.Basics.compose (fun arg_69__ =>
                                 match arg_69__ with
                                   | p => Coq.Program.Basics.compose getAny
                                                                     (instance_Foldable__Data_Either_Either_a__foldMap
                                                                     (Coq.Program.Basics.compose Data.Monoid.Mk_Any p))
                                 end) GHC.Base.op_zeze__.

Local Definition instance_Foldable__Data_Either_Either_a__foldr {inst_a}
    : forall {a} {b}, (a -> b -> b) -> b -> (Data.Either.Either inst_a) a -> b :=
  fun {a} {b} =>
    fun arg_435__ arg_436__ arg_437__ =>
      match arg_435__ , arg_436__ , arg_437__ with
        | _ , z , Data.Either.Mk_Left _ => z
        | f , z , Data.Either.Mk_Right y => f y z
      end.

Local Definition instance_Foldable__Data_Either_Either_a__toList {inst_a}
    : forall {a}, (Data.Either.Either inst_a) a -> list a :=
  fun {a} =>
    fun arg_54__ =>
      match arg_54__ with
        | t => GHC.Base.build (fun arg_55__ arg_56__ =>
                                match arg_55__ , arg_56__ with
                                  | c , n => instance_Foldable__Data_Either_Either_a__foldr c n t
                                end)
      end.

Local Definition instance_Foldable__Data_Either_Either_a__foldl' {inst_a}
    : forall {b} {a}, (b -> a -> b) -> b -> (Data.Either.Either inst_a) a -> b :=
  fun {b} {a} =>
    fun arg_24__ arg_25__ arg_26__ =>
      match arg_24__ , arg_25__ , arg_26__ with
        | f , z0 , xs => let f' :=
                           fun arg_27__ arg_28__ arg_29__ =>
                             match arg_27__ , arg_28__ , arg_29__ with
                               | x , k , z => GHC.Base.op_zdzn__ k (f z x)
                             end in
                         instance_Foldable__Data_Either_Either_a__foldr f' GHC.Base.id xs z0
      end.

Local Definition instance_Foldable__Data_Either_Either_a__length {inst_a}
    : forall {a}, (Data.Either.Either inst_a) a -> GHC.Num.Int :=
  fun {a} =>
    fun arg_440__ =>
      match arg_440__ with
        | Data.Either.Mk_Left _ => GHC.Num.fromInteger 0
        | Data.Either.Mk_Right _ => GHC.Num.fromInteger 1
      end.

Local Definition instance_Foldable__Data_Either_Either_a__null {inst_a}
    : forall {a}, (Data.Either.Either inst_a) a -> bool :=
  fun {a} => Data.Either.isLeft.

Local Definition instance_Foldable__GHC_Tuple_pair_type_a__foldMap {inst_a}
    : forall {m} {a},
        forall `{GHC.Base.Monoid m}, (a -> m) -> (GHC.Tuple.pair_type inst_a) a -> m :=
  fun {m} {a} `{GHC.Base.Monoid m} =>
    fun arg_422__ arg_423__ =>
      match arg_422__ , arg_423__ with
        | f , pair _ y => f y
      end.

Local Definition instance_Foldable__GHC_Tuple_pair_type_a__foldl {inst_a}
    : forall {b} {a}, (b -> a -> b) -> b -> (GHC.Tuple.pair_type inst_a) a -> b :=
  fun {b} {a} =>
    fun arg_19__ arg_20__ arg_21__ =>
      match arg_19__ , arg_20__ , arg_21__ with
        | f , z , t => appEndo (getDual
                               (instance_Foldable__GHC_Tuple_pair_type_a__foldMap (Coq.Program.Basics.compose
                                                                                  Data.Monoid.Mk_Dual
                                                                                  (Coq.Program.Basics.compose
                                                                                  Data.Monoid.Mk_Endo (GHC.Base.flip
                                                                                  f))) t)) z
      end.

Local Definition instance_Foldable__GHC_Tuple_pair_type_a__foldr' {inst_a}
    : forall {a} {b}, (a -> b -> b) -> b -> (GHC.Tuple.pair_type inst_a) a -> b :=
  fun {a} {b} =>
    fun arg_9__ arg_10__ arg_11__ =>
      match arg_9__ , arg_10__ , arg_11__ with
        | f , z0 , xs => let f' :=
                           fun arg_12__ arg_13__ arg_14__ =>
                             match arg_12__ , arg_13__ , arg_14__ with
                               | k , x , z => GHC.Base.op_zdzn__ k (f x z)
                             end in
                         instance_Foldable__GHC_Tuple_pair_type_a__foldl f' GHC.Base.id xs z0
      end.

Local Definition instance_Foldable__GHC_Tuple_pair_type_a__fold {inst_a}
    : forall {m},
        forall `{GHC.Base.Monoid m}, (GHC.Tuple.pair_type inst_a) m -> m :=
  fun {m} `{GHC.Base.Monoid m} =>
    instance_Foldable__GHC_Tuple_pair_type_a__foldMap GHC.Base.id.

Local Definition instance_Foldable__GHC_Tuple_pair_type_a__elem {inst_a}
    : forall {a},
        forall `{GHC.Base.Eq_ a}, a -> (GHC.Tuple.pair_type inst_a) a -> bool :=
  fun {a} `{GHC.Base.Eq_ a} =>
    Coq.Program.Basics.compose (fun arg_69__ =>
                                 match arg_69__ with
                                   | p => Coq.Program.Basics.compose getAny
                                                                     (instance_Foldable__GHC_Tuple_pair_type_a__foldMap
                                                                     (Coq.Program.Basics.compose Data.Monoid.Mk_Any p))
                                 end) GHC.Base.op_zeze__.

Local Definition instance_Foldable__GHC_Tuple_pair_type_a__foldr {inst_a}
    : forall {a} {b}, (a -> b -> b) -> b -> (GHC.Tuple.pair_type inst_a) a -> b :=
  fun {a} {b} =>
    fun arg_426__ arg_427__ arg_428__ =>
      match arg_426__ , arg_427__ , arg_428__ with
        | f , z , pair _ y => f y z
      end.

Local Definition instance_Foldable__GHC_Tuple_pair_type_a__null {inst_a}
    : forall {a}, (GHC.Tuple.pair_type inst_a) a -> bool :=
  fun {a} =>
    instance_Foldable__GHC_Tuple_pair_type_a__foldr (fun arg_61__ arg_62__ => false)
    true.

Local Definition instance_Foldable__GHC_Tuple_pair_type_a__toList {inst_a}
    : forall {a}, (GHC.Tuple.pair_type inst_a) a -> list a :=
  fun {a} =>
    fun arg_54__ =>
      match arg_54__ with
        | t => GHC.Base.build (fun arg_55__ arg_56__ =>
                                match arg_55__ , arg_56__ with
                                  | c , n => instance_Foldable__GHC_Tuple_pair_type_a__foldr c n t
                                end)
      end.

Local Definition instance_Foldable__GHC_Tuple_pair_type_a__foldl' {inst_a}
    : forall {b} {a}, (b -> a -> b) -> b -> (GHC.Tuple.pair_type inst_a) a -> b :=
  fun {b} {a} =>
    fun arg_24__ arg_25__ arg_26__ =>
      match arg_24__ , arg_25__ , arg_26__ with
        | f , z0 , xs => let f' :=
                           fun arg_27__ arg_28__ arg_29__ =>
                             match arg_27__ , arg_28__ , arg_29__ with
                               | x , k , z => GHC.Base.op_zdzn__ k (f z x)
                             end in
                         instance_Foldable__GHC_Tuple_pair_type_a__foldr f' GHC.Base.id xs z0
      end.

Local Definition instance_Foldable__GHC_Tuple_pair_type_a__length {inst_a}
    : forall {a}, (GHC.Tuple.pair_type inst_a) a -> GHC.Num.Int :=
  fun {a} =>
    instance_Foldable__GHC_Tuple_pair_type_a__foldl' (fun arg_64__ arg_65__ =>
                                                       match arg_64__ , arg_65__ with
                                                         | c , _ => GHC.Num.op_zp__ c (GHC.Num.fromInteger 1)
                                                       end) (GHC.Num.fromInteger 0).

(* Skipping instance instance_Foldable__GHC_Arr_Array_i_ *)

Local Definition instance_Foldable_Data_Proxy_Proxy_elem : forall {a},
                                                             forall `{GHC.Base.Eq_ a},
                                                               a -> Data.Proxy.Proxy a -> bool :=
  fun {a} `{GHC.Base.Eq_ a} => fun arg_411__ arg_412__ => false.

Local Definition instance_Foldable_Data_Proxy_Proxy_fold : forall {m},
                                                             forall `{GHC.Base.Monoid m}, Data.Proxy.Proxy m -> m :=
  fun {m} `{GHC.Base.Monoid m} => fun arg_390__ => GHC.Base.mempty.

Local Definition instance_Foldable_Data_Proxy_Proxy_foldMap : forall {m} {a},
                                                                forall `{GHC.Base.Monoid m},
                                                                  (a -> m) -> Data.Proxy.Proxy a -> m :=
  fun {m} {a} `{GHC.Base.Monoid m} => fun arg_388__ arg_389__ => GHC.Base.mempty.

Local Definition instance_Foldable_Data_Proxy_Proxy_foldl : forall {b} {a},
                                                              (b -> a -> b) -> b -> Data.Proxy.Proxy a -> b :=
  fun {b} {a} =>
    fun arg_395__ arg_396__ arg_397__ =>
      match arg_395__ , arg_396__ , arg_397__ with
        | _ , z , _ => z
      end.

Local Definition instance_Foldable_Data_Proxy_Proxy_foldr' : forall {a} {b},
                                                               (a -> b -> b) -> b -> Data.Proxy.Proxy a -> b :=
  fun {a} {b} =>
    fun arg_9__ arg_10__ arg_11__ =>
      match arg_9__ , arg_10__ , arg_11__ with
        | f , z0 , xs => let f' :=
                           fun arg_12__ arg_13__ arg_14__ =>
                             match arg_12__ , arg_13__ , arg_14__ with
                               | k , x , z => GHC.Base.op_zdzn__ k (f x z)
                             end in
                         instance_Foldable_Data_Proxy_Proxy_foldl f' GHC.Base.id xs z0
      end.

Local Definition instance_Foldable_Data_Proxy_Proxy_foldr : forall {a} {b},
                                                              (a -> b -> b) -> b -> Data.Proxy.Proxy a -> b :=
  fun {a} {b} =>
    fun arg_391__ arg_392__ arg_393__ =>
      match arg_391__ , arg_392__ , arg_393__ with
        | _ , z , _ => z
      end.

Local Definition instance_Foldable_Data_Proxy_Proxy_toList : forall {a},
                                                               Data.Proxy.Proxy a -> list a :=
  fun {a} =>
    fun arg_54__ =>
      match arg_54__ with
        | t => GHC.Base.build (fun arg_55__ arg_56__ =>
                                match arg_55__ , arg_56__ with
                                  | c , n => instance_Foldable_Data_Proxy_Proxy_foldr c n t
                                end)
      end.

Local Definition instance_Foldable_Data_Proxy_Proxy_foldl' : forall {b} {a},
                                                               (b -> a -> b) -> b -> Data.Proxy.Proxy a -> b :=
  fun {b} {a} =>
    fun arg_24__ arg_25__ arg_26__ =>
      match arg_24__ , arg_25__ , arg_26__ with
        | f , z0 , xs => let f' :=
                           fun arg_27__ arg_28__ arg_29__ =>
                             match arg_27__ , arg_28__ , arg_29__ with
                               | x , k , z => GHC.Base.op_zdzn__ k (f z x)
                             end in
                         instance_Foldable_Data_Proxy_Proxy_foldr f' GHC.Base.id xs z0
      end.

Local Definition instance_Foldable_Data_Proxy_Proxy_length : forall {a},
                                                               Data.Proxy.Proxy a -> GHC.Num.Int :=
  fun {a} => fun arg_407__ => GHC.Num.fromInteger 0.

Local Definition instance_Foldable_Data_Proxy_Proxy_null : forall {a},
                                                             Data.Proxy.Proxy a -> bool :=
  fun {a} => fun arg_410__ => true.

Local Definition instance_Foldable_Data_Proxy_Proxy_product : forall {a},
                                                                forall `{GHC.Num.Num a}, Data.Proxy.Proxy a -> a :=
  fun {a} `{GHC.Num.Num a} => fun arg_416__ => GHC.Num.fromInteger 1.

Local Definition instance_Foldable_Data_Proxy_Proxy_sum : forall {a},
                                                            forall `{GHC.Num.Num a}, Data.Proxy.Proxy a -> a :=
  fun {a} `{GHC.Num.Num a} => fun arg_413__ => GHC.Num.fromInteger 0.

Instance instance_Foldable_Data_Proxy_Proxy : Foldable Data.Proxy.Proxy := fun _
                                                                               k =>
    k (Foldable__Dict_Build Data.Proxy.Proxy (fun {a} `{GHC.Base.Eq_ a} =>
                              instance_Foldable_Data_Proxy_Proxy_elem) (fun {m} `{GHC.Base.Monoid m} =>
                              instance_Foldable_Data_Proxy_Proxy_fold) (fun {m} {a} `{GHC.Base.Monoid m} =>
                              instance_Foldable_Data_Proxy_Proxy_foldMap) (fun {b} {a} =>
                              instance_Foldable_Data_Proxy_Proxy_foldl) (fun {b} {a} =>
                              instance_Foldable_Data_Proxy_Proxy_foldl') (fun {a} {b} =>
                              instance_Foldable_Data_Proxy_Proxy_foldr) (fun {a} {b} =>
                              instance_Foldable_Data_Proxy_Proxy_foldr') (fun {a} =>
                              instance_Foldable_Data_Proxy_Proxy_length) (fun {a} =>
                              instance_Foldable_Data_Proxy_Proxy_null) (fun {a} `{GHC.Num.Num a} =>
                              instance_Foldable_Data_Proxy_Proxy_product) (fun {a} `{GHC.Num.Num a} =>
                              instance_Foldable_Data_Proxy_Proxy_sum) (fun {a} =>
                              instance_Foldable_Data_Proxy_Proxy_toList)).

(* Skipping instance instance_Foldable_Data_Monoid_Dual *)

(* Skipping instance instance_Foldable_Data_Monoid_Sum *)

(* Skipping instance instance_Foldable_Data_Monoid_Product *)

(* Skipping instance instance_Foldable_Data_Monoid_First *)

(* Skipping instance instance_Foldable_Data_Monoid_Last *)

(* Skipping instance
   instance_forall___GHC_Base_Ord_a___GHC_Base_Monoid__Max_a_ *)

(* Skipping instance
   instance_forall___GHC_Base_Ord_a___GHC_Base_Monoid__Min_a_ *)

(* Skipping instance instance_Foldable_GHC_Generics_U1 *)

(* Skipping instance instance_Foldable_GHC_Generics_V1 *)

(* Skipping instance instance_Foldable_GHC_Generics_Par1 *)

(* Skipping instance
   instance_forall___Foldable_f___Foldable__GHC_Generics_Rec1_f_ *)

(* Skipping instance instance_Foldable__GHC_Generics_K1_i_c_ *)

(* Skipping instance
   instance_forall___Foldable_f___Foldable__GHC_Generics_M1_i_c_f_ *)

(* Skipping instance
   instance_forall___Foldable_f____Foldable_g___Foldable__GHC_Generics_____f_g_ *)

(* Skipping instance
   instance_forall___Foldable_f____Foldable_g___Foldable__GHC_Generics_____f_g_ *)

(* Skipping instance
   instance_forall___Foldable_f____Foldable_g___Foldable__GHC_Generics_____f_g_ *)

(* Skipping instance instance_Foldable__GHC_Generics_URec__GHC_Ptr_Ptr_unit__ *)

(* Skipping instance instance_Foldable__GHC_Generics_URec_GHC_Char_Char_ *)

(* Skipping instance instance_Foldable__GHC_Generics_URec_GHC_Types_Double_ *)

(* Skipping instance instance_Foldable__GHC_Generics_URec_GHC_Types_Float_ *)

(* Skipping instance instance_Foldable__GHC_Generics_URec_GHC_Num_Int_ *)

(* Skipping instance instance_Foldable__GHC_Generics_URec_GHC_Num_Word_ *)

Definition asum {t} {f} {a} `{Foldable t} `{GHC.Base.Alternative f} : t (f
                                                                        a) -> f a :=
  foldr GHC.Base.op_zlzbzg__ GHC.Base.empty.

Definition msum {t} {m} {a} `{Foldable t} `{GHC.Base.MonadPlus m} : t (m a) -> m
                                                                    a :=
  asum.

Definition concatMap {t} {a} {b} `{Foldable t} : (a -> list b) -> t a -> list
                                                 b :=
  fun arg_98__ arg_99__ =>
    match arg_98__ , arg_99__ with
      | f , xs => GHC.Base.build (fun arg_100__ arg_101__ =>
                                   match arg_100__ , arg_101__ with
                                     | c , n => foldr (fun arg_102__ arg_103__ =>
                                                        match arg_102__ , arg_103__ with
                                                          | x , b => foldr c b (f x)
                                                        end) n xs
                                   end)
    end.

Definition concat {t} {a} `{Foldable t} : t (list a) -> list a :=
  fun arg_110__ =>
    match arg_110__ with
      | xs => GHC.Base.build (fun arg_111__ arg_112__ =>
                               match arg_111__ , arg_112__ with
                                 | c , n => foldr (fun arg_113__ arg_114__ =>
                                                    match arg_113__ , arg_114__ with
                                                      | x , y => foldr c y x
                                                    end) n xs
                               end)
    end.

Definition find {t} {a} `{Foldable t} : (a -> bool) -> t a -> option a :=
  fun arg_81__ =>
    match arg_81__ with
      | p => Coq.Program.Basics.compose getFirst (foldMap (fun arg_82__ =>
                                                            match arg_82__ with
                                                              | x => Data.Monoid.Mk_First (if p x : bool
                                                                                          then Some x
                                                                                          else None)
                                                            end))
    end.

Definition foldlM {t} {m} {b} {a} `{Foldable t} `{GHC.Base.Monad m}
    : (b -> a -> m b) -> b -> t a -> m b :=
  fun arg_132__ arg_133__ arg_134__ =>
    match arg_132__ , arg_133__ , arg_134__ with
      | f , z0 , xs => let f' :=
                         fun arg_135__ arg_136__ arg_137__ =>
                           match arg_135__ , arg_136__ , arg_137__ with
                             | x , k , z => GHC.Base.op_zgzgze__ (f z x) k
                           end in
                       foldr f' GHC.Base.return_ xs z0
    end.

Definition foldrM {t} {m} {a} {b} `{Foldable t} `{GHC.Base.Monad m}
    : (a -> b -> m b) -> b -> t a -> m b :=
  fun arg_142__ arg_143__ arg_144__ =>
    match arg_142__ , arg_143__ , arg_144__ with
      | f , z0 , xs => let f' :=
                         fun arg_145__ arg_146__ arg_147__ =>
                           match arg_145__ , arg_146__ , arg_147__ with
                             | k , x , z => GHC.Base.op_zgzgze__ (f x z) k
                           end in
                       foldl f' GHC.Base.return_ xs z0
    end.

Definition hash_compose {a} {b} {c} :=
  (@Coq.Program.Basics.compose a b c).

Definition or {t} `{Foldable t} : t bool -> bool :=
  hash_compose getAny (foldMap Data.Monoid.Mk_Any).

Definition any {t} {a} `{Foldable t} : (a -> bool) -> t a -> bool :=
  fun arg_93__ =>
    match arg_93__ with
      | p => hash_compose getAny (foldMap (hash_compose Data.Monoid.Mk_Any p))
    end.

Definition and {t} `{Foldable t} : t bool -> bool :=
  hash_compose getAll (foldMap Data.Monoid.Mk_All).

Definition all {t} {a} `{Foldable t} : (a -> bool) -> t a -> bool :=
  fun arg_90__ =>
    match arg_90__ with
      | p => hash_compose getAll (foldMap (hash_compose Data.Monoid.Mk_All p))
    end.

Local Definition instance_Foldable__GHC_Tuple_pair_type_a__product {inst_a}
    : forall {a}, forall `{GHC.Num.Num a}, (GHC.Tuple.pair_type inst_a) a -> a :=
  fun {a} `{GHC.Num.Num a} =>
    hash_compose getProduct (instance_Foldable__GHC_Tuple_pair_type_a__foldMap
                 Data.Monoid.Mk_Product).

Local Definition instance_Foldable__GHC_Tuple_pair_type_a__sum {inst_a}
    : forall {a}, forall `{GHC.Num.Num a}, (GHC.Tuple.pair_type inst_a) a -> a :=
  fun {a} `{GHC.Num.Num a} =>
    hash_compose getSum (instance_Foldable__GHC_Tuple_pair_type_a__foldMap
                 Data.Monoid.Mk_Sum).

Instance instance_Foldable__GHC_Tuple_pair_type_a_ {a} : Foldable
                                                         (GHC.Tuple.pair_type a) := fun _ k =>
    k (Foldable__Dict_Build (GHC.Tuple.pair_type a) (fun {a} `{GHC.Base.Eq_ a} =>
                              instance_Foldable__GHC_Tuple_pair_type_a__elem) (fun {m} `{GHC.Base.Monoid m} =>
                              instance_Foldable__GHC_Tuple_pair_type_a__fold) (fun {m}
                                                                                   {a}
                                                                                   `{GHC.Base.Monoid m} =>
                              instance_Foldable__GHC_Tuple_pair_type_a__foldMap) (fun {b} {a} =>
                              instance_Foldable__GHC_Tuple_pair_type_a__foldl) (fun {b} {a} =>
                              instance_Foldable__GHC_Tuple_pair_type_a__foldl') (fun {a} {b} =>
                              instance_Foldable__GHC_Tuple_pair_type_a__foldr) (fun {a} {b} =>
                              instance_Foldable__GHC_Tuple_pair_type_a__foldr') (fun {a} =>
                              instance_Foldable__GHC_Tuple_pair_type_a__length) (fun {a} =>
                              instance_Foldable__GHC_Tuple_pair_type_a__null) (fun {a} `{GHC.Num.Num a} =>
                              instance_Foldable__GHC_Tuple_pair_type_a__product) (fun {a} `{GHC.Num.Num a} =>
                              instance_Foldable__GHC_Tuple_pair_type_a__sum) (fun {a} =>
                              instance_Foldable__GHC_Tuple_pair_type_a__toList)).

Local Definition instance_Foldable__Data_Either_Either_a__product {inst_a}
    : forall {a}, forall `{GHC.Num.Num a}, (Data.Either.Either inst_a) a -> a :=
  fun {a} `{GHC.Num.Num a} =>
    hash_compose getProduct (instance_Foldable__Data_Either_Either_a__foldMap
                 Data.Monoid.Mk_Product).

Local Definition instance_Foldable__Data_Either_Either_a__sum {inst_a}
    : forall {a}, forall `{GHC.Num.Num a}, (Data.Either.Either inst_a) a -> a :=
  fun {a} `{GHC.Num.Num a} =>
    hash_compose getSum (instance_Foldable__Data_Either_Either_a__foldMap
                 Data.Monoid.Mk_Sum).

Instance instance_Foldable__Data_Either_Either_a_ {a} : Foldable
                                                        (Data.Either.Either a) := fun _ k =>
    k (Foldable__Dict_Build (Data.Either.Either a) (fun {a} `{GHC.Base.Eq_ a} =>
                              instance_Foldable__Data_Either_Either_a__elem) (fun {m} `{GHC.Base.Monoid m} =>
                              instance_Foldable__Data_Either_Either_a__fold) (fun {m}
                                                                                  {a}
                                                                                  `{GHC.Base.Monoid m} =>
                              instance_Foldable__Data_Either_Either_a__foldMap) (fun {b} {a} =>
                              instance_Foldable__Data_Either_Either_a__foldl) (fun {b} {a} =>
                              instance_Foldable__Data_Either_Either_a__foldl') (fun {a} {b} =>
                              instance_Foldable__Data_Either_Either_a__foldr) (fun {a} {b} =>
                              instance_Foldable__Data_Either_Either_a__foldr') (fun {a} =>
                              instance_Foldable__Data_Either_Either_a__length) (fun {a} =>
                              instance_Foldable__Data_Either_Either_a__null) (fun {a} `{GHC.Num.Num a} =>
                              instance_Foldable__Data_Either_Either_a__product) (fun {a} `{GHC.Num.Num a} =>
                              instance_Foldable__Data_Either_Either_a__sum) (fun {a} =>
                              instance_Foldable__Data_Either_Either_a__toList)).

Local Definition instance_Foldable_option_product : forall {a},
                                                      forall `{GHC.Num.Num a}, option a -> a :=
  fun {a} `{GHC.Num.Num a} =>
    hash_compose getProduct (instance_Foldable_option_foldMap
                 Data.Monoid.Mk_Product).

Local Definition instance_Foldable_option_sum : forall {a},
                                                  forall `{GHC.Num.Num a}, option a -> a :=
  fun {a} `{GHC.Num.Num a} =>
    hash_compose getSum (instance_Foldable_option_foldMap Data.Monoid.Mk_Sum).

Instance instance_Foldable_option : Foldable option := fun _ k =>
    k (Foldable__Dict_Build option (fun {a} `{GHC.Base.Eq_ a} =>
                              instance_Foldable_option_elem) (fun {m} `{GHC.Base.Monoid m} =>
                              instance_Foldable_option_fold) (fun {m} {a} `{GHC.Base.Monoid m} =>
                              instance_Foldable_option_foldMap) (fun {b} {a} =>
                              instance_Foldable_option_foldl) (fun {b} {a} => instance_Foldable_option_foldl')
                            (fun {a} {b} => instance_Foldable_option_foldr) (fun {a} {b} =>
                              instance_Foldable_option_foldr') (fun {a} => instance_Foldable_option_length)
                            (fun {a} => instance_Foldable_option_null) (fun {a} `{GHC.Num.Num a} =>
                              instance_Foldable_option_product) (fun {a} `{GHC.Num.Num a} =>
                              instance_Foldable_option_sum) (fun {a} => instance_Foldable_option_toList)).

Definition mapM_ {t} {m} {a} {b} `{Foldable t} `{GHC.Base.Monad m} : (a -> m
                                                                     b) -> t a -> m unit :=
  fun arg_124__ =>
    match arg_124__ with
      | f => foldr (Coq.Program.Basics.compose GHC.Base.op_zgzg__ f) (GHC.Base.return_
                                                                     tt)
    end.

Definition forM_ {t} {m} {a} {b} `{Foldable t} `{GHC.Base.Monad m} : t
                                                                     a -> (a -> m b) -> m unit :=
  GHC.Base.flip mapM_.

Definition notElem {t} {a} `{Foldable t} `{GHC.Base.Eq_ a} : a -> t a -> bool :=
  fun arg_87__ =>
    match arg_87__ with
      | x => Coq.Program.Basics.compose negb (elem x)
    end.

Definition sequenceA_ {t} {f} {a} `{Foldable t} `{GHC.Base.Applicative f} : t (f
                                                                              a) -> f unit :=
  foldr GHC.Base.op_ztzg__ (GHC.Base.pure tt).

Definition sequence_ {t} {m} {a} `{Foldable t} `{GHC.Base.Monad m} : t (m
                                                                       a) -> m unit :=
  foldr GHC.Base.op_zgzg__ (GHC.Base.return_ tt).

Definition traverse_ {t} {f} {a} {b} `{Foldable t} `{GHC.Base.Applicative f}
    : (a -> f b) -> t a -> f unit :=
  fun arg_128__ =>
    match arg_128__ with
      | f => foldr (Coq.Program.Basics.compose GHC.Base.op_ztzg__ f) (GHC.Base.pure
                                                                     tt)
    end.

Definition for__ {t} {f} {a} {b} `{Foldable t} `{GHC.Base.Applicative f} : t
                                                                           a -> (a -> f b) -> f unit :=
  GHC.Base.flip traverse_.

(* Unbound variables:
     Coq.Program.Basics.compose Data.Either.Either Data.Either.Mk_Left
     Data.Either.Mk_Right Data.Either.isLeft Data.Monoid.Mk_All Data.Monoid.Mk_Any
     Data.Monoid.Mk_Dual Data.Monoid.Mk_Endo Data.Monoid.Mk_First
     Data.Monoid.Mk_Product Data.Monoid.Mk_Sum Data.Proxy.Proxy GHC.Base.Alternative
     GHC.Base.Applicative GHC.Base.Eq_ GHC.Base.Monad GHC.Base.MonadPlus
     GHC.Base.Monoid GHC.Base.build GHC.Base.empty GHC.Base.flip GHC.Base.foldl
     GHC.Base.foldl' GHC.Base.foldr GHC.Base.id GHC.Base.mappend GHC.Base.mempty
     GHC.Base.op_zdzn__ GHC.Base.op_zeze__ GHC.Base.op_zgzg__ GHC.Base.op_zgzgze__
     GHC.Base.op_zlzbzg__ GHC.Base.op_ztzg__ GHC.Base.pure GHC.Base.return_
     GHC.List.elem GHC.List.length GHC.List.null GHC.List.product GHC.List.sum
     GHC.Num.Int GHC.Num.Num GHC.Num.op_zp__ GHC.Tuple.pair_type None Some appEndo
     bool false getAll getAny getDual getFirst getProduct getSum list negb option
     pair true tt unit
*)
