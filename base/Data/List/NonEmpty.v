(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Coq.Program.Tactics.
Require Coq.Program.Wf.

(* Preamble *)

Open Scope type_scope.

(* Converted imports: *)

Require Coq.Init.Datatypes.
Require Coq.Program.Basics.
Require Data.Foldable.
Require Data.Functor.
Require Data.Monoid.
Require Data.OldList.
Require Data.Ord.
Require Data.Traversable.
Require Data.Tuple.
Require GHC.Base.
Require GHC.List.
Require GHC.Num.

(* Converted type declarations: *)

Inductive NonEmpty a : Type := NEcons : a -> list a -> NonEmpty a.

Arguments NEcons {_} _ _.
(* Converted value declarations: *)

(* Translating `instance forall {a}, GHC.Exts.IsList
   (Data.List.NonEmpty.NonEmpty a)' failed: OOPS! Cannot find information for class
   Qualified "GHC.Exts" "IsList" unsupported *)

(* Translating `instance Control.Monad.Fix.MonadFix Data.List.NonEmpty.NonEmpty'
   failed: OOPS! Cannot find information for class Qualified "Control.Monad.Fix"
   "MonadFix" unsupported *)

(* Translating `instance Control.Monad.Zip.MonadZip Data.List.NonEmpty.NonEmpty'
   failed: OOPS! Cannot find information for class Qualified "Control.Monad.Zip"
   "MonadZip" unsupported *)

Local Definition instance_GHC_Base_Functor_Data_List_NonEmpty_NonEmpty_fmap
    : forall {a} {b}, (a -> b) -> NonEmpty a -> NonEmpty b :=
  fun {a} {b} =>
    fun arg_155__ arg_156__ =>
      match arg_155__ , arg_156__ with
        | f , NEcons a as_ => NEcons (f a) (GHC.Base.fmap f as_)
      end.

Local Definition instance_GHC_Base_Functor_Data_List_NonEmpty_NonEmpty_op_zlzd__
    : forall {a} {b}, a -> NonEmpty b -> NonEmpty a :=
  fun {a} {b} f x =>
    match x with
      | NEcons a as_ => NEcons f (GHC.Base.op_zlzd__ f as_)
    end.

Program Instance instance_GHC_Base_Functor_Data_List_NonEmpty_NonEmpty
  : GHC.Base.Functor NonEmpty := fun _ k =>
    k {|GHC.Base.op_zlzd____ := fun {a} {b} =>
        instance_GHC_Base_Functor_Data_List_NonEmpty_NonEmpty_op_zlzd__ ;
      GHC.Base.fmap__ := fun {a} {b} =>
        instance_GHC_Base_Functor_Data_List_NonEmpty_NonEmpty_fmap |}.

Local Definition instance_GHC_Base_Applicative_Data_List_NonEmpty_NonEmpty_pure
    : forall {a}, a -> NonEmpty a :=
  fun {a} => fun a => NEcons a nil.

Local Definition instance_Data_Traversable_Traversable_Data_List_NonEmpty_NonEmpty_traverse
    : forall {f} {a} {b} {H : GHC.Base.Functor f} {_ : GHC.Base.Applicative f},
        (a -> f b) -> NonEmpty a -> f (NonEmpty b) :=
  fun {f} {a} {b} {_} {_} =>
    fun arg_144__ arg_145__ =>
      match arg_144__ , arg_145__ with
        | f , NEcons a as_ => GHC.Base.op_zlztzg__ (Data.Functor.op_zlzdzg__ NEcons (f
                                                                             a)) (Data.Traversable.traverse f as_)
      end.

Local Definition instance_Data_Traversable_Traversable_Data_List_NonEmpty_NonEmpty_sequenceA
    : forall {f} {a},
        forall `{GHC.Base.Applicative f}, NonEmpty (f a) -> f (NonEmpty a) :=
  fun {f} {a} `{GHC.Base.Applicative f} =>
    instance_Data_Traversable_Traversable_Data_List_NonEmpty_NonEmpty_traverse
    GHC.Base.id.

Local Definition instance_Data_Traversable_Traversable_Data_List_NonEmpty_NonEmpty_sequence
    : forall {m} {a},
        forall `{GHC.Base.Monad m}, NonEmpty (m a) -> m (NonEmpty a) :=
  fun {m} {a} `{GHC.Base.Monad m} =>
    instance_Data_Traversable_Traversable_Data_List_NonEmpty_NonEmpty_sequenceA.

Local Definition instance_Data_Traversable_Traversable_Data_List_NonEmpty_NonEmpty_mapM
    : forall {m} {a} {b},
        forall `{GHC.Base.Monad m}, (a -> m b) -> NonEmpty a -> m (NonEmpty b) :=
  fun {m} {a} {b} `{GHC.Base.Monad m} =>
    instance_Data_Traversable_Traversable_Data_List_NonEmpty_NonEmpty_traverse.

Local Definition instance_Data_Foldable_Foldable_Data_List_NonEmpty_NonEmpty_fold
    : forall {m} {_ : GHC.Base.Monoid m}, NonEmpty m -> m :=
  fun {m} {_} =>
    fun arg_141__ =>
      match arg_141__ with
        | NEcons m ms => GHC.Base.mappend m (Data.Foldable.fold ms)
      end.

Local Definition instance_Data_Foldable_Foldable_Data_List_NonEmpty_NonEmpty_foldMap
    : forall {m} {a} {_ : GHC.Base.Monoid m}, (a -> m) -> NonEmpty a -> m :=
  fun {m} {a} {_} =>
    fun f arg_141__ =>
      match arg_141__ with
        | NEcons m ms => GHC.Base.mappend (f m) (Data.Foldable.foldMap f ms)
      end.

Local Definition instance_Data_Foldable_Foldable_Data_List_NonEmpty_NonEmpty_product
    : forall {a}, forall `{GHC.Num.Num a}, NonEmpty a -> a :=
  fun {a} `{GHC.Num.Num a} =>
    Data.Foldable.hash_compose Data.Monoid.getProduct
                               (instance_Data_Foldable_Foldable_Data_List_NonEmpty_NonEmpty_foldMap
                               Data.Monoid.Mk_Product).

Local Definition instance_Data_Foldable_Foldable_Data_List_NonEmpty_NonEmpty_sum
    : forall {a}, forall `{GHC.Num.Num a}, NonEmpty a -> a :=
  fun {a} `{GHC.Num.Num a} =>
    Data.Foldable.hash_compose Data.Monoid.getSum
                               (instance_Data_Foldable_Foldable_Data_List_NonEmpty_NonEmpty_foldMap
                               Data.Monoid.Mk_Sum).

Local Definition instance_Data_Foldable_Foldable_Data_List_NonEmpty_NonEmpty_elem
    : forall {a}, forall `{_ : GHC.Base.Eq_ a}, a -> NonEmpty a -> bool :=
  fun {a} `{_ : GHC.Base.Eq_ a} =>
    Coq.Program.Basics.compose (fun p =>
                                 Data.Foldable.hash_compose Data.Monoid.getAny
                                                            (instance_Data_Foldable_Foldable_Data_List_NonEmpty_NonEmpty_foldMap
                                                            (Data.Foldable.hash_compose Data.Monoid.Mk_Any p)))
                               GHC.Base.op_zeze__.

Local Definition instance_Data_Foldable_Foldable_Data_List_NonEmpty_NonEmpty_foldl
    : forall {b} {a}, (b -> a -> b) -> b -> NonEmpty a -> b :=
  fun {b} {a} =>
    fun arg_128__ arg_129__ arg_130__ =>
      match arg_128__ , arg_129__ , arg_130__ with
        | f , z , NEcons a as_ => Data.Foldable.foldl f (f z a) as_
      end.

Local Definition instance_Data_Foldable_Foldable_Data_List_NonEmpty_NonEmpty_foldr'
    : forall {a} {b}, (a -> b -> b) -> b -> NonEmpty a -> b :=
  fun {a} {b} =>
    fun arg_9__ arg_10__ arg_11__ =>
      match arg_9__ , arg_10__ , arg_11__ with
        | f , z0 , xs => let f' :=
                           fun arg_12__ arg_13__ arg_14__ =>
                             match arg_12__ , arg_13__ , arg_14__ with
                               | k , x , z => GHC.Base.op_zdzn__ k (f x z)
                             end in
                         instance_Data_Foldable_Foldable_Data_List_NonEmpty_NonEmpty_foldl f' GHC.Base.id
                         xs z0
      end.

Local Definition instance_Data_Foldable_Foldable_Data_List_NonEmpty_NonEmpty_foldr
    : forall {a} {b}, (a -> b -> b) -> b -> NonEmpty a -> b :=
  fun {a} {b} =>
    fun arg_128__ arg_129__ arg_130__ =>
      match arg_128__ , arg_129__ , arg_130__ with
        | f , z , NEcons a as_ => f a (Data.Foldable.foldr f z as_)
      end.

Local Definition instance_Data_Foldable_Foldable_Data_List_NonEmpty_NonEmpty_null
    : forall {a}, NonEmpty a -> bool :=
  fun {a} =>
    instance_Data_Foldable_Foldable_Data_List_NonEmpty_NonEmpty_foldr (fun arg_61__
                                                                           arg_62__ =>
                                                                        false) true.

Local Definition instance_Data_Foldable_Foldable_Data_List_NonEmpty_NonEmpty_toList
    : forall {a}, NonEmpty a -> list a :=
  fun {a} =>
    fun arg_54__ =>
      match arg_54__ with
        | t => GHC.Base.build (fun arg_55__ arg_56__ =>
                                match arg_55__ , arg_56__ with
                                  | c , n => instance_Data_Foldable_Foldable_Data_List_NonEmpty_NonEmpty_foldr c n
                                             t
                                end)
      end.

Local Definition instance_GHC_Base_Monad_Data_List_NonEmpty_NonEmpty_op_zgzgze__
    : forall {a} {b}, NonEmpty a -> (a -> NonEmpty b) -> NonEmpty b :=
  fun {a} {b} =>
    fun arg_148__ arg_149__ =>
      match arg_148__ , arg_149__ with
        | NEcons a as_ , f => match f a with
                                | NEcons b bs => NEcons b (Coq.Init.Datatypes.app bs (GHC.Base.op_zgzgze__ as_
                                                                                                           (GHC.Base.op_z2218U__
                                                                                                           instance_Data_Foldable_Foldable_Data_List_NonEmpty_NonEmpty_toList
                                                                                                           f)))
                              end
      end.

Local Definition instance_Data_Foldable_Foldable_Data_List_NonEmpty_NonEmpty_foldl'
    : forall {b} {a}, (b -> a -> b) -> b -> NonEmpty a -> b :=
  fun {b} {a} =>
    fun arg_24__ arg_25__ arg_26__ =>
      match arg_24__ , arg_25__ , arg_26__ with
        | f , z0 , xs => let f' :=
                           fun arg_27__ arg_28__ arg_29__ =>
                             match arg_27__ , arg_28__ , arg_29__ with
                               | x , k , z => GHC.Base.op_zdzn__ k (f z x)
                             end in
                         instance_Data_Foldable_Foldable_Data_List_NonEmpty_NonEmpty_foldr f' GHC.Base.id
                         xs z0
      end.

Local Definition instance_Data_Foldable_Foldable_Data_List_NonEmpty_NonEmpty_length
    : forall {a}, NonEmpty a -> GHC.Num.Int :=
  fun {a} =>
    instance_Data_Foldable_Foldable_Data_List_NonEmpty_NonEmpty_foldl' (fun arg_64__
                                                                            arg_65__ =>
                                                                         match arg_64__ , arg_65__ with
                                                                           | c , _ => GHC.Num.op_zp__ c
                                                                                                      (GHC.Num.fromInteger
                                                                                                      1)
                                                                         end) (GHC.Num.fromInteger 0).

Program Instance instance_Data_Foldable_Foldable_Data_List_NonEmpty_NonEmpty
  : Data.Foldable.Foldable NonEmpty := fun _ k =>
    k {|Data.Foldable.elem__ := fun {a} `{GHC.Base.Eq_ a} =>
        instance_Data_Foldable_Foldable_Data_List_NonEmpty_NonEmpty_elem ;
      Data.Foldable.fold__ := fun {m} `{GHC.Base.Monoid m} =>
        instance_Data_Foldable_Foldable_Data_List_NonEmpty_NonEmpty_fold ;
      Data.Foldable.foldMap__ := fun {m} {a} `{GHC.Base.Monoid m} =>
        instance_Data_Foldable_Foldable_Data_List_NonEmpty_NonEmpty_foldMap ;
      Data.Foldable.foldl__ := fun {b} {a} =>
        instance_Data_Foldable_Foldable_Data_List_NonEmpty_NonEmpty_foldl ;
      Data.Foldable.foldl'__ := fun {b} {a} =>
        instance_Data_Foldable_Foldable_Data_List_NonEmpty_NonEmpty_foldl' ;
      Data.Foldable.foldr__ := fun {a} {b} =>
        instance_Data_Foldable_Foldable_Data_List_NonEmpty_NonEmpty_foldr ;
      Data.Foldable.foldr'__ := fun {a} {b} =>
        instance_Data_Foldable_Foldable_Data_List_NonEmpty_NonEmpty_foldr' ;
      Data.Foldable.length__ := fun {a} =>
        instance_Data_Foldable_Foldable_Data_List_NonEmpty_NonEmpty_length ;
      Data.Foldable.null__ := fun {a} =>
        instance_Data_Foldable_Foldable_Data_List_NonEmpty_NonEmpty_null ;
      Data.Foldable.product__ := fun {a} `{GHC.Num.Num a} =>
        instance_Data_Foldable_Foldable_Data_List_NonEmpty_NonEmpty_product ;
      Data.Foldable.sum__ := fun {a} `{GHC.Num.Num a} =>
        instance_Data_Foldable_Foldable_Data_List_NonEmpty_NonEmpty_sum ;
      Data.Foldable.toList__ := fun {a} =>
        instance_Data_Foldable_Foldable_Data_List_NonEmpty_NonEmpty_toList |}.

Program Instance instance_Data_Traversable_Traversable_Data_List_NonEmpty_NonEmpty
  : Data.Traversable.Traversable NonEmpty := fun _ k =>
    k {|Data.Traversable.mapM__ := fun {m} {a} {b} `{GHC.Base.Monad m} =>
        instance_Data_Traversable_Traversable_Data_List_NonEmpty_NonEmpty_mapM ;
      Data.Traversable.sequence__ := fun {m} {a} `{GHC.Base.Monad m} =>
        instance_Data_Traversable_Traversable_Data_List_NonEmpty_NonEmpty_sequence ;
      Data.Traversable.sequenceA__ := fun {f} {a} `{GHC.Base.Applicative f} =>
        instance_Data_Traversable_Traversable_Data_List_NonEmpty_NonEmpty_sequenceA ;
      Data.Traversable.traverse__ := fun {f} {a} {b} `{GHC.Base.Applicative f} =>
        instance_Data_Traversable_Traversable_Data_List_NonEmpty_NonEmpty_traverse |}.

(* Translating `instance GHC.Generics.Generic1 Data.List.NonEmpty.NonEmpty'
   failed: OOPS! Cannot find information for class Qualified "GHC.Generics"
   "Generic1" unsupported *)

(* Translating `instance forall {a}, GHC.Generics.Generic
   (Data.List.NonEmpty.NonEmpty a)' failed: OOPS! Cannot find information for class
   Qualified "GHC.Generics" "Generic" unsupported *)

(* Translating `instance forall {a}, forall `{Data.Data.Data a}, Data.Data.Data
   (Data.List.NonEmpty.NonEmpty a)' failed: OOPS! Cannot find information for class
   Qualified "Data.Data" "Data" unsupported *)

(* Translating `instance forall {a}, forall `{GHC.Read.Read a}, GHC.Read.Read
   (Data.List.NonEmpty.NonEmpty a)' failed: OOPS! Cannot find information for class
   Qualified "GHC.Read" "Read" unsupported *)

(* Translating `instance forall {a}, forall `{GHC.Show.Show a}, GHC.Show.Show
   (Data.List.NonEmpty.NonEmpty a)' failed: OOPS! Cannot find information for class
   Qualified "GHC.Show" "Show" unsupported *)

(* Skipping instance
   instance_forall___GHC_Base_Ord_a___GHC_Base_Ord__Data_List_NonEmpty_NonEmpty_a_ *)

Local Definition instance_forall___GHC_Base_Eq__a___GHC_Base_Eq___Data_List_NonEmpty_NonEmpty_a__op_zeze__ {inst_a}
                                                                                                           `{GHC.Base.Eq_
                                                                                                           inst_a}
    : NonEmpty inst_a -> NonEmpty inst_a -> bool :=
  fun arg_78__ arg_79__ =>
    match arg_78__ , arg_79__ with
      | NEcons a1 a2 , NEcons b1 b2 => (andb ((GHC.Base.op_zeze__ a1 b1))
                                             ((GHC.Base.op_zeze__ a2 b2)))
    end.

Local Definition instance_forall___GHC_Base_Eq__a___GHC_Base_Eq___Data_List_NonEmpty_NonEmpty_a__op_zsze__ {inst_a}
                                                                                                           `{_
                                                                                                             : GHC.Base.Eq_
                                                                                                               inst_a}
    : NonEmpty inst_a -> NonEmpty inst_a -> bool :=
  fun arg_198__ arg_199__ =>
    match arg_198__ , arg_199__ with
      | a , b => negb
                 (instance_forall___GHC_Base_Eq__a___GHC_Base_Eq___Data_List_NonEmpty_NonEmpty_a__op_zeze__
                 a b)
    end.

Program Instance instance_forall___GHC_Base_Eq__a___GHC_Base_Eq___Data_List_NonEmpty_NonEmpty_a_ {a}
                                                                                                 `{GHC.Base.Eq_ a}
  : GHC.Base.Eq_ (NonEmpty a) := fun _ k =>
    k
    {|GHC.Base.op_zeze____ := instance_forall___GHC_Base_Eq__a___GHC_Base_Eq___Data_List_NonEmpty_NonEmpty_a__op_zeze__ ;
    GHC.Base.op_zsze____ := instance_forall___GHC_Base_Eq__a___GHC_Base_Eq___Data_List_NonEmpty_NonEmpty_a__op_zsze__ |}.

Definition fromList {a} : list a -> NonEmpty a :=
  fun arg_37__ =>
    match arg_37__ with
      | cons a as_ => NEcons a as_
      | nil => GHC.Base.errorWithoutStackTrace (GHC.Base.hs_string__
                                               "NonEmpty.fromList: empty list")
    end.

Definition insert {f} {a} `{Data.Foldable.Foldable f} `{GHC.Base.Ord a} : a -> f
                                                                          a -> NonEmpty a :=
  fun a =>
    GHC.Base.op_z2218U__ fromList (GHC.Base.op_z2218U__ (Data.OldList.insert a)
                                                        Data.Foldable.toList).

Definition lift {f} {a} {b} `{Data.Foldable.Foldable f} : (list a -> list
                                                          b) -> f a -> NonEmpty b :=
  fun f =>
    GHC.Base.op_z2218U__ fromList (GHC.Base.op_z2218U__ f Data.Foldable.toList).

Definition reverse {a} : NonEmpty a -> NonEmpty a :=
  lift GHC.List.reverse.

Definition sort {a} `{GHC.Base.Ord a} : NonEmpty a -> NonEmpty a :=
  lift Data.OldList.sort.

Definition sortBy {a} : (a -> a -> comparison) -> NonEmpty a -> NonEmpty a :=
  fun f => lift (Data.OldList.sortBy f).

Definition sortWith {o} {a} `{GHC.Base.Ord o} : (a -> o) -> NonEmpty
                                                a -> NonEmpty a :=
  GHC.Base.op_z2218U__ sortBy Data.Ord.comparing.

Definition scanl {f} {b} {a} `{Data.Foldable.Foldable f}
    : (b -> a -> b) -> b -> f a -> NonEmpty b :=
  fun f z =>
    GHC.Base.op_z2218U__ fromList (GHC.Base.op_z2218U__ (GHC.List.scanl f z)
                                                        Data.Foldable.toList).

Definition scanl1 {a} : (a -> a -> a) -> NonEmpty a -> NonEmpty a :=
  fun arg_49__ arg_50__ =>
    match arg_49__ , arg_50__ with
      | f , NEcons a as_ => fromList (GHC.List.scanl f a as_)
    end.

Definition scanr {f} {a} {b} `{Data.Foldable.Foldable f}
    : (a -> b -> b) -> b -> f a -> NonEmpty b :=
  fun f z =>
    GHC.Base.op_z2218U__ fromList (GHC.Base.op_z2218U__ (GHC.List.scanr f z)
                                                        Data.Foldable.toList).

Definition tails {f} {a} `{Data.Foldable.Foldable f} : f a -> NonEmpty (list
                                                                       a) :=
  GHC.Base.op_z2218U__ fromList (GHC.Base.op_z2218U__ Data.OldList.tails
                                                      Data.Foldable.toList).

Definition head {a} : NonEmpty a -> a :=
  fun arg_60__ => match arg_60__ with | NEcons a _ => a end.

Definition isPrefixOf {a} `{GHC.Base.Eq_ a} : list a -> NonEmpty a -> bool :=
  fun arg_16__ arg_17__ =>
    match arg_16__ , arg_17__ with
      | nil , _ => true
      | cons y ys , NEcons x xs => andb (GHC.Base.op_zeze__ y x)
                                        (Data.OldList.isPrefixOf ys xs)
    end.

Definition length {a} : NonEmpty a -> GHC.Num.Int :=
  fun arg_75__ =>
    match arg_75__ with
      | NEcons _ xs => GHC.Num.op_zp__ (GHC.Num.fromInteger 1) (Data.Foldable.length
                                       xs)
    end.

Definition map {a} {b} : (a -> b) -> NonEmpty a -> NonEmpty b :=
  fun arg_21__ arg_22__ =>
    match arg_21__ , arg_22__ with
      | f , NEcons a as_ => NEcons (f a) (GHC.Base.fmap f as_)
    end.

Definition nonEmpty {a} : list a -> option (NonEmpty a) :=
  fun arg_62__ =>
    match arg_62__ with
      | nil => None
      | cons a as_ => Some (NEcons a as_)
    end.

Definition uncons {a} : NonEmpty a -> a * option (NonEmpty a) :=
  fun arg_65__ => match arg_65__ with | NEcons a as_ => pair a (nonEmpty as_) end.

Definition nubBy {a} : (a -> a -> bool) -> NonEmpty a -> NonEmpty a :=
  fun arg_0__ arg_1__ =>
    match arg_0__ , arg_1__ with
      | eq , NEcons a as_ => NEcons a (Data.OldList.nubBy eq (GHC.List.filter
                                                             (fun b => negb (eq a b)) as_))
    end.

Definition nub {a} `{GHC.Base.Eq_ a} : NonEmpty a -> NonEmpty a :=
  nubBy GHC.Base.op_zeze__.

Definition op_zlzb__ {a} : a -> NonEmpty a -> NonEmpty a :=
  fun arg_54__ arg_55__ =>
    match arg_54__ , arg_55__ with
      | a , NEcons b bs => NEcons a (cons b bs)
    end.

Infix "<|" := (op_zlzb__) (at level 99).

Notation "'_<|_'" := (op_zlzb__).

Definition cons_ {a} : a -> NonEmpty a -> NonEmpty a :=
  op_zlzb__.

Definition some1 {f} {a} `{GHC.Base.Alternative f} : f a -> f (NonEmpty a) :=
  fun x =>
    GHC.Base.op_zlztzg__ (Data.Functor.op_zlzdzg__ NEcons x) (GHC.Base.many x).

Definition tail {a} : NonEmpty a -> list a :=
  fun arg_58__ => match arg_58__ with | NEcons _ as_ => as_ end.

Definition toList {a} : NonEmpty a -> list a :=
  fun arg_25__ => match arg_25__ with | NEcons a as_ => cons a as_ end.

Definition takeWhile {a} : (a -> bool) -> NonEmpty a -> list a :=
  fun p => GHC.Base.op_z2218U__ (GHC.List.takeWhile p) toList.

Definition take {a} : GHC.Num.Int -> NonEmpty a -> list a :=
  fun n => GHC.Base.op_z2218U__ (GHC.List.take n) toList.

Definition splitAt {a} : GHC.Num.Int -> NonEmpty a -> list a * list a :=
  fun n => GHC.Base.op_z2218U__ (GHC.List.splitAt n) toList.

Definition span {a} : (a -> bool) -> NonEmpty a -> list a * list a :=
  fun p => GHC.Base.op_z2218U__ (GHC.List.span p) toList.

Definition break {a} : (a -> bool) -> NonEmpty a -> list a * list a :=
  fun p => span (GHC.Base.op_z2218U__ negb p).

Definition partition {a} : (a -> bool) -> NonEmpty a -> list a * list a :=
  fun p => GHC.Base.op_z2218U__ (Data.OldList.partition p) toList.

Definition filter {a} : (a -> bool) -> NonEmpty a -> list a :=
  fun p => GHC.Base.op_z2218U__ (GHC.List.filter p) toList.

Definition dropWhile {a} : (a -> bool) -> NonEmpty a -> list a :=
  fun p => GHC.Base.op_z2218U__ (GHC.List.dropWhile p) toList.

Definition drop {a} : GHC.Num.Int -> NonEmpty a -> list a :=
  fun n => GHC.Base.op_z2218U__ (GHC.List.drop n) toList.

Definition unzip {f} {a} {b} `{GHC.Base.Functor f} : f (a * b) -> f a * f b :=
  fun xs =>
    pair (Data.Functor.op_zlzdzg__ Data.Tuple.fst xs) (Data.Functor.op_zlzdzg__
         Data.Tuple.snd xs).

Definition xor : NonEmpty bool -> bool :=
  fun arg_68__ =>
    match arg_68__ with
      | NEcons x xs => let xor' :=
                         fun arg_69__ arg_70__ =>
                           match arg_69__ , arg_70__ with
                             | true , y => negb y
                             | false , y => y
                           end in
                       Data.Foldable.foldr xor' x xs
    end.

Definition zip {a} {b} : NonEmpty a -> NonEmpty b -> NonEmpty (a * b) :=
  fun arg_12__ arg_13__ =>
    match arg_12__ , arg_13__ with
      | NEcons x xs , NEcons y ys => NEcons (pair x y) (GHC.List.zip xs ys)
    end.

Definition zipWith {a} {b} {c} : (a -> b -> c) -> NonEmpty a -> NonEmpty
                                 b -> NonEmpty c :=
  fun arg_7__ arg_8__ arg_9__ =>
    match arg_7__ , arg_8__ , arg_9__ with
      | f , NEcons x xs , NEcons y ys => NEcons (f x y) (GHC.List.zipWith f xs ys)
    end.

Local Definition instance_GHC_Base_Applicative_Data_List_NonEmpty_NonEmpty_op_zlztzg__
    : forall {a} {b}, NonEmpty (a -> b) -> NonEmpty a -> NonEmpty b :=
  fun {a} {b} => zipWith id.

Local Definition instance_GHC_Base_Applicative_Data_List_NonEmpty_NonEmpty_op_ztzg__
    : forall {a} {b}, NonEmpty a -> NonEmpty b -> NonEmpty b :=
  fun {a} {b} =>
    fun x y =>
      instance_GHC_Base_Applicative_Data_List_NonEmpty_NonEmpty_op_zlztzg__
      (GHC.Base.fmap (GHC.Base.const GHC.Base.id) x) y.

Program Instance instance_GHC_Base_Applicative_Data_List_NonEmpty_NonEmpty
  : GHC.Base.Applicative NonEmpty := fun _ k =>
    k {|GHC.Base.op_ztzg____ := fun {a} {b} =>
        instance_GHC_Base_Applicative_Data_List_NonEmpty_NonEmpty_op_ztzg__ ;
      GHC.Base.op_zlztzg____ := fun {a} {b} =>
        instance_GHC_Base_Applicative_Data_List_NonEmpty_NonEmpty_op_zlztzg__ ;
      GHC.Base.pure__ := fun {a} =>
        instance_GHC_Base_Applicative_Data_List_NonEmpty_NonEmpty_pure |}.

Local Definition instance_GHC_Base_Monad_Data_List_NonEmpty_NonEmpty_op_zgzg__
    : forall {a} {b}, NonEmpty a -> NonEmpty b -> NonEmpty b :=
  fun {a} {b} => GHC.Base.op_ztzg__.

Local Definition instance_GHC_Base_Monad_Data_List_NonEmpty_NonEmpty_return_
    : forall {a}, a -> NonEmpty a :=
  fun {a} => GHC.Base.pure.

Program Instance instance_GHC_Base_Monad_Data_List_NonEmpty_NonEmpty
  : GHC.Base.Monad NonEmpty := fun _ k =>
    k {|GHC.Base.op_zgzg____ := fun {a} {b} =>
        instance_GHC_Base_Monad_Data_List_NonEmpty_NonEmpty_op_zgzg__ ;
      GHC.Base.op_zgzgze____ := fun {a} {b} =>
        instance_GHC_Base_Monad_Data_List_NonEmpty_NonEmpty_op_zgzgze__ ;
      GHC.Base.return___ := fun {a} =>
        instance_GHC_Base_Monad_Data_List_NonEmpty_NonEmpty_return_ |}.

(* Unbound variables:
     None Some andb bool comparison cons false id list negb nil op_zt__ option pair
     true Coq.Init.Datatypes.app Coq.Program.Basics.compose Data.Foldable.Foldable
     Data.Foldable.fold Data.Foldable.foldMap Data.Foldable.foldl Data.Foldable.foldr
     Data.Foldable.hash_compose Data.Foldable.length Data.Foldable.toList
     Data.Functor.op_zlzdzg__ Data.Monoid.Mk_Any Data.Monoid.Mk_Product
     Data.Monoid.Mk_Sum Data.Monoid.getAny Data.Monoid.getProduct Data.Monoid.getSum
     Data.OldList.insert Data.OldList.isPrefixOf Data.OldList.nubBy
     Data.OldList.partition Data.OldList.sort Data.OldList.sortBy Data.OldList.tails
     Data.Ord.comparing Data.Traversable.Traversable Data.Traversable.traverse
     Data.Tuple.fst Data.Tuple.snd GHC.Base.Alternative GHC.Base.Applicative
     GHC.Base.Eq_ GHC.Base.Functor GHC.Base.Monad GHC.Base.Monoid GHC.Base.Ord
     GHC.Base.build GHC.Base.const GHC.Base.errorWithoutStackTrace GHC.Base.fmap
     GHC.Base.id GHC.Base.many GHC.Base.mappend GHC.Base.op_z2218U__
     GHC.Base.op_zdzn__ GHC.Base.op_zeze__ GHC.Base.op_zgzgze__ GHC.Base.op_zlzd__
     GHC.Base.op_zlztzg__ GHC.Base.op_ztzg__ GHC.Base.pure GHC.List.drop
     GHC.List.dropWhile GHC.List.filter GHC.List.reverse GHC.List.scanl
     GHC.List.scanr GHC.List.span GHC.List.splitAt GHC.List.take GHC.List.takeWhile
     GHC.List.zip GHC.List.zipWith GHC.Num.Int GHC.Num.Num GHC.Num.op_zp__
*)
