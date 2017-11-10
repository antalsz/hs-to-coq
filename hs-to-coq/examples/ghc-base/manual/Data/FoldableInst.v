
(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Set Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Data.Bool.
Require Data.Either.
Require GHC.List.
Require Data.Maybe.
Require Data.Monoid.
Require Data.Ord.
Require Data.Proxy.
Require GHC.Base.
Require GHC.Num.

Require Coq.Program.Basics.

Definition zero : BinNums.Z := BinNums.Z0.
Definition one  : BinNums.Z := BinNums.Zpos BinNums.xH.

Require Import Data.Foldable.

Local Definition instance_Foldable__sum_a__null : forall {a} {b},
                                                    (a + b) -> bool :=
  fun {a}{b} => Data.Either.isLeft.

Local Definition instance_Foldable__sum_a__length : forall {a}{b},
                                                      (a + b) -> GHC.Num.Int :=
  fun {a}{b} =>
    fun arg_304__ => match arg_304__ with | (inr _) => BinNums.Z0 | (inl _) => one end.

Local Definition instance_Foldable__sum_a__foldr : forall {a0} {a} {b},
                                                     (a -> b -> b) -> b -> (a + a0) -> b :=
  fun {a0} {a} {b} =>
    fun arg_299__ arg_300__ arg_301__ =>
      match arg_299__ , arg_300__ , arg_301__ with
        | _ , z , (inr _) => z
        | f , z , (inl y) => f y z
      end.

(* skip instance_Foldable__sum_a__foldr1 *)

Local Definition instance_Foldable__sum_a__toList : forall {a}{b},
                                                      (a + b) -> list a :=
  fun {a}{b} =>
    fun arg_54__ =>
      match arg_54__ with
        | t => Base.build (fun arg_55__ arg_56__ =>
                                match arg_55__ , arg_56__ with
                                  | c , n => instance_Foldable__sum_a__foldr c n t
                                end)
      end.

Local Definition instance_Foldable__sum_a__foldl' : forall{a0} {b} {a},
                                                      (b -> a -> b) -> b -> (a + a0) -> b :=
  fun {a0} {b} {a} =>
    fun arg_24__ arg_25__ arg_26__ =>
      match arg_24__ , arg_25__ , arg_26__ with
        | f , z0 , xs => let f' :=
                           fun arg_27__ arg_28__ arg_29__ =>
                             match arg_27__ , arg_28__ , arg_29__ with
                               | x , k , z => GHC.Base.op_zdzn__ k (f z x)
                             end in
                         instance_Foldable__sum_a__foldr f' GHC.Base.id xs z0
      end.

Local Definition instance_Foldable__sum_a__foldMap :
  forall {a0}{m} {a},
  forall `{GHC.Base.Monoid m}, (a -> m) -> (a0 + a) -> m :=
  fun {a0} {m} {a} `{GHC.Base.Monoid m} =>
    fun arg_295__ arg_296__ =>
      match arg_295__ , arg_296__ with
        | _ , (inl _) => GHC.Base.mempty
        | f , (inr y) => f y
      end.


Local Definition instance_Foldable__sum_a__product :
  forall {a}{a0},
  forall `{GHC.Num.Num a}, (a0 + a) -> a :=
  fun {a}{a0} `{GHC.Num.Num a} x =>
    Data.Monoid.getProduct (instance_Foldable__sum_a__foldMap Data.Monoid.Mk_Product x).

Local Definition instance_Foldable__sum_a__sum :
  forall {a}{a0},
  forall `{GHC.Num.Num a}, (a0 + a) -> a :=
  fun {a}{a0} `{GHC.Num.Num a} x =>
    Data.Monoid.getSum (instance_Foldable__sum_a__foldMap Data.Monoid.Mk_Sum x).

Local Definition instance_Foldable__sum_a__fold :
  forall {a}{m},
  forall `{GHC.Base.Monoid m}, (a + m) -> m :=
  fun {a}{m} `{GHC.Base.Monoid m} =>
    instance_Foldable__sum_a__foldMap GHC.Base.id.

Local Definition instance_Foldable_option_foldl : forall {b} {a},
                                                    (b -> a -> b) -> b -> option a -> b :=
  fun {b} {a} =>
    fun arg_313__ arg_314__ arg_315__ =>
      match arg_313__ , arg_314__ , arg_315__ with
        | _ , z , None => z
        | f , z , (Some x) => f z x
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
    fun arg_308__ arg_309__ arg_310__ =>
      match arg_308__ , arg_309__ , arg_310__ with
        | _ , z , None => z
        | f , z , (Some x) => f x z
      end.

Local Definition instance_Foldable_option_null : forall {a}, option a -> bool :=
  fun {a} => instance_Foldable_option_foldr (fun arg_61__ arg_62__ => false) true.

Local Definition instance_Foldable_option_toList : forall {a},
                                                     option a -> list a :=
  fun {a} =>
    fun arg_54__ =>
      match arg_54__ with
        | t => Base.build (fun arg_55__ arg_56__ =>
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
                                        | c , _ => GHC.Num.op_zp__ c one
                                      end) zero.

Local Definition instance_Foldable_option_foldMap : forall {m} {a},
                                                      forall `{GHC.Base.Monoid m}, (a -> m) -> option a -> m :=
  fun {m} {a} `{GHC.Base.Monoid m} =>
    fun arg_1__ =>
      match arg_1__ with
        | f => instance_Foldable_option_foldr (Coq.Program.Basics.compose
                                              GHC.Base.mappend f) GHC.Base.mempty
      end.

Local Definition instance_Foldable_option_product : forall {a},
                                                      forall `{GHC.Num.Num a}, option a -> a :=
  fun {a} `{GHC.Num.Num a} x =>
    Data.Monoid.getProduct (instance_Foldable_option_foldMap Data.Monoid.Mk_Product x).

Local Definition instance_Foldable_option_sum : forall {a},
                                                  forall `{GHC.Num.Num a}, option a -> a :=
  fun {a} `{GHC.Num.Num a} x =>
    Data.Monoid.getSum (instance_Foldable_option_foldMap Data.Monoid.Mk_Sum x).

Local Definition instance_Foldable_option_fold : forall {m},
                                                   forall `{GHC.Base.Monoid m}, option m -> m :=
  fun {m} `{GHC.Base.Monoid m} =>
    instance_Foldable_option_foldMap GHC.Base.id.

Definition anyWith {t} {a} (foldMap : (forall {m} {a}, forall `{GHC.Base.Monoid m}, (a -> m) -> t a -> m))  : (a -> bool) -> t a -> bool :=
  fun arg_108__ x =>
    match arg_108__ with
      | p => Data.Monoid.getAny (foldMap (fun y => Data.Monoid.Mk_Any (p y)) x)
    end.


Local Definition instance_Foldable_option_elem : forall {a},
                                                   forall `{GHC.Base.Eq_ a}, a -> option a -> bool :=
  fun {a} `{GHC.Base.Eq_ a} => Coq.Program.Basics.compose (anyWith (fun _ _ _ => instance_Foldable_option_foldMap)) GHC.Base.op_zeze__.

Instance instance_Foldable_option : !Foldable option := fun _ k => k {|
  elem__ := fun {a} `{GHC.Base.Eq_ a} => instance_Foldable_option_elem ;
  fold__ := fun {m} `{GHC.Base.Monoid m} => instance_Foldable_option_fold ;
  foldMap__ := fun {m} {a} `{GHC.Base.Monoid m} =>
    instance_Foldable_option_foldMap ;
  foldl__ := fun {b} {a} => instance_Foldable_option_foldl ;
  foldl'__ := fun {b} {a} => instance_Foldable_option_foldl' ;
  foldr__ := fun {a} {b} => instance_Foldable_option_foldr ;
  foldr'__ := fun {a} {b} => instance_Foldable_option_foldr' ;
  length__ := fun {a} => instance_Foldable_option_length ;
  null__ := fun {a} => instance_Foldable_option_null ;
  product__ := fun {a} `{GHC.Num.Num a} => instance_Foldable_option_product ;
  sum__ := fun {a} `{GHC.Num.Num a} => instance_Foldable_option_sum ;
  toList__ := fun {a} => instance_Foldable_option_toList |}.



Local Definition instance_Foldable__sum_a__elem :
forall {b}{a},
forall `{GHC.Base.Eq_ a}, a -> Datatypes.sum b a -> bool :=
  fun {b}{a} `{GHC.Base.Eq_ a} =>
    Coq.Program.Basics.compose
      (anyWith (fun _ _ _ => instance_Foldable__sum_a__foldMap)) GHC.Base.op_zeze__.
