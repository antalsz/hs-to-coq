(*

skip minimumBy
skip maximumBy

Remove these methods from Foldable class.
  foldl1
  foldr1
  maximum
  minimum


skip instance_Foldable_option_foldl1
skip instance_Foldable_option_foldr1
instance_Foldable_option_maximum
instance_Foldable_option_minimum

skip instance_Foldable_list_foldl1
skip instance_Foldable_list_foldr1
skip instance_Foldable_list_maximum
skip instance_Foldable_list_minimum

instance_Foldable_Data_Proxy_Proxy_foldr1
instance_Foldable_Data_Proxy_Proxy_foldl1
instance_Foldable_Data_Proxy_Proxy_minimum
instance_Foldable_Data_Proxy_Proxy_maximum

 instance_Foldable__GHC_Tuple_____a__foldMap
 instance_Foldable__GHC_Tuple_____a__foldl
 instance_Foldable__GHC_Tuple_____a__foldl1
 instance_Foldable__GHC_Tuple_____a__foldr'
 instance_Foldable__GHC_Tuple_____a__product
 instance_Foldable__GHC_Tuple_____a__sum
 instance_Foldable__GHC_Tuple_____a__foldr
 instance_Foldable__GHC_Tuple_____a__foldr1
 instance_Foldable__GHC_Tuple_____a__null
 instance_Foldable__GHC_Tuple_____a__toList
 instance_Foldable__GHC_Tuple_____a__foldl'
 instance_Foldable__GHC_Tuple_____a__length
 instance_Foldable__GHC_Tuple_____a__fold

 instance_Foldable__GHC_Arr_Array_i__foldl
 instance_Foldable__GHC_Arr_Array_i__foldl'
 instance_Foldable__GHC_Arr_Array_i__foldl1
 instance_Foldable__GHC_Arr_Array_i__foldr
 instance_Foldable__GHC_Arr_Array_i__foldMap
 instance_Foldable__GHC_Arr_Array_i__product
 instance_Foldable__GHC_Arr_Array_i__sum
 instance_Foldable__GHC_Arr_Array_i__fold
 instance_Foldable__GHC_Arr_Array_i__foldr'
 instance_Foldable__GHC_Arr_Array_i__foldr1
 instance_Foldable__GHC_Arr_Array_i__length
 instance_Foldable__GHC_Arr_Array_i__null
 instance_Foldable__GHC_Arr_Array_i__toList



*)


(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Set Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Preamble *)

(* Converted imports: *)

Require Data.Bool.
Require Data.Either.
Require GHC.List.
Require Data.Maybe.
Require Data.Monoid.
Require Data.Ord.
Require Data.Proxy.
Require GHC.Base.
Require GHC.Num.
(* Require #. *)
Require Coq.Program.Basics.

Definition zero : BinNums.Z := BinNums.Z0.
Definition one  : BinNums.Z := BinNums.Zpos BinNums.xH.

(*
Definition hashDotop___ {b} {c} {a} `{GHC.Types.Coercible b c}
    : (b -> c) -> (a -> b) -> (a -> c) :=
  fun arg_76__ => match arg_76__ with | _f => GHC.Base.coerce end.

Infix "hashDot" := (hashDotop___) (at level 99).

Notation "'_hashDot_'" := (hashDotop___).
*)

(* Converted declarations: *)

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

Local Definition instance_Foldable_list_elem : forall {a},
                                                 forall `{GHC.Base.Eq_ a}, a -> list a -> bool :=
  fun {a} `{GHC.Base.Eq_ a} => GHC.List.elem.

Local Definition instance_Foldable_list_foldl : forall {b} {a},
                                                  (b -> a -> b) -> b -> list a -> b :=
  fun {b} {a} => Base.foldl.

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
  fun {b} {a} => Base.foldl'.

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
  fun {m} `{GHC.Base.Monoid m} =>
    instance_Foldable_list_foldMap GHC.Base.id.

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

Local Definition instance_Foldable_Data_Proxy_Proxy_elem : forall {a},
                                                             forall `{GHC.Base.Eq_ a},
                                                               a -> Data.Proxy.Proxy a -> bool :=
  fun {a} `{GHC.Base.Eq_ a} => fun arg_275__ arg_276__ => false.

Local Definition instance_Foldable_Data_Proxy_Proxy_fold : forall {m},
                                                             forall `{GHC.Base.Monoid m}, Data.Proxy.Proxy m -> m :=
  fun {m} `{GHC.Base.Monoid m} => fun arg_254__ => GHC.Base.mempty.

Local Definition instance_Foldable_Data_Proxy_Proxy_foldMap : forall {m} {a},
                                                                forall `{GHC.Base.Monoid m},
                                                                  (a -> m) -> Data.Proxy.Proxy a -> m :=
  fun {m} {a} `{GHC.Base.Monoid m} =>
    fun arg_252__ arg_253__ => GHC.Base.mempty.

Local Definition instance_Foldable_Data_Proxy_Proxy_foldl : forall {b} {a},
                                                              (b -> a -> b) -> b -> Data.Proxy.Proxy a -> b :=
  fun {b} {a} =>
    fun arg_259__ arg_260__ arg_261__ =>
      match arg_259__ , arg_260__ , arg_261__ with
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
    fun arg_255__ arg_256__ arg_257__ =>
      match arg_255__ , arg_256__ , arg_257__ with
        | _ , z , _ => z
      end.

Local Definition instance_Foldable_Data_Proxy_Proxy_toList : forall {a},
                                                               Data.Proxy.Proxy a -> list a :=
  fun {a} =>
    fun arg_54__ =>
      match arg_54__ with
        | t => Base.build (fun arg_55__ arg_56__ =>
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
  fun {a} => fun arg_271__ => BinNums.Z0.

Local Definition instance_Foldable_Data_Proxy_Proxy_null : forall {a},
                                                             Data.Proxy.Proxy a -> bool :=
  fun {a} => fun arg_274__ => true.

Local Definition instance_Foldable_Data_Proxy_Proxy_product : forall {a},
                                                                forall `{GHC.Num.Num a}, Data.Proxy.Proxy a -> a :=
  fun {a} `{GHC.Num.Num a} => fun arg_280__ => GHC.Num.fromInteger one.

Local Definition instance_Foldable_Data_Proxy_Proxy_sum : forall {a},
                                                            forall `{GHC.Num.Num a}, Data.Proxy.Proxy a -> a :=
  fun {a} `{GHC.Num.Num a} => fun arg_277__ => GHC.Num.fromInteger BinNums.Z0.


Class Foldable t := {
  elem : forall {a}, forall `{GHC.Base.Eq_ a}, a -> t a -> bool ;
  fold : forall {m}, forall `{GHC.Base.Monoid m}, t m -> m ;
  foldMap : forall {m} {a}, forall `{GHC.Base.Monoid m}, (a -> m) -> t a -> m ;
  foldl : forall {b} {a}, (b -> a -> b) -> b -> t a -> b ;
  foldl' : forall {b} {a}, (b -> a -> b) -> b -> t a -> b ;
(*  foldl1 : forall {a}, (a -> a -> a) -> t a -> a ; *)
  foldr : forall {a} {b}, (a -> b -> b) -> b -> t a -> b ;
  foldr' : forall {a} {b}, (a -> b -> b) -> b -> t a -> b ;
(*   foldr1 : forall {a}, (a -> a -> a) -> t a -> a ; *)
  length : forall {a}, t a -> GHC.Num.Int ;
(*  maximum : forall {a}, forall `{GHC.Base.Ord a}, t a -> a ; *)
(*  minimum : forall {a}, forall `{GHC.Base.Ord a}, t a -> a ; *)
  null : forall {a}, t a -> bool ;
  product : forall {a}, forall `{GHC.Num.Num a}, t a -> a ;
  sum : forall {a}, forall `{GHC.Num.Num a}, t a -> a ;
  toList : forall {a}, t a -> list a }.

Definition traverse_ {t} {f} {a} {b} `{Foldable t} `{GHC.Base.Applicative f}
    : (a -> f b) -> t a -> f unit :=
  fun arg_143__ =>
    match arg_143__ with
      | f => foldr (Coq.Program.Basics.compose GHC.Base.op_ztzg__ f) (GHC.Base.pure
                                                                     tt)
    end.

Definition sequence_ {t} {m} {a} `{Foldable t} `{GHC.Base.Monad m} : t (m
                                                                          a) -> m unit :=
  foldr GHC.Base.op_zgzg__ (GHC.Base.return_ tt).

Definition sequenceA_ {t} {f} {a} `{Foldable t} `{GHC.Base.Applicative f} : t
                                                                               (f a) -> f unit :=
  foldr GHC.Base.op_ztzg__ (GHC.Base.pure tt).


Definition or {t} `{Foldable t} (x : t bool) : bool :=
  Data.Monoid.getAny (foldMap Data.Monoid.Mk_Any x).

Definition notElem {t} {a} `{Foldable t} `{GHC.Base.Eq_ a} : a -> t a -> bool :=
  fun arg_84__ =>
    match arg_84__ with
      | x => Coq.Program.Basics.compose negb (elem x)
    end.


Definition mapM_ {t} {m} {a} {b} `{Foldable t} `{GHC.Base.Monad m} : (a -> m
                                                                        b) -> t a -> m unit :=
  fun arg_139__ =>
    match arg_139__ with
      | f => foldr (Coq.Program.Basics.compose GHC.Base.op_zgzg__ f) (GHC.Base.return_
                                                                     tt)
    end.

Definition for_ {t} {f} {a} {b} `{Foldable t} `{GHC.Base.Applicative f} : t
                                                                             a -> (a -> f b) -> f unit :=
  GHC.Base.flip traverse_.

Definition forM_ {t} {m} {a} {b} `{Foldable t} `{GHC.Base.Monad m} : t
                                                                        a -> (a -> m b) -> m unit :=
  GHC.Base.flip mapM_.

Definition foldrM {t} {m} {a} {b} `{Foldable t} `{GHC.Base.Monad m}
    : (a -> b -> m b) -> b -> t a -> m b :=
  fun arg_157__ arg_158__ arg_159__ =>
    match arg_157__ , arg_158__ , arg_159__ with
      | f , z0 , xs => let f' :=
                         fun arg_160__ arg_161__ arg_162__ =>
                           match arg_160__ , arg_161__ , arg_162__ with
                             | k , x , z => GHC.Base.op_zgzgze__ (f x z) k
                           end in
                       foldl f' GHC.Base.return_ xs z0
    end.

Definition foldlM {t} {m} {b} {a} `{Foldable t} `{GHC.Base.Monad m}
    : (b -> a -> m b) -> b -> t a -> m b :=
  fun arg_147__ arg_148__ arg_149__ =>
    match arg_147__ , arg_148__ , arg_149__ with
      | f , z0 , xs => let f' :=
                         fun arg_150__ arg_151__ arg_152__ =>
                           match arg_150__ , arg_151__ , arg_152__ with
                             | x , k , z => GHC.Base.op_zgzgze__ (f z x) k
                           end in
                       foldr f' GHC.Base.return_ xs z0
    end.

Definition find {t} {a} `{Foldable t} : (a -> bool) -> t a -> option a :=
  fun arg_78__ =>
    match arg_78__ with
      | p => Coq.Program.Basics.compose
              Data.Monoid.getFirst (foldMap (fun arg_79__ =>
                                               match arg_79__ with
                                               | x => Data.Monoid.Mk_First (if p x then Some x else None)
                                               end))
    end.


Definition asum {t} {f} {a} `{Foldable t} `{GHC.Base.Alternative f} : t (f
                                                                           a) -> f a :=
  foldr GHC.Base.op_zlzbzg__ GHC.Base.empty.

Definition msum {t} {m} {a} `{Foldable t} `{GHC.Base.MonadPlus m} : t (m a) -> m
                                                                    a :=
  asum.


Definition anyWith {t} {a} (foldMap : (forall {m} {a}, forall `{GHC.Base.Monoid m}, (a -> m) -> t a -> m))  : (a -> bool) -> t a -> bool :=
  fun arg_108__ x =>
    match arg_108__ with
      | p => Data.Monoid.getAny (foldMap (fun y => Data.Monoid.Mk_Any (p y)) x)
    end.

Definition any {t} {a} `{Foldable t} : (a -> bool) -> t a -> bool := anyWith (fun _ _ _ => foldMap).

Local Definition instance_Foldable_option_elem : forall {a},
                                                   forall `{GHC.Base.Eq_ a}, a -> option a -> bool :=
  fun {a} `{GHC.Base.Eq_ a} => Coq.Program.Basics.compose (anyWith (fun _ _ _ => instance_Foldable_option_foldMap)) GHC.Base.op_zeze__.


Definition and {t} `{Foldable t} (x : t bool) : bool :=
  Data.Monoid.getAll (foldMap Data.Monoid.Mk_All x).

Definition all {t} {a} `{Foldable t} : (a -> bool) -> t a -> bool :=
  fun arg_105__ x =>
    match arg_105__ with
      | p => Data.Monoid.getAll (foldMap (fun y => Data.Monoid.Mk_All (p y)) x)
    end.


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

Local Definition instance_Foldable__sum_a__foldMap : forall {a0}{m} {a},
                                                       forall `{GHC.Base.Monoid m}, (a -> m) -> (a + a0) -> m :=
  fun {a0} {m} {a} `{GHC.Base.Monoid m} =>
    fun arg_295__ arg_296__ =>
      match arg_295__ , arg_296__ with
        | _ , (inr _) => GHC.Base.mempty
        | f , (inl y) => f y
      end.


Local Definition instance_Foldable__sum_a__product : forall {a}{a0},
                                                       forall `{GHC.Num.Num a}, (a + a0) -> a :=
  fun {a}{a0} `{GHC.Num.Num a} x =>
    Data.Monoid.getProduct (instance_Foldable__sum_a__foldMap Data.Monoid.Mk_Product x).

Local Definition instance_Foldable__sum_a__sum : forall {a}{a0},
                                                   forall `{GHC.Num.Num a}, (a + a0) -> a :=
  fun {a}{a0} `{GHC.Num.Num a} x =>
    Data.Monoid.getSum (instance_Foldable__sum_a__foldMap Data.Monoid.Mk_Sum x).

Local Definition instance_Foldable__sum_a__fold : forall {a}{m},
                                                    forall `{GHC.Base.Monoid m}, (m + a) -> m :=
  fun {a}{m} `{GHC.Base.Monoid m} =>
    instance_Foldable__sum_a__foldMap GHC.Base.id.

Instance instance_Foldable_list : !Foldable list := {
  elem := fun {a} `{GHC.Base.Eq_ a} => instance_Foldable_list_elem ;
  fold := fun {m} `{GHC.Base.Monoid m} => instance_Foldable_list_fold ;
  foldMap := fun {m} {a} `{GHC.Base.Monoid m} =>
    instance_Foldable_list_foldMap ;
  foldl := fun {b} {a} => instance_Foldable_list_foldl ;
  foldl' := fun {b} {a} => instance_Foldable_list_foldl' ;
(*   foldl1 := fun {a} => instance_Foldable_list_foldl1 ; *)
  foldr := fun {a} {b} => instance_Foldable_list_foldr ;
  foldr' := fun {a} {b} => instance_Foldable_list_foldr' ;
(*   foldr1 := fun {a} => instance_Foldable_list_foldr1 ; *)
  length := fun {a} => instance_Foldable_list_length ;
(*   maximum := fun {a} `{GHC.Base.Ord a} => instance_Foldable_list_maximum ;
     minimum := fun {a} `{GHC.Base.Ord a} => instance_Foldable_list_minimum ; *)
  null := fun {a} => instance_Foldable_list_null ;
  product := fun {a} `{GHC.Num.Num a} => instance_Foldable_list_product ;
  sum := fun {a} `{GHC.Num.Num a} => instance_Foldable_list_sum ;
  toList := fun {a} => instance_Foldable_list_toList }.


Definition concatMap {t} {a} {b} `{Foldable t} : (a -> list b) -> t a -> list
                                                 b :=
  fun arg_113__ arg_114__ =>
    match arg_113__ , arg_114__ with
      | f , xs => Base.build (fun arg_115__ arg_116__ =>
                                   match arg_115__ , arg_116__ with
                                     | c , n => foldr (fun arg_117__ arg_118__ =>
                                                        match arg_117__ , arg_118__ with
                                                          | x , b => foldr c b (f x)
                                                        end) n xs
                                   end)
    end.

Definition concat {t} {a} `{Foldable t} : t (list a) -> list a :=
  fun arg_125__ =>
    match arg_125__ with
      | xs => Base.build (fun arg_126__ arg_127__ =>
                               match arg_126__ , arg_127__ with
                                 | c , n => foldr (fun arg_128__ arg_129__ =>
                                                    match arg_128__ , arg_129__ with
                                                      | x , y => foldr c y x
                                                    end) n xs
                               end)
    end.


Inductive Max a : Type := Mk_Max : option a -> Max a.

Definition getMax {a} (arg_75__ : Max a) :=
  match arg_75__ with
    | (Mk_Max getMax) => getMax
  end.

Inductive Min a : Type := Mk_Min : option a -> Min a.

Definition getMin {a} (arg_74__ : Min a) :=
  match arg_74__ with
    | (Mk_Min getMin) => getMin
  end.



Instance instance_Foldable_Data_Proxy_Proxy : !Foldable Data.Proxy.Proxy := {
  elem := fun {a} `{GHC.Base.Eq_ a} => instance_Foldable_Data_Proxy_Proxy_elem ;
  fold := fun {m} `{GHC.Base.Monoid m} =>
    instance_Foldable_Data_Proxy_Proxy_fold ;
  foldMap := fun {m} {a} `{GHC.Base.Monoid m} =>
    instance_Foldable_Data_Proxy_Proxy_foldMap ;
  foldl := fun {b} {a} => instance_Foldable_Data_Proxy_Proxy_foldl ;
  foldl' := fun {b} {a} => instance_Foldable_Data_Proxy_Proxy_foldl' ;
  foldr := fun {a} {b} => instance_Foldable_Data_Proxy_Proxy_foldr ;
  foldr' := fun {a} {b} => instance_Foldable_Data_Proxy_Proxy_foldr' ;
  length := fun {a} => instance_Foldable_Data_Proxy_Proxy_length ;
  null := fun {a} => instance_Foldable_Data_Proxy_Proxy_null ;
  product := fun {a} `{GHC.Num.Num a} =>
    instance_Foldable_Data_Proxy_Proxy_product ;
  sum := fun {a} `{GHC.Num.Num a} => instance_Foldable_Data_Proxy_Proxy_sum ;
  toList := fun {a} => instance_Foldable_Data_Proxy_Proxy_toList }.



Instance instance_Foldable_option : !Foldable option := {
  elem := fun {a} `{GHC.Base.Eq_ a} => instance_Foldable_option_elem ;
  fold := fun {m} `{GHC.Base.Monoid m} => instance_Foldable_option_fold ;
  foldMap := fun {m} {a} `{GHC.Base.Monoid m} =>
    instance_Foldable_option_foldMap ;
  foldl := fun {b} {a} => instance_Foldable_option_foldl ;
  foldl' := fun {b} {a} => instance_Foldable_option_foldl' ;
  foldr := fun {a} {b} => instance_Foldable_option_foldr ;
  foldr' := fun {a} {b} => instance_Foldable_option_foldr' ;
  length := fun {a} => instance_Foldable_option_length ;
  null := fun {a} => instance_Foldable_option_null ;
  product := fun {a} `{GHC.Num.Num a} => instance_Foldable_option_product ;
  sum := fun {a} `{GHC.Num.Num a} => instance_Foldable_option_sum ;
  toList := fun {a} => instance_Foldable_option_toList }.
