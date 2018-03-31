(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Coq.Program.Tactics.
Require Coq.Program.Wf.

(* Converted imports: *)

Require Coq.ZArith.BinInt.
Require Data.Foldable.
Require Data.IntMap.Internal.
Require Data.IntSet.Internal.
Require Data.Semigroup.
Require Data.Traversable.
Require GHC.Base.
Require GHC.Num.
Require GHC.Prim.
Require Unique.
Import GHC.Base.Notations.

(* Converted type declarations: *)

Inductive UniqFM ele : Type
  := UFM : (Data.IntMap.Internal.IntMap ele) -> UniqFM ele.

Arguments UFM {_} _.
(* Midamble *)

Require GHC.Err.

Instance Default_UniqFM {a} : Err.Default (UniqFM a) :=
  Err.Build_Default _ (UFM Data.IntMap.Internal.empty).

(* Converted value declarations: *)

Instance Unpeel_UniqFM ele
   : GHC.Prim.Unpeel (UniqFM ele) (Data.IntMap.Internal.IntMap ele) :=
  GHC.Prim.Build_Unpeel _ _ (fun x => let 'UFM y := x in y) UFM.

(* Translating `instance Outputable__UniqFM' failed: OOPS! Cannot find
   information for class Qualified "Outputable" "Outputable" unsupported *)

Local Definition Traversable__UniqFM_traverse
   : forall {f} {a} {b},
     forall `{GHC.Base.Applicative f}, (a -> f b) -> UniqFM a -> f (UniqFM b) :=
  fun {f} {a} {b} `{GHC.Base.Applicative f} =>
    fun arg_0__ arg_1__ =>
      match arg_0__, arg_1__ with
      | f, UFM a1 => GHC.Base.fmap (fun b1 => UFM b1) (Data.Traversable.traverse f a1)
      end.

Local Definition Traversable__UniqFM_sequenceA
   : forall {f} {a},
     forall `{GHC.Base.Applicative f}, UniqFM (f a) -> f (UniqFM a) :=
  fun {f} {a} `{GHC.Base.Applicative f} =>
    Traversable__UniqFM_traverse GHC.Base.id.

Local Definition Traversable__UniqFM_sequence
   : forall {m} {a}, forall `{GHC.Base.Monad m}, UniqFM (m a) -> m (UniqFM a) :=
  fun {m} {a} `{GHC.Base.Monad m} => Traversable__UniqFM_sequenceA.

Local Definition Traversable__UniqFM_mapM
   : forall {m} {a} {b},
     forall `{GHC.Base.Monad m}, (a -> m b) -> UniqFM a -> m (UniqFM b) :=
  fun {m} {a} {b} `{GHC.Base.Monad m} => Traversable__UniqFM_traverse.

Local Definition Functor__UniqFM_fmap
   : forall {a} {b}, (a -> b) -> UniqFM a -> UniqFM b :=
  fun {a} {b} => GHC.Prim.coerce GHC.Base.fmap.

Local Definition Functor__UniqFM_op_zlzd__
   : forall {a} {b}, a -> UniqFM b -> UniqFM a :=
  fun {a} {b} => GHC.Prim.coerce _GHC.Base.<$_.

Program Instance Functor__UniqFM : GHC.Base.Functor UniqFM :=
  fun _ k =>
    k {| GHC.Base.op_zlzd____ := fun {a} {b} => Functor__UniqFM_op_zlzd__ ;
         GHC.Base.fmap__ := fun {a} {b} => Functor__UniqFM_fmap |}.

Local Definition Eq___UniqFM_op_zeze__ {inst_ele} `{GHC.Base.Eq_ inst_ele}
   : UniqFM inst_ele -> UniqFM inst_ele -> bool :=
  GHC.Prim.coerce _GHC.Base.==_.

Local Definition Eq___UniqFM_op_zsze__ {inst_ele} `{GHC.Base.Eq_ inst_ele}
   : UniqFM inst_ele -> UniqFM inst_ele -> bool :=
  GHC.Prim.coerce _GHC.Base./=_.

Program Instance Eq___UniqFM {ele} `{GHC.Base.Eq_ ele}
   : GHC.Base.Eq_ (UniqFM ele) :=
  fun _ k =>
    k {| GHC.Base.op_zeze____ := Eq___UniqFM_op_zeze__ ;
         GHC.Base.op_zsze____ := Eq___UniqFM_op_zsze__ |}.

(* Translating `instance Data__UniqFM' failed: OOPS! Cannot find information for
   class Qualified "Data.Data" "Data" unsupported *)

Local Definition Foldable__UniqFM_elem
   : forall {a}, forall `{GHC.Base.Eq_ a}, a -> UniqFM a -> bool :=
  fun {a} `{GHC.Base.Eq_ a} => GHC.Prim.coerce Data.Foldable.elem.

Local Definition Foldable__UniqFM_fold
   : forall {m}, forall `{GHC.Base.Monoid m}, UniqFM m -> m :=
  fun {m} `{GHC.Base.Monoid m} => GHC.Prim.coerce Data.Foldable.fold.

Local Definition Foldable__UniqFM_foldMap
   : forall {m} {a}, forall `{GHC.Base.Monoid m}, (a -> m) -> UniqFM a -> m :=
  fun {m} {a} `{GHC.Base.Monoid m} => GHC.Prim.coerce Data.Foldable.foldMap.

Local Definition Foldable__UniqFM_foldl
   : forall {b} {a}, (b -> a -> b) -> b -> UniqFM a -> b :=
  fun {b} {a} => GHC.Prim.coerce Data.Foldable.foldl.

Local Definition Foldable__UniqFM_foldl'
   : forall {b} {a}, (b -> a -> b) -> b -> UniqFM a -> b :=
  fun {b} {a} => GHC.Prim.coerce Data.Foldable.foldl'.

Local Definition Foldable__UniqFM_foldr
   : forall {a} {b}, (a -> b -> b) -> b -> UniqFM a -> b :=
  fun {a} {b} => GHC.Prim.coerce Data.Foldable.foldr.

Local Definition Foldable__UniqFM_foldr'
   : forall {a} {b}, (a -> b -> b) -> b -> UniqFM a -> b :=
  fun {a} {b} => GHC.Prim.coerce Data.Foldable.foldr'.

Local Definition Foldable__UniqFM_length
   : forall {a}, UniqFM a -> GHC.Num.Int :=
  fun {a} => GHC.Prim.coerce Data.Foldable.length.

Local Definition Foldable__UniqFM_null : forall {a}, UniqFM a -> bool :=
  fun {a} => GHC.Prim.coerce Data.Foldable.null.

Local Definition Foldable__UniqFM_product
   : forall {a}, forall `{GHC.Num.Num a}, UniqFM a -> a :=
  fun {a} `{GHC.Num.Num a} => GHC.Prim.coerce Data.Foldable.product.

Local Definition Foldable__UniqFM_sum
   : forall {a}, forall `{GHC.Num.Num a}, UniqFM a -> a :=
  fun {a} `{GHC.Num.Num a} => GHC.Prim.coerce Data.Foldable.sum.

Local Definition Foldable__UniqFM_toList : forall {a}, UniqFM a -> list a :=
  fun {a} => GHC.Prim.coerce Data.Foldable.toList.

Program Instance Foldable__UniqFM : Data.Foldable.Foldable UniqFM :=
  fun _ k =>
    k {| Data.Foldable.elem__ := fun {a} `{GHC.Base.Eq_ a} =>
           Foldable__UniqFM_elem ;
         Data.Foldable.fold__ := fun {m} `{GHC.Base.Monoid m} => Foldable__UniqFM_fold ;
         Data.Foldable.foldMap__ := fun {m} {a} `{GHC.Base.Monoid m} =>
           Foldable__UniqFM_foldMap ;
         Data.Foldable.foldl__ := fun {b} {a} => Foldable__UniqFM_foldl ;
         Data.Foldable.foldl'__ := fun {b} {a} => Foldable__UniqFM_foldl' ;
         Data.Foldable.foldr__ := fun {a} {b} => Foldable__UniqFM_foldr ;
         Data.Foldable.foldr'__ := fun {a} {b} => Foldable__UniqFM_foldr' ;
         Data.Foldable.length__ := fun {a} => Foldable__UniqFM_length ;
         Data.Foldable.null__ := fun {a} => Foldable__UniqFM_null ;
         Data.Foldable.product__ := fun {a} `{GHC.Num.Num a} =>
           Foldable__UniqFM_product ;
         Data.Foldable.sum__ := fun {a} `{GHC.Num.Num a} => Foldable__UniqFM_sum ;
         Data.Foldable.toList__ := fun {a} => Foldable__UniqFM_toList |}.

Program Instance Traversable__UniqFM : Data.Traversable.Traversable UniqFM :=
  fun _ k =>
    k {| Data.Traversable.mapM__ := fun {m} {a} {b} `{GHC.Base.Monad m} =>
           Traversable__UniqFM_mapM ;
         Data.Traversable.sequence__ := fun {m} {a} `{GHC.Base.Monad m} =>
           Traversable__UniqFM_sequence ;
         Data.Traversable.sequenceA__ := fun {f} {a} `{GHC.Base.Applicative f} =>
           Traversable__UniqFM_sequenceA ;
         Data.Traversable.traverse__ := fun {f} {a} {b} `{GHC.Base.Applicative f} =>
           Traversable__UniqFM_traverse |}.

Definition addToUFM {key} {elt} `{Unique.Uniquable key}
   : UniqFM elt -> key -> elt -> UniqFM elt :=
  fun arg_0__ arg_1__ arg_2__ =>
    match arg_0__, arg_1__, arg_2__ with
    | UFM m, k, v =>
        UFM (Data.IntMap.Internal.insert (Unique.getWordKey (Unique.getUnique k)) v m)
    end.

Definition addListToUFM {key} {elt} `{Unique.Uniquable key}
   : UniqFM elt -> list (key * elt)%type -> UniqFM elt :=
  Data.Foldable.foldl (fun arg_0__ arg_1__ =>
                         match arg_0__, arg_1__ with
                         | m, pair k v => addToUFM m k v
                         end).

Definition addToUFM_Acc {key} {elt} {elts} `{Unique.Uniquable key}
   : (elt -> elts -> elts) ->
     (elt -> elts) -> UniqFM elts -> key -> elt -> UniqFM elts :=
  fun arg_0__ arg_1__ arg_2__ arg_3__ arg_4__ =>
    match arg_0__, arg_1__, arg_2__, arg_3__, arg_4__ with
    | exi, new, UFM m, k, v =>
        UFM (Data.IntMap.Internal.insertWith (fun _new old => exi v old)
             (Unique.getWordKey (Unique.getUnique k)) (new v) m)
    end.

Definition addToUFM_C {key} {elt} `{Unique.Uniquable key}
   : (elt -> elt -> elt) -> UniqFM elt -> key -> elt -> UniqFM elt :=
  fun arg_0__ arg_1__ arg_2__ arg_3__ =>
    match arg_0__, arg_1__, arg_2__, arg_3__ with
    | f, UFM m, k, v =>
        UFM (Data.IntMap.Internal.insertWith (GHC.Base.flip f) (Unique.getWordKey
                                                                (Unique.getUnique k)) v m)
    end.

Definition addListToUFM_C {key} {elt} `{Unique.Uniquable key}
   : (elt -> elt -> elt) -> UniqFM elt -> list (key * elt)%type -> UniqFM elt :=
  fun f =>
    Data.Foldable.foldl (fun arg_0__ arg_1__ =>
                           match arg_0__, arg_1__ with
                           | m, pair k v => addToUFM_C f m k v
                           end).

Definition addToUFM_Directly {elt}
   : UniqFM elt -> Unique.Unique -> elt -> UniqFM elt :=
  fun arg_0__ arg_1__ arg_2__ =>
    match arg_0__, arg_1__, arg_2__ with
    | UFM m, u, v => UFM (Data.IntMap.Internal.insert (Unique.getWordKey u) v m)
    end.

Definition addListToUFM_Directly {elt}
   : UniqFM elt -> list (Unique.Unique * elt)%type -> UniqFM elt :=
  Data.Foldable.foldl (fun arg_0__ arg_1__ =>
                         match arg_0__, arg_1__ with
                         | m, pair k v => addToUFM_Directly m k v
                         end).

Definition adjustUFM {key} {elt} `{Unique.Uniquable key}
   : (elt -> elt) -> UniqFM elt -> key -> UniqFM elt :=
  fun arg_0__ arg_1__ arg_2__ =>
    match arg_0__, arg_1__, arg_2__ with
    | f, UFM m, k =>
        UFM (Data.IntMap.Internal.adjust f (Unique.getWordKey (Unique.getUnique k)) m)
    end.

Definition adjustUFM_Directly {elt}
   : (elt -> elt) -> UniqFM elt -> Unique.Unique -> UniqFM elt :=
  fun arg_0__ arg_1__ arg_2__ =>
    match arg_0__, arg_1__, arg_2__ with
    | f, UFM m, u => UFM (Data.IntMap.Internal.adjust f (Unique.getWordKey u) m)
    end.

Definition alterUFM {key} {elt} `{Unique.Uniquable key}
   : (option elt -> option elt) -> UniqFM elt -> key -> UniqFM elt :=
  fun arg_0__ arg_1__ arg_2__ =>
    match arg_0__, arg_1__, arg_2__ with
    | f, UFM m, k =>
        UFM (Data.IntMap.Internal.alter f (Unique.getWordKey (Unique.getUnique k)) m)
    end.

Definition delFromUFM {key} {elt} `{Unique.Uniquable key}
   : UniqFM elt -> key -> UniqFM elt :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | UFM m, k =>
        UFM (Data.IntMap.Internal.delete (Unique.getWordKey (Unique.getUnique k)) m)
    end.

Definition delListFromUFM {key} {elt} `{Unique.Uniquable key}
   : UniqFM elt -> list key -> UniqFM elt :=
  Data.Foldable.foldl delFromUFM.

Definition delFromUFM_Directly {elt}
   : UniqFM elt -> Unique.Unique -> UniqFM elt :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | UFM m, u => UFM (Data.IntMap.Internal.delete (Unique.getWordKey u) m)
    end.

Definition delListFromUFM_Directly {elt}
   : UniqFM elt -> list Unique.Unique -> UniqFM elt :=
  Data.Foldable.foldl delFromUFM_Directly.

Definition disjointUFM {elt1} {elt2} : UniqFM elt1 -> UniqFM elt2 -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | UFM x, UFM y =>
        Data.IntMap.Internal.null (Data.IntMap.Internal.intersection x y)
    end.

Definition elemUFM {key} {elt} `{Unique.Uniquable key}
   : key -> UniqFM elt -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | k, UFM m =>
        Data.IntMap.Internal.member (Unique.getWordKey (Unique.getUnique k)) m
    end.

Definition elemUFM_Directly {elt} : Unique.Unique -> UniqFM elt -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | u, UFM m => Data.IntMap.Internal.member (Unique.getWordKey u) m
    end.

Definition eltsUFM {elt} : UniqFM elt -> list elt :=
  fun arg_0__ => let 'UFM m := arg_0__ in Data.IntMap.Internal.elems m.

Definition emptyUFM {elt} : UniqFM elt :=
  UFM Data.IntMap.Internal.empty.

Definition listToUFM_Directly {elt}
   : list (Unique.Unique * elt)%type -> UniqFM elt :=
  Data.Foldable.foldl (fun arg_0__ arg_1__ =>
                         match arg_0__, arg_1__ with
                         | m, pair u v => addToUFM_Directly m u v
                         end) emptyUFM.

Definition listToUFM_C {key} {elt} `{Unique.Uniquable key}
   : (elt -> elt -> elt) -> list (key * elt)%type -> UniqFM elt :=
  fun f =>
    Data.Foldable.foldl (fun arg_0__ arg_1__ =>
                           match arg_0__, arg_1__ with
                           | m, pair k v => addToUFM_C f m k v
                           end) emptyUFM.

Definition listToUFM {key} {elt} `{Unique.Uniquable key}
   : list (key * elt)%type -> UniqFM elt :=
  Data.Foldable.foldl (fun arg_0__ arg_1__ =>
                         match arg_0__, arg_1__ with
                         | m, pair k v => addToUFM m k v
                         end) emptyUFM.

Local Definition Monoid__UniqFM_mempty {inst_a} : (UniqFM inst_a) :=
  emptyUFM.

Definition filterUFM {elt} : (elt -> bool) -> UniqFM elt -> UniqFM elt :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | p, UFM m => UFM (Data.IntMap.Internal.filter p m)
    end.

Definition filterUFM_Directly {elt}
   : (Unique.Unique -> elt -> bool) -> UniqFM elt -> UniqFM elt :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | p, UFM m =>
        UFM (Data.IntMap.Internal.filterWithKey (p GHC.Base.∘ Unique.getUnique) m)
    end.

Definition foldUFM {elt} {a} : (elt -> a -> a) -> a -> UniqFM elt -> a :=
  fun arg_0__ arg_1__ arg_2__ =>
    match arg_0__, arg_1__, arg_2__ with
    | k, z, UFM m => Data.IntMap.Internal.foldr k z m
    end.

Definition foldUFM_Directly {elt} {a}
   : (Unique.Unique -> elt -> a -> a) -> a -> UniqFM elt -> a :=
  fun arg_0__ arg_1__ arg_2__ =>
    match arg_0__, arg_1__, arg_2__ with
    | k, z, UFM m =>
        Data.IntMap.Internal.foldrWithKey (k GHC.Base.∘ Unique.getUnique) z m
    end.

Definition intersectUFM {elt} : UniqFM elt -> UniqFM elt -> UniqFM elt :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | UFM x, UFM y => UFM (Data.IntMap.Internal.intersection x y)
    end.

Definition intersectUFM_C {elt1} {elt2} {elt3}
   : (elt1 -> elt2 -> elt3) -> UniqFM elt1 -> UniqFM elt2 -> UniqFM elt3 :=
  fun arg_0__ arg_1__ arg_2__ =>
    match arg_0__, arg_1__, arg_2__ with
    | f, UFM x, UFM y => UFM (Data.IntMap.Internal.intersectionWith f x y)
    end.

Definition isNullUFM {elt} : UniqFM elt -> bool :=
  fun arg_0__ => let 'UFM m := arg_0__ in Data.IntMap.Internal.null m.

Definition keysUFM {elt} : UniqFM elt -> list Unique.Unique :=
  fun arg_0__ =>
    let 'UFM m := arg_0__ in
    GHC.Base.map Unique.getUnique (Data.IntMap.Internal.keys m).

Definition lookupUFM {key} {elt} `{Unique.Uniquable key}
   : UniqFM elt -> key -> option elt :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | UFM m, k =>
        Data.IntMap.Internal.lookup (Unique.getWordKey (Unique.getUnique k)) m
    end.

Definition lookupUFM_Directly {elt}
   : UniqFM elt -> Unique.Unique -> option elt :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | UFM m, u => Data.IntMap.Internal.lookup (Unique.getWordKey u) m
    end.

Definition lookupWithDefaultUFM {key} {elt} `{Unique.Uniquable key}
   : UniqFM elt -> elt -> key -> elt :=
  fun arg_0__ arg_1__ arg_2__ =>
    match arg_0__, arg_1__, arg_2__ with
    | UFM m, v, k =>
        Data.IntMap.Internal.findWithDefault v (Unique.getWordKey (Unique.getUnique k))
        m
    end.

Definition lookupWithDefaultUFM_Directly {elt}
   : UniqFM elt -> elt -> Unique.Unique -> elt :=
  fun arg_0__ arg_1__ arg_2__ =>
    match arg_0__, arg_1__, arg_2__ with
    | UFM m, v, u => Data.IntMap.Internal.findWithDefault v (Unique.getWordKey u) m
    end.

Definition mapUFM {elt1} {elt2}
   : (elt1 -> elt2) -> UniqFM elt1 -> UniqFM elt2 :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | f, UFM m => UFM (Data.IntMap.Internal.map f m)
    end.

Definition mapUFM_Directly {elt1} {elt2}
   : (Unique.Unique -> elt1 -> elt2) -> UniqFM elt1 -> UniqFM elt2 :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | f, UFM m =>
        UFM (Data.IntMap.Internal.mapWithKey (f GHC.Base.∘ Unique.getUnique) m)
    end.

Definition minusUFM {elt1} {elt2} : UniqFM elt1 -> UniqFM elt2 -> UniqFM elt1 :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | UFM x, UFM y => UFM (Data.IntMap.Internal.difference x y)
    end.

Definition nonDetEltsUFM {elt} : UniqFM elt -> list elt :=
  fun arg_0__ => let 'UFM m := arg_0__ in Data.IntMap.Internal.elems m.

Definition partitionUFM {elt}
   : (elt -> bool) -> UniqFM elt -> (UniqFM elt * UniqFM elt)%type :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | p, UFM m =>
        let 'pair left_ right_ := Data.IntMap.Internal.partition p m in
        pair (UFM left_) (UFM right_)
    end.

Definition plusUFM {elt} : UniqFM elt -> UniqFM elt -> UniqFM elt :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | UFM x, UFM y => UFM (Data.IntMap.Internal.union y x)
    end.

Local Definition Monoid__UniqFM_mappend {inst_a}
   : (UniqFM inst_a) -> (UniqFM inst_a) -> (UniqFM inst_a) :=
  plusUFM.

Local Definition Monoid__UniqFM_mconcat {inst_a}
   : list (UniqFM inst_a) -> (UniqFM inst_a) :=
  GHC.Base.foldr Monoid__UniqFM_mappend Monoid__UniqFM_mempty.

Program Instance Monoid__UniqFM {a} : GHC.Base.Monoid (UniqFM a) :=
  fun _ k =>
    k {| GHC.Base.mappend__ := Monoid__UniqFM_mappend ;
         GHC.Base.mconcat__ := Monoid__UniqFM_mconcat ;
         GHC.Base.mempty__ := Monoid__UniqFM_mempty |}.

Local Definition Semigroup__UniqFM_op_zlzg__ {inst_a}
   : (UniqFM inst_a) -> (UniqFM inst_a) -> (UniqFM inst_a) :=
  plusUFM.

Program Instance Semigroup__UniqFM {a} : Data.Semigroup.Semigroup (UniqFM a) :=
  fun _ k => k {| Data.Semigroup.op_zlzg____ := Semigroup__UniqFM_op_zlzg__ |}.

Definition plusUFM_C {elt}
   : (elt -> elt -> elt) -> UniqFM elt -> UniqFM elt -> UniqFM elt :=
  fun arg_0__ arg_1__ arg_2__ =>
    match arg_0__, arg_1__, arg_2__ with
    | f, UFM x, UFM y => UFM (Data.IntMap.Internal.unionWith f x y)
    end.

Definition plusUFM_CD {elt}
   : (elt -> elt -> elt) ->
     UniqFM elt -> elt -> UniqFM elt -> elt -> UniqFM elt :=
  fun arg_0__ arg_1__ arg_2__ arg_3__ arg_4__ =>
    match arg_0__, arg_1__, arg_2__, arg_3__, arg_4__ with
    | f, UFM xm, dx, UFM ym, dy =>
        UFM (Data.IntMap.Internal.mergeWithKey (fun arg_5__ arg_6__ arg_7__ =>
                                                  match arg_5__, arg_6__, arg_7__ with
                                                  | _, x, y => Some (f x y)
                                                  end) (Data.IntMap.Internal.map (fun x => f x dy))
                                               (Data.IntMap.Internal.map (fun y => f dx y)) xm ym)
    end.

Definition sizeUFM {elt} : UniqFM elt -> GHC.Num.Int :=
  fun um =>
    let 'UFM m := um in
    Coq.ZArith.BinInt.Z.of_N (Data.IntMap.Internal.size m).

Definition splitUFM {key} {elt} `{Unique.Uniquable key}
   : UniqFM elt -> key -> (UniqFM elt * option elt * UniqFM elt)%type :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | UFM m, k =>
        let 'pair (pair less equal) greater := Data.IntMap.Internal.splitLookup
                                                 (Unique.getWordKey (Unique.getUnique k)) m in
        pair (pair (UFM less) equal) (UFM greater)
    end.

Definition ufmToIntMap {elt} : UniqFM elt -> Data.IntMap.Internal.IntMap elt :=
  fun arg_0__ => let 'UFM m := arg_0__ in m.

Definition ufmToList {elt} : UniqFM elt -> list (Unique.Unique * elt)%type :=
  fun arg_0__ =>
    let 'UFM m := arg_0__ in
    GHC.Base.map (fun arg_1__ =>
                    let 'pair k v := arg_1__ in
                    pair (Unique.getUnique k) v) (Data.IntMap.Internal.toList m).

Definition ufmToSet_Directly {elt}
   : UniqFM elt -> Data.IntSet.Internal.IntSet :=
  fun arg_0__ => let 'UFM m := arg_0__ in Data.IntMap.Internal.keysSet m.

Definition unitDirectlyUFM {elt} : Unique.Unique -> elt -> UniqFM elt :=
  fun u v => UFM (Data.IntMap.Internal.singleton (Unique.getWordKey u) v).

Definition unitUFM {key} {elt} `{Unique.Uniquable key}
   : key -> elt -> UniqFM elt :=
  fun k v =>
    UFM (Data.IntMap.Internal.singleton (Unique.getWordKey (Unique.getUnique k)) v).

(* Unbound variables:
     Some bool list op_zt__ option pair Coq.ZArith.BinInt.Z.of_N
     Data.Foldable.Foldable Data.Foldable.elem Data.Foldable.fold
     Data.Foldable.foldMap Data.Foldable.foldl Data.Foldable.foldl'
     Data.Foldable.foldr Data.Foldable.foldr' Data.Foldable.length Data.Foldable.null
     Data.Foldable.product Data.Foldable.sum Data.Foldable.toList
     Data.IntMap.Internal.IntMap Data.IntMap.Internal.adjust
     Data.IntMap.Internal.alter Data.IntMap.Internal.delete
     Data.IntMap.Internal.difference Data.IntMap.Internal.elems
     Data.IntMap.Internal.empty Data.IntMap.Internal.filter
     Data.IntMap.Internal.filterWithKey Data.IntMap.Internal.findWithDefault
     Data.IntMap.Internal.foldr Data.IntMap.Internal.foldrWithKey
     Data.IntMap.Internal.insert Data.IntMap.Internal.insertWith
     Data.IntMap.Internal.intersection Data.IntMap.Internal.intersectionWith
     Data.IntMap.Internal.keys Data.IntMap.Internal.keysSet
     Data.IntMap.Internal.lookup Data.IntMap.Internal.map
     Data.IntMap.Internal.mapWithKey Data.IntMap.Internal.member
     Data.IntMap.Internal.mergeWithKey Data.IntMap.Internal.null
     Data.IntMap.Internal.partition Data.IntMap.Internal.singleton
     Data.IntMap.Internal.size Data.IntMap.Internal.splitLookup
     Data.IntMap.Internal.toList Data.IntMap.Internal.union
     Data.IntMap.Internal.unionWith Data.IntSet.Internal.IntSet
     Data.Semigroup.Semigroup Data.Traversable.Traversable Data.Traversable.traverse
     GHC.Base.Applicative GHC.Base.Eq_ GHC.Base.Functor GHC.Base.Monad
     GHC.Base.Monoid GHC.Base.flip GHC.Base.fmap GHC.Base.foldr GHC.Base.id
     GHC.Base.map GHC.Base.op_z2218U__ GHC.Base.op_zeze__ GHC.Base.op_zlzd__
     GHC.Base.op_zsze__ GHC.Num.Int GHC.Num.Num GHC.Prim.Build_Unpeel GHC.Prim.Unpeel
     GHC.Prim.coerce Unique.Uniquable Unique.Unique Unique.getUnique
     Unique.getWordKey
*)
