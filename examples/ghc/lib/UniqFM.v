(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Coq.Program.Tactics.
Require Coq.Program.Wf.

(* Converted imports: *)

Require BinNat.
Require Data.Foldable.
Require Data.IntMap.Internal.
Require Data.IntSet.Internal.
Require GHC.Base.
Require GHC.Prim.
Require Unique.
Import GHC.Base.Notations.

(* Converted type declarations: *)

Inductive UniqFM ele : Type
  := UFM : (Data.IntMap.Internal.IntMap ele) -> UniqFM ele.

Arguments UFM {_} _.

(* Midamble *)

Require GHC.Err.

Instance Default__UniqFM {a} : Err.Default (UniqFM a) :=
  Err.Build_Default _ (UFM Data.IntMap.Internal.empty).

(* Converted value declarations: *)

Definition unitUFM {key} {elt} `{Unique.Uniquable key}
   : key -> elt -> UniqFM elt :=
  fun k v =>
    UFM (Data.IntMap.Internal.singleton (Unique.getWordKey (Unique.getUnique k)) v).

Definition unitDirectlyUFM {elt} : Unique.Unique -> elt -> UniqFM elt :=
  fun u v => UFM (Data.IntMap.Internal.singleton (Unique.getWordKey u) v).

Definition ufmToSet_Directly {elt}
   : UniqFM elt -> Data.IntSet.Internal.IntSet :=
  fun '(UFM m) => Data.IntMap.Internal.keysSet m.

Definition ufmToIntMap {elt} : UniqFM elt -> Data.IntMap.Internal.IntMap elt :=
  fun '(UFM m) => m.

Definition sizeUFM {elt} : UniqFM elt -> nat :=
  fun '(UFM m) => BinNat.N.to_nat (Data.IntMap.Internal.size m).

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

Definition plusUFM_C {elt}
   : (elt -> elt -> elt) -> UniqFM elt -> UniqFM elt -> UniqFM elt :=
  fun arg_0__ arg_1__ arg_2__ =>
    match arg_0__, arg_1__, arg_2__ with
    | f, UFM x, UFM y => UFM (Data.IntMap.Internal.unionWith f x y)
    end.

Definition plusUFM {elt} : UniqFM elt -> UniqFM elt -> UniqFM elt :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | UFM x, UFM y => UFM (Data.IntMap.Internal.union y x)
    end.

Definition plusMaybeUFM_C {elt}
   : (elt -> elt -> option elt) -> UniqFM elt -> UniqFM elt -> UniqFM elt :=
  fun arg_0__ arg_1__ arg_2__ =>
    match arg_0__, arg_1__, arg_2__ with
    | f, UFM xm, UFM ym =>
        UFM (Data.IntMap.Internal.mergeWithKey (fun arg_3__ arg_4__ arg_5__ =>
                                                  match arg_3__, arg_4__, arg_5__ with
                                                  | _, x, y => f x y
                                                  end) GHC.Base.id GHC.Base.id xm ym)
    end.

Definition partitionUFM {elt}
   : (elt -> bool) -> UniqFM elt -> (UniqFM elt * UniqFM elt)%type :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | p, UFM m =>
        let 'pair left_ right_ := Data.IntMap.Internal.partition p m in
        pair (UFM left_) (UFM right_)
    end.

Definition nonDetUFMToList {elt}
   : UniqFM elt -> list (Unique.Unique * elt)%type :=
  fun '(UFM m) =>
    GHC.Base.map (fun '(pair k v) => pair (Unique.getUnique k) v)
    (Data.IntMap.Internal.toList m).

Definition pprUFMWithKeys {a}
   : UniqFM a ->
     (list (Unique.Unique * a)%type -> GHC.Base.String) -> GHC.Base.String :=
  fun ufm pp => pp (nonDetUFMToList ufm).

Definition nonDetKeysUFM {elt} : UniqFM elt -> list Unique.Unique :=
  fun '(UFM m) => GHC.Base.map Unique.getUnique (Data.IntMap.Internal.keys m).

Definition nonDetFoldUFM_Directly {elt} {a}
   : (Unique.Unique -> elt -> a -> a) -> a -> UniqFM elt -> a :=
  fun arg_0__ arg_1__ arg_2__ =>
    match arg_0__, arg_1__, arg_2__ with
    | k, z, UFM m =>
        Data.IntMap.Internal.foldrWithKey (k GHC.Base.∘ Unique.getUnique) z m
    end.

Definition nonDetFoldUFM {elt} {a} : (elt -> a -> a) -> a -> UniqFM elt -> a :=
  fun arg_0__ arg_1__ arg_2__ =>
    match arg_0__, arg_1__, arg_2__ with
    | k, z, UFM m => Data.IntMap.Internal.foldr k z m
    end.

Definition nonDetEltsUFM {elt} : UniqFM elt -> list elt :=
  fun '(UFM m) => Data.IntMap.Internal.elems m.

Definition seqEltsUFM {elt} : (list elt -> unit) -> UniqFM elt -> unit :=
  fun seqList => seqList GHC.Base.∘ nonDetEltsUFM.

Definition minusUFM {elt1} {elt2} : UniqFM elt1 -> UniqFM elt2 -> UniqFM elt1 :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | UFM x, UFM y => UFM (Data.IntMap.Internal.difference x y)
    end.

Definition mapUFM_Directly {elt1} {elt2}
   : (Unique.Unique -> elt1 -> elt2) -> UniqFM elt1 -> UniqFM elt2 :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | f, UFM m =>
        UFM (Data.IntMap.Internal.mapWithKey (f GHC.Base.∘ Unique.getUnique) m)
    end.

Definition mapUFM {elt1} {elt2}
   : (elt1 -> elt2) -> UniqFM elt1 -> UniqFM elt2 :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | f, UFM m => UFM (Data.IntMap.Internal.map f m)
    end.

Definition lookupWithDefaultUFM_Directly {elt}
   : UniqFM elt -> elt -> Unique.Unique -> elt :=
  fun arg_0__ arg_1__ arg_2__ =>
    match arg_0__, arg_1__, arg_2__ with
    | UFM m, v, u => Data.IntMap.Internal.findWithDefault v (Unique.getWordKey u) m
    end.

Definition lookupWithDefaultUFM {key} {elt} `{Unique.Uniquable key}
   : UniqFM elt -> elt -> key -> elt :=
  fun arg_0__ arg_1__ arg_2__ =>
    match arg_0__, arg_1__, arg_2__ with
    | UFM m, v, k =>
        Data.IntMap.Internal.findWithDefault v (Unique.getWordKey (Unique.getUnique k))
        m
    end.

Definition lookupUFM_Directly {elt}
   : UniqFM elt -> Unique.Unique -> option elt :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | UFM m, u => Data.IntMap.Internal.lookup (Unique.getWordKey u) m
    end.

Definition lookupUFM {key} {elt} `{Unique.Uniquable key}
   : UniqFM elt -> key -> option elt :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | UFM m, k =>
        Data.IntMap.Internal.lookup (Unique.getWordKey (Unique.getUnique k)) m
    end.

Definition isNullUFM {elt} : UniqFM elt -> bool :=
  fun '(UFM m) => Data.IntMap.Internal.null m.

Definition intersectUFM_C {elt1} {elt2} {elt3}
   : (elt1 -> elt2 -> elt3) -> UniqFM elt1 -> UniqFM elt2 -> UniqFM elt3 :=
  fun arg_0__ arg_1__ arg_2__ =>
    match arg_0__, arg_1__, arg_2__ with
    | f, UFM x, UFM y => UFM (Data.IntMap.Internal.intersectionWith f x y)
    end.

Definition intersectUFM {elt1} {elt2}
   : UniqFM elt1 -> UniqFM elt2 -> UniqFM elt1 :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | UFM x, UFM y => UFM (Data.IntMap.Internal.intersection x y)
    end.

Definition foldUFM {elt} {a} : (elt -> a -> a) -> a -> UniqFM elt -> a :=
  fun arg_0__ arg_1__ arg_2__ =>
    match arg_0__, arg_1__, arg_2__ with
    | k, z, UFM m => Data.IntMap.Internal.foldr k z m
    end.

Definition filterUFM_Directly {elt}
   : (Unique.Unique -> elt -> bool) -> UniqFM elt -> UniqFM elt :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | p, UFM m =>
        UFM (Data.IntMap.Internal.filterWithKey (p GHC.Base.∘ Unique.getUnique) m)
    end.

Definition filterUFM {elt} : (elt -> bool) -> UniqFM elt -> UniqFM elt :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | p, UFM m => UFM (Data.IntMap.Internal.filter p m)
    end.

Definition emptyUFM {elt} : UniqFM elt :=
  UFM Data.IntMap.Internal.empty.

Definition plusUFMList {elt} : list (UniqFM elt) -> UniqFM elt :=
  Data.Foldable.foldl' plusUFM emptyUFM.

Definition eltsUFM {elt} : UniqFM elt -> list elt :=
  fun '(UFM m) => Data.IntMap.Internal.elems m.

Definition elemUFM_Directly {elt} : Unique.Unique -> UniqFM elt -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | u, UFM m => Data.IntMap.Internal.member (Unique.getWordKey u) m
    end.

Definition elemUFM {key} {elt} `{Unique.Uniquable key}
   : key -> UniqFM elt -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | k, UFM m =>
        Data.IntMap.Internal.member (Unique.getWordKey (Unique.getUnique k)) m
    end.

Definition disjointUFM {elt1} {elt2} : UniqFM elt1 -> UniqFM elt2 -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | UFM x, UFM y =>
        Data.IntMap.Internal.null (Data.IntMap.Internal.intersection x y)
    end.

Definition delFromUFM_Directly {elt}
   : UniqFM elt -> Unique.Unique -> UniqFM elt :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | UFM m, u => UFM (Data.IntMap.Internal.delete (Unique.getWordKey u) m)
    end.

Definition delListFromUFM_Directly {elt}
   : UniqFM elt -> list Unique.Unique -> UniqFM elt :=
  Data.Foldable.foldl delFromUFM_Directly.

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

Definition anyUFM {elt} : (elt -> bool) -> UniqFM elt -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | p, UFM m => Data.IntMap.Internal.foldr (orb GHC.Base.∘ p) false m
    end.

Definition alterUFM {key} {elt} `{Unique.Uniquable key}
   : (option elt -> option elt) -> UniqFM elt -> key -> UniqFM elt :=
  fun arg_0__ arg_1__ arg_2__ =>
    match arg_0__, arg_1__, arg_2__ with
    | f, UFM m, k =>
        UFM (Data.IntMap.Internal.alter f (Unique.getWordKey (Unique.getUnique k)) m)
    end.

Definition allUFM {elt} : (elt -> bool) -> UniqFM elt -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | p, UFM m => Data.IntMap.Internal.foldr (andb GHC.Base.∘ p) true m
    end.

Definition adjustUFM_Directly {elt}
   : (elt -> elt) -> UniqFM elt -> Unique.Unique -> UniqFM elt :=
  fun arg_0__ arg_1__ arg_2__ =>
    match arg_0__, arg_1__, arg_2__ with
    | f, UFM m, u => UFM (Data.IntMap.Internal.adjust f (Unique.getWordKey u) m)
    end.

Definition adjustUFM {key} {elt} `{Unique.Uniquable key}
   : (elt -> elt) -> UniqFM elt -> key -> UniqFM elt :=
  fun arg_0__ arg_1__ arg_2__ =>
    match arg_0__, arg_1__, arg_2__ with
    | f, UFM m, k =>
        UFM (Data.IntMap.Internal.adjust f (Unique.getWordKey (Unique.getUnique k)) m)
    end.

Definition addToUFM_Directly {elt}
   : UniqFM elt -> Unique.Unique -> elt -> UniqFM elt :=
  fun arg_0__ arg_1__ arg_2__ =>
    match arg_0__, arg_1__, arg_2__ with
    | UFM m, u, v => UFM (Data.IntMap.Internal.insert (Unique.getWordKey u) v m)
    end.

Definition listToUFM_Directly {elt}
   : list (Unique.Unique * elt)%type -> UniqFM elt :=
  Data.Foldable.foldl (fun arg_0__ arg_1__ =>
                         match arg_0__, arg_1__ with
                         | m, pair u v => addToUFM_Directly m u v
                         end) emptyUFM.

Definition addToUFM_C {key} {elt} `{Unique.Uniquable key}
   : (elt -> elt -> elt) -> UniqFM elt -> key -> elt -> UniqFM elt :=
  fun arg_0__ arg_1__ arg_2__ arg_3__ =>
    match arg_0__, arg_1__, arg_2__, arg_3__ with
    | f, UFM m, k, v =>
        UFM (Data.IntMap.Internal.insertWith (GHC.Base.flip f) (Unique.getWordKey
                                                                (Unique.getUnique k)) v m)
    end.

Definition listToUFM_C {key} {elt} `{Unique.Uniquable key}
   : (elt -> elt -> elt) -> list (key * elt)%type -> UniqFM elt :=
  fun f =>
    Data.Foldable.foldl (fun arg_0__ arg_1__ =>
                           match arg_0__, arg_1__ with
                           | m, pair k v => addToUFM_C f m k v
                           end) emptyUFM.

Definition addToUFM_Acc {key} {elt} {elts} `{Unique.Uniquable key}
   : (elt -> elts -> elts) ->
     (elt -> elts) -> UniqFM elts -> key -> elt -> UniqFM elts :=
  fun arg_0__ arg_1__ arg_2__ arg_3__ arg_4__ =>
    match arg_0__, arg_1__, arg_2__, arg_3__, arg_4__ with
    | exi, new, UFM m, k, v =>
        UFM (Data.IntMap.Internal.insertWith (fun _new old => exi v old)
             (Unique.getWordKey (Unique.getUnique k)) (new v) m)
    end.

Definition addToUFM {key} {elt} `{Unique.Uniquable key}
   : UniqFM elt -> key -> elt -> UniqFM elt :=
  fun arg_0__ arg_1__ arg_2__ =>
    match arg_0__, arg_1__, arg_2__ with
    | UFM m, k, v =>
        UFM (Data.IntMap.Internal.insert (Unique.getWordKey (Unique.getUnique k)) v m)
    end.

Definition listToUFM {key} {elt} `{Unique.Uniquable key}
   : list (key * elt)%type -> UniqFM elt :=
  Data.Foldable.foldl (fun arg_0__ arg_1__ =>
                         match arg_0__, arg_1__ with
                         | m, pair k v => addToUFM m k v
                         end) emptyUFM.

Definition addListToUFM_Directly {elt}
   : UniqFM elt -> list (Unique.Unique * elt)%type -> UniqFM elt :=
  Data.Foldable.foldl (fun arg_0__ arg_1__ =>
                         match arg_0__, arg_1__ with
                         | m, pair k v => addToUFM_Directly m k v
                         end).

Definition addListToUFM_C {key} {elt} `{Unique.Uniquable key}
   : (elt -> elt -> elt) -> UniqFM elt -> list (key * elt)%type -> UniqFM elt :=
  fun f =>
    Data.Foldable.foldl (fun arg_0__ arg_1__ =>
                           match arg_0__, arg_1__ with
                           | m, pair k v => addToUFM_C f m k v
                           end).

Definition addListToUFM {key} {elt} `{Unique.Uniquable key}
   : UniqFM elt -> list (key * elt)%type -> UniqFM elt :=
  Data.Foldable.foldl (fun arg_0__ arg_1__ =>
                         match arg_0__, arg_1__ with
                         | m, pair k v => addToUFM m k v
                         end).

(* Skipping all instances of class `Data.Data.Data', including
   `UniqFM.Data__UniqFM' *)

Instance Unpeel_UniqFM ele
   : GHC.Prim.Unpeel (UniqFM ele) (Data.IntMap.Internal.IntMap ele) :=
  GHC.Prim.Build_Unpeel _ _ (fun '(UFM y) => y) UFM.

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

Local Definition Functor__UniqFM_fmap
   : forall {a} {b}, (a -> b) -> UniqFM a -> UniqFM b :=
  fun {a} {b} => GHC.Prim.coerce GHC.Base.fmap.

Local Definition Functor__UniqFM_op_zlzd__
   : forall {a} {b}, a -> UniqFM b -> UniqFM a :=
  fun {a} {b} => GHC.Prim.coerce _GHC.Base.<$_.

Program Instance Functor__UniqFM : GHC.Base.Functor UniqFM :=
  fun _ k =>
    k {| GHC.Base.fmap__ := fun {a} {b} => Functor__UniqFM_fmap ;
         GHC.Base.op_zlzd____ := fun {a} {b} => Functor__UniqFM_op_zlzd__ |}.

(* Skipping all instances of class `Outputable.Outputable', including
   `UniqFM.Outputable__UniqFM' *)

Local Definition Semigroup__UniqFM_op_zlzlzgzg__ {inst_a}
   : (UniqFM inst_a) -> (UniqFM inst_a) -> (UniqFM inst_a) :=
  plusUFM.

Program Instance Semigroup__UniqFM {a} : GHC.Base.Semigroup (UniqFM a) :=
  fun _ k => k {| GHC.Base.op_zlzlzgzg____ := Semigroup__UniqFM_op_zlzlzgzg__ |}.

Local Definition Monoid__UniqFM_mappend {inst_a}
   : (UniqFM inst_a) -> (UniqFM inst_a) -> (UniqFM inst_a) :=
  _GHC.Base.<<>>_.

Local Definition Monoid__UniqFM_mempty {inst_a} : (UniqFM inst_a) :=
  emptyUFM.

Local Definition Monoid__UniqFM_mconcat {inst_a}
   : list (UniqFM inst_a) -> (UniqFM inst_a) :=
  GHC.Base.foldr Monoid__UniqFM_mappend Monoid__UniqFM_mempty.

Program Instance Monoid__UniqFM {a} : GHC.Base.Monoid (UniqFM a) :=
  fun _ k =>
    k {| GHC.Base.mappend__ := Monoid__UniqFM_mappend ;
         GHC.Base.mconcat__ := Monoid__UniqFM_mconcat ;
         GHC.Base.mempty__ := Monoid__UniqFM_mempty |}.

(* External variables:
     Some andb bool false list nat op_zt__ option orb pair true unit BinNat.N.to_nat
     Data.Foldable.foldl Data.Foldable.foldl' Data.IntMap.Internal.IntMap
     Data.IntMap.Internal.adjust Data.IntMap.Internal.alter
     Data.IntMap.Internal.delete Data.IntMap.Internal.difference
     Data.IntMap.Internal.elems Data.IntMap.Internal.empty
     Data.IntMap.Internal.filter Data.IntMap.Internal.filterWithKey
     Data.IntMap.Internal.findWithDefault Data.IntMap.Internal.foldr
     Data.IntMap.Internal.foldrWithKey Data.IntMap.Internal.insert
     Data.IntMap.Internal.insertWith Data.IntMap.Internal.intersection
     Data.IntMap.Internal.intersectionWith Data.IntMap.Internal.keys
     Data.IntMap.Internal.keysSet Data.IntMap.Internal.lookup
     Data.IntMap.Internal.map Data.IntMap.Internal.mapWithKey
     Data.IntMap.Internal.member Data.IntMap.Internal.mergeWithKey
     Data.IntMap.Internal.null Data.IntMap.Internal.partition
     Data.IntMap.Internal.singleton Data.IntMap.Internal.size
     Data.IntMap.Internal.toList Data.IntMap.Internal.union
     Data.IntMap.Internal.unionWith Data.IntSet.Internal.IntSet GHC.Base.Eq_
     GHC.Base.Functor GHC.Base.Monoid GHC.Base.Semigroup GHC.Base.String
     GHC.Base.flip GHC.Base.fmap GHC.Base.fmap__ GHC.Base.foldr GHC.Base.id
     GHC.Base.map GHC.Base.mappend__ GHC.Base.mconcat__ GHC.Base.mempty__
     GHC.Base.op_z2218U__ GHC.Base.op_zeze__ GHC.Base.op_zeze____ GHC.Base.op_zlzd__
     GHC.Base.op_zlzd____ GHC.Base.op_zlzlzgzg__ GHC.Base.op_zlzlzgzg____
     GHC.Base.op_zsze__ GHC.Base.op_zsze____ GHC.Prim.Build_Unpeel GHC.Prim.Unpeel
     GHC.Prim.coerce Unique.Uniquable Unique.Unique Unique.getUnique
     Unique.getWordKey
*)
