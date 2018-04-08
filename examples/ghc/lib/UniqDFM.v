(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Coq.Program.Tactics.
Require Coq.Program.Wf.

(* Converted imports: *)

Require Coq.Lists.List.
Require Coq.ZArith.BinInt.
Require Data.Foldable.
Require Data.Function.
Require Data.IntMap.Internal.
Require Data.OldList.
Require Data.Tuple.
Require GHC.Base.
Require GHC.Num.
Require UniqFM.
Require Unique.
Import GHC.Base.Notations.
Import GHC.Num.Notations.

(* Converted type declarations: *)

Inductive TaggedVal val : Type
  := Mk_TaggedVal : val -> GHC.Num.Int -> TaggedVal val.

Inductive UniqDFM ele : Type
  := UDFM
   : (Data.IntMap.Internal.IntMap (TaggedVal ele)) -> GHC.Num.Int -> UniqDFM ele.

Arguments Mk_TaggedVal {_} _ _.

Arguments UDFM {_} _ _.
(* Converted value declarations: *)

(* Skipping instance Outputable__UniqDFM of class Outputable *)

Local Definition Eq___TaggedVal_op_zeze__ {inst_val} `{GHC.Base.Eq_ inst_val}
   : (TaggedVal inst_val) -> (TaggedVal inst_val) -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | Mk_TaggedVal v1 _, Mk_TaggedVal v2 _ => v1 GHC.Base.== v2
    end.

Local Definition Eq___TaggedVal_op_zsze__ {inst_val} `{GHC.Base.Eq_ inst_val}
   : (TaggedVal inst_val) -> (TaggedVal inst_val) -> bool :=
  fun x y => negb (Eq___TaggedVal_op_zeze__ x y).

Program Instance Eq___TaggedVal {val} `{GHC.Base.Eq_ val}
   : GHC.Base.Eq_ (TaggedVal val) :=
  fun _ k =>
    k {| GHC.Base.op_zeze____ := Eq___TaggedVal_op_zeze__ ;
         GHC.Base.op_zsze____ := Eq___TaggedVal_op_zsze__ |}.

Local Definition Functor__TaggedVal_fmap
   : forall {a} {b}, (a -> b) -> TaggedVal a -> TaggedVal b :=
  fun {a} {b} =>
    fun arg_0__ arg_1__ =>
      match arg_0__, arg_1__ with
      | f, Mk_TaggedVal val i => Mk_TaggedVal (f val) i
      end.

Local Definition Functor__TaggedVal_op_zlzd__
   : forall {a} {b}, a -> TaggedVal b -> TaggedVal a :=
  fun {a} {b} => Functor__TaggedVal_fmap GHC.Base.∘ GHC.Base.const.

Program Instance Functor__TaggedVal : GHC.Base.Functor TaggedVal :=
  fun _ k =>
    k {| GHC.Base.fmap__ := fun {a} {b} => Functor__TaggedVal_fmap ;
         GHC.Base.op_zlzd____ := fun {a} {b} => Functor__TaggedVal_op_zlzd__ |}.

(* Skipping instance Functor__UniqDFM *)

(* Skipping instance Data__UniqDFM of class Data *)

(* Skipping instance Data__TaggedVal of class Data *)

Definition addToUDFM_Directly {elt}
   : UniqDFM elt -> Unique.Unique -> elt -> UniqDFM elt :=
  fun arg_0__ arg_1__ arg_2__ =>
    match arg_0__, arg_1__, arg_2__ with
    | UDFM m i, u, v =>
        let tf :=
          fun arg_3__ arg_4__ =>
            match arg_3__, arg_4__ with
            | Mk_TaggedVal new_v _, Mk_TaggedVal _ old_i => Mk_TaggedVal new_v old_i
            end in
        UDFM (Data.IntMap.Internal.insertWith tf (Unique.getWordKey u) (Mk_TaggedVal v
                                                                        i) m) (i GHC.Num.+ #1)
    end.

Definition addToUDFM {key} {elt} `{Unique.Uniquable key}
   : UniqDFM elt -> key -> elt -> UniqDFM elt :=
  fun m k v => addToUDFM_Directly m (Unique.getUnique k) v.

Definition addListToUDFM {key} {elt} `{Unique.Uniquable key}
   : UniqDFM elt -> list (key * elt)%type -> UniqDFM elt :=
  Data.Foldable.foldl (fun arg_0__ arg_1__ =>
                         match arg_0__, arg_1__ with
                         | m, pair k v => addToUDFM m k v
                         end).

Definition addListToUDFM_Directly {elt}
   : UniqDFM elt -> list (Unique.Unique * elt)%type -> UniqDFM elt :=
  Data.Foldable.foldl (fun arg_0__ arg_1__ =>
                         match arg_0__, arg_1__ with
                         | m, pair k v => addToUDFM_Directly m k v
                         end).

Definition addToUDFM_Directly_C {elt}
   : (elt -> elt -> elt) -> UniqDFM elt -> Unique.Unique -> elt -> UniqDFM elt :=
  fun arg_0__ arg_1__ arg_2__ arg_3__ =>
    match arg_0__, arg_1__, arg_2__, arg_3__ with
    | f, UDFM m i, u, v =>
        let tf :=
          fun arg_4__ arg_5__ =>
            match arg_4__, arg_5__ with
            | Mk_TaggedVal new_v _, Mk_TaggedVal old_v old_i =>
                Mk_TaggedVal (f old_v new_v) old_i
            end in
        UDFM (Data.IntMap.Internal.insertWith tf (Unique.getWordKey u) (Mk_TaggedVal v
                                                                        i) m) (i GHC.Num.+ #1)
    end.

Definition addToUDFM_C {key} {elt} `{Unique.Uniquable key}
   : (elt -> elt -> elt) -> UniqDFM elt -> key -> elt -> UniqDFM elt :=
  fun f m k v => addToUDFM_Directly_C f m (Unique.getUnique k) v.

Definition addListToUDFM_Directly_C {elt}
   : (elt -> elt -> elt) ->
     UniqDFM elt -> list (Unique.Unique * elt)%type -> UniqDFM elt :=
  fun f =>
    Data.Foldable.foldl (fun arg_0__ arg_1__ =>
                           match arg_0__, arg_1__ with
                           | m, pair k v => addToUDFM_Directly_C f m k v
                           end).

Definition adjustUDFM {key} {elt} `{Unique.Uniquable key}
   : (elt -> elt) -> UniqDFM elt -> key -> UniqDFM elt :=
  fun arg_0__ arg_1__ arg_2__ =>
    match arg_0__, arg_1__, arg_2__ with
    | f, UDFM m i, k =>
        UDFM (Data.IntMap.Internal.adjust (GHC.Base.fmap f) (Unique.getWordKey
                                                             (Unique.getUnique k)) m) i
    end.

Definition alterUDFM {key} {elt} `{Unique.Uniquable key}
   : (option elt -> option elt) -> UniqDFM elt -> key -> UniqDFM elt :=
  fun arg_0__ arg_1__ arg_2__ =>
    match arg_0__, arg_1__, arg_2__ with
    | f, UDFM m i, k =>
        let inject :=
          fun arg_3__ =>
            match arg_3__ with
            | None => None
            | Some v => Some (Mk_TaggedVal v i)
            end in
        let alterf :=
          fun arg_6__ =>
            match arg_6__ with
            | None => inject (f None)
            | Some (Mk_TaggedVal v _) => inject (f (Some v))
            end in
        UDFM (Data.IntMap.Internal.alter alterf (Unique.getWordKey (Unique.getUnique k))
              m) (i GHC.Num.+ #1)
    end.

Definition delFromUDFM {key} {elt} `{Unique.Uniquable key}
   : UniqDFM elt -> key -> UniqDFM elt :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | UDFM m i, k =>
        UDFM (Data.IntMap.Internal.delete (Unique.getWordKey (Unique.getUnique k)) m) i
    end.

Definition delListFromUDFM {key} {elt} `{Unique.Uniquable key}
   : UniqDFM elt -> list key -> UniqDFM elt :=
  Data.Foldable.foldl delFromUDFM.

Definition disjointUDFM {elt} : UniqDFM elt -> UniqDFM elt -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | UDFM x _i, UDFM y _j =>
        Data.IntMap.Internal.null (Data.IntMap.Internal.intersection x y)
    end.

Definition disjointUdfmUfm {elt} {elt2}
   : UniqDFM elt -> UniqFM.UniqFM elt2 -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | UDFM x _i, y =>
        Data.IntMap.Internal.null (Data.IntMap.Internal.intersection x
                                   (UniqFM.ufmToIntMap y))
    end.

Definition elemUDFM {key} {elt} `{Unique.Uniquable key}
   : key -> UniqDFM elt -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | k, UDFM m _i =>
        Data.IntMap.Internal.member (Unique.getWordKey (Unique.getUnique k)) m
    end.

Definition emptyUDFM {elt} : UniqDFM elt :=
  UDFM Data.IntMap.Internal.empty #0.

Definition listToUDFM_Directly {elt}
   : list (Unique.Unique * elt)%type -> UniqDFM elt :=
  Data.Foldable.foldl (fun arg_0__ arg_1__ =>
                         match arg_0__, arg_1__ with
                         | m, pair u v => addToUDFM_Directly m u v
                         end) emptyUDFM.

Definition alwaysUnsafeUfmToUdfm {elt} : UniqFM.UniqFM elt -> UniqDFM elt :=
  listToUDFM_Directly GHC.Base.∘ UniqFM.nonDetUFMToList.

Definition listToUDFM {key} {elt} `{Unique.Uniquable key}
   : list (key * elt)%type -> UniqDFM elt :=
  Data.Foldable.foldl (fun arg_0__ arg_1__ =>
                         match arg_0__, arg_1__ with
                         | m, pair k v => addToUDFM m k v
                         end) emptyUDFM.

Local Definition Monoid__UniqDFM_mempty {inst_a} : (UniqDFM inst_a) :=
  emptyUDFM.

Definition filterUDFM {elt} : (elt -> bool) -> UniqDFM elt -> UniqDFM elt :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | p, UDFM m i =>
        UDFM (Data.IntMap.Internal.filter (fun arg_2__ =>
                                             let 'Mk_TaggedVal v _ := arg_2__ in
                                             p v) m) i
    end.

Definition filterUDFM_Directly {elt}
   : (Unique.Unique -> elt -> bool) -> UniqDFM elt -> UniqDFM elt :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | p, UDFM m i =>
        let p' :=
          fun arg_2__ arg_3__ =>
            match arg_2__, arg_3__ with
            | k, Mk_TaggedVal v _ => p (Unique.getUnique k) v
            end in
        UDFM (Data.IntMap.Internal.filterWithKey p' m) i
    end.

Definition intersectUDFM {elt} : UniqDFM elt -> UniqDFM elt -> UniqDFM elt :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | UDFM x i, UDFM y _j => UDFM (Data.IntMap.Internal.intersection x y) i
    end.

Definition isNullUDFM {elt} : UniqDFM elt -> bool :=
  fun arg_0__ => let 'UDFM m _ := arg_0__ in Data.IntMap.Internal.null m.

Definition intersectsUDFM {elt} : UniqDFM elt -> UniqDFM elt -> bool :=
  fun x y => isNullUDFM (intersectUDFM x y).

Definition mapUDFM {elt1} {elt2}
   : (elt1 -> elt2) -> UniqDFM elt1 -> UniqDFM elt2 :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | f, UDFM m i => UDFM (Data.IntMap.Internal.map (GHC.Base.fmap f) m) i
    end.

Definition minusUDFM {elt1} {elt2}
   : UniqDFM elt1 -> UniqDFM elt2 -> UniqDFM elt1 :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | UDFM x i, UDFM y _j => UDFM (Data.IntMap.Internal.difference x y) i
    end.

Definition sizeUDFM {elt} : UniqDFM elt -> GHC.Num.Int :=
  fun um =>
    let 'UDFM m _ := um in
    Coq.ZArith.BinInt.Z.of_N (Data.IntMap.Internal.size m).

Definition taggedFst {val} : TaggedVal val -> val :=
  fun arg_0__ => let 'Mk_TaggedVal v _ := arg_0__ in v.

Definition udfmToUfm {elt} : UniqDFM elt -> UniqFM.UniqFM elt :=
  fun arg_0__ =>
    let 'UDFM m _i := arg_0__ in
    UniqFM.listToUFM_Directly (let cont_1__ arg_2__ :=
                                 let 'pair k tv := arg_2__ in
                                 cons (pair (Unique.getUnique k) (taggedFst tv)) nil in
                               Coq.Lists.List.flat_map cont_1__ (Data.IntMap.Internal.toList m)).

Definition partitionUDFM {elt}
   : (elt -> bool) -> UniqDFM elt -> (UniqDFM elt * UniqDFM elt)%type :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | p, UDFM m i =>
        let 'pair left_ right_ := Data.IntMap.Internal.partition (p GHC.Base.∘
                                                                  taggedFst) m in
        pair (UDFM left_ i) (UDFM right_ i)
    end.

Definition nonDetFoldUDFM {elt} {a}
   : (elt -> a -> a) -> a -> UniqDFM elt -> a :=
  fun arg_0__ arg_1__ arg_2__ =>
    match arg_0__, arg_1__, arg_2__ with
    | k, z, UDFM m _i =>
        Data.Foldable.foldr k z (GHC.Base.map taggedFst (Data.IntMap.Internal.elems m))
    end.

Definition lookupUDFM_Directly {elt}
   : UniqDFM elt -> Unique.Unique -> option elt :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | UDFM m _i, k =>
        GHC.Base.fmap taggedFst (Data.IntMap.Internal.lookup (Unique.getWordKey k) m)
    end.

Definition lookupUDFM {key} {elt} `{Unique.Uniquable key}
   : UniqDFM elt -> key -> option elt :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | UDFM m _i, k =>
        GHC.Base.fmap taggedFst (Data.IntMap.Internal.lookup (Unique.getWordKey
                                                              (Unique.getUnique k)) m)
    end.

Definition anyUDFM {elt} : (elt -> bool) -> UniqDFM elt -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | p, UDFM m _i =>
        Data.IntMap.Internal.foldr (orb GHC.Base.∘ (p GHC.Base.∘ taggedFst)) false m
    end.

Definition allUDFM {elt} : (elt -> bool) -> UniqDFM elt -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | p, UDFM m _i =>
        Data.IntMap.Internal.foldr (andb GHC.Base.∘ (p GHC.Base.∘ taggedFst)) true m
    end.

Definition taggedSnd {val} : TaggedVal val -> GHC.Num.Int :=
  fun arg_0__ => let 'Mk_TaggedVal _ i := arg_0__ in i.

Definition udfmToList {elt} : UniqDFM elt -> list (Unique.Unique * elt)%type :=
  fun arg_0__ =>
    let 'UDFM m _i := arg_0__ in
    let cont_1__ arg_2__ :=
      let 'pair k v := arg_2__ in
      cons (pair (Unique.getUnique k) (taggedFst v)) nil in
    Coq.Lists.List.flat_map cont_1__ (Data.OldList.sortBy (Data.Function.on
                                                           GHC.Base.compare (taggedSnd GHC.Base.∘ Data.Tuple.snd))
                             (Data.IntMap.Internal.toList m)).

Definition insertUDFMIntoLeft_C {elt}
   : (elt -> elt -> elt) -> UniqDFM elt -> UniqDFM elt -> UniqDFM elt :=
  fun f udfml udfmr => addListToUDFM_Directly_C f udfml (udfmToList udfmr).

Definition plusUDFM_C {elt}
   : (elt -> elt -> elt) -> UniqDFM elt -> UniqDFM elt -> UniqDFM elt :=
  fun arg_0__ arg_1__ arg_2__ =>
    match arg_0__, arg_1__, arg_2__ with
    | f, (UDFM _ i as udfml), (UDFM _ j as udfmr) =>
        if i GHC.Base.> j : bool then insertUDFMIntoLeft_C f udfml udfmr else
        insertUDFMIntoLeft_C f udfmr udfml
    end.

Definition insertUDFMIntoLeft {elt}
   : UniqDFM elt -> UniqDFM elt -> UniqDFM elt :=
  fun udfml udfmr => addListToUDFM_Directly udfml (udfmToList udfmr).

Definition plusUDFM {elt} : UniqDFM elt -> UniqDFM elt -> UniqDFM elt :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | (UDFM _ i as udfml), (UDFM _ j as udfmr) =>
        if i GHC.Base.> j : bool then insertUDFMIntoLeft udfml udfmr else
        insertUDFMIntoLeft udfmr udfml
    end.

Local Definition Semigroup__UniqDFM_op_zlzlzgzg__ {inst_a}
   : (UniqDFM inst_a) -> (UniqDFM inst_a) -> (UniqDFM inst_a) :=
  plusUDFM.

Program Instance Semigroup__UniqDFM {a} : GHC.Base.Semigroup (UniqDFM a) :=
  fun _ k => k {| GHC.Base.op_zlzlzgzg____ := Semigroup__UniqDFM_op_zlzlzgzg__ |}.

Local Definition Monoid__UniqDFM_mappend {inst_a}
   : (UniqDFM inst_a) -> (UniqDFM inst_a) -> (UniqDFM inst_a) :=
  _GHC.Base.<<>>_.

Local Definition Monoid__UniqDFM_mconcat {inst_a}
   : list (UniqDFM inst_a) -> (UniqDFM inst_a) :=
  GHC.Base.foldr Monoid__UniqDFM_mappend Monoid__UniqDFM_mempty.

Program Instance Monoid__UniqDFM {a} : GHC.Base.Monoid (UniqDFM a) :=
  fun _ k =>
    k {| GHC.Base.mappend__ := Monoid__UniqDFM_mappend ;
         GHC.Base.mconcat__ := Monoid__UniqDFM_mconcat ;
         GHC.Base.mempty__ := Monoid__UniqDFM_mempty |}.

Definition eltsUDFM {elt} : UniqDFM elt -> list elt :=
  fun arg_0__ =>
    let 'UDFM m _i := arg_0__ in
    GHC.Base.map taggedFst (Data.OldList.sortBy (Data.Function.on GHC.Base.compare
                                                                  taggedSnd) (Data.IntMap.Internal.elems m)).

Definition foldUDFM {elt} {a} : (elt -> a -> a) -> a -> UniqDFM elt -> a :=
  fun k z m => Data.Foldable.foldr k z (eltsUDFM m).

Definition pprUDFM {a}
   : UniqDFM a -> (list a -> GHC.Base.String) -> GHC.Base.String :=
  fun ufm pp => pp (eltsUDFM ufm).

Definition udfmIntersectUFM {elt1} {elt2}
   : UniqDFM elt1 -> UniqFM.UniqFM elt2 -> UniqDFM elt1 :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | UDFM x i, y =>
        UDFM (Data.IntMap.Internal.intersection x (UniqFM.ufmToIntMap y)) i
    end.

Definition udfmMinusUFM {elt1} {elt2}
   : UniqDFM elt1 -> UniqFM.UniqFM elt2 -> UniqDFM elt1 :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | UDFM x i, y =>
        UDFM (Data.IntMap.Internal.difference x (UniqFM.ufmToIntMap y)) i
    end.

Definition unitUDFM {key} {elt} `{Unique.Uniquable key}
   : key -> elt -> UniqDFM elt :=
  fun k v =>
    UDFM (Data.IntMap.Internal.singleton (Unique.getWordKey (Unique.getUnique k))
          (Mk_TaggedVal v #0)) #1.

(* External variables:
     None Some andb bool cons false list negb nil op_zt__ option orb pair true
     Coq.Lists.List.flat_map Coq.ZArith.BinInt.Z.of_N Data.Foldable.foldl
     Data.Foldable.foldr Data.Function.on Data.IntMap.Internal.IntMap
     Data.IntMap.Internal.adjust Data.IntMap.Internal.alter
     Data.IntMap.Internal.delete Data.IntMap.Internal.difference
     Data.IntMap.Internal.elems Data.IntMap.Internal.empty
     Data.IntMap.Internal.filter Data.IntMap.Internal.filterWithKey
     Data.IntMap.Internal.foldr Data.IntMap.Internal.insertWith
     Data.IntMap.Internal.intersection Data.IntMap.Internal.lookup
     Data.IntMap.Internal.map Data.IntMap.Internal.member Data.IntMap.Internal.null
     Data.IntMap.Internal.partition Data.IntMap.Internal.singleton
     Data.IntMap.Internal.size Data.IntMap.Internal.toList Data.OldList.sortBy
     Data.Tuple.snd GHC.Base.Eq_ GHC.Base.Functor GHC.Base.Monoid GHC.Base.Semigroup
     GHC.Base.String GHC.Base.compare GHC.Base.const GHC.Base.fmap GHC.Base.fmap__
     GHC.Base.foldr GHC.Base.map GHC.Base.mappend__ GHC.Base.mconcat__
     GHC.Base.mempty__ GHC.Base.op_z2218U__ GHC.Base.op_zeze__ GHC.Base.op_zeze____
     GHC.Base.op_zg__ GHC.Base.op_zlzd____ GHC.Base.op_zlzlzgzg__
     GHC.Base.op_zlzlzgzg____ GHC.Base.op_zsze____ GHC.Num.Int GHC.Num.fromInteger
     GHC.Num.op_zp__ UniqFM.UniqFM UniqFM.listToUFM_Directly UniqFM.nonDetUFMToList
     UniqFM.ufmToIntMap Unique.Uniquable Unique.Unique Unique.getUnique
     Unique.getWordKey
*)
