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

Inductive TaggedVal val : Type := Mk_TaggedVal : val -> GHC.Num.Int -> TaggedVal
                                                 val.

Inductive UniqDFM ele : Type := UDFM : (Data.IntMap.Internal.IntMap (TaggedVal
                                                                    ele)) -> GHC.Num.Int -> UniqDFM ele.

Arguments Mk_TaggedVal {_} _ _.

Arguments UDFM {_} _ _.
(* Converted value declarations: *)

Local Definition Eq___TaggedVal_op_zeze__ {inst_val} `{GHC.Base.Eq_ inst_val}
    : (TaggedVal inst_val) -> (TaggedVal inst_val) -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__ , arg_1__ with
      | Mk_TaggedVal v1 _ , Mk_TaggedVal v2 _ => v1 GHC.Base.== v2
    end.

Local Definition Eq___TaggedVal_op_zsze__ {inst_val} `{GHC.Base.Eq_ inst_val}
    : (TaggedVal inst_val) -> (TaggedVal inst_val) -> bool :=
  fun x y => negb (Eq___TaggedVal_op_zeze__ x y).

Program Instance Eq___TaggedVal {val} `{GHC.Base.Eq_ val} : GHC.Base.Eq_
                                                            (TaggedVal val) := fun _ k =>
    k {|GHC.Base.op_zeze____ := Eq___TaggedVal_op_zeze__ ;
      GHC.Base.op_zsze____ := Eq___TaggedVal_op_zsze__ |}.
Admit Obligations.

Local Definition Functor__TaggedVal_fmap : forall {a} {b},
                                             (a -> b) -> TaggedVal a -> TaggedVal b :=
  fun {a} {b} =>
    fun arg_0__ arg_1__ =>
      match arg_0__ , arg_1__ with
        | f , Mk_TaggedVal val i => Mk_TaggedVal (f val) i
      end.

Local Definition Functor__TaggedVal_op_zlzd__ : forall {a} {b},
                                                  a -> TaggedVal b -> TaggedVal a :=
  fun {a} {b} => fun x => Functor__TaggedVal_fmap (GHC.Base.const x).

Program Instance Functor__TaggedVal : GHC.Base.Functor TaggedVal := fun _ k =>
    k {|GHC.Base.op_zlzd____ := fun {a} {b} => Functor__TaggedVal_op_zlzd__ ;
      GHC.Base.fmap__ := fun {a} {b} => Functor__TaggedVal_fmap |}.
Admit Obligations.

(* Translating `instance forall {a}, forall `{Outputable.Outputable a},
   Outputable.Outputable (UniqDFM.UniqDFM a)' failed: OOPS! Cannot find information
   for class Qualified "Outputable" "Outputable" unsupported *)

(* Skipping instance Functor__UniqDFM *)

(* Translating `instance forall {ele}, forall `{Data.Data.Data ele},
   Data.Data.Data (UniqDFM.UniqDFM ele)' failed: OOPS! Cannot find information for
   class Qualified "Data.Data" "Data" unsupported *)

(* Translating `instance forall {val}, forall `{Data.Data.Data val},
   Data.Data.Data (UniqDFM.TaggedVal val)' failed: OOPS! Cannot find information
   for class Qualified "Data.Data" "Data" unsupported *)

Definition addToUDFM {key} {elt} `{Unique.Uniquable key} : UniqDFM
                                                           elt -> key -> elt -> UniqDFM elt :=
  fun arg_0__ arg_1__ arg_2__ =>
    match arg_0__ , arg_1__ , arg_2__ with
      | UDFM m i , k , v => UDFM (Data.IntMap.Internal.insert (Unique.getKey
                                                              GHC.Base.$ Unique.getUnique k) (Mk_TaggedVal v i) m) (i
                                                                                                                   GHC.Num.+
                                                                                                                   GHC.Num.fromInteger
                                                                                                                   1)
    end.

Definition addToUDFM_C {key} {elt} `{Unique.Uniquable key}
    : (elt -> elt -> elt) -> UniqDFM elt -> key -> elt -> UniqDFM elt :=
  fun arg_0__ arg_1__ arg_2__ arg_3__ =>
    match arg_0__ , arg_1__ , arg_2__ , arg_3__ with
      | f , UDFM m i , k , v => let tf :=
                                  fun arg_4__ arg_5__ =>
                                    match arg_4__ , arg_5__ with
                                      | Mk_TaggedVal a j , Mk_TaggedVal b _ => Mk_TaggedVal (f b a) j
                                    end in
                                UDFM (Data.IntMap.Internal.insertWith tf (Unique.getKey GHC.Base.$
                                                                         Unique.getUnique k) (Mk_TaggedVal v i) m) (i
                                                                                                                   GHC.Num.+
                                                                                                                   GHC.Num.fromInteger
                                                                                                                   1)
    end.

Definition addToUDFM_Directly {elt} : UniqDFM
                                      elt -> Unique.Unique -> elt -> UniqDFM elt :=
  fun arg_0__ arg_1__ arg_2__ =>
    match arg_0__ , arg_1__ , arg_2__ with
      | UDFM m i , u , v => UDFM (Data.IntMap.Internal.insert (Unique.getKey u)
                                 (Mk_TaggedVal v i) m) (i GHC.Num.+ GHC.Num.fromInteger 1)
    end.

Definition addListToUDFM_Directly {elt} : UniqDFM elt -> list (Unique.Unique *
                                                              elt)%type -> UniqDFM elt :=
  Data.Foldable.foldl (fun arg_0__ arg_1__ =>
                        match arg_0__ , arg_1__ with
                          | m , pair k v => addToUDFM_Directly m k v
                        end).

Definition addToUDFM_Directly_C {elt} : (elt -> elt -> elt) -> UniqDFM
                                        elt -> Unique.Unique -> elt -> UniqDFM elt :=
  fun arg_0__ arg_1__ arg_2__ arg_3__ =>
    match arg_0__ , arg_1__ , arg_2__ , arg_3__ with
      | f , UDFM m i , u , v => let tf :=
                                  fun arg_4__ arg_5__ =>
                                    match arg_4__ , arg_5__ with
                                      | Mk_TaggedVal a j , Mk_TaggedVal b _ => Mk_TaggedVal (f a b) j
                                    end in
                                UDFM (Data.IntMap.Internal.insertWith tf (Unique.getKey u) (Mk_TaggedVal v i) m)
                                (i GHC.Num.+ GHC.Num.fromInteger 1)
    end.

Definition addListToUDFM_Directly_C {elt} : (elt -> elt -> elt) -> UniqDFM
                                            elt -> list (Unique.Unique * elt)%type -> UniqDFM elt :=
  fun f =>
    Data.Foldable.foldl (fun arg_0__ arg_1__ =>
                          match arg_0__ , arg_1__ with
                            | m , pair k v => addToUDFM_Directly_C f m k v
                          end).

Definition adjustUDFM {key} {elt} `{Unique.Uniquable key}
    : (elt -> elt) -> UniqDFM elt -> key -> UniqDFM elt :=
  fun arg_0__ arg_1__ arg_2__ =>
    match arg_0__ , arg_1__ , arg_2__ with
      | f , UDFM m i , k => UDFM (Data.IntMap.Internal.adjust (GHC.Base.fmap f)
                                 (Unique.getKey GHC.Base.$ Unique.getUnique k) m) i
    end.

Definition alterUDFM {key} {elt} `{Unique.Uniquable key} : (option elt -> option
                                                           elt) -> UniqDFM elt -> key -> UniqDFM elt :=
  fun arg_0__ arg_1__ arg_2__ =>
    match arg_0__ , arg_1__ , arg_2__ with
      | f , UDFM m i , k => let inject :=
                              fun arg_3__ =>
                                match arg_3__ with
                                  | None => None
                                  | Some v => Some GHC.Base.$ Mk_TaggedVal v i
                                end in
                            let alterf :=
                              fun arg_6__ =>
                                match arg_6__ with
                                  | None => inject GHC.Base.$ f None
                                  | Some (Mk_TaggedVal v _) => inject GHC.Base.$ f (Some v)
                                end in
                            UDFM (Data.IntMap.Internal.alter alterf (Unique.getKey GHC.Base.$
                                                                    Unique.getUnique k) m) (i GHC.Num.+
                                                                                           GHC.Num.fromInteger 1)
    end.

Definition delFromUDFM {key} {elt} `{Unique.Uniquable key} : UniqDFM
                                                             elt -> key -> UniqDFM elt :=
  fun arg_0__ arg_1__ =>
    match arg_0__ , arg_1__ with
      | UDFM m i , k => UDFM (Data.IntMap.Internal.delete (Unique.getKey GHC.Base.$
                                                          Unique.getUnique k) m) i
    end.

Definition delListFromUDFM {key} {elt} `{Unique.Uniquable key} : UniqDFM
                                                                 elt -> list key -> UniqDFM elt :=
  Data.Foldable.foldl delFromUDFM.

Definition disjointUDFM {elt} : UniqDFM elt -> UniqDFM elt -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__ , arg_1__ with
      | UDFM x _i , UDFM y _j => Data.IntMap.Internal.null
                                 (Data.IntMap.Internal.intersection x y)
    end.

Definition disjointUdfmUfm {elt} {elt2} : UniqDFM elt -> UniqFM.UniqFM
                                          elt2 -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__ , arg_1__ with
      | UDFM x _i , y => Data.IntMap.Internal.null (Data.IntMap.Internal.intersection
                                                   x (UniqFM.ufmToIntMap y))
    end.

Definition elemUDFM {key} {elt} `{Unique.Uniquable key} : key -> UniqDFM
                                                          elt -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__ , arg_1__ with
      | k , UDFM m _i => Data.IntMap.Internal.member (Unique.getKey GHC.Base.$
                                                     Unique.getUnique k) m
    end.

Definition emptyUDFM {elt} : UniqDFM elt :=
  UDFM Data.IntMap.Internal.empty (GHC.Num.fromInteger 0).

Definition listToUDFM_Directly {elt} : list (Unique.Unique *
                                            elt)%type -> UniqDFM elt :=
  Data.Foldable.foldl (fun arg_0__ arg_1__ =>
                        match arg_0__ , arg_1__ with
                          | m , pair u v => addToUDFM_Directly m u v
                        end) emptyUDFM.

Definition alwaysUnsafeUfmToUdfm {elt} : UniqFM.UniqFM elt -> UniqDFM elt :=
  listToUDFM_Directly GHC.Base.∘ UniqFM.ufmToList.

Local Definition Monoid__UniqDFM_mempty {inst_a} : (UniqDFM inst_a) :=
  emptyUDFM.

Definition filterUDFM {elt} : (elt -> bool) -> UniqDFM elt -> UniqDFM elt :=
  fun arg_0__ arg_1__ =>
    match arg_0__ , arg_1__ with
      | p , UDFM m i => UDFM (Data.IntMap.Internal.filter (fun arg_2__ =>
                                                            match arg_2__ with
                                                              | Mk_TaggedVal v _ => p v
                                                            end) m) i
    end.

Definition filterUDFM_Directly {elt} : (Unique.Unique -> elt -> bool) -> UniqDFM
                                       elt -> UniqDFM elt :=
  fun arg_0__ arg_1__ =>
    match arg_0__ , arg_1__ with
      | p , UDFM m i => let p' :=
                          fun arg_2__ arg_3__ =>
                            match arg_2__ , arg_3__ with
                              | k , Mk_TaggedVal v _ => p (Unique.getUnique k) v
                            end in
                        UDFM (Data.IntMap.Internal.filterWithKey p' m) i
    end.

Definition intersectUDFM {elt} : UniqDFM elt -> UniqDFM elt -> UniqDFM elt :=
  fun arg_0__ arg_1__ =>
    match arg_0__ , arg_1__ with
      | UDFM x i , UDFM y _j => UDFM (Data.IntMap.Internal.intersection x y) i
    end.

Definition isNullUDFM {elt} : UniqDFM elt -> bool :=
  fun arg_0__ => match arg_0__ with | UDFM m _ => Data.IntMap.Internal.null m end.

Definition intersectsUDFM {elt} : UniqDFM elt -> UniqDFM elt -> bool :=
  fun x y => isNullUDFM (intersectUDFM x y).

Definition mapUDFM {elt1} {elt2} : (elt1 -> elt2) -> UniqDFM elt1 -> UniqDFM
                                   elt2 :=
  fun arg_0__ arg_1__ =>
    match arg_0__ , arg_1__ with
      | f , UDFM m i => UDFM (Data.IntMap.Internal.map (GHC.Base.fmap f) m) i
    end.

Definition minusUDFM {elt1} {elt2} : UniqDFM elt1 -> UniqDFM elt2 -> UniqDFM
                                     elt1 :=
  fun arg_0__ arg_1__ =>
    match arg_0__ , arg_1__ with
      | UDFM x i , UDFM y _j => UDFM (Data.IntMap.Internal.difference x y) i
    end.

Definition sizeUDFM {elt} : UniqDFM elt -> GHC.Num.Int :=
  fun arg_0__ =>
    match arg_0__ with
      | UDFM m _i => Data.IntMap.Internal.size m
    end.

Definition taggedFst {val} : TaggedVal val -> val :=
  fun arg_0__ => match arg_0__ with | Mk_TaggedVal v _ => v end.

Definition udfmToUfm {elt} : UniqDFM elt -> UniqFM.UniqFM elt :=
  fun arg_0__ =>
    match arg_0__ with
      | UDFM m _i => UniqFM.listToUFM_Directly (let cont_1__ arg_2__ :=
                                                 match arg_2__ with
                                                   | pair k tv => cons (pair (Unique.getUnique k) (taggedFst tv)) nil
                                                 end in
                                               Coq.Lists.List.flat_map cont_1__ (Data.IntMap.Internal.toList m))
    end.

Definition partitionUDFM {elt} : (elt -> bool) -> UniqDFM elt -> (UniqDFM elt *
                                 UniqDFM elt)%type :=
  fun arg_0__ arg_1__ =>
    match arg_0__ , arg_1__ with
      | p , UDFM m i => match Data.IntMap.Internal.partition (p GHC.Base.∘ taggedFst)
                                m with
                          | pair left_ right_ => pair (UDFM left_ i) (UDFM right_ i)
                        end
    end.

Definition nonDetFoldUDFM {elt} {a} : (elt -> a -> a) -> a -> UniqDFM
                                      elt -> a :=
  fun arg_0__ arg_1__ arg_2__ =>
    match arg_0__ , arg_1__ , arg_2__ with
      | k , z , UDFM m _i => Data.Foldable.foldr k z GHC.Base.$ (GHC.Base.map
                             taggedFst GHC.Base.$ Data.IntMap.Internal.elems m)
    end.

Definition lookupUDFM {key} {elt} `{Unique.Uniquable key} : UniqDFM
                                                            elt -> key -> option elt :=
  fun arg_0__ arg_1__ =>
    match arg_0__ , arg_1__ with
      | UDFM m _i , k => GHC.Base.fmap taggedFst (Data.IntMap.Internal.lookup
                                       (Unique.getKey GHC.Base.$ Unique.getUnique k) m)
    end.

Definition anyUDFM {elt} : (elt -> bool) -> UniqDFM elt -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__ , arg_1__ with
      | p , UDFM m _i => Data.IntMap.Internal.foldr (orb GHC.Base.∘ (p GHC.Base.∘
                                                    taggedFst)) false m
    end.

Definition taggedSnd {val} : TaggedVal val -> GHC.Num.Int :=
  fun arg_0__ => match arg_0__ with | Mk_TaggedVal _ i => i end.

Definition udfmToList {elt} : UniqDFM elt -> list (Unique.Unique * elt)%type :=
  fun arg_0__ =>
    match arg_0__ with
      | UDFM m _i => let cont_1__ arg_2__ :=
                       match arg_2__ with
                         | pair k v => cons (pair (Unique.getUnique k) (taggedFst v)) nil
                       end in
                     Coq.Lists.List.flat_map cont_1__ (Data.OldList.sortBy (Data.Function.on
                                                                           GHC.Base.compare (taggedSnd GHC.Base.∘
                                                                           Data.Tuple.snd)) GHC.Base.$
                                             Data.IntMap.Internal.toList m)
    end.

Definition insertUDFMIntoLeft_C {elt} : (elt -> elt -> elt) -> UniqDFM
                                        elt -> UniqDFM elt -> UniqDFM elt :=
  fun f udfml udfmr =>
    addListToUDFM_Directly_C f udfml GHC.Base.$ udfmToList udfmr.

Definition plusUDFM_C {elt} : (elt -> elt -> elt) -> UniqDFM elt -> UniqDFM
                              elt -> UniqDFM elt :=
  fun arg_0__ arg_1__ arg_2__ =>
    match arg_0__ , arg_1__ , arg_2__ with
      | f , (UDFM _ i as udfml) , (UDFM _ j as udfmr) => if i GHC.Base.> j : bool
                                                         then insertUDFMIntoLeft_C f udfml udfmr
                                                         else insertUDFMIntoLeft_C f udfmr udfml
    end.

Definition insertUDFMIntoLeft {elt} : UniqDFM elt -> UniqDFM elt -> UniqDFM
                                      elt :=
  fun udfml udfmr => addListToUDFM_Directly udfml GHC.Base.$ udfmToList udfmr.

Definition plusUDFM {elt} : UniqDFM elt -> UniqDFM elt -> UniqDFM elt :=
  fun arg_0__ arg_1__ =>
    match arg_0__ , arg_1__ with
      | (UDFM _ i as udfml) , (UDFM _ j as udfmr) => if i GHC.Base.> j : bool
                                                     then insertUDFMIntoLeft udfml udfmr
                                                     else insertUDFMIntoLeft udfmr udfml
    end.

Local Definition Monoid__UniqDFM_mappend {inst_a} : (UniqDFM inst_a) -> (UniqDFM
                                                    inst_a) -> (UniqDFM inst_a) :=
  plusUDFM.

Local Definition Monoid__UniqDFM_mconcat {inst_a} : list (UniqDFM
                                                         inst_a) -> (UniqDFM inst_a) :=
  GHC.Base.foldr Monoid__UniqDFM_mappend Monoid__UniqDFM_mempty.

Program Instance Monoid__UniqDFM {a} : GHC.Base.Monoid (UniqDFM a) := fun _ k =>
    k {|GHC.Base.mappend__ := Monoid__UniqDFM_mappend ;
      GHC.Base.mconcat__ := Monoid__UniqDFM_mconcat ;
      GHC.Base.mempty__ := Monoid__UniqDFM_mempty |}.
Admit Obligations.

Definition eltsUDFM {elt} : UniqDFM elt -> list elt :=
  fun arg_0__ =>
    match arg_0__ with
      | UDFM m _i => GHC.Base.map taggedFst GHC.Base.$ (Data.OldList.sortBy
                     (Data.Function.on GHC.Base.compare taggedSnd) GHC.Base.$
                     Data.IntMap.Internal.elems m)
    end.

Definition foldUDFM {elt} {a} : (elt -> a -> a) -> a -> UniqDFM elt -> a :=
  fun k z m => Data.Foldable.foldr k z (eltsUDFM m).

Definition udfmIntersectUFM {elt} : UniqDFM elt -> UniqFM.UniqFM elt -> UniqDFM
                                    elt :=
  fun arg_0__ arg_1__ =>
    match arg_0__ , arg_1__ with
      | UDFM x i , y => UDFM (Data.IntMap.Internal.intersection x (UniqFM.ufmToIntMap
                                                                  y)) i
    end.

Definition udfmMinusUFM {elt1} {elt2} : UniqDFM elt1 -> UniqFM.UniqFM
                                        elt2 -> UniqDFM elt1 :=
  fun arg_0__ arg_1__ =>
    match arg_0__ , arg_1__ with
      | UDFM x i , y => UDFM (Data.IntMap.Internal.difference x (UniqFM.ufmToIntMap
                                                                y)) i
    end.

Definition unitUDFM {key} {elt} `{Unique.Uniquable key} : key -> elt -> UniqDFM
                                                          elt :=
  fun k v =>
    UDFM (Data.IntMap.Internal.singleton (Unique.getKey GHC.Base.$ Unique.getUnique
                                         k) (Mk_TaggedVal v (GHC.Num.fromInteger 0))) (GHC.Num.fromInteger 1).

(* Unbound variables:
     None Some bool cons false list negb nil op_zt__ option orb pair
     Coq.Lists.List.flat_map Data.Foldable.foldl Data.Foldable.foldr Data.Function.on
     Data.IntMap.Internal.IntMap Data.IntMap.Internal.adjust
     Data.IntMap.Internal.alter Data.IntMap.Internal.delete
     Data.IntMap.Internal.difference Data.IntMap.Internal.elems
     Data.IntMap.Internal.empty Data.IntMap.Internal.filter
     Data.IntMap.Internal.filterWithKey Data.IntMap.Internal.foldr
     Data.IntMap.Internal.insert Data.IntMap.Internal.insertWith
     Data.IntMap.Internal.intersection Data.IntMap.Internal.lookup
     Data.IntMap.Internal.map Data.IntMap.Internal.member Data.IntMap.Internal.null
     Data.IntMap.Internal.partition Data.IntMap.Internal.singleton
     Data.IntMap.Internal.size Data.IntMap.Internal.toList Data.OldList.sortBy
     Data.Tuple.snd GHC.Base.Eq_ GHC.Base.Functor GHC.Base.Monoid GHC.Base.compare
     GHC.Base.const GHC.Base.fmap GHC.Base.foldr GHC.Base.map GHC.Base.op_z2218U__
     GHC.Base.op_zd__ GHC.Base.op_zeze__ GHC.Base.op_zg__ GHC.Num.Int GHC.Num.op_zp__
     UniqFM.UniqFM UniqFM.listToUFM_Directly UniqFM.ufmToIntMap UniqFM.ufmToList
     Unique.Uniquable Unique.Unique Unique.getKey Unique.getUnique
*)
