(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Coq.Program.Tactics.
Require Coq.Program.Wf.

(* Converted imports: *)

Require Data.Foldable.
Require Data.IntMap.Internal.
Require GHC.Base.
Require GHC.Num.
Require GHC.Prim.
Require Unique.
Import GHC.Base.Notations.

(* Converted type declarations: *)

Inductive UniqFM ele : Type := UFM : (Data.IntMap.Internal.IntMap ele) -> UniqFM
                                     ele.

Arguments UFM {_} _.
(* Midamble *)

Require Data.IntSet.Internal.

Axiom ufmToSet_Directly : forall {elt}, UniqFM elt -> Data.IntSet.Internal.IntSet.

Require Panic.

Instance Default_UniqFM {a} : Panic.Default (UniqFM a) :=
  Panic.Build_Default _ (UFM Data.IntMap.Internal.empty).

(* Converted value declarations: *)

Instance Unpeel_UniqFM ele : GHC.Prim.Unpeel (UniqFM ele)
                                             (Data.IntMap.Internal.IntMap ele) := GHC.Prim.Build_Unpeel _ _ (fun x =>
                                                                                                          match x with
                                                                                                            | UFM y => y
                                                                                                          end) UFM.

(* Translating `instance forall {a}, Data.Semigroup.Semigroup (UniqFM.UniqFM a)'
   failed: OOPS! Cannot find information for class Qualified "Data.Semigroup"
   "Semigroup" unsupported *)

(* Translating `instance forall {a}, forall `{Outputable.Outputable a},
   Outputable.Outputable (UniqFM.UniqFM a)' failed: OOPS! Cannot find information
   for class Qualified "Outputable" "Outputable" unsupported *)

(* Skipping instance Traversable__UniqFM *)

(* Skipping instance Functor__UniqFM *)

Local Definition Eq___UniqFM_op_zeze__ {inst_ele} `{GHC.Base.Eq_ inst_ele}
    : UniqFM inst_ele -> UniqFM inst_ele -> bool :=
  GHC.Prim.coerce _GHC.Base.==_.

Local Definition Eq___UniqFM_op_zsze__ {inst_ele} `{GHC.Base.Eq_ inst_ele}
    : UniqFM inst_ele -> UniqFM inst_ele -> bool :=
  GHC.Prim.coerce _GHC.Base./=_.

Program Instance Eq___UniqFM {ele} `{GHC.Base.Eq_ ele} : GHC.Base.Eq_ (UniqFM
                                                                      ele) := fun _ k =>
    k {|GHC.Base.op_zeze____ := Eq___UniqFM_op_zeze__ ;
      GHC.Base.op_zsze____ := Eq___UniqFM_op_zsze__ |}.

(* Translating `instance forall {ele}, forall `{Data.Data.Data ele},
   Data.Data.Data (UniqFM.UniqFM ele)' failed: OOPS! Cannot find information for
   class Qualified "Data.Data" "Data" unsupported *)

(* Skipping instance Foldable__UniqFM *)

Definition addToUFM {key} {elt} `{Unique.Uniquable key} : UniqFM
                                                          elt -> key -> elt -> UniqFM elt :=
  fun arg_0__ arg_1__ arg_2__ =>
    match arg_0__ , arg_1__ , arg_2__ with
      | UFM m , k , v => UFM (Data.IntMap.Internal.insert (Unique.getKey GHC.Base.$
                                                          Unique.getUnique k) v m)
    end.

Definition addListToUFM {key} {elt} `{Unique.Uniquable key} : UniqFM elt -> list
                                                              (key * elt)%type -> UniqFM elt :=
  Data.Foldable.foldl (fun arg_0__ arg_1__ =>
                        match arg_0__ , arg_1__ with
                          | m , pair k v => addToUFM m k v
                        end).

Definition addToUFM_Acc {key} {elt} {elts} `{Unique.Uniquable key}
    : (elt -> elts -> elts) -> (elt -> elts) -> UniqFM elts -> key -> elt -> UniqFM
      elts :=
  fun arg_0__ arg_1__ arg_2__ arg_3__ arg_4__ =>
    match arg_0__ , arg_1__ , arg_2__ , arg_3__ , arg_4__ with
      | exi , new , UFM m , k , v => UFM (Data.IntMap.Internal.insertWith (fun _new
                                                                               old =>
                                                                            exi v old) (Unique.getKey GHC.Base.$
                                                                                       Unique.getUnique k) (new v) m)
    end.

Definition addToUFM_C {key} {elt} `{Unique.Uniquable key}
    : (elt -> elt -> elt) -> UniqFM elt -> key -> elt -> UniqFM elt :=
  fun arg_0__ arg_1__ arg_2__ arg_3__ =>
    match arg_0__ , arg_1__ , arg_2__ , arg_3__ with
      | f , UFM m , k , v => UFM (Data.IntMap.Internal.insertWith (GHC.Base.flip f)
                                 (Unique.getKey GHC.Base.$ Unique.getUnique k) v m)
    end.

Definition addListToUFM_C {key} {elt} `{Unique.Uniquable key}
    : (elt -> elt -> elt) -> UniqFM elt -> list (key * elt)%type -> UniqFM elt :=
  fun f =>
    Data.Foldable.foldl (fun arg_0__ arg_1__ =>
                          match arg_0__ , arg_1__ with
                            | m , pair k v => addToUFM_C f m k v
                          end).

Definition addToUFM_Directly {elt} : UniqFM
                                     elt -> Unique.Unique -> elt -> UniqFM elt :=
  fun arg_0__ arg_1__ arg_2__ =>
    match arg_0__ , arg_1__ , arg_2__ with
      | UFM m , u , v => UFM (Data.IntMap.Internal.insert (Unique.getKey u) v m)
    end.

Definition addListToUFM_Directly {elt} : UniqFM elt -> list (Unique.Unique *
                                                            elt)%type -> UniqFM elt :=
  Data.Foldable.foldl (fun arg_0__ arg_1__ =>
                        match arg_0__ , arg_1__ with
                          | m , pair k v => addToUFM_Directly m k v
                        end).

Definition adjustUFM {key} {elt} `{Unique.Uniquable key}
    : (elt -> elt) -> UniqFM elt -> key -> UniqFM elt :=
  fun arg_0__ arg_1__ arg_2__ =>
    match arg_0__ , arg_1__ , arg_2__ with
      | f , UFM m , k => UFM (Data.IntMap.Internal.adjust f (Unique.getKey GHC.Base.$
                                                            Unique.getUnique k) m)
    end.

Definition adjustUFM_Directly {elt} : (elt -> elt) -> UniqFM
                                      elt -> Unique.Unique -> UniqFM elt :=
  fun arg_0__ arg_1__ arg_2__ =>
    match arg_0__ , arg_1__ , arg_2__ with
      | f , UFM m , u => UFM (Data.IntMap.Internal.adjust f (Unique.getKey u) m)
    end.

Definition alterUFM {key} {elt} `{Unique.Uniquable key} : (option elt -> option
                                                          elt) -> UniqFM elt -> key -> UniqFM elt :=
  fun arg_0__ arg_1__ arg_2__ =>
    match arg_0__ , arg_1__ , arg_2__ with
      | f , UFM m , k => UFM (Data.IntMap.Internal.alter f (Unique.getKey GHC.Base.$
                                                           Unique.getUnique k) m)
    end.

Definition delFromUFM {key} {elt} `{Unique.Uniquable key} : UniqFM
                                                            elt -> key -> UniqFM elt :=
  fun arg_0__ arg_1__ =>
    match arg_0__ , arg_1__ with
      | UFM m , k => UFM (Data.IntMap.Internal.delete (Unique.getKey GHC.Base.$
                                                      Unique.getUnique k) m)
    end.

Definition delListFromUFM {key} {elt} `{Unique.Uniquable key} : UniqFM
                                                                elt -> list key -> UniqFM elt :=
  Data.Foldable.foldl delFromUFM.

Definition delFromUFM_Directly {elt} : UniqFM elt -> Unique.Unique -> UniqFM
                                       elt :=
  fun arg_0__ arg_1__ =>
    match arg_0__ , arg_1__ with
      | UFM m , u => UFM (Data.IntMap.Internal.delete (Unique.getKey u) m)
    end.

Definition delListFromUFM_Directly {elt} : UniqFM elt -> list
                                           Unique.Unique -> UniqFM elt :=
  Data.Foldable.foldl delFromUFM_Directly.

Definition disjointUFM {elt1} {elt2} : UniqFM elt1 -> UniqFM elt2 -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__ , arg_1__ with
      | UFM x , UFM y => Data.IntMap.Internal.null (Data.IntMap.Internal.intersection
                                                   x y)
    end.

Definition elemUFM {key} {elt} `{Unique.Uniquable key} : key -> UniqFM
                                                         elt -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__ , arg_1__ with
      | k , UFM m => Data.IntMap.Internal.member (Unique.getKey GHC.Base.$
                                                 Unique.getUnique k) m
    end.

Definition elemUFM_Directly {elt} : Unique.Unique -> UniqFM elt -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__ , arg_1__ with
      | u , UFM m => Data.IntMap.Internal.member (Unique.getKey u) m
    end.

Definition eltsUFM {elt} : UniqFM elt -> list elt :=
  fun arg_0__ => match arg_0__ with | UFM m => Data.IntMap.Internal.elems m end.

Definition emptyUFM {elt} : UniqFM elt :=
  UFM Data.IntMap.Internal.empty.

Definition listToUFM_Directly {elt} : list (Unique.Unique * elt)%type -> UniqFM
                                      elt :=
  Data.Foldable.foldl (fun arg_0__ arg_1__ =>
                        match arg_0__ , arg_1__ with
                          | m , pair u v => addToUFM_Directly m u v
                        end) emptyUFM.

Definition listToUFM_C {key} {elt} `{Unique.Uniquable key}
    : (elt -> elt -> elt) -> list (key * elt)%type -> UniqFM elt :=
  fun f =>
    Data.Foldable.foldl (fun arg_0__ arg_1__ =>
                          match arg_0__ , arg_1__ with
                            | m , pair k v => addToUFM_C f m k v
                          end) emptyUFM.

Definition listToUFM {key} {elt} `{Unique.Uniquable key} : list (key *
                                                                elt)%type -> UniqFM elt :=
  Data.Foldable.foldl (fun arg_0__ arg_1__ =>
                        match arg_0__ , arg_1__ with
                          | m , pair k v => addToUFM m k v
                        end) emptyUFM.

Local Definition Monoid__UniqFM_mempty {inst_a} : (UniqFM inst_a) :=
  emptyUFM.

Definition filterUFM {elt} : (elt -> bool) -> UniqFM elt -> UniqFM elt :=
  fun arg_0__ arg_1__ =>
    match arg_0__ , arg_1__ with
      | p , UFM m => UFM (Data.IntMap.Internal.filter p m)
    end.

Definition filterUFM_Directly {elt} : (Unique.Unique -> elt -> bool) -> UniqFM
                                      elt -> UniqFM elt :=
  fun arg_0__ arg_1__ =>
    match arg_0__ , arg_1__ with
      | p , UFM m => UFM (Data.IntMap.Internal.filterWithKey (p GHC.Base.∘
                                                             Unique.getUnique) m)
    end.

Definition foldUFM {elt} {a} : (elt -> a -> a) -> a -> UniqFM elt -> a :=
  fun arg_0__ arg_1__ arg_2__ =>
    match arg_0__ , arg_1__ , arg_2__ with
      | k , z , UFM m => Data.IntMap.Internal.fold k z m
    end.

Definition foldUFM_Directly {elt} {a}
    : (Unique.Unique -> elt -> a -> a) -> a -> UniqFM elt -> a :=
  fun arg_0__ arg_1__ arg_2__ =>
    match arg_0__ , arg_1__ , arg_2__ with
      | k , z , UFM m => Data.IntMap.Internal.foldWithKey (k GHC.Base.∘
                                                          Unique.getUnique) z m
    end.

Definition intersectUFM {elt} : UniqFM elt -> UniqFM elt -> UniqFM elt :=
  fun arg_0__ arg_1__ =>
    match arg_0__ , arg_1__ with
      | UFM x , UFM y => UFM (Data.IntMap.Internal.intersection x y)
    end.

Definition intersectUFM_C {elt1} {elt2} {elt3}
    : (elt1 -> elt2 -> elt3) -> UniqFM elt1 -> UniqFM elt2 -> UniqFM elt3 :=
  fun arg_0__ arg_1__ arg_2__ =>
    match arg_0__ , arg_1__ , arg_2__ with
      | f , UFM x , UFM y => UFM (Data.IntMap.Internal.intersectionWith f x y)
    end.

Definition isNullUFM {elt} : UniqFM elt -> bool :=
  fun arg_0__ => match arg_0__ with | UFM m => Data.IntMap.Internal.null m end.

Definition keysUFM {elt} : UniqFM elt -> list Unique.Unique :=
  fun arg_0__ =>
    match arg_0__ with
      | UFM m => GHC.Base.map Unique.getUnique GHC.Base.$ Data.IntMap.Internal.keys m
    end.

Definition lookupUFM {key} {elt} `{Unique.Uniquable key} : UniqFM
                                                           elt -> key -> option elt :=
  fun arg_0__ arg_1__ =>
    match arg_0__ , arg_1__ with
      | UFM m , k => Data.IntMap.Internal.lookup (Unique.getKey GHC.Base.$
                                                 Unique.getUnique k) m
    end.

Definition lookupUFM_Directly {elt} : UniqFM elt -> Unique.Unique -> option
                                      elt :=
  fun arg_0__ arg_1__ =>
    match arg_0__ , arg_1__ with
      | UFM m , u => Data.IntMap.Internal.lookup (Unique.getKey u) m
    end.

Definition lookupWithDefaultUFM {key} {elt} `{Unique.Uniquable key} : UniqFM
                                                                      elt -> elt -> key -> elt :=
  fun arg_0__ arg_1__ arg_2__ =>
    match arg_0__ , arg_1__ , arg_2__ with
      | UFM m , v , k => Data.IntMap.Internal.findWithDefault v (Unique.getKey
                                                                GHC.Base.$ Unique.getUnique k) m
    end.

Definition lookupWithDefaultUFM_Directly {elt} : UniqFM
                                                 elt -> elt -> Unique.Unique -> elt :=
  fun arg_0__ arg_1__ arg_2__ =>
    match arg_0__ , arg_1__ , arg_2__ with
      | UFM m , v , u => Data.IntMap.Internal.findWithDefault v (Unique.getKey u) m
    end.

Definition mapUFM {elt1} {elt2} : (elt1 -> elt2) -> UniqFM elt1 -> UniqFM
                                  elt2 :=
  fun arg_0__ arg_1__ =>
    match arg_0__ , arg_1__ with
      | f , UFM m => UFM (Data.IntMap.Internal.map f m)
    end.

Definition mapUFM_Directly {elt1} {elt2}
    : (Unique.Unique -> elt1 -> elt2) -> UniqFM elt1 -> UniqFM elt2 :=
  fun arg_0__ arg_1__ =>
    match arg_0__ , arg_1__ with
      | f , UFM m => UFM (Data.IntMap.Internal.mapWithKey (f GHC.Base.∘
                                                          Unique.getUnique) m)
    end.

Definition minusUFM {elt1} {elt2} : UniqFM elt1 -> UniqFM elt2 -> UniqFM elt1 :=
  fun arg_0__ arg_1__ =>
    match arg_0__ , arg_1__ with
      | UFM x , UFM y => UFM (Data.IntMap.Internal.difference x y)
    end.

Definition nonDetEltsUFM {elt} : UniqFM elt -> list elt :=
  fun arg_0__ => match arg_0__ with | UFM m => Data.IntMap.Internal.elems m end.

Definition partitionUFM {elt} : (elt -> bool) -> UniqFM elt -> (UniqFM elt *
                                UniqFM elt)%type :=
  fun arg_0__ arg_1__ =>
    match arg_0__ , arg_1__ with
      | p , UFM m => match Data.IntMap.Internal.partition p m with
                       | pair left_ right_ => pair (UFM left_) (UFM right_)
                     end
    end.

Definition plusUFM {elt} : UniqFM elt -> UniqFM elt -> UniqFM elt :=
  fun arg_0__ arg_1__ =>
    match arg_0__ , arg_1__ with
      | UFM x , UFM y => UFM (Data.IntMap.Internal.union y x)
    end.

Local Definition Monoid__UniqFM_mappend {inst_a} : (UniqFM inst_a) -> (UniqFM
                                                   inst_a) -> (UniqFM inst_a) :=
  plusUFM.

Local Definition Monoid__UniqFM_mconcat {inst_a} : list (UniqFM
                                                        inst_a) -> (UniqFM inst_a) :=
  GHC.Base.foldr Monoid__UniqFM_mappend Monoid__UniqFM_mempty.

Program Instance Monoid__UniqFM {a} : GHC.Base.Monoid (UniqFM a) := fun _ k =>
    k {|GHC.Base.mappend__ := Monoid__UniqFM_mappend ;
      GHC.Base.mconcat__ := Monoid__UniqFM_mconcat ;
      GHC.Base.mempty__ := Monoid__UniqFM_mempty |}.

Definition plusUFM_C {elt} : (elt -> elt -> elt) -> UniqFM elt -> UniqFM
                             elt -> UniqFM elt :=
  fun arg_0__ arg_1__ arg_2__ =>
    match arg_0__ , arg_1__ , arg_2__ with
      | f , UFM x , UFM y => UFM (Data.IntMap.Internal.unionWith f x y)
    end.

Definition sizeUFM {elt} : UniqFM elt -> GHC.Num.Int :=
  fun arg_0__ => match arg_0__ with | UFM m => Data.IntMap.Internal.size m end.

Definition splitUFM {key} {elt} `{Unique.Uniquable key} : UniqFM
                                                          elt -> key -> (UniqFM elt * option elt * UniqFM elt)%type :=
  fun arg_0__ arg_1__ =>
    match arg_0__ , arg_1__ with
      | UFM m , k => match Data.IntMap.Internal.splitLookup (Unique.getKey GHC.Base.$
                                                            Unique.getUnique k) m with
                       | pair (pair less equal) greater => pair (pair (UFM less) equal) (UFM greater)
                     end
    end.

Definition ufmToIntMap {elt} : UniqFM elt -> Data.IntMap.Internal.IntMap elt :=
  fun arg_0__ => match arg_0__ with | UFM m => m end.

Definition ufmToList {elt} : UniqFM elt -> list (Unique.Unique * elt)%type :=
  fun arg_0__ =>
    match arg_0__ with
      | UFM m => GHC.Base.map (fun arg_1__ =>
                                match arg_1__ with
                                  | pair k v => pair (Unique.getUnique k) v
                                end) GHC.Base.$ Data.IntMap.Internal.toList m
    end.

Definition unitDirectlyUFM {elt} : Unique.Unique -> elt -> UniqFM elt :=
  fun u v => UFM (Data.IntMap.Internal.singleton (Unique.getKey u) v).

Definition unitUFM {key} {elt} `{Unique.Uniquable key} : key -> elt -> UniqFM
                                                         elt :=
  fun k v =>
    UFM (Data.IntMap.Internal.singleton (Unique.getKey GHC.Base.$ Unique.getUnique
                                        k) v).

(* Unbound variables:
     bool list op_zt__ option pair Data.Foldable.foldl Data.IntMap.Internal.IntMap
     Data.IntMap.Internal.adjust Data.IntMap.Internal.alter
     Data.IntMap.Internal.delete Data.IntMap.Internal.difference
     Data.IntMap.Internal.elems Data.IntMap.Internal.empty
     Data.IntMap.Internal.filter Data.IntMap.Internal.filterWithKey
     Data.IntMap.Internal.findWithDefault Data.IntMap.Internal.fold
     Data.IntMap.Internal.foldWithKey Data.IntMap.Internal.insert
     Data.IntMap.Internal.insertWith Data.IntMap.Internal.intersection
     Data.IntMap.Internal.intersectionWith Data.IntMap.Internal.keys
     Data.IntMap.Internal.lookup Data.IntMap.Internal.map
     Data.IntMap.Internal.mapWithKey Data.IntMap.Internal.member
     Data.IntMap.Internal.null Data.IntMap.Internal.partition
     Data.IntMap.Internal.singleton Data.IntMap.Internal.size
     Data.IntMap.Internal.splitLookup Data.IntMap.Internal.toList
     Data.IntMap.Internal.union Data.IntMap.Internal.unionWith GHC.Base.Eq_
     GHC.Base.Monoid GHC.Base.flip GHC.Base.foldr GHC.Base.map GHC.Base.op_z2218U__
     GHC.Base.op_zd__ GHC.Base.op_zeze__ GHC.Base.op_zsze__ GHC.Num.Int
     GHC.Prim.Build_Unpeel GHC.Prim.Unpeel GHC.Prim.coerce Unique.Uniquable
     Unique.Unique Unique.getKey Unique.getUnique
*)
