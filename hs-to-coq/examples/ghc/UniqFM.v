(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Preamble *)

Require Import GHC.Base.
Open Scope type_scope.

(* Converted imports: *)

Require Coq.Program.Basics.
Require Data.Foldable.
Require Data.IntMap.
Require GHC.Base.
Require GHC.Num.
Require Unique.

(* Converted declarations: *)

(* Translating `instance forall {a}, Data.Semigroup.Semigroup (UniqFM a)'
   failed: OOPS! Cannot find information for class "Data.Semigroup.Semigroup"
   unsupported *)

(* Translating `instance forall {a}, GHC.Base.Monoid (UniqFM a)' failed: OOPS!
   Cannot find information for class "GHC.Base.Monoid" unsupported *)

(* Translating `instance forall {a}, forall `{Outputable.Outputable a},
   Outputable.Outputable (UniqFM a)' failed: OOPS! Cannot find information for
   class "Outputable.Outputable" unsupported *)

(* Translating `instance Data.Traversable.Traversable UniqFM' failed: OOPS!
   Cannot find information for class "Data.Traversable.Traversable" unsupported *)

(* Translating `instance GHC.Base.Functor UniqFM' failed: type applications
   unsupported *)

(* Translating `instance forall {ele}, forall `{GHC.Base.Eq_ ele}, GHC.Base.Eq_
   (UniqFM ele)' failed: type applications unsupported *)

(* Translating `instance forall {ele}, forall `{Data.Data.Data ele},
   Data.Data.Data (UniqFM ele)' failed: OOPS! Cannot find information for class
   "Data.Data.Data" unsupported *)

(* Translating `instance Data.Foldable.Foldable UniqFM' failed: type
   applications unsupported *)

Inductive UniqFM ele : Type := Mk_UFM : (Data.IntMap.Base.IntMap ele) -> UniqFM
                                        ele.

Arguments Mk_UFM {_} _.

Definition unitUFM {key} {elt} `{Unique.Uniquable key} : key -> elt -> UniqFM
                                                         elt :=
  fun arg_178__ arg_179__ =>
    match arg_178__ , arg_179__ with
      | k , v => Mk_UFM (Data.IntMap.Base.singleton (GHC.Base.op_zd__ Unique.getKey
                                                                      (Unique.getUnique k)) v)
    end.

Definition unitDirectlyUFM {elt} : Unique.Unique -> elt -> UniqFM elt :=
  fun arg_174__ arg_175__ =>
    match arg_174__ , arg_175__ with
      | u , v => Mk_UFM (Data.IntMap.Base.singleton (Unique.getKey u) v)
    end.

Definition ufmToList {elt} : UniqFM elt -> list (Unique.Unique * elt) :=
  fun arg_5__ =>
    match arg_5__ with
      | Mk_UFM m => GHC.Base.op_zd__ (GHC.Base.map (fun arg_6__ =>
                                                     match arg_6__ with
                                                       | pair k v => pair (Unique.getUnique k) v
                                                     end)) (Data.IntMap.Base.toList m)
    end.

Definition ufmToIntMap {elt} : UniqFM elt -> Data.IntMap.Base.IntMap elt :=
  fun arg_3__ => match arg_3__ with | Mk_UFM m => m end.

Definition splitUFM {key} {elt} `{Unique.Uniquable key} : UniqFM
                                                          elt -> key -> UniqFM elt * option elt * UniqFM elt :=
  fun arg_35__ arg_36__ =>
    match arg_35__ , arg_36__ with
      | Mk_UFM m , k => let scrut_37__ :=
                          Data.IntMap.Base.splitLookup (GHC.Base.op_zd__ Unique.getKey (Unique.getUnique
                                                                         k)) m in
                        match scrut_37__ with
                          | pair (pair less equal) greater => pair (pair (Mk_UFM less) equal) (Mk_UFM
                                                                   greater)
                        end
    end.

Definition sizeUFM {elt} : UniqFM elt -> GHC.Num.Int :=
  fun arg_50__ => match arg_50__ with | Mk_UFM m => Data.IntMap.Base.size m end.

Definition plusUFM_C {elt} : (elt -> elt -> elt) -> UniqFM elt -> UniqFM
                             elt -> UniqFM elt :=
  fun arg_96__ arg_97__ arg_98__ =>
    match arg_96__ , arg_97__ , arg_98__ with
      | f , Mk_UFM x , Mk_UFM y => Mk_UFM (Data.IntMap.Base.unionWith f x y)
    end.

Definition plusUFM {elt} : UniqFM elt -> UniqFM elt -> UniqFM elt :=
  fun arg_101__ arg_102__ =>
    match arg_101__ , arg_102__ with
      | Mk_UFM x , Mk_UFM y => Mk_UFM (Data.IntMap.Base.union y x)
    end.

Definition nonDetEltsUFM {elt} : UniqFM elt -> list elt :=
  fun arg_0__ => match arg_0__ with | Mk_UFM m => Data.IntMap.Base.elems m end.

Definition minusUFM {elt1} {elt2} : UniqFM elt1 -> UniqFM elt2 -> UniqFM elt1 :=
  fun arg_92__ arg_93__ =>
    match arg_92__ , arg_93__ with
      | Mk_UFM x , Mk_UFM y => Mk_UFM (Data.IntMap.Base.difference x y)
    end.

Definition mapUFM_Directly {elt1} {elt2}
    : (Unique.Unique -> elt1 -> elt2) -> UniqFM elt1 -> UniqFM elt2 :=
  fun arg_61__ arg_62__ =>
    match arg_61__ , arg_62__ with
      | f , Mk_UFM m => Mk_UFM (Data.IntMap.Base.mapWithKey
                               (Coq.Program.Basics.compose f Unique.getUnique) m)
    end.

Definition mapUFM {elt1} {elt2} : (elt1 -> elt2) -> UniqFM elt1 -> UniqFM
                                  elt2 :=
  fun arg_65__ arg_66__ =>
    match arg_65__ , arg_66__ with
      | f , Mk_UFM m => Mk_UFM (Data.IntMap.Base.map f m)
    end.

Definition lookupWithDefaultUFM_Directly {elt} : UniqFM
                                                 elt -> elt -> Unique.Unique -> elt :=
  fun arg_17__ arg_18__ arg_19__ =>
    match arg_17__ , arg_18__ , arg_19__ with
      | Mk_UFM m , v , u => Data.IntMap.Base.findWithDefault v (Unique.getKey u) m
    end.

Definition lookupWithDefaultUFM {key} {elt} `{Unique.Uniquable key} : UniqFM
                                                                      elt -> elt -> key -> elt :=
  fun arg_22__ arg_23__ arg_24__ =>
    match arg_22__ , arg_23__ , arg_24__ with
      | Mk_UFM m , v , k => Data.IntMap.Base.findWithDefault v (GHC.Base.op_zd__
                                                               Unique.getKey (Unique.getUnique k)) m
    end.

Definition lookupUFM_Directly {elt} : UniqFM elt -> Unique.Unique -> option
                                      elt :=
  fun arg_27__ arg_28__ =>
    match arg_27__ , arg_28__ with
      | Mk_UFM m , u => Data.IntMap.Base.lookup (Unique.getKey u) m
    end.

Definition lookupUFM {key} {elt} `{Unique.Uniquable key} : UniqFM
                                                           elt -> key -> option elt :=
  fun arg_31__ arg_32__ =>
    match arg_31__ , arg_32__ with
      | Mk_UFM m , k => Data.IntMap.Base.lookup (GHC.Base.op_zd__ Unique.getKey
                                                                  (Unique.getUnique k)) m
    end.

Definition keysUFM {elt} : UniqFM elt -> list Unique.Unique :=
  fun arg_14__ =>
    match arg_14__ with
      | Mk_UFM m => GHC.Base.op_zd__ (GHC.Base.map Unique.getUnique)
                                     (Data.IntMap.Base.keys m)
    end.

Definition isNullUFM {elt} : UniqFM elt -> bool :=
  fun arg_182__ => match arg_182__ with | Mk_UFM m => Data.IntMap.Base.null m end.

Definition intersectUFM_C {elt1} {elt2} {elt3}
    : (elt1 -> elt2 -> elt3) -> UniqFM elt1 -> UniqFM elt2 -> UniqFM elt3 :=
  fun arg_83__ arg_84__ arg_85__ =>
    match arg_83__ , arg_84__ , arg_85__ with
      | f , Mk_UFM x , Mk_UFM y => Mk_UFM (Data.IntMap.Base.intersectionWith f x y)
    end.

Definition intersectUFM {elt} : UniqFM elt -> UniqFM elt -> UniqFM elt :=
  fun arg_88__ arg_89__ =>
    match arg_88__ , arg_89__ with
      | Mk_UFM x , Mk_UFM y => Mk_UFM (Data.IntMap.Base.intersection x y)
    end.

Definition foldUFM_Directly {elt} {a}
    : (Unique.Unique -> elt -> a -> a) -> a -> UniqFM elt -> a :=
  fun arg_69__ arg_70__ arg_71__ =>
    match arg_69__ , arg_70__ , arg_71__ with
      | k , z , Mk_UFM m => Data.IntMap.foldWithKey (Coq.Program.Basics.compose k
                                                                                Unique.getUnique) z m
    end.

Definition foldUFM {elt} {a} : (elt -> a -> a) -> a -> UniqFM elt -> a :=
  fun arg_74__ arg_75__ arg_76__ =>
    match arg_74__ , arg_75__ , arg_76__ with
      | k , z , Mk_UFM m => Data.IntMap.fold k z m
    end.

Definition filterUFM_Directly {elt} : (Unique.Unique -> elt -> bool) -> UniqFM
                                      elt -> UniqFM elt :=
  fun arg_53__ arg_54__ =>
    match arg_53__ , arg_54__ with
      | p , Mk_UFM m => Mk_UFM (Data.IntMap.Base.filterWithKey
                               (Coq.Program.Basics.compose p Unique.getUnique) m)
    end.

Definition filterUFM {elt} : (elt -> bool) -> UniqFM elt -> UniqFM elt :=
  fun arg_57__ arg_58__ =>
    match arg_57__ , arg_58__ with
      | p , Mk_UFM m => Mk_UFM (Data.IntMap.Base.filter p m)
    end.

Definition emptyUFM {elt} : UniqFM elt :=
  Mk_UFM Data.IntMap.Base.empty.

Definition eltsUFM {elt} : UniqFM elt -> list elt :=
  fun arg_11__ => match arg_11__ with | Mk_UFM m => Data.IntMap.Base.elems m end.

Definition elemUFM_Directly {elt} : Unique.Unique -> UniqFM elt -> bool :=
  fun arg_42__ arg_43__ =>
    match arg_42__ , arg_43__ with
      | u , Mk_UFM m => Data.IntMap.Base.member (Unique.getKey u) m
    end.

Definition elemUFM {key} {elt} `{Unique.Uniquable key} : key -> UniqFM
                                                         elt -> bool :=
  fun arg_46__ arg_47__ =>
    match arg_46__ , arg_47__ with
      | k , Mk_UFM m => Data.IntMap.Base.member (GHC.Base.op_zd__ Unique.getKey
                                                                  (Unique.getUnique k)) m
    end.

Definition disjointUFM {elt1} {elt2} : UniqFM elt1 -> UniqFM elt2 -> bool :=
  fun arg_79__ arg_80__ =>
    match arg_79__ , arg_80__ with
      | Mk_UFM x , Mk_UFM y => Data.IntMap.Base.null (Data.IntMap.Base.intersection x
                                                     y)
    end.

Definition delFromUFM_Directly {elt} : UniqFM elt -> Unique.Unique -> UniqFM
                                       elt :=
  fun arg_105__ arg_106__ =>
    match arg_105__ , arg_106__ with
      | Mk_UFM m , u => Mk_UFM (Data.IntMap.Base.delete (Unique.getKey u) m)
    end.

Definition delListFromUFM_Directly {elt} : UniqFM elt -> list
                                           Unique.Unique -> UniqFM elt :=
  Data.Foldable.foldl delFromUFM_Directly.

Definition delFromUFM {key} {elt} `{Unique.Uniquable key} : UniqFM
                                                            elt -> key -> UniqFM elt :=
  fun arg_110__ arg_111__ =>
    match arg_110__ , arg_111__ with
      | Mk_UFM m , k => Mk_UFM (Data.IntMap.Base.delete (GHC.Base.op_zd__
                                                        Unique.getKey (Unique.getUnique k)) m)
    end.

Definition delListFromUFM {key} {elt} `{Unique.Uniquable key} : UniqFM
                                                                elt -> list key -> UniqFM elt :=
  Data.Foldable.foldl delFromUFM.

Definition alterUFM {key} {elt} `{Unique.Uniquable key} : (option elt -> option
                                                          elt) -> UniqFM elt -> key -> UniqFM elt :=
  fun arg_169__ arg_170__ arg_171__ =>
    match arg_169__ , arg_170__ , arg_171__ with
      | f , Mk_UFM m , k => Mk_UFM (Data.IntMap.Base.alter f (GHC.Base.op_zd__
                                                             Unique.getKey (Unique.getUnique k)) m)
    end.

Definition adjustUFM_Directly {elt} : (elt -> elt) -> UniqFM
                                      elt -> Unique.Unique -> UniqFM elt :=
  fun arg_115__ arg_116__ arg_117__ =>
    match arg_115__ , arg_116__ , arg_117__ with
      | f , Mk_UFM m , u => Mk_UFM (Data.IntMap.Base.adjust f (Unique.getKey u) m)
    end.

Definition adjustUFM {key} {elt} `{Unique.Uniquable key}
    : (elt -> elt) -> UniqFM elt -> key -> UniqFM elt :=
  fun arg_120__ arg_121__ arg_122__ =>
    match arg_120__ , arg_121__ , arg_122__ with
      | f , Mk_UFM m , k => Mk_UFM (Data.IntMap.Base.adjust f (GHC.Base.op_zd__
                                                              Unique.getKey (Unique.getUnique k)) m)
    end.

Definition addToUFM_Directly {elt} : UniqFM
                                     elt -> Unique.Unique -> elt -> UniqFM elt :=
  fun arg_149__ arg_150__ arg_151__ =>
    match arg_149__ , arg_150__ , arg_151__ with
      | Mk_UFM m , u , v => Mk_UFM (Data.IntMap.Base.insert (Unique.getKey u) v m)
    end.

Definition listToUFM_Directly {elt} : list (Unique.Unique * elt) -> UniqFM
                                      elt :=
  Data.Foldable.foldl (fun arg_191__ arg_192__ =>
                        match arg_191__ , arg_192__ with
                          | m , pair u v => addToUFM_Directly m u v
                        end) emptyUFM.

Definition addToUFM_C {key} {elt} `{Unique.Uniquable key}
    : (elt -> elt -> elt) -> UniqFM elt -> key -> elt -> UniqFM elt :=
  fun arg_136__ arg_137__ arg_138__ arg_139__ =>
    match arg_136__ , arg_137__ , arg_138__ , arg_139__ with
      | f , Mk_UFM m , k , v => Mk_UFM (Data.IntMap.Base.insertWith (GHC.Base.flip f)
                                       (GHC.Base.op_zd__ Unique.getKey (Unique.getUnique k)) v m)
    end.

Definition listToUFM_C {key} {elt} `{Unique.Uniquable key}
    : (elt -> elt -> elt) -> list (key * elt) -> UniqFM elt :=
  fun arg_196__ =>
    match arg_196__ with
      | f => Data.Foldable.foldl (fun arg_197__ arg_198__ =>
                                   match arg_197__ , arg_198__ with
                                     | m , pair k v => addToUFM_C f m k v
                                   end) emptyUFM
    end.

Definition addToUFM_Acc {key} {elt} {elts} `{Unique.Uniquable key}
    : (elt -> elts -> elts) -> (elt -> elts) -> UniqFM elts -> key -> elt -> UniqFM
      elts :=
  fun arg_125__ arg_126__ arg_127__ arg_128__ arg_129__ =>
    match arg_125__ , arg_126__ , arg_127__ , arg_128__ , arg_129__ with
      | exi , new , Mk_UFM m , k , v => Mk_UFM (Data.IntMap.Base.insertWith
                                               (fun arg_130__ arg_131__ =>
                                                 match arg_130__ , arg_131__ with
                                                   | _new , old => exi v old
                                                 end) (GHC.Base.op_zd__ Unique.getKey (Unique.getUnique k)) (new v) m)
    end.

Definition addToUFM {key} {elt} `{Unique.Uniquable key} : UniqFM
                                                          elt -> key -> elt -> UniqFM elt :=
  fun arg_159__ arg_160__ arg_161__ =>
    match arg_159__ , arg_160__ , arg_161__ with
      | Mk_UFM m , k , v => Mk_UFM (Data.IntMap.Base.insert (GHC.Base.op_zd__
                                                            Unique.getKey (Unique.getUnique k)) v m)
    end.

Definition listToUFM {key} {elt} `{Unique.Uniquable key} : list (key *
                                                                elt) -> UniqFM elt :=
  Data.Foldable.foldl (fun arg_186__ arg_187__ =>
                        match arg_186__ , arg_187__ with
                          | m , pair k v => addToUFM m k v
                        end) emptyUFM.

Definition addListToUFM_Directly {elt} : UniqFM elt -> list (Unique.Unique *
                                                            elt) -> UniqFM elt :=
  Data.Foldable.foldl (fun arg_154__ arg_155__ =>
                        match arg_154__ , arg_155__ with
                          | m , pair k v => addToUFM_Directly m k v
                        end).

Definition addListToUFM_C {key} {elt} `{Unique.Uniquable key}
    : (elt -> elt -> elt) -> UniqFM elt -> list (key * elt) -> UniqFM elt :=
  fun arg_142__ =>
    match arg_142__ with
      | f => Data.Foldable.foldl (fun arg_143__ arg_144__ =>
                                   match arg_143__ , arg_144__ with
                                     | m , pair k v => addToUFM_C f m k v
                                   end)
    end.

Definition addListToUFM {key} {elt} `{Unique.Uniquable key} : UniqFM elt -> list
                                                              (key * elt) -> UniqFM elt :=
  Data.Foldable.foldl (fun arg_164__ arg_165__ =>
                        match arg_164__ , arg_165__ with
                          | m , pair k v => addToUFM m k v
                        end).

(* Unbound variables:
     * Coq.Program.Basics.compose Data.Foldable.foldl Data.IntMap.Base.IntMap
     Data.IntMap.Base.adjust Data.IntMap.Base.alter Data.IntMap.Base.delete
     Data.IntMap.Base.difference Data.IntMap.Base.elems Data.IntMap.Base.empty
     Data.IntMap.Base.filter Data.IntMap.Base.filterWithKey
     Data.IntMap.Base.findWithDefault Data.IntMap.Base.insert
     Data.IntMap.Base.insertWith Data.IntMap.Base.intersection
     Data.IntMap.Base.intersectionWith Data.IntMap.Base.keys Data.IntMap.Base.lookup
     Data.IntMap.Base.map Data.IntMap.Base.mapWithKey Data.IntMap.Base.member
     Data.IntMap.Base.null Data.IntMap.Base.singleton Data.IntMap.Base.size
     Data.IntMap.Base.splitLookup Data.IntMap.Base.toList Data.IntMap.Base.union
     Data.IntMap.Base.unionWith Data.IntMap.fold Data.IntMap.foldWithKey
     GHC.Base.flip GHC.Base.map GHC.Base.op_zd__ GHC.Num.Int Unique.Uniquable
     Unique.Unique Unique.getKey Unique.getUnique bool list option pair
*)
