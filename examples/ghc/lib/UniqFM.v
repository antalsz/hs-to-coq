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
Require Data.IntMap.
Require Data.IntMap.Base.
Require Data.Traversable.
Require GHC.Base.
Require GHC.Num.
Require GHC.Prim.
Require Unique.
Import GHC.Base.Notations.

(* Converted type declarations: *)

Inductive UniqFM ele : Type := UFM : (Data.IntMap.Base.IntMap ele) -> UniqFM
                                     ele.

Arguments UFM {_} _.
(* Midamble *)

Require Data.IntSet.Base.

Axiom ufmToSet_Directly : forall {elt}, UniqFM elt -> Data.IntSet.Base.IntSet.

Require Panic.

Instance Default_UniqFM {a} : Panic.Default (UniqFM a) :=
  Panic.Build_Default _ (UFM Data.IntMap.Base.empty).

(* Converted value declarations: *)

Instance Unpeel_UniqFM ele : GHC.Prim.Unpeel (UniqFM ele)
                                             (Data.IntMap.Base.IntMap ele) := GHC.Prim.Build_Unpeel _ _ (fun x =>
                                                                                                      match x with
                                                                                                        | UFM y => y
                                                                                                      end) UFM.

(* Translating `instance forall {a}, Data.Semigroup.Semigroup (UniqFM.UniqFM a)'
   failed: OOPS! Cannot find information for class Qualified "Data.Semigroup"
   "Semigroup" unsupported *)

(* Translating `instance forall {a}, forall `{Outputable.Outputable a},
   Outputable.Outputable (UniqFM.UniqFM a)' failed: OOPS! Cannot find information
   for class Qualified "Outputable" "Outputable" unsupported *)

Local Definition Traversable__UniqFM_traverse : forall {f} {a} {b},
                                                  forall `{GHC.Base.Applicative f},
                                                    (a -> f b) -> UniqFM a -> f (UniqFM b) :=
  fun {f} {a} {b} `{GHC.Base.Applicative f} =>
    fun arg_217__ arg_218__ =>
      match arg_217__ , arg_218__ with
        | f , UFM a1 => GHC.Base.fmap (fun b1 => UFM b1) (Data.Traversable.traverse f
                                                         a1)
      end.

Local Definition Traversable__UniqFM_sequenceA : forall {f} {a},
                                                   forall `{GHC.Base.Applicative f}, UniqFM (f a) -> f (UniqFM a) :=
  fun {f} {a} `{GHC.Base.Applicative f} =>
    Traversable__UniqFM_traverse GHC.Base.id.

Local Definition Traversable__UniqFM_sequence : forall {m} {a},
                                                  forall `{GHC.Base.Monad m}, UniqFM (m a) -> m (UniqFM a) :=
  fun {m} {a} `{GHC.Base.Monad m} => Traversable__UniqFM_sequenceA.

Local Definition Traversable__UniqFM_mapM : forall {m} {a} {b},
                                              forall `{GHC.Base.Monad m}, (a -> m b) -> UniqFM a -> m (UniqFM b) :=
  fun {m} {a} {b} `{GHC.Base.Monad m} => Traversable__UniqFM_traverse.

Local Definition Functor__UniqFM_fmap : forall {a} {b},
                                          (a -> b) -> UniqFM a -> UniqFM b :=
  fun {a} {b} => GHC.Prim.coerce GHC.Base.fmap.

Local Definition Functor__UniqFM_op_zlzd__ : forall {a} {b},
                                               a -> UniqFM b -> UniqFM a :=
  fun {a} {b} => GHC.Prim.coerce _GHC.Base.<$_.

Program Instance Functor__UniqFM : GHC.Base.Functor UniqFM := fun _ k =>
    k {|GHC.Base.op_zlzd____ := fun {a} {b} => Functor__UniqFM_op_zlzd__ ;
      GHC.Base.fmap__ := fun {a} {b} => Functor__UniqFM_fmap |}.

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

Local Definition Foldable__UniqFM_elem : forall {a},
                                           forall `{GHC.Base.Eq_ a}, a -> UniqFM a -> bool :=
  fun {a} `{GHC.Base.Eq_ a} => GHC.Prim.coerce Data.Foldable.elem.

Local Definition Foldable__UniqFM_fold : forall {m},
                                           forall `{GHC.Base.Monoid m}, UniqFM m -> m :=
  fun {m} `{GHC.Base.Monoid m} => GHC.Prim.coerce Data.Foldable.fold.

Local Definition Foldable__UniqFM_foldMap : forall {m} {a},
                                              forall `{GHC.Base.Monoid m}, (a -> m) -> UniqFM a -> m :=
  fun {m} {a} `{GHC.Base.Monoid m} => GHC.Prim.coerce Data.Foldable.foldMap.

Local Definition Foldable__UniqFM_foldl : forall {b} {a},
                                            (b -> a -> b) -> b -> UniqFM a -> b :=
  fun {b} {a} => GHC.Prim.coerce Data.Foldable.foldl.

Local Definition Foldable__UniqFM_foldl' : forall {b} {a},
                                             (b -> a -> b) -> b -> UniqFM a -> b :=
  fun {b} {a} => GHC.Prim.coerce Data.Foldable.foldl'.

Local Definition Foldable__UniqFM_foldr : forall {a} {b},
                                            (a -> b -> b) -> b -> UniqFM a -> b :=
  fun {a} {b} => GHC.Prim.coerce Data.Foldable.foldr.

Local Definition Foldable__UniqFM_foldr' : forall {a} {b},
                                             (a -> b -> b) -> b -> UniqFM a -> b :=
  fun {a} {b} => GHC.Prim.coerce Data.Foldable.foldr'.

Local Definition Foldable__UniqFM_length : forall {a},
                                             UniqFM a -> GHC.Num.Int :=
  fun {a} => GHC.Prim.coerce Data.Foldable.length.

Local Definition Foldable__UniqFM_null : forall {a}, UniqFM a -> bool :=
  fun {a} => GHC.Prim.coerce Data.Foldable.null.

Local Definition Foldable__UniqFM_product : forall {a},
                                              forall `{GHC.Num.Num a}, UniqFM a -> a :=
  fun {a} `{GHC.Num.Num a} => GHC.Prim.coerce Data.Foldable.product.

Local Definition Foldable__UniqFM_sum : forall {a},
                                          forall `{GHC.Num.Num a}, UniqFM a -> a :=
  fun {a} `{GHC.Num.Num a} => GHC.Prim.coerce Data.Foldable.sum.

Local Definition Foldable__UniqFM_toList : forall {a}, UniqFM a -> list a :=
  fun {a} => GHC.Prim.coerce Data.Foldable.toList.

Program Instance Foldable__UniqFM : Data.Foldable.Foldable UniqFM := fun _ k =>
    k {|Data.Foldable.elem__ := fun {a} `{GHC.Base.Eq_ a} => Foldable__UniqFM_elem ;
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
    k {|Data.Traversable.mapM__ := fun {m} {a} {b} `{GHC.Base.Monad m} =>
        Traversable__UniqFM_mapM ;
      Data.Traversable.sequence__ := fun {m} {a} `{GHC.Base.Monad m} =>
        Traversable__UniqFM_sequence ;
      Data.Traversable.sequenceA__ := fun {f} {a} `{GHC.Base.Applicative f} =>
        Traversable__UniqFM_sequenceA ;
      Data.Traversable.traverse__ := fun {f} {a} {b} `{GHC.Base.Applicative f} =>
        Traversable__UniqFM_traverse |}.

Definition addToUFM {key} {elt} `{Unique.Uniquable key} : UniqFM
                                                          elt -> key -> elt -> UniqFM elt :=
  fun arg_161__ arg_162__ arg_163__ =>
    match arg_161__ , arg_162__ , arg_163__ with
      | UFM m , k , v => UFM (Data.IntMap.Base.insert (Unique.getKey GHC.Base.$
                                                      Unique.getUnique k) v m)
    end.

Definition addListToUFM {key} {elt} `{Unique.Uniquable key} : UniqFM elt -> list
                                                              (key * elt)%type -> UniqFM elt :=
  Data.Foldable.foldl (fun arg_166__ arg_167__ =>
                        match arg_166__ , arg_167__ with
                          | m , pair k v => addToUFM m k v
                        end).

Definition addToUFM_Acc {key} {elt} {elts} `{Unique.Uniquable key}
    : (elt -> elts -> elts) -> (elt -> elts) -> UniqFM elts -> key -> elt -> UniqFM
      elts :=
  fun arg_132__ arg_133__ arg_134__ arg_135__ arg_136__ =>
    match arg_132__ , arg_133__ , arg_134__ , arg_135__ , arg_136__ with
      | exi , new , UFM m , k , v => UFM (Data.IntMap.Base.insertWith (fun _new old =>
                                                                        exi v old) (Unique.getKey GHC.Base.$
                                                                                   Unique.getUnique k) (new v) m)
    end.

Definition addToUFM_C {key} {elt} `{Unique.Uniquable key}
    : (elt -> elt -> elt) -> UniqFM elt -> key -> elt -> UniqFM elt :=
  fun arg_140__ arg_141__ arg_142__ arg_143__ =>
    match arg_140__ , arg_141__ , arg_142__ , arg_143__ with
      | f , UFM m , k , v => UFM (Data.IntMap.Base.insertWith (GHC.Base.flip f)
                                 (Unique.getKey GHC.Base.$ Unique.getUnique k) v m)
    end.

Definition addListToUFM_C {key} {elt} `{Unique.Uniquable key}
    : (elt -> elt -> elt) -> UniqFM elt -> list (key * elt)%type -> UniqFM elt :=
  fun f =>
    Data.Foldable.foldl (fun arg_146__ arg_147__ =>
                          match arg_146__ , arg_147__ with
                            | m , pair k v => addToUFM_C f m k v
                          end).

Definition addToUFM_Directly {elt} : UniqFM
                                     elt -> Unique.Unique -> elt -> UniqFM elt :=
  fun arg_151__ arg_152__ arg_153__ =>
    match arg_151__ , arg_152__ , arg_153__ with
      | UFM m , u , v => UFM (Data.IntMap.Base.insert (Unique.getKey u) v m)
    end.

Definition addListToUFM_Directly {elt} : UniqFM elt -> list (Unique.Unique *
                                                            elt)%type -> UniqFM elt :=
  Data.Foldable.foldl (fun arg_156__ arg_157__ =>
                        match arg_156__ , arg_157__ with
                          | m , pair k v => addToUFM_Directly m k v
                        end).

Definition adjustUFM {key} {elt} `{Unique.Uniquable key}
    : (elt -> elt) -> UniqFM elt -> key -> UniqFM elt :=
  fun arg_127__ arg_128__ arg_129__ =>
    match arg_127__ , arg_128__ , arg_129__ with
      | f , UFM m , k => UFM (Data.IntMap.Base.adjust f (Unique.getKey GHC.Base.$
                                                        Unique.getUnique k) m)
    end.

Definition adjustUFM_Directly {elt} : (elt -> elt) -> UniqFM
                                      elt -> Unique.Unique -> UniqFM elt :=
  fun arg_122__ arg_123__ arg_124__ =>
    match arg_122__ , arg_123__ , arg_124__ with
      | f , UFM m , u => UFM (Data.IntMap.Base.adjust f (Unique.getKey u) m)
    end.

Definition alterUFM {key} {elt} `{Unique.Uniquable key} : (option elt -> option
                                                          elt) -> UniqFM elt -> key -> UniqFM elt :=
  fun arg_171__ arg_172__ arg_173__ =>
    match arg_171__ , arg_172__ , arg_173__ with
      | f , UFM m , k => UFM (Data.IntMap.Base.alter f (Unique.getKey GHC.Base.$
                                                       Unique.getUnique k) m)
    end.

Definition delFromUFM {key} {elt} `{Unique.Uniquable key} : UniqFM
                                                            elt -> key -> UniqFM elt :=
  fun arg_117__ arg_118__ =>
    match arg_117__ , arg_118__ with
      | UFM m , k => UFM (Data.IntMap.Base.delete (Unique.getKey GHC.Base.$
                                                  Unique.getUnique k) m)
    end.

Definition delListFromUFM {key} {elt} `{Unique.Uniquable key} : UniqFM
                                                                elt -> list key -> UniqFM elt :=
  Data.Foldable.foldl delFromUFM.

Definition delFromUFM_Directly {elt} : UniqFM elt -> Unique.Unique -> UniqFM
                                       elt :=
  fun arg_112__ arg_113__ =>
    match arg_112__ , arg_113__ with
      | UFM m , u => UFM (Data.IntMap.Base.delete (Unique.getKey u) m)
    end.

Definition delListFromUFM_Directly {elt} : UniqFM elt -> list
                                           Unique.Unique -> UniqFM elt :=
  Data.Foldable.foldl delFromUFM_Directly.

Definition disjointUFM {elt1} {elt2} : UniqFM elt1 -> UniqFM elt2 -> bool :=
  fun arg_86__ arg_87__ =>
    match arg_86__ , arg_87__ with
      | UFM x , UFM y => Data.IntMap.Base.null (Data.IntMap.Base.intersection x y)
    end.

Definition elemUFM {key} {elt} `{Unique.Uniquable key} : key -> UniqFM
                                                         elt -> bool :=
  fun arg_46__ arg_47__ =>
    match arg_46__ , arg_47__ with
      | k , UFM m => Data.IntMap.Base.member (Unique.getKey GHC.Base.$
                                             Unique.getUnique k) m
    end.

Definition elemUFM_Directly {elt} : Unique.Unique -> UniqFM elt -> bool :=
  fun arg_42__ arg_43__ =>
    match arg_42__ , arg_43__ with
      | u , UFM m => Data.IntMap.Base.member (Unique.getKey u) m
    end.

Definition eltsUFM {elt} : UniqFM elt -> list elt :=
  fun arg_11__ => match arg_11__ with | UFM m => Data.IntMap.Base.elems m end.

Definition emptyUFM {elt} : UniqFM elt :=
  UFM Data.IntMap.Base.empty.

Definition listToUFM_Directly {elt} : list (Unique.Unique * elt)%type -> UniqFM
                                      elt :=
  Data.Foldable.foldl (fun arg_187__ arg_188__ =>
                        match arg_187__ , arg_188__ with
                          | m , pair u v => addToUFM_Directly m u v
                        end) emptyUFM.

Definition listToUFM_C {key} {elt} `{Unique.Uniquable key}
    : (elt -> elt -> elt) -> list (key * elt)%type -> UniqFM elt :=
  fun f =>
    Data.Foldable.foldl (fun arg_192__ arg_193__ =>
                          match arg_192__ , arg_193__ with
                            | m , pair k v => addToUFM_C f m k v
                          end) emptyUFM.

Definition listToUFM {key} {elt} `{Unique.Uniquable key} : list (key *
                                                                elt)%type -> UniqFM elt :=
  Data.Foldable.foldl (fun arg_182__ arg_183__ =>
                        match arg_182__ , arg_183__ with
                          | m , pair k v => addToUFM m k v
                        end) emptyUFM.

Local Definition Monoid__UniqFM_mempty {inst_a} : (UniqFM inst_a) :=
  emptyUFM.

Definition filterUFM {elt} : (elt -> bool) -> UniqFM elt -> UniqFM elt :=
  fun arg_64__ arg_65__ =>
    match arg_64__ , arg_65__ with
      | p , UFM m => UFM (Data.IntMap.Base.filter p m)
    end.

Definition filterUFM_Directly {elt} : (Unique.Unique -> elt -> bool) -> UniqFM
                                      elt -> UniqFM elt :=
  fun arg_60__ arg_61__ =>
    match arg_60__ , arg_61__ with
      | p , UFM m => UFM (Data.IntMap.Base.filterWithKey (p GHC.Base.∘
                                                         Unique.getUnique) m)
    end.

Definition foldUFM {elt} {a} : (elt -> a -> a) -> a -> UniqFM elt -> a :=
  fun arg_81__ arg_82__ arg_83__ =>
    match arg_81__ , arg_82__ , arg_83__ with
      | k , z , UFM m => Data.IntMap.fold k z m
    end.

Definition foldUFM_Directly {elt} {a}
    : (Unique.Unique -> elt -> a -> a) -> a -> UniqFM elt -> a :=
  fun arg_76__ arg_77__ arg_78__ =>
    match arg_76__ , arg_77__ , arg_78__ with
      | k , z , UFM m => Data.IntMap.foldWithKey (k GHC.Base.∘ Unique.getUnique) z m
    end.

Definition intersectUFM {elt} : UniqFM elt -> UniqFM elt -> UniqFM elt :=
  fun arg_95__ arg_96__ =>
    match arg_95__ , arg_96__ with
      | UFM x , UFM y => UFM (Data.IntMap.Base.intersection x y)
    end.

Definition intersectUFM_C {elt1} {elt2} {elt3}
    : (elt1 -> elt2 -> elt3) -> UniqFM elt1 -> UniqFM elt2 -> UniqFM elt3 :=
  fun arg_90__ arg_91__ arg_92__ =>
    match arg_90__ , arg_91__ , arg_92__ with
      | f , UFM x , UFM y => UFM (Data.IntMap.Base.intersectionWith f x y)
    end.

Definition isNullUFM {elt} : UniqFM elt -> bool :=
  fun arg_178__ => match arg_178__ with | UFM m => Data.IntMap.Base.null m end.

Definition keysUFM {elt} : UniqFM elt -> list Unique.Unique :=
  fun arg_14__ =>
    match arg_14__ with
      | UFM m => GHC.Base.map Unique.getUnique GHC.Base.$ Data.IntMap.Base.keys m
    end.

Definition lookupUFM {key} {elt} `{Unique.Uniquable key} : UniqFM
                                                           elt -> key -> option elt :=
  fun arg_31__ arg_32__ =>
    match arg_31__ , arg_32__ with
      | UFM m , k => Data.IntMap.Base.lookup (Unique.getKey GHC.Base.$
                                             Unique.getUnique k) m
    end.

Definition lookupUFM_Directly {elt} : UniqFM elt -> Unique.Unique -> option
                                      elt :=
  fun arg_27__ arg_28__ =>
    match arg_27__ , arg_28__ with
      | UFM m , u => Data.IntMap.Base.lookup (Unique.getKey u) m
    end.

Definition lookupWithDefaultUFM {key} {elt} `{Unique.Uniquable key} : UniqFM
                                                                      elt -> elt -> key -> elt :=
  fun arg_22__ arg_23__ arg_24__ =>
    match arg_22__ , arg_23__ , arg_24__ with
      | UFM m , v , k => Data.IntMap.Base.findWithDefault v (Unique.getKey GHC.Base.$
                                                            Unique.getUnique k) m
    end.

Definition lookupWithDefaultUFM_Directly {elt} : UniqFM
                                                 elt -> elt -> Unique.Unique -> elt :=
  fun arg_17__ arg_18__ arg_19__ =>
    match arg_17__ , arg_18__ , arg_19__ with
      | UFM m , v , u => Data.IntMap.Base.findWithDefault v (Unique.getKey u) m
    end.

Definition mapUFM {elt1} {elt2} : (elt1 -> elt2) -> UniqFM elt1 -> UniqFM
                                  elt2 :=
  fun arg_72__ arg_73__ =>
    match arg_72__ , arg_73__ with
      | f , UFM m => UFM (Data.IntMap.Base.map f m)
    end.

Definition mapUFM_Directly {elt1} {elt2}
    : (Unique.Unique -> elt1 -> elt2) -> UniqFM elt1 -> UniqFM elt2 :=
  fun arg_68__ arg_69__ =>
    match arg_68__ , arg_69__ with
      | f , UFM m => UFM (Data.IntMap.Base.mapWithKey (f GHC.Base.∘ Unique.getUnique)
                         m)
    end.

Definition minusUFM {elt1} {elt2} : UniqFM elt1 -> UniqFM elt2 -> UniqFM elt1 :=
  fun arg_99__ arg_100__ =>
    match arg_99__ , arg_100__ with
      | UFM x , UFM y => UFM (Data.IntMap.Base.difference x y)
    end.

Definition nonDetEltsUFM {elt} : UniqFM elt -> list elt :=
  fun arg_0__ => match arg_0__ with | UFM m => Data.IntMap.Base.elems m end.

Definition partitionUFM {elt} : (elt -> bool) -> UniqFM elt -> (UniqFM elt *
                                UniqFM elt)%type :=
  fun arg_53__ arg_54__ =>
    match arg_53__ , arg_54__ with
      | p , UFM m => let scrut_55__ := Data.IntMap.Base.partition p m in
                     match scrut_55__ with
                       | pair left_ right_ => pair (UFM left_) (UFM right_)
                     end
    end.

Definition plusUFM {elt} : UniqFM elt -> UniqFM elt -> UniqFM elt :=
  fun arg_108__ arg_109__ =>
    match arg_108__ , arg_109__ with
      | UFM x , UFM y => UFM (Data.IntMap.Base.union y x)
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
  fun arg_103__ arg_104__ arg_105__ =>
    match arg_103__ , arg_104__ , arg_105__ with
      | f , UFM x , UFM y => UFM (Data.IntMap.Base.unionWith f x y)
    end.

Definition sizeUFM {elt} : UniqFM elt -> GHC.Num.Int :=
  fun arg_50__ => match arg_50__ with | UFM m => Data.IntMap.Base.size m end.

Definition splitUFM {key} {elt} `{Unique.Uniquable key} : UniqFM
                                                          elt -> key -> (UniqFM elt * option elt * UniqFM elt)%type :=
  fun arg_35__ arg_36__ =>
    match arg_35__ , arg_36__ with
      | UFM m , k => let scrut_37__ :=
                       Data.IntMap.Base.splitLookup (Unique.getKey GHC.Base.$ Unique.getUnique k) m in
                     match scrut_37__ with
                       | pair (pair less equal) greater => pair (pair (UFM less) equal) (UFM greater)
                     end
    end.

Definition ufmToIntMap {elt} : UniqFM elt -> Data.IntMap.Base.IntMap elt :=
  fun arg_3__ => match arg_3__ with | UFM m => m end.

Definition ufmToList {elt} : UniqFM elt -> list (Unique.Unique * elt)%type :=
  fun arg_5__ =>
    match arg_5__ with
      | UFM m => GHC.Base.map (fun arg_6__ =>
                                match arg_6__ with
                                  | pair k v => pair (Unique.getUnique k) v
                                end) GHC.Base.$ Data.IntMap.Base.toList m
    end.

Definition unitDirectlyUFM {elt} : Unique.Unique -> elt -> UniqFM elt :=
  fun u v => UFM (Data.IntMap.Base.singleton (Unique.getKey u) v).

Definition unitUFM {key} {elt} `{Unique.Uniquable key} : key -> elt -> UniqFM
                                                         elt :=
  fun k v =>
    UFM (Data.IntMap.Base.singleton (Unique.getKey GHC.Base.$ Unique.getUnique k)
        v).

(* Unbound variables:
     bool list op_zt__ option pair Data.Foldable.Foldable Data.Foldable.elem
     Data.Foldable.fold Data.Foldable.foldMap Data.Foldable.foldl
     Data.Foldable.foldl' Data.Foldable.foldr Data.Foldable.foldr'
     Data.Foldable.length Data.Foldable.null Data.Foldable.product Data.Foldable.sum
     Data.Foldable.toList Data.IntMap.fold Data.IntMap.foldWithKey
     Data.IntMap.Base.IntMap Data.IntMap.Base.adjust Data.IntMap.Base.alter
     Data.IntMap.Base.delete Data.IntMap.Base.difference Data.IntMap.Base.elems
     Data.IntMap.Base.empty Data.IntMap.Base.filter Data.IntMap.Base.filterWithKey
     Data.IntMap.Base.findWithDefault Data.IntMap.Base.insert
     Data.IntMap.Base.insertWith Data.IntMap.Base.intersection
     Data.IntMap.Base.intersectionWith Data.IntMap.Base.keys Data.IntMap.Base.lookup
     Data.IntMap.Base.map Data.IntMap.Base.mapWithKey Data.IntMap.Base.member
     Data.IntMap.Base.null Data.IntMap.Base.partition Data.IntMap.Base.singleton
     Data.IntMap.Base.size Data.IntMap.Base.splitLookup Data.IntMap.Base.toList
     Data.IntMap.Base.union Data.IntMap.Base.unionWith Data.Traversable.Traversable
     Data.Traversable.traverse GHC.Base.Applicative GHC.Base.Eq_ GHC.Base.Functor
     GHC.Base.Monad GHC.Base.Monoid GHC.Base.flip GHC.Base.fmap GHC.Base.foldr
     GHC.Base.id GHC.Base.map GHC.Base.op_z2218U__ GHC.Base.op_zd__
     GHC.Base.op_zeze__ GHC.Base.op_zlzd__ GHC.Base.op_zsze__ GHC.Num.Int GHC.Num.Num
     GHC.Prim.Build_Unpeel GHC.Prim.Unpeel GHC.Prim.coerce Unique.Uniquable
     Unique.Unique Unique.getKey Unique.getUnique
*)
