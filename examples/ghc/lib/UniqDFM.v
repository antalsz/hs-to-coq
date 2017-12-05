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
Require Data.IntMap.
Require Data.IntMap.Base.
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

Inductive UniqDFM ele : Type := UDFM : (Data.IntMap.Base.IntMap (TaggedVal
                                                                ele)) -> GHC.Num.Int -> UniqDFM ele.

Arguments Mk_TaggedVal {_} _ _.

Arguments UDFM {_} _ _.
(* Converted value declarations: *)

Local Definition Eq___TaggedVal_op_zeze__ {inst_val} `{GHC.Base.Eq_ inst_val}
    : (TaggedVal inst_val) -> (TaggedVal inst_val) -> bool :=
  fun arg_183__ arg_184__ =>
    match arg_183__ , arg_184__ with
      | Mk_TaggedVal v1 _ , Mk_TaggedVal v2 _ => v1 GHC.Base.== v2
    end.

Local Definition Eq___TaggedVal_op_zsze__ {inst_val} `{GHC.Base.Eq_ inst_val}
    : (TaggedVal inst_val) -> (TaggedVal inst_val) -> bool :=
  fun x y => negb (Eq___TaggedVal_op_zeze__ x y).

Program Instance Eq___TaggedVal {val} `{GHC.Base.Eq_ val} : GHC.Base.Eq_
                                                            (TaggedVal val) := fun _ k =>
    k {|GHC.Base.op_zeze____ := Eq___TaggedVal_op_zeze__ ;
      GHC.Base.op_zsze____ := Eq___TaggedVal_op_zsze__ |}.

Local Definition Functor__TaggedVal_fmap : forall {a} {b},
                                             (a -> b) -> TaggedVal a -> TaggedVal b :=
  fun {a} {b} =>
    fun arg_179__ arg_180__ =>
      match arg_179__ , arg_180__ with
        | f , Mk_TaggedVal val i => Mk_TaggedVal (f val) i
      end.

Local Definition Functor__TaggedVal_op_zlzd__ : forall {a} {b},
                                                  a -> TaggedVal b -> TaggedVal a :=
  fun {a} {b} => fun x => Functor__TaggedVal_fmap (GHC.Base.const x).

Program Instance Functor__TaggedVal : GHC.Base.Functor TaggedVal := fun _ k =>
    k {|GHC.Base.op_zlzd____ := fun {a} {b} => Functor__TaggedVal_op_zlzd__ ;
      GHC.Base.fmap__ := fun {a} {b} => Functor__TaggedVal_fmap |}.

(* Translating `instance forall {a}, forall `{Outputable.Outputable a},
   Outputable.Outputable (UniqDFM.UniqDFM a)' failed: OOPS! Cannot find information
   for class Qualified "Outputable" "Outputable" unsupported *)

Local Definition Functor__UniqDFM_fmap : forall {a} {b},
                                           (a -> b) -> UniqDFM a -> UniqDFM b :=
  fun {a} {b} =>
    fun arg_175__ arg_176__ =>
      match arg_175__ , arg_176__ with
        | f , UDFM a1 a2 => UDFM (GHC.Base.fmap (GHC.Base.fmap f) a1) ((fun b1 => b1)
                                                                      a2)
      end.

Local Definition Functor__UniqDFM_op_zlzd__ : forall {a} {b},
                                                a -> UniqDFM b -> UniqDFM a :=
  fun {a} {b} => fun x => Functor__UniqDFM_fmap (GHC.Base.const x).

Program Instance Functor__UniqDFM : GHC.Base.Functor UniqDFM := fun _ k =>
    k {|GHC.Base.op_zlzd____ := fun {a} {b} => Functor__UniqDFM_op_zlzd__ ;
      GHC.Base.fmap__ := fun {a} {b} => Functor__UniqDFM_fmap |}.

(* Translating `instance forall {ele}, forall `{Data.Data.Data ele},
   Data.Data.Data (UniqDFM.UniqDFM ele)' failed: OOPS! Cannot find information for
   class Qualified "Data.Data" "Data" unsupported *)

(* Translating `instance forall {val}, forall `{Data.Data.Data val},
   Data.Data.Data (UniqDFM.TaggedVal val)' failed: OOPS! Cannot find information
   for class Qualified "Data.Data" "Data" unsupported *)

Definition addToUDFM {key} {elt} `{Unique.Uniquable key} : UniqDFM
                                                           elt -> key -> elt -> UniqDFM elt :=
  fun arg_111__ arg_112__ arg_113__ =>
    match arg_111__ , arg_112__ , arg_113__ with
      | UDFM m i , k , v => UDFM (Data.IntMap.Base.insert (Unique.getKey GHC.Base.$
                                                          Unique.getUnique k) (Mk_TaggedVal v i) m) (i GHC.Num.+
                                                                                                    GHC.Num.fromInteger
                                                                                                    1)
    end.

Definition addToUDFM_C {key} {elt} `{Unique.Uniquable key}
    : (elt -> elt -> elt) -> UniqDFM elt -> key -> elt -> UniqDFM elt :=
  fun arg_76__ arg_77__ arg_78__ arg_79__ =>
    match arg_76__ , arg_77__ , arg_78__ , arg_79__ with
      | f , UDFM m i , k , v => let tf :=
                                  fun arg_80__ arg_81__ =>
                                    match arg_80__ , arg_81__ with
                                      | Mk_TaggedVal a j , Mk_TaggedVal b _ => Mk_TaggedVal (f b a) j
                                    end in
                                UDFM (Data.IntMap.Base.insertWith tf (Unique.getKey GHC.Base.$ Unique.getUnique
                                                                     k) (Mk_TaggedVal v i) m) (i GHC.Num.+
                                                                                              GHC.Num.fromInteger 1)
    end.

Definition addToUDFM_Directly {elt} : UniqDFM
                                      elt -> Unique.Unique -> elt -> UniqDFM elt :=
  fun arg_101__ arg_102__ arg_103__ =>
    match arg_101__ , arg_102__ , arg_103__ with
      | UDFM m i , u , v => UDFM (Data.IntMap.Base.insert (Unique.getKey u)
                                 (Mk_TaggedVal v i) m) (i GHC.Num.+ GHC.Num.fromInteger 1)
    end.

Definition addListToUDFM_Directly {elt} : UniqDFM elt -> list (Unique.Unique *
                                                              elt)%type -> UniqDFM elt :=
  Data.Foldable.foldl (fun arg_106__ arg_107__ =>
                        match arg_106__ , arg_107__ with
                          | m , pair k v => addToUDFM_Directly m k v
                        end).

Definition addToUDFM_Directly_C {elt} : (elt -> elt -> elt) -> UniqDFM
                                        elt -> Unique.Unique -> elt -> UniqDFM elt :=
  fun arg_86__ arg_87__ arg_88__ arg_89__ =>
    match arg_86__ , arg_87__ , arg_88__ , arg_89__ with
      | f , UDFM m i , u , v => let tf :=
                                  fun arg_90__ arg_91__ =>
                                    match arg_90__ , arg_91__ with
                                      | Mk_TaggedVal a j , Mk_TaggedVal b _ => Mk_TaggedVal (f a b) j
                                    end in
                                UDFM (Data.IntMap.Base.insertWith tf (Unique.getKey u) (Mk_TaggedVal v i) m) (i
                                                                                                             GHC.Num.+
                                                                                                             GHC.Num.fromInteger
                                                                                                             1)
    end.

Definition addListToUDFM_Directly_C {elt} : (elt -> elt -> elt) -> UniqDFM
                                            elt -> list (Unique.Unique * elt)%type -> UniqDFM elt :=
  fun f =>
    Data.Foldable.foldl (fun arg_96__ arg_97__ =>
                          match arg_96__ , arg_97__ with
                            | m , pair k v => addToUDFM_Directly_C f m k v
                          end).

Definition adjustUDFM {key} {elt} `{Unique.Uniquable key}
    : (elt -> elt) -> UniqDFM elt -> key -> UniqDFM elt :=
  fun arg_16__ arg_17__ arg_18__ =>
    match arg_16__ , arg_17__ , arg_18__ with
      | f , UDFM m i , k => UDFM (Data.IntMap.Base.adjust (GHC.Base.fmap f)
                                 (Unique.getKey GHC.Base.$ Unique.getUnique k) m) i
    end.

Definition alterUDFM {key} {elt} `{Unique.Uniquable key} : (option elt -> option
                                                           elt) -> UniqDFM elt -> key -> UniqDFM elt :=
  fun arg_4__ arg_5__ arg_6__ =>
    match arg_4__ , arg_5__ , arg_6__ with
      | f , UDFM m i , k => let inject :=
                              fun arg_7__ =>
                                match arg_7__ with
                                  | None => None
                                  | Some v => Some GHC.Base.$ Mk_TaggedVal v i
                                end in
                            let alterf :=
                              fun arg_10__ =>
                                match arg_10__ with
                                  | None => inject GHC.Base.$ f None
                                  | Some (Mk_TaggedVal v _) => inject GHC.Base.$ f (Some v)
                                end in
                            UDFM (Data.IntMap.Base.alter alterf (Unique.getKey GHC.Base.$ Unique.getUnique
                                                                k) m) (i GHC.Num.+ GHC.Num.fromInteger 1)
    end.

Definition delFromUDFM {key} {elt} `{Unique.Uniquable key} : UniqDFM
                                                             elt -> key -> UniqDFM elt :=
  fun arg_71__ arg_72__ =>
    match arg_71__ , arg_72__ with
      | UDFM m i , k => UDFM (Data.IntMap.Base.delete (Unique.getKey GHC.Base.$
                                                      Unique.getUnique k) m) i
    end.

Definition delListFromUDFM {key} {elt} `{Unique.Uniquable key} : UniqDFM
                                                                 elt -> list key -> UniqDFM elt :=
  Data.Foldable.foldl delFromUDFM.

Definition disjointUDFM {elt} : UniqDFM elt -> UniqDFM elt -> bool :=
  fun arg_33__ arg_34__ =>
    match arg_33__ , arg_34__ with
      | UDFM x _i , UDFM y _j => Data.IntMap.Base.null (Data.IntMap.Base.intersection
                                                       x y)
    end.

Definition disjointUdfmUfm {elt} {elt2} : UniqDFM elt -> UniqFM.UniqFM
                                          elt2 -> bool :=
  fun arg_29__ arg_30__ =>
    match arg_29__ , arg_30__ with
      | UDFM x _i , y => Data.IntMap.Base.null (Data.IntMap.Base.intersection x
                                               (UniqFM.ufmToIntMap y))
    end.

Definition elemUDFM {key} {elt} `{Unique.Uniquable key} : key -> UniqDFM
                                                          elt -> bool :=
  fun arg_67__ arg_68__ =>
    match arg_67__ , arg_68__ with
      | k , UDFM m _i => Data.IntMap.Base.member (Unique.getKey GHC.Base.$
                                                 Unique.getUnique k) m
    end.

Definition emptyUDFM {elt} : UniqDFM elt :=
  UDFM Data.IntMap.Base.empty (GHC.Num.fromInteger 0).

Definition listToUDFM_Directly {elt} : list (Unique.Unique *
                                            elt)%type -> UniqDFM elt :=
  Data.Foldable.foldl (fun arg_118__ arg_119__ =>
                        match arg_118__ , arg_119__ with
                          | m , pair u v => addToUDFM_Directly m u v
                        end) emptyUDFM.

Definition alwaysUnsafeUfmToUdfm {elt} : UniqFM.UniqFM elt -> UniqDFM elt :=
  listToUDFM_Directly GHC.Base.∘ UniqFM.ufmToList.

Local Definition Monoid__UniqDFM_mempty {inst_a} : (UniqDFM inst_a) :=
  emptyUDFM.

Definition filterUDFM {elt} : (elt -> bool) -> UniqDFM elt -> UniqDFM elt :=
  fun arg_60__ arg_61__ =>
    match arg_60__ , arg_61__ with
      | p , UDFM m i => UDFM (Data.IntMap.Base.filter (fun arg_62__ =>
                                                        match arg_62__ with
                                                          | Mk_TaggedVal v _ => p v
                                                        end) m) i
    end.

Definition filterUDFM_Directly {elt} : (Unique.Unique -> elt -> bool) -> UniqDFM
                                       elt -> UniqDFM elt :=
  fun arg_52__ arg_53__ =>
    match arg_52__ , arg_53__ with
      | p , UDFM m i => let p' :=
                          fun arg_54__ arg_55__ =>
                            match arg_54__ , arg_55__ with
                              | k , Mk_TaggedVal v _ => p (Unique.getUnique k) v
                            end in
                        UDFM (Data.IntMap.Base.filterWithKey p' m) i
    end.

Definition intersectUDFM {elt} : UniqDFM elt -> UniqDFM elt -> UniqDFM elt :=
  fun arg_41__ arg_42__ =>
    match arg_41__ , arg_42__ with
      | UDFM x i , UDFM y _j => UDFM (Data.IntMap.Base.intersection x y) i
    end.

Definition isNullUDFM {elt} : UniqDFM elt -> bool :=
  fun arg_48__ => match arg_48__ with | UDFM m _ => Data.IntMap.Base.null m end.

Definition intersectsUDFM {elt} : UniqDFM elt -> UniqDFM elt -> bool :=
  fun x y => isNullUDFM (intersectUDFM x y).

Definition mapUDFM {elt1} {elt2} : (elt1 -> elt2) -> UniqDFM elt1 -> UniqDFM
                                   elt2 :=
  fun arg_0__ arg_1__ =>
    match arg_0__ , arg_1__ with
      | f , UDFM m i => UDFM (Data.IntMap.Base.map (GHC.Base.fmap f) m) i
    end.

Definition minusUDFM {elt1} {elt2} : UniqDFM elt1 -> UniqDFM elt2 -> UniqDFM
                                     elt1 :=
  fun arg_25__ arg_26__ =>
    match arg_25__ , arg_26__ with
      | UDFM x i , UDFM y _j => UDFM (Data.IntMap.Base.difference x y) i
    end.

Definition sizeUDFM {elt} : UniqDFM elt -> GHC.Num.Int :=
  fun arg_45__ => match arg_45__ with | UDFM m _i => Data.IntMap.Base.size m end.

Definition taggedFst {val} : TaggedVal val -> val :=
  fun arg_126__ => match arg_126__ with | Mk_TaggedVal v _ => v end.

Definition udfmToUfm {elt} : UniqDFM elt -> UniqFM.UniqFM elt :=
  fun arg_166__ =>
    match arg_166__ with
      | UDFM m _i => UniqFM.listToUFM_Directly (let cont_167__ arg_168__ :=
                                                 match arg_168__ with
                                                   | pair k tv => cons (pair (Unique.getUnique k) (taggedFst tv)) nil
                                                 end in
                                               Coq.Lists.List.flat_map cont_167__ (Data.IntMap.Base.toList m))
    end.

Definition partitionUDFM {elt} : (elt -> bool) -> UniqDFM elt -> (UniqDFM elt *
                                 UniqDFM elt)%type :=
  fun arg_159__ arg_160__ =>
    match arg_159__ , arg_160__ with
      | p , UDFM m i => let scrut_161__ :=
                          Data.IntMap.Base.partition (p GHC.Base.∘ taggedFst) m in
                        match scrut_161__ with
                          | pair left_ right_ => pair (UDFM left_ i) (UDFM right_ i)
                        end
    end.

Definition nonDetFoldUDFM {elt} {a} : (elt -> a -> a) -> a -> UniqDFM
                                      elt -> a :=
  fun arg_132__ arg_133__ arg_134__ =>
    match arg_132__ , arg_133__ , arg_134__ with
      | k , z , UDFM m _i => Data.Foldable.foldr k z GHC.Base.$ (GHC.Base.map
                             taggedFst GHC.Base.$ Data.IntMap.Base.elems m)
    end.

Definition lookupUDFM {key} {elt} `{Unique.Uniquable key} : UniqDFM
                                                            elt -> key -> option elt :=
  fun arg_128__ arg_129__ =>
    match arg_128__ , arg_129__ with
      | UDFM m _i , k => GHC.Base.fmap taggedFst (Data.IntMap.Base.lookup
                                       (Unique.getKey GHC.Base.$ Unique.getUnique k) m)
    end.

Definition anyUDFM {elt} : (elt -> bool) -> UniqDFM elt -> bool :=
  fun arg_171__ arg_172__ =>
    match arg_171__ , arg_172__ with
      | p , UDFM m _i => Data.IntMap.fold (orb GHC.Base.∘ (p GHC.Base.∘ taggedFst))
                         false m
    end.

Definition taggedSnd {val} : TaggedVal val -> GHC.Num.Int :=
  fun arg_124__ => match arg_124__ with | Mk_TaggedVal _ i => i end.

Definition udfmToList {elt} : UniqDFM elt -> list (Unique.Unique * elt)%type :=
  fun arg_141__ =>
    match arg_141__ with
      | UDFM m _i => let cont_142__ arg_143__ :=
                       match arg_143__ with
                         | pair k v => cons (pair (Unique.getUnique k) (taggedFst v)) nil
                       end in
                     Coq.Lists.List.flat_map cont_142__ (Data.OldList.sortBy (Data.Function.on
                                                                             GHC.Base.compare (taggedSnd GHC.Base.∘
                                                                             Data.Tuple.snd)) GHC.Base.$
                                             Data.IntMap.Base.toList m)
    end.

Definition insertUDFMIntoLeft_C {elt} : (elt -> elt -> elt) -> UniqDFM
                                        elt -> UniqDFM elt -> UniqDFM elt :=
  fun f udfml udfmr =>
    addListToUDFM_Directly_C f udfml GHC.Base.$ udfmToList udfmr.

Definition plusUDFM_C {elt} : (elt -> elt -> elt) -> UniqDFM elt -> UniqDFM
                              elt -> UniqDFM elt :=
  fun arg_153__ arg_154__ arg_155__ =>
    match arg_153__ , arg_154__ , arg_155__ with
      | f , (UDFM _ i as udfml) , (UDFM _ j as udfmr) => let j_156__ :=
                                                           insertUDFMIntoLeft_C f udfmr udfml in
                                                         if i GHC.Base.> j : bool
                                                         then insertUDFMIntoLeft_C f udfml udfmr
                                                         else j_156__
    end.

Definition insertUDFMIntoLeft {elt} : UniqDFM elt -> UniqDFM elt -> UniqDFM
                                      elt :=
  fun udfml udfmr => addListToUDFM_Directly udfml GHC.Base.$ udfmToList udfmr.

Definition plusUDFM {elt} : UniqDFM elt -> UniqDFM elt -> UniqDFM elt :=
  fun arg_147__ arg_148__ =>
    match arg_147__ , arg_148__ with
      | (UDFM _ i as udfml) , (UDFM _ j as udfmr) => let j_149__ :=
                                                       insertUDFMIntoLeft udfmr udfml in
                                                     if i GHC.Base.> j : bool
                                                     then insertUDFMIntoLeft udfml udfmr
                                                     else j_149__
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

Definition eltsUDFM {elt} : UniqDFM elt -> list elt :=
  fun arg_137__ =>
    match arg_137__ with
      | UDFM m _i => GHC.Base.map taggedFst GHC.Base.$ (Data.OldList.sortBy
                     (Data.Function.on GHC.Base.compare taggedSnd) GHC.Base.$ Data.IntMap.Base.elems
                     m)
    end.

Definition foldUDFM {elt} {a} : (elt -> a -> a) -> a -> UniqDFM elt -> a :=
  fun k z m => Data.Foldable.foldr k z (eltsUDFM m).

Definition udfmIntersectUFM {elt} : UniqDFM elt -> UniqFM.UniqFM elt -> UniqDFM
                                    elt :=
  fun arg_37__ arg_38__ =>
    match arg_37__ , arg_38__ with
      | UDFM x i , y => UDFM (Data.IntMap.Base.intersection x (UniqFM.ufmToIntMap y))
                        i
    end.

Definition udfmMinusUFM {elt1} {elt2} : UniqDFM elt1 -> UniqFM.UniqFM
                                        elt2 -> UniqDFM elt1 :=
  fun arg_21__ arg_22__ =>
    match arg_21__ , arg_22__ with
      | UDFM x i , y => UDFM (Data.IntMap.Base.difference x (UniqFM.ufmToIntMap y)) i
    end.

Definition unitUDFM {key} {elt} `{Unique.Uniquable key} : key -> elt -> UniqDFM
                                                          elt :=
  fun k v =>
    UDFM (Data.IntMap.Base.singleton (Unique.getKey GHC.Base.$ Unique.getUnique k)
         (Mk_TaggedVal v (GHC.Num.fromInteger 0))) (GHC.Num.fromInteger 1).

(* Unbound variables:
     Some bool cons false list negb nil op_zt__ option orb pair
     Coq.Lists.List.flat_map Data.Foldable.foldl Data.Foldable.foldr Data.Function.on
     Data.IntMap.fold Data.IntMap.Base.IntMap Data.IntMap.Base.adjust
     Data.IntMap.Base.alter Data.IntMap.Base.delete Data.IntMap.Base.difference
     Data.IntMap.Base.elems Data.IntMap.Base.empty Data.IntMap.Base.filter
     Data.IntMap.Base.filterWithKey Data.IntMap.Base.insert
     Data.IntMap.Base.insertWith Data.IntMap.Base.intersection
     Data.IntMap.Base.lookup Data.IntMap.Base.map Data.IntMap.Base.member
     Data.IntMap.Base.null Data.IntMap.Base.partition Data.IntMap.Base.singleton
     Data.IntMap.Base.size Data.IntMap.Base.toList Data.OldList.sortBy Data.Tuple.snd
     GHC.Base.Eq_ GHC.Base.Functor GHC.Base.Monoid GHC.Base.compare GHC.Base.const
     GHC.Base.fmap GHC.Base.foldr GHC.Base.map GHC.Base.op_z2218U__ GHC.Base.op_zd__
     GHC.Base.op_zeze__ GHC.Base.op_zg__ GHC.Num.Int GHC.Num.op_zp__ UniqFM.UniqFM
     UniqFM.listToUFM_Directly UniqFM.ufmToIntMap UniqFM.ufmToList Unique.Uniquable
     Unique.Unique Unique.getKey Unique.getUnique
*)
