(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Coq.Program.Tactics.
Require Coq.Program.Wf.

(* Preamble *)

Require Import GHC.Base.

Module GHC.
  Module Err.
    Axiom undefined : forall {a}, a.
    Axiom error : forall {a}, String -> a.
  End Err.
End GHC.

(* Converted imports: *)

Require Data.Foldable.
Require GHC.Base.
Require GHC.Num.
Require GHC.Prim.

(* Converted type declarations: *)

Definition Size :=
  GHC.Num.Int%type.

Inductive Set_ a : Type := Mk_Bin : Size -> a -> (Set_ a) -> (Set_ a) -> Set_ a
                        |  Mk_Tip : Set_ a.

Inductive MaybeS a : Type := Mk_NothingS : MaybeS a
                          |  Mk_JustS : a -> MaybeS a.

Arguments Mk_Bin {_} _ _ _ _.

Arguments Mk_Tip {_}.

Arguments Mk_NothingS {_}.

Arguments Mk_JustS {_} _.
(* Converted value declarations: *)

(* The Haskell code containes partial or untranslateable code, which needs the
   following *)

Axiom patternFailure : forall {a}, a.

(* Translating `instance forall {a}, forall `{GHC.Base.Ord a}, GHC.Base.Monoid
   (Set_ a)' failed: missing "mappend" in fromList
   [("mconcat","instance_forall___GHC_Base_Ord_a___GHC_Base_Monoid__Set__a__mconcat"),("mempty","instance_forall___GHC_Base_Ord_a___GHC_Base_Monoid__Set__a__mempty")]
   unsupported *)

(* Translating `instance forall {a}, forall `{GHC.Base.Ord a},
   Data.Semigroup.Semigroup (Set_ a)' failed: OOPS! Cannot find information for
   class "Data.Semigroup.Semigroup" unsupported *)

Local Definition instance_Data_Foldable_Foldable_Set__elem : forall {a},
                                                               forall `{GHC.Base.Eq_ a}, a -> Set_ a -> bool :=
  fun {a} `{GHC.Base.Eq_ a} =>
    let go :=
      fix go arg_370__ arg_371__
            := let j_373__ :=
                 match arg_370__ , arg_371__ with
                   | _ , Mk_Tip => false
                   | x , Mk_Bin _ y l r => orb (GHC.Base.op_zeze__ x y) (orb (go x l) (go x r))
                 end in
               match arg_370__ , arg_371__ with
                 | arg , _ => if GHC.Prim.seq arg false : bool
                              then GHC.Err.undefined
                              else j_373__
               end in
    go.

Local Definition instance_Data_Foldable_Foldable_Set__fold : forall {m},
                                                               forall `{GHC.Base.Monoid m}, Set_ m -> m :=
  fun {m} `{GHC.Base.Monoid m} =>
    let go :=
      fix go arg_357__
            := let j_360__ :=
                 match arg_357__ with
                   | Mk_Bin _ k l r => GHC.Base.mappend (go l) (GHC.Base.mappend k (go r))
                   | _ => patternFailure
                 end in
               match arg_357__ with
                 | Mk_Tip => GHC.Base.mempty
                 | Mk_Bin num_358__ k _ _ => if (num_358__ == GHC.Num.fromInteger 1) : bool
                                             then k
                                             else j_360__
               end in
    go.

Local Definition instance_Data_Foldable_Foldable_Set__foldMap : forall {m} {a},
                                                                  forall `{GHC.Base.Monoid m},
                                                                    (a -> m) -> Set_ a -> m :=
  fun {m} {a} `{GHC.Base.Monoid m} =>
    fun f t =>
      let go :=
        fix go arg_363__
              := let j_366__ :=
                   match arg_363__ with
                     | Mk_Bin _ k l r => GHC.Base.mappend (go l) (GHC.Base.mappend (f k) (go r))
                     | _ => patternFailure
                   end in
                 match arg_363__ with
                   | Mk_Tip => GHC.Base.mempty
                   | Mk_Bin num_364__ k _ _ => if (num_364__ == GHC.Num.fromInteger 1) : bool
                                               then f k
                                               else j_366__
                 end in
      go t.

(* Translating `instance forall {a}, forall `{Data.Data.Data a} `{GHC.Base.Ord
   a}, Data.Data.Data (Set_ a)' failed: OOPS! Cannot find information for class
   "Data.Data.Data" unsupported *)

(* Translating `instance forall {a}, forall `{(GHC.Base.Ord a)}, GHC.Exts.IsList
   (Set_ a)' failed: OOPS! Cannot find information for class "GHC.Exts.IsList"
   unsupported *)

(* Translating `instance forall {a}, forall `{GHC.Show.Show a}, GHC.Show.Show
   (Set_ a)' failed: OOPS! Cannot find information for class "GHC.Show.Show"
   unsupported *)

(* Translating `instance forall {a}, forall `{GHC.Read.Read a} `{GHC.Base.Ord
   a}, GHC.Read.Read (Set_ a)' failed: OOPS! Cannot find information for class
   "GHC.Read.Read" unsupported *)

(* Translating `instance forall {a}, forall `{Control.DeepSeq.NFData a},
   Control.DeepSeq.NFData (Set_ a)' failed: OOPS! Cannot find information for class
   "Control.DeepSeq.NFData" unsupported *)

Definition delta : GHC.Num.Int :=
  GHC.Num.fromInteger 3.

Definition empty {a} : Set_ a :=
  Mk_Tip.

Definition findMax {a} : Set_ a -> a :=
  fix findMax arg_66__
        := match arg_66__ with
             | Mk_Bin _ x _ Mk_Tip => x
             | Mk_Bin _ _ _ r => findMax r
             | Mk_Tip => GHC.Err.error (GHC.Base.hs_string__
                                       "Set.findMax: empty set has no maximal element")
           end.

Definition findMin {a} : Set_ a -> a :=
  fix findMin arg_70__
        := match arg_70__ with
             | Mk_Bin _ x Mk_Tip _ => x
             | Mk_Bin _ _ l _ => findMin l
             | Mk_Tip => GHC.Err.error (GHC.Base.hs_string__
                                       "Set.findMin: empty set has no minimal element")
           end.

Definition foldl {a} {b} : (a -> b -> a) -> a -> Set_ b -> a :=
  fun f z =>
    let go :=
      fix go arg_43__ arg_44__
            := match arg_43__ , arg_44__ with
                 | z' , Mk_Tip => z'
                 | z' , Mk_Bin _ x l r => go (f (go z' l) x) r
               end in
    go z.

Definition foldlFB {a} {b} : (a -> b -> a) -> a -> Set_ b -> a :=
  foldl.

Definition toDescList {a} : Set_ a -> list a :=
  foldl (GHC.Base.flip cons) nil.

Local Definition instance_Data_Foldable_Foldable_Set__foldl : forall {b} {a},
                                                                (b -> a -> b) -> b -> Set_ a -> b :=
  fun {b} {a} => foldl.

Definition foldl' {a} {b} : (a -> b -> a) -> a -> Set_ b -> a :=
  fun f z =>
    let go :=
      fix go arg_36__ arg_37__
            := let j_39__ :=
                 match arg_36__ , arg_37__ with
                   | z' , Mk_Tip => z'
                   | z' , Mk_Bin _ x l r => go (f (go z' l) x) r
                 end in
               match arg_36__ , arg_37__ with
                 | arg , _ => if GHC.Prim.seq arg false : bool
                              then GHC.Err.undefined
                              else j_39__
               end in
    go z.

Local Definition instance_Data_Foldable_Foldable_Set__foldl' : forall {b} {a},
                                                                 (b -> a -> b) -> b -> Set_ a -> b :=
  fun {b} {a} => foldl'.

Local Definition instance_Data_Foldable_Foldable_Set__product : forall {a},
                                                                  forall `{GHC.Num.Num a}, Set_ a -> a :=
  fun {a} `{GHC.Num.Num a} =>
    instance_Data_Foldable_Foldable_Set__foldl' GHC.Num.op_zt__ (GHC.Num.fromInteger
                                                                1).

Local Definition instance_Data_Foldable_Foldable_Set__sum : forall {a},
                                                              forall `{GHC.Num.Num a}, Set_ a -> a :=
  fun {a} `{GHC.Num.Num a} =>
    instance_Data_Foldable_Foldable_Set__foldl' GHC.Num.op_zp__ (GHC.Num.fromInteger
                                                                0).

Definition foldr {a} {b} : (a -> b -> b) -> b -> Set_ a -> b :=
  fun f z =>
    let go :=
      fix go arg_56__ arg_57__
            := match arg_56__ , arg_57__ with
                 | z' , Mk_Tip => z'
                 | z' , Mk_Bin _ x l r => go (f x (go z' r)) l
               end in
    go z.

Definition foldrFB {a} {b} : (a -> b -> b) -> b -> Set_ a -> b :=
  foldr.

Definition toAscList {a} : Set_ a -> list a :=
  foldr cons nil.

Definition toList {a} : Set_ a -> list a :=
  toAscList.

Local Definition instance_Data_Foldable_Foldable_Set__toList : forall {a},
                                                                 Set_ a -> list a :=
  fun {a} => toList.

Definition elems {a} : Set_ a -> list a :=
  toAscList.

Local Definition instance_forall___GHC_Base_Ord_a___GHC_Base_Ord__Set__a__compare {inst_a}
                                                                                  `{GHC.Base.Ord inst_a} : (Set_
                                                                                                           inst_a) -> (Set_
                                                                                                           inst_a) -> comparison :=
  fun s1 s2 => GHC.Base.compare (toAscList s1) (toAscList s2).

Local Definition instance_forall___GHC_Base_Ord_a___GHC_Base_Ord__Set__a__op_zg__ {inst_a}
                                                                                  `{GHC.Base.Ord inst_a} : (Set_
                                                                                                           inst_a) -> (Set_
                                                                                                           inst_a) -> bool :=
  fun x y =>
    op_zeze__ (instance_forall___GHC_Base_Ord_a___GHC_Base_Ord__Set__a__compare x y)
              Gt.

Local Definition instance_forall___GHC_Base_Ord_a___GHC_Base_Ord__Set__a__op_zgze__ {inst_a}
                                                                                    `{GHC.Base.Ord inst_a} : (Set_
                                                                                                             inst_a) -> (Set_
                                                                                                             inst_a) -> bool :=
  fun x y =>
    op_zsze__ (instance_forall___GHC_Base_Ord_a___GHC_Base_Ord__Set__a__compare x y)
              Lt.

Local Definition instance_forall___GHC_Base_Ord_a___GHC_Base_Ord__Set__a__op_zl__ {inst_a}
                                                                                  `{GHC.Base.Ord inst_a} : (Set_
                                                                                                           inst_a) -> (Set_
                                                                                                           inst_a) -> bool :=
  fun x y =>
    op_zeze__ (instance_forall___GHC_Base_Ord_a___GHC_Base_Ord__Set__a__compare x y)
              Lt.

Local Definition instance_forall___GHC_Base_Ord_a___GHC_Base_Ord__Set__a__op_zlze__ {inst_a}
                                                                                    `{GHC.Base.Ord inst_a} : (Set_
                                                                                                             inst_a) -> (Set_
                                                                                                             inst_a) -> bool :=
  fun x y =>
    op_zsze__ (instance_forall___GHC_Base_Ord_a___GHC_Base_Ord__Set__a__compare x y)
              Gt.

Local Definition instance_forall___GHC_Base_Ord_a___GHC_Base_Ord__Set__a__max {inst_a}
                                                                              `{GHC.Base.Ord inst_a} : (Set_
                                                                                                       inst_a) -> (Set_
                                                                                                       inst_a) -> (Set_
                                                                                                       inst_a) :=
  fun x y =>
    if instance_forall___GHC_Base_Ord_a___GHC_Base_Ord__Set__a__op_zlze__ x y : bool
    then y
    else x.

Local Definition instance_forall___GHC_Base_Ord_a___GHC_Base_Ord__Set__a__min {inst_a}
                                                                              `{GHC.Base.Ord inst_a} : (Set_
                                                                                                       inst_a) -> (Set_
                                                                                                       inst_a) -> (Set_
                                                                                                       inst_a) :=
  fun x y =>
    if instance_forall___GHC_Base_Ord_a___GHC_Base_Ord__Set__a__op_zlze__ x y : bool
    then x
    else y.

Definition fold {a} {b} : (a -> b -> b) -> b -> Set_ a -> b :=
  foldr.

Local Definition instance_Data_Foldable_Foldable_Set__foldr : forall {a} {b},
                                                                (a -> b -> b) -> b -> Set_ a -> b :=
  fun {a} {b} => foldr.

Definition foldr' {a} {b} : (a -> b -> b) -> b -> Set_ a -> b :=
  fun f z =>
    let go :=
      fix go arg_49__ arg_50__
            := let j_52__ :=
                 match arg_49__ , arg_50__ with
                   | z' , Mk_Tip => z'
                   | z' , Mk_Bin _ x l r => go (f x (go z' r)) l
                 end in
               match arg_49__ , arg_50__ with
                 | arg , _ => if GHC.Prim.seq arg false : bool
                              then GHC.Err.undefined
                              else j_52__
               end in
    go z.

Local Definition instance_Data_Foldable_Foldable_Set__foldr' : forall {a} {b},
                                                                 (a -> b -> b) -> b -> Set_ a -> b :=
  fun {a} {b} => foldr'.

Definition lookupGE {a} `{GHC.Base.Ord a} : a -> Set_ a -> option a :=
  let goJust :=
    fix goJust arg_78__ arg_79__ arg_80__
          := let j_88__ :=
               match arg_78__ , arg_79__ , arg_80__ with
                 | _ , best , Mk_Tip => Some best
                 | x , best , Mk_Bin _ y l r => let scrut_82__ := GHC.Base.compare x y in
                                                match scrut_82__ with
                                                  | Lt => goJust x y l
                                                  | Eq => Some y
                                                  | Gt => goJust x best r
                                                end
               end in
             match arg_78__ , arg_79__ , arg_80__ with
               | arg , _ , _ => if GHC.Prim.seq arg false : bool
                                then GHC.Err.undefined
                                else j_88__
             end in
  let goNothing :=
    fix goNothing arg_91__ arg_92__
          := let j_99__ :=
               match arg_91__ , arg_92__ with
                 | _ , Mk_Tip => None
                 | x , Mk_Bin _ y l r => let scrut_93__ := GHC.Base.compare x y in
                                         match scrut_93__ with
                                           | Lt => goJust x y l
                                           | Eq => Some y
                                           | Gt => goNothing x r
                                         end
               end in
             match arg_91__ , arg_92__ with
               | arg , _ => if GHC.Prim.seq arg false : bool
                            then GHC.Err.undefined
                            else j_99__
             end in
  goNothing.

Definition lookupGT {a} `{GHC.Base.Ord a} : a -> Set_ a -> option a :=
  let goJust :=
    fix goJust arg_126__ arg_127__ arg_128__
          := let j_132__ :=
               match arg_126__ , arg_127__ , arg_128__ with
                 | _ , best , Mk_Tip => Some best
                 | x , best , Mk_Bin _ y l r => let j_130__ := goJust x best r in
                                                if GHC.Base.op_zl__ x y : bool
                                                then goJust x y l
                                                else j_130__
               end in
             match arg_126__ , arg_127__ , arg_128__ with
               | arg , _ , _ => if GHC.Prim.seq arg false : bool
                                then GHC.Err.undefined
                                else j_132__
             end in
  let goNothing :=
    fix goNothing arg_135__ arg_136__
          := let j_139__ :=
               match arg_135__ , arg_136__ with
                 | _ , Mk_Tip => None
                 | x , Mk_Bin _ y l r => let j_137__ := goNothing x r in
                                         if GHC.Base.op_zl__ x y : bool
                                         then goJust x y l
                                         else j_137__
               end in
             match arg_135__ , arg_136__ with
               | arg , _ => if GHC.Prim.seq arg false : bool
                            then GHC.Err.undefined
                            else j_139__
             end in
  goNothing.

Definition lookupLE {a} `{GHC.Base.Ord a} : a -> Set_ a -> option a :=
  let goJust :=
    fix goJust arg_102__ arg_103__ arg_104__
          := let j_112__ :=
               match arg_102__ , arg_103__ , arg_104__ with
                 | _ , best , Mk_Tip => Some best
                 | x , best , Mk_Bin _ y l r => let scrut_106__ := GHC.Base.compare x y in
                                                match scrut_106__ with
                                                  | Lt => goJust x best l
                                                  | Eq => Some y
                                                  | Gt => goJust x y r
                                                end
               end in
             match arg_102__ , arg_103__ , arg_104__ with
               | arg , _ , _ => if GHC.Prim.seq arg false : bool
                                then GHC.Err.undefined
                                else j_112__
             end in
  let goNothing :=
    fix goNothing arg_115__ arg_116__
          := let j_123__ :=
               match arg_115__ , arg_116__ with
                 | _ , Mk_Tip => None
                 | x , Mk_Bin _ y l r => let scrut_117__ := GHC.Base.compare x y in
                                         match scrut_117__ with
                                           | Lt => goNothing x l
                                           | Eq => Some y
                                           | Gt => goJust x y r
                                         end
               end in
             match arg_115__ , arg_116__ with
               | arg , _ => if GHC.Prim.seq arg false : bool
                            then GHC.Err.undefined
                            else j_123__
             end in
  goNothing.

Definition lookupLT {a} `{GHC.Base.Ord a} : a -> Set_ a -> option a :=
  let goJust :=
    fix goJust arg_142__ arg_143__ arg_144__
          := let j_148__ :=
               match arg_142__ , arg_143__ , arg_144__ with
                 | _ , best , Mk_Tip => Some best
                 | x , best , Mk_Bin _ y l r => let j_146__ := goJust x y r in
                                                if GHC.Base.op_zlze__ x y : bool
                                                then goJust x best l
                                                else j_146__
               end in
             match arg_142__ , arg_143__ , arg_144__ with
               | arg , _ , _ => if GHC.Prim.seq arg false : bool
                                then GHC.Err.undefined
                                else j_148__
             end in
  let goNothing :=
    fix goNothing arg_151__ arg_152__
          := let j_155__ :=
               match arg_151__ , arg_152__ with
                 | _ , Mk_Tip => None
                 | x , Mk_Bin _ y l r => let j_153__ := goJust x y r in
                                         if GHC.Base.op_zlze__ x y : bool
                                         then goNothing x l
                                         else j_153__
               end in
             match arg_151__ , arg_152__ with
               | arg , _ => if GHC.Prim.seq arg false : bool
                            then GHC.Err.undefined
                            else j_155__
             end in
  goNothing.

Definition mapMonotonic {a} {b} : (a -> b) -> Set_ a -> Set_ b :=
  fix mapMonotonic arg_62__ arg_63__
        := match arg_62__ , arg_63__ with
             | _ , Mk_Tip => Mk_Tip
             | f , Mk_Bin sz x l r => Mk_Bin sz (f x) (mapMonotonic f l) (mapMonotonic f r)
           end.

Definition member {a} `{GHC.Base.Ord a} : a -> Set_ a -> bool :=
  let go :=
    fix go arg_158__ arg_159__
          := let j_165__ :=
               match arg_158__ , arg_159__ with
                 | _ , Mk_Tip => false
                 | x , Mk_Bin _ y l r => let scrut_160__ := GHC.Base.compare x y in
                                         match scrut_160__ with
                                           | Lt => go x l
                                           | Gt => go x r
                                           | Eq => true
                                         end
               end in
             match arg_158__ , arg_159__ with
               | arg , _ => if GHC.Prim.seq arg false : bool
                            then GHC.Err.undefined
                            else j_165__
             end in
  go.

Definition notMember {a} `{GHC.Base.Ord a} : a -> Set_ a -> bool :=
  fun a t => GHC.Base.op_zd__ negb (member a t).

Definition node : GHC.Base.String :=
  GHC.Base.hs_string__ "+--".

Definition null {a} : Set_ a -> bool :=
  fun arg_353__ =>
    match arg_353__ with
      | Mk_Tip => true
      | Mk_Bin _ _ _ _ => false
    end.

Local Definition instance_Data_Foldable_Foldable_Set__null : forall {a},
                                                               Set_ a -> bool :=
  fun {a} => null.

Definition ordered {a} `{GHC.Base.Ord a} : Set_ a -> bool :=
  fun t =>
    let bounded :=
      fix bounded lo hi t'
            := match t' with
                 | Mk_Tip => true
                 | Mk_Bin _ x l r => andb (lo x) (andb (hi x) (andb (bounded lo (fun arg_0__ =>
                                                                                  GHC.Base.op_zl__ arg_0__ x) l)
                                                                    (bounded (fun arg_1__ => GHC.Base.op_zg__ arg_1__ x)
                                                                    hi r)))
               end in
    bounded (GHC.Base.const true) (GHC.Base.const true) t.

Definition ratio : GHC.Num.Int :=
  GHC.Num.fromInteger 2.

Definition singleton {a} : a -> Set_ a :=
  fun x => Mk_Bin (GHC.Num.fromInteger 1) x Mk_Tip Mk_Tip.

Definition splitRoot {a} : Set_ a -> list (Set_ a) :=
  fun orig =>
    match orig with
      | Mk_Tip => nil
      | Mk_Bin _ v l r => cons l (cons (singleton v) (cons r nil))
    end.

Definition size {a} : Set_ a -> GHC.Num.Int :=
  fun arg_169__ =>
    match arg_169__ with
      | Mk_Tip => GHC.Num.fromInteger 0
      | Mk_Bin sz _ _ _ => sz
    end.

Definition validsize {a} : Set_ a -> bool :=
  fun t =>
    let realsize :=
      fix realsize t'
            := match t' with
                 | Mk_Tip => Some (GHC.Num.fromInteger 0)
                 | Mk_Bin sz _ l r => let scrut_345__ := pair (realsize l) (realsize r) in
                                      match scrut_345__ with
                                        | pair (Some n) (Some m) => if GHC.Base.op_zeze__ (GHC.Num.op_zp__
                                                                                          (GHC.Num.op_zp__ n m)
                                                                                          (GHC.Num.fromInteger 1))
                                                                                          sz : bool
                                                                    then Some sz
                                                                    else None
                                        | _ => None
                                      end
               end in
    (GHC.Base.op_zeze__ (realsize t) (Some (size t))).

Definition lookupIndex {a} `{GHC.Base.Ord a} : a -> Set_ a -> option
                                               GHC.Num.Int :=
  let go {a} `{GHC.Base.Ord a} : GHC.Num.Int -> a -> Set_ a -> option
                                 GHC.Num.Int :=
    fix go arg_188__ arg_189__ arg_190__
          := let j_197__ :=
               match arg_188__ , arg_189__ , arg_190__ with
                 | _ , _ , Mk_Tip => None
                 | idx , x , Mk_Bin _ kx l r => let scrut_191__ := GHC.Base.compare x kx in
                                                match scrut_191__ with
                                                  | Lt => go idx x l
                                                  | Gt => go (GHC.Num.op_zp__ (GHC.Num.op_zp__ idx (size l))
                                                                              (GHC.Num.fromInteger 1)) x r
                                                  | Eq => GHC.Base.op_zdzn__ Some (GHC.Num.op_zp__ idx (size l))
                                                end
               end in
             let j_199__ :=
               match arg_188__ , arg_189__ , arg_190__ with
                 | _ , arg , _ => if GHC.Prim.seq arg false : bool
                                  then GHC.Err.undefined
                                  else j_197__
               end in
             match arg_188__ , arg_189__ , arg_190__ with
               | arg , _ , _ => if GHC.Prim.seq arg false : bool
                                then GHC.Err.undefined
                                else j_199__
             end in
  go (GHC.Num.fromInteger 0).

Definition findIndex {a} `{GHC.Base.Ord a} : a -> Set_ a -> GHC.Num.Int :=
  let go {a} `{GHC.Base.Ord a} : GHC.Num.Int -> a -> Set_ a -> GHC.Num.Int :=
    fix go arg_172__ arg_173__ arg_174__
          := let j_182__ :=
               match arg_172__ , arg_173__ , arg_174__ with
                 | _ , _ , Mk_Tip => GHC.Err.error (GHC.Base.hs_string__
                                                   "Set.findIndex: element is not in the set")
                 | idx , x , Mk_Bin _ kx l r => let scrut_176__ := GHC.Base.compare x kx in
                                                match scrut_176__ with
                                                  | Lt => go idx x l
                                                  | Gt => go (GHC.Num.op_zp__ (GHC.Num.op_zp__ idx (size l))
                                                                              (GHC.Num.fromInteger 1)) x r
                                                  | Eq => GHC.Num.op_zp__ idx (size l)
                                                end
               end in
             let j_184__ :=
               match arg_172__ , arg_173__ , arg_174__ with
                 | _ , arg , _ => if GHC.Prim.seq arg false : bool
                                  then GHC.Err.undefined
                                  else j_182__
               end in
             match arg_172__ , arg_173__ , arg_174__ with
               | arg , _ , _ => if GHC.Prim.seq arg false : bool
                                then GHC.Err.undefined
                                else j_184__
             end in
  go (GHC.Num.fromInteger 0).

Definition elemAt {a} : GHC.Num.Int -> Set_ a -> a :=
  fix elemAt arg_203__ arg_204__
        := let j_212__ :=
             match arg_203__ , arg_204__ with
               | _ , Mk_Tip => GHC.Err.error (GHC.Base.hs_string__
                                             "Set.elemAt: index out of range")
               | i , Mk_Bin _ x l r => let sizeL := size l in
                                       let scrut_207__ := GHC.Base.compare i sizeL in
                                       match scrut_207__ with
                                         | Lt => elemAt i l
                                         | Gt => elemAt (GHC.Num.op_zm__ (GHC.Num.op_zm__ i sizeL) (GHC.Num.fromInteger
                                                                         1)) r
                                         | Eq => x
                                       end
             end in
           match arg_203__ , arg_204__ with
             | arg , _ => if GHC.Prim.seq arg false : bool
                          then GHC.Err.undefined
                          else j_212__
           end.

Definition bin {a} : a -> Set_ a -> Set_ a -> Set_ a :=
  fun x l r =>
    Mk_Bin (GHC.Num.op_zp__ (GHC.Num.op_zp__ (size l) (size r)) (GHC.Num.fromInteger
                            1)) x l r.

Definition balanced {a} : Set_ a -> bool :=
  fix balanced t
        := match t with
             | Mk_Tip => true
             | Mk_Bin _ _ l r => andb (orb (GHC.Base.op_zlze__ (GHC.Num.op_zp__ (size l)
                                                                                (size r)) (GHC.Num.fromInteger 1)) (andb
                                           (GHC.Base.op_zlze__ (size l) (GHC.Num.op_zt__ delta (size r)))
                                           (GHC.Base.op_zlze__ (size r) (GHC.Num.op_zt__ delta (size l))))) (andb
                                      (balanced l) (balanced r))
           end.

Definition valid {a} `{GHC.Base.Ord a} : Set_ a -> bool :=
  fun t => andb (balanced t) (andb (ordered t) (validsize t)).

Definition balanceR {a} : a -> Set_ a -> Set_ a -> Set_ a :=
  fun x l r =>
    match l with
      | Mk_Tip => match r with
                    | Mk_Tip => Mk_Bin (GHC.Num.fromInteger 1) x Mk_Tip Mk_Tip
                    | Mk_Bin _ _ Mk_Tip Mk_Tip => Mk_Bin (GHC.Num.fromInteger 2) x Mk_Tip r
                    | Mk_Bin _ rx Mk_Tip (Mk_Bin _ _ _ _ as rr) => Mk_Bin (GHC.Num.fromInteger 3) rx
                                                                   (Mk_Bin (GHC.Num.fromInteger 1) x Mk_Tip Mk_Tip) rr
                    | Mk_Bin _ rx (Mk_Bin _ rlx _ _) Mk_Tip => Mk_Bin (GHC.Num.fromInteger 3) rlx
                                                               (Mk_Bin (GHC.Num.fromInteger 1) x Mk_Tip Mk_Tip) (Mk_Bin
                                                                                                                (GHC.Num.fromInteger
                                                                                                                1) rx
                                                                                                                Mk_Tip
                                                                                                                Mk_Tip)
                    | Mk_Bin rs rx (Mk_Bin rls rlx rll rlr as rl) (Mk_Bin rrs _ _ _ as rr) =>
                      let j_256__ :=
                        Mk_Bin (GHC.Num.op_zp__ (GHC.Num.fromInteger 1) rs) rlx (Mk_Bin (GHC.Num.op_zp__
                                                                                        (GHC.Num.fromInteger 1) (size
                                                                                        rll)) x Mk_Tip rll) (Mk_Bin
                                                                                                            (GHC.Num.op_zp__
                                                                                                            (GHC.Num.op_zp__
                                                                                                            (GHC.Num.fromInteger
                                                                                                            1) rrs)
                                                                                                            (size rlr))
                                                                                                            rx rlr
                                                                                                            rr) in
                      if GHC.Base.op_zl__ rls (GHC.Num.op_zt__ ratio rrs) : bool
                      then Mk_Bin (GHC.Num.op_zp__ (GHC.Num.fromInteger 1) rs) rx (Mk_Bin
                                                                                  (GHC.Num.op_zp__ (GHC.Num.fromInteger
                                                                                                   1) rls) x Mk_Tip rl)
                           rr
                      else j_256__
                  end
      | Mk_Bin ls _ _ _ => match r with
                             | Mk_Tip => Mk_Bin (GHC.Num.op_zp__ (GHC.Num.fromInteger 1) ls) x l Mk_Tip
                             | Mk_Bin rs rx rl rr => let j_261__ :=
                                                       Mk_Bin (GHC.Num.op_zp__ (GHC.Num.op_zp__ (GHC.Num.fromInteger 1)
                                                                                                ls) rs) x l r in
                                                     if GHC.Base.op_zg__ rs (GHC.Num.op_zt__ delta ls) : bool
                                                     then let scrut_262__ := pair rl rr in
                                                          let j_264__ :=
                                                            match scrut_262__ with
                                                              | pair _ _ => GHC.Err.error (GHC.Base.hs_string__
                                                                                          "Failure in Data.Map.balanceR")
                                                            end in
                                                          match scrut_262__ with
                                                            | pair (Mk_Bin rls rlx rll rlr) (Mk_Bin rrs _ _ _) =>
                                                              let j_265__ :=
                                                                Mk_Bin (GHC.Num.op_zp__ (GHC.Num.op_zp__
                                                                                        (GHC.Num.fromInteger 1) ls) rs)
                                                                rlx (Mk_Bin (GHC.Num.op_zp__ (GHC.Num.op_zp__
                                                                                             (GHC.Num.fromInteger 1) ls)
                                                                                             (size rll)) x l rll)
                                                                (Mk_Bin (GHC.Num.op_zp__ (GHC.Num.op_zp__
                                                                                         (GHC.Num.fromInteger 1) rrs)
                                                                                         (size rlr)) rx rlr rr) in
                                                              if GHC.Base.op_zl__ rls (GHC.Num.op_zt__ ratio rrs) : bool
                                                              then Mk_Bin (GHC.Num.op_zp__ (GHC.Num.op_zp__
                                                                                           (GHC.Num.fromInteger 1) ls)
                                                                                           rs) rx (Mk_Bin
                                                                                                  (GHC.Num.op_zp__
                                                                                                  (GHC.Num.op_zp__
                                                                                                  (GHC.Num.fromInteger
                                                                                                  1) ls) rls) x l rl) rr
                                                              else j_265__
                                                            | _ => j_264__
                                                          end
                                                     else j_261__
                           end
    end.

Definition deleteFindMin {a} : Set_ a -> a * Set_ a :=
  fix deleteFindMin t
        := match t with
             | Mk_Bin _ x Mk_Tip r => pair x r
             | Mk_Bin _ x l r => match deleteFindMin l with
                                   | pair xm l' => pair xm (balanceR x l' r)
                                 end
             | Mk_Tip => pair (GHC.Err.error (GHC.Base.hs_string__
                                             "Set.deleteFindMin: can not return the minimal element of an empty set"))
                              Mk_Tip
           end.

Definition minView {a} : Set_ a -> option (a * Set_ a) :=
  fun arg_337__ =>
    match arg_337__ with
      | Mk_Tip => None
      | x => Some (deleteFindMin x)
    end.

Definition deleteMin {a} : Set_ a -> Set_ a :=
  fix deleteMin arg_296__
        := match arg_296__ with
             | Mk_Bin _ _ Mk_Tip r => r
             | Mk_Bin _ x l r => balanceR x (deleteMin l) r
             | Mk_Tip => Mk_Tip
           end.

Definition insertMax {a} : a -> Set_ a -> Set_ a :=
  fix insertMax x t
        := match t with
             | Mk_Tip => singleton x
             | Mk_Bin _ y l r => balanceR y l (insertMax x r)
           end.

Definition balanceL {a} : a -> Set_ a -> Set_ a -> Set_ a :=
  fun x l r =>
    match r with
      | Mk_Tip => match l with
                    | Mk_Tip => Mk_Bin (GHC.Num.fromInteger 1) x Mk_Tip Mk_Tip
                    | Mk_Bin _ _ Mk_Tip Mk_Tip => Mk_Bin (GHC.Num.fromInteger 2) x l Mk_Tip
                    | Mk_Bin _ lx Mk_Tip (Mk_Bin _ lrx _ _) => Mk_Bin (GHC.Num.fromInteger 3) lrx
                                                               (Mk_Bin (GHC.Num.fromInteger 1) lx Mk_Tip Mk_Tip) (Mk_Bin
                                                                                                                 (GHC.Num.fromInteger
                                                                                                                 1) x
                                                                                                                 Mk_Tip
                                                                                                                 Mk_Tip)
                    | Mk_Bin _ lx (Mk_Bin _ _ _ _ as ll) Mk_Tip => Mk_Bin (GHC.Num.fromInteger 3) lx
                                                                   ll (Mk_Bin (GHC.Num.fromInteger 1) x Mk_Tip Mk_Tip)
                    | Mk_Bin ls lx (Mk_Bin lls _ _ _ as ll) (Mk_Bin lrs lrx lrl lrr as lr) =>
                      let j_219__ :=
                        Mk_Bin (GHC.Num.op_zp__ (GHC.Num.fromInteger 1) ls) lrx (Mk_Bin (GHC.Num.op_zp__
                                                                                        (GHC.Num.op_zp__
                                                                                        (GHC.Num.fromInteger 1) lls)
                                                                                        (size lrl)) lx ll lrl) (Mk_Bin
                                                                                                               (GHC.Num.op_zp__
                                                                                                               (GHC.Num.fromInteger
                                                                                                               1) (size
                                                                                                               lrr)) x
                                                                                                               lrr
                                                                                                               Mk_Tip) in
                      if GHC.Base.op_zl__ lrs (GHC.Num.op_zt__ ratio lls) : bool
                      then Mk_Bin (GHC.Num.op_zp__ (GHC.Num.fromInteger 1) ls) lx ll (Mk_Bin
                                                                                     (GHC.Num.op_zp__
                                                                                     (GHC.Num.fromInteger 1) lrs) x lr
                                                                                     Mk_Tip)
                      else j_219__
                  end
      | Mk_Bin rs _ _ _ => match l with
                             | Mk_Tip => Mk_Bin (GHC.Num.op_zp__ (GHC.Num.fromInteger 1) rs) x Mk_Tip r
                             | Mk_Bin ls lx ll lr => let j_224__ :=
                                                       Mk_Bin (GHC.Num.op_zp__ (GHC.Num.op_zp__ (GHC.Num.fromInteger 1)
                                                                                                ls) rs) x l r in
                                                     if GHC.Base.op_zg__ ls (GHC.Num.op_zt__ delta rs) : bool
                                                     then let scrut_225__ := pair ll lr in
                                                          let j_227__ :=
                                                            match scrut_225__ with
                                                              | pair _ _ => GHC.Err.error (GHC.Base.hs_string__
                                                                                          "Failure in Data.Map.balanceL")
                                                            end in
                                                          match scrut_225__ with
                                                            | pair (Mk_Bin lls _ _ _) (Mk_Bin lrs lrx lrl lrr) =>
                                                              let j_228__ :=
                                                                Mk_Bin (GHC.Num.op_zp__ (GHC.Num.op_zp__
                                                                                        (GHC.Num.fromInteger 1) ls) rs)
                                                                lrx (Mk_Bin (GHC.Num.op_zp__ (GHC.Num.op_zp__
                                                                                             (GHC.Num.fromInteger 1)
                                                                                             lls) (size lrl)) lx ll lrl)
                                                                (Mk_Bin (GHC.Num.op_zp__ (GHC.Num.op_zp__
                                                                                         (GHC.Num.fromInteger 1) rs)
                                                                                         (size lrr)) x lrr r) in
                                                              if GHC.Base.op_zl__ lrs (GHC.Num.op_zt__ ratio lls) : bool
                                                              then Mk_Bin (GHC.Num.op_zp__ (GHC.Num.op_zp__
                                                                                           (GHC.Num.fromInteger 1) ls)
                                                                                           rs) lx ll (Mk_Bin
                                                                                                     (GHC.Num.op_zp__
                                                                                                     (GHC.Num.op_zp__
                                                                                                     (GHC.Num.fromInteger
                                                                                                     1) rs) lrs) x lr r)
                                                              else j_228__
                                                            | _ => j_227__
                                                          end
                                                     else j_224__
                           end
    end.

Definition deleteFindMax {a} : Set_ a -> a * Set_ a :=
  fix deleteFindMax t
        := match t with
             | Mk_Bin _ x l Mk_Tip => pair x l
             | Mk_Bin _ x l r => match deleteFindMax r with
                                   | pair xm r' => pair xm (balanceL x l r')
                                 end
             | Mk_Tip => pair (GHC.Err.error (GHC.Base.hs_string__
                                             "Set.deleteFindMax: can not return the maximal element of an empty set"))
                              Mk_Tip
           end.

Definition maxView {a} : Set_ a -> option (a * Set_ a) :=
  fun arg_249__ =>
    match arg_249__ with
      | Mk_Tip => None
      | x => Some (deleteFindMax x)
    end.

Definition deleteMax {a} : Set_ a -> Set_ a :=
  fix deleteMax arg_236__
        := match arg_236__ with
             | Mk_Bin _ _ l Mk_Tip => l
             | Mk_Bin _ x l r => balanceL x l (deleteMax r)
             | Mk_Tip => Mk_Tip
           end.

Definition insert {a} `{GHC.Base.Ord a} : a -> Set_ a -> Set_ a :=
  let go {a} `{GHC.Base.Ord a} : a -> Set_ a -> Set_ a :=
    fix go arg_273__ arg_274__
          := let j_282__ :=
               match arg_273__ , arg_274__ with
                 | x , Mk_Tip => singleton x
                 | x , Mk_Bin sz y l r => let scrut_276__ := GHC.Base.compare x y in
                                          match scrut_276__ with
                                            | Lt => balanceL y (go x l) r
                                            | Gt => balanceR y l (go x r)
                                            | Eq => Mk_Bin sz x l r
                                          end
               end in
             match arg_273__ , arg_274__ with
               | arg , _ => if GHC.Prim.seq arg false : bool
                            then GHC.Err.undefined
                            else j_282__
             end in
  go.

Definition insertMin {a} : a -> Set_ a -> Set_ a :=
  fix insertMin x t
        := match t with
             | Mk_Tip => singleton x
             | Mk_Bin _ y l r => balanceL y (insertMin x l) r
           end.

Definition insertR {a} `{GHC.Base.Ord a} : a -> Set_ a -> Set_ a :=
  let go {a} `{GHC.Base.Ord a} : a -> Set_ a -> Set_ a :=
    fix go arg_285__ arg_286__
          := let j_293__ :=
               match arg_285__ , arg_286__ with
                 | x , Mk_Tip => singleton x
                 | x , (Mk_Bin _ y l r as t) => let scrut_288__ := GHC.Base.compare x y in
                                                match scrut_288__ with
                                                  | Lt => balanceL y (go x l) r
                                                  | Gt => balanceR y l (go x r)
                                                  | Eq => t
                                                end
               end in
             match arg_285__ , arg_286__ with
               | arg , _ => if GHC.Prim.seq arg false : bool
                            then GHC.Err.undefined
                            else j_293__
             end in
  go.

Definition glue {a} : Set_ a -> Set_ a -> Set_ a :=
  fun arg_309__ arg_310__ =>
    match arg_309__ , arg_310__ with
      | Mk_Tip , r => r
      | l , Mk_Tip => l
      | l , r => let j_312__ :=
                   match deleteFindMin r with
                     | pair m r' => balanceL m l r'
                   end in
                 if GHC.Base.op_zg__ (size l) (size r) : bool
                 then match deleteFindMax l with
                        | pair m l' => balanceR m l' r
                      end
                 else j_312__
    end.

Definition delete {a} `{GHC.Base.Ord a} : a -> Set_ a -> Set_ a :=
  let go {a} `{GHC.Base.Ord a} : a -> Set_ a -> Set_ a :=
    fix go arg_316__ arg_317__
          := let j_324__ :=
               match arg_316__ , arg_317__ with
                 | _ , Mk_Tip => Mk_Tip
                 | x , Mk_Bin _ y l r => let scrut_318__ := GHC.Base.compare x y in
                                         match scrut_318__ with
                                           | Lt => balanceR y (go x l) r
                                           | Gt => balanceL y l (go x r)
                                           | Eq => glue l r
                                         end
               end in
             match arg_316__ , arg_317__ with
               | arg , _ => if GHC.Prim.seq arg false : bool
                            then GHC.Err.undefined
                            else j_324__
             end in
  go.

Definition deleteAt {a} : GHC.Num.Int -> Set_ a -> Set_ a :=
  fix deleteAt i t
        := GHC.Prim.seq i (match t with
                          | Mk_Tip => GHC.Err.error (GHC.Base.hs_string__
                                                    "Set.deleteAt: index out of range")
                          | Mk_Bin _ x l r => let sizeL := size l in
                                              let scrut_329__ := GHC.Base.compare i sizeL in
                                              match scrut_329__ with
                                                | Lt => balanceR x (deleteAt i l) r
                                                | Gt => balanceL x l (deleteAt (GHC.Num.op_zm__ (GHC.Num.op_zm__ i
                                                                                                                 sizeL)
                                                                                                (GHC.Num.fromInteger 1))
                                                                     r)
                                                | Eq => glue l r
                                              end
                        end).

Local Definition instance_forall___GHC_Base_Eq__a___GHC_Base_Eq___Set__a__op_zeze__ {inst_a}
                                                                                    `{GHC.Base.Eq_ inst_a} : (Set_
                                                                                                             inst_a) -> (Set_
                                                                                                             inst_a) -> bool :=
  fun t1 t2 =>
    andb (GHC.Base.op_zeze__ (size t1) (size t2)) (GHC.Base.op_zeze__ (toAscList t1)
                                                                      (toAscList t2)).

Local Definition instance_forall___GHC_Base_Eq__a___GHC_Base_Eq___Set__a__op_zsze__ {inst_a}
                                                                                    `{GHC.Base.Eq_ inst_a} : (Set_
                                                                                                             inst_a) -> (Set_
                                                                                                             inst_a) -> bool :=
  fun x y =>
    negb (instance_forall___GHC_Base_Eq__a___GHC_Base_Eq___Set__a__op_zeze__ x y).

Program Instance instance_forall___GHC_Base_Eq__a___GHC_Base_Eq___Set__a_ {a}
                                                                          `{GHC.Base.Eq_ a} : GHC.Base.Eq_ (Set_ a) :=
  fun _ k =>
    k
    {|GHC.Base.op_zeze____ := instance_forall___GHC_Base_Eq__a___GHC_Base_Eq___Set__a__op_zeze__ ;
    GHC.Base.op_zsze____ := instance_forall___GHC_Base_Eq__a___GHC_Base_Eq___Set__a__op_zsze__ |}.

Program Instance instance_forall___GHC_Base_Ord_a___GHC_Base_Ord__Set__a_ {a}
                                                                          `{GHC.Base.Ord a} : GHC.Base.Ord (Set_ a) :=
  fun _ k =>
    k
    {|GHC.Base.op_zl____ := instance_forall___GHC_Base_Ord_a___GHC_Base_Ord__Set__a__op_zl__ ;
    GHC.Base.op_zlze____ := instance_forall___GHC_Base_Ord_a___GHC_Base_Ord__Set__a__op_zlze__ ;
    GHC.Base.op_zg____ := instance_forall___GHC_Base_Ord_a___GHC_Base_Ord__Set__a__op_zg__ ;
    GHC.Base.op_zgze____ := instance_forall___GHC_Base_Ord_a___GHC_Base_Ord__Set__a__op_zgze__ ;
    GHC.Base.compare__ := instance_forall___GHC_Base_Ord_a___GHC_Base_Ord__Set__a__compare ;
    GHC.Base.max__ := instance_forall___GHC_Base_Ord_a___GHC_Base_Ord__Set__a__max ;
    GHC.Base.min__ := instance_forall___GHC_Base_Ord_a___GHC_Base_Ord__Set__a__min |}.

Local Definition instance_Data_Foldable_Foldable_Set__length : forall {a},
                                                                 Set_ a -> GHC.Num.Int :=
  fun {a} => size.

Program Instance instance_Data_Foldable_Foldable_Set_ : Data.Foldable.Foldable
                                                        Set_ := fun _ k =>
    k {|Data.Foldable.elem__ := fun {a} `{GHC.Base.Eq_ a} =>
        instance_Data_Foldable_Foldable_Set__elem ;
      Data.Foldable.fold__ := fun {m} `{GHC.Base.Monoid m} =>
        instance_Data_Foldable_Foldable_Set__fold ;
      Data.Foldable.foldMap__ := fun {m} {a} `{GHC.Base.Monoid m} =>
        instance_Data_Foldable_Foldable_Set__foldMap ;
      Data.Foldable.foldl__ := fun {b} {a} =>
        instance_Data_Foldable_Foldable_Set__foldl ;
      Data.Foldable.foldl'__ := fun {b} {a} =>
        instance_Data_Foldable_Foldable_Set__foldl' ;
      Data.Foldable.foldr__ := fun {a} {b} =>
        instance_Data_Foldable_Foldable_Set__foldr ;
      Data.Foldable.foldr'__ := fun {a} {b} =>
        instance_Data_Foldable_Foldable_Set__foldr' ;
      Data.Foldable.length__ := fun {a} =>
        instance_Data_Foldable_Foldable_Set__length ;
      Data.Foldable.null__ := fun {a} => instance_Data_Foldable_Foldable_Set__null ;
      Data.Foldable.product__ := fun {a} `{GHC.Num.Num a} =>
        instance_Data_Foldable_Foldable_Set__product ;
      Data.Foldable.sum__ := fun {a} `{GHC.Num.Num a} =>
        instance_Data_Foldable_Foldable_Set__sum ;
      Data.Foldable.toList__ := fun {a} =>
        instance_Data_Foldable_Foldable_Set__toList |}.

Definition trim {a} `{GHC.Base.Ord a} : MaybeS a -> MaybeS a -> Set_ a -> Set_
                                        a :=
  fun arg_11__ arg_12__ arg_13__ =>
    match arg_11__ , arg_12__ , arg_13__ with
      | Mk_NothingS , Mk_NothingS , t => t
      | Mk_JustS lx , Mk_NothingS , t => let greater :=
                                           fix greater arg_14__ arg_15__
                                                 := let j_16__ := match arg_14__ , arg_15__ with | _ , t' => t' end in
                                                    match arg_14__ , arg_15__ with
                                                      | lo , Mk_Bin _ x _ r => if GHC.Base.op_zlze__ x lo : bool
                                                                               then greater lo r
                                                                               else j_16__
                                                      | _ , _ => j_16__
                                                    end in
                                         greater lx t
      | Mk_NothingS , Mk_JustS hx , t => let lesser :=
                                           fix lesser arg_20__ arg_21__
                                                 := let j_22__ := match arg_20__ , arg_21__ with | _ , t' => t' end in
                                                    match arg_20__ , arg_21__ with
                                                      | hi , Mk_Bin _ x l _ => if GHC.Base.op_zgze__ x hi : bool
                                                                               then lesser hi l
                                                                               else j_22__
                                                      | _ , _ => j_22__
                                                    end in
                                         lesser hx t
      | Mk_JustS lx , Mk_JustS hx , t => let middle :=
                                           fix middle arg_26__ arg_27__ arg_28__
                                                 := let j_29__ :=
                                                      match arg_26__ , arg_27__ , arg_28__ with
                                                        | _ , _ , t' => t'
                                                      end in
                                                    let j_31__ :=
                                                      match arg_26__ , arg_27__ , arg_28__ with
                                                        | lo , hi , Mk_Bin _ x l _ => if GHC.Base.op_zgze__ x hi : bool
                                                                                      then middle lo hi l
                                                                                      else j_29__
                                                        | _ , _ , _ => j_29__
                                                      end in
                                                    match arg_26__ , arg_27__ , arg_28__ with
                                                      | lo , hi , Mk_Bin _ x _ r => if GHC.Base.op_zlze__ x lo : bool
                                                                                    then middle lo hi r
                                                                                    else j_31__
                                                      | _ , _ , _ => j_31__
                                                    end in
                                         middle lx hx t
    end.

Definition withBar : list GHC.Base.String -> list GHC.Base.String :=
  fun bars => cons (GHC.Base.hs_string__ "|  ") bars.

Definition withEmpty : list GHC.Base.String -> list GHC.Base.String :=
  fun bars => cons (GHC.Base.hs_string__ "   ") bars.

(* Unbound variables:
     * == Data.Foldable.Foldable GHC.Base.Eq_ GHC.Base.Monoid GHC.Base.Ord
     GHC.Base.String GHC.Base.compare GHC.Base.const GHC.Base.flip GHC.Base.mappend
     GHC.Base.mempty GHC.Base.op_zd__ GHC.Base.op_zdzn__ GHC.Base.op_zeze__
     GHC.Base.op_zg__ GHC.Base.op_zgze__ GHC.Base.op_zl__ GHC.Base.op_zlze__
     GHC.Err.error GHC.Err.undefined GHC.Num.Int GHC.Num.Num GHC.Num.op_zm__
     GHC.Num.op_zp__ GHC.Num.op_zt__ GHC.Prim.seq Gt Lt None Some andb bool
     comparison cons false list negb nil op_zeze__ op_zsze__ option orb pair true
*)
