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
Import GHC.Base.Notations.
Import GHC.Num.Notations.

(* Converted type declarations: *)

Definition Size :=
  GHC.Num.Int%type.

Inductive Set_ a : Type := Bin : Size -> a -> (Set_ a) -> (Set_ a) -> Set_ a
                        |  Tip : Set_ a.

Inductive MaybeS a : Type := NothingS : MaybeS a
                          |  JustS : a -> MaybeS a.

Arguments Bin {_} _ _ _ _.

Arguments Tip {_}.

Arguments NothingS {_}.

Arguments JustS {_} _.
(* Converted value declarations: *)

(* The Haskell code containes partial or untranslateable code, which needs the
   following *)

Axiom patternFailure : forall {a}, a.

(* Skipping instance Monoid__Set_ *)

(* Translating `instance forall {a}, forall `{GHC.Base.Ord a},
   Data.Semigroup.Semigroup (Data.Set.Base.Set_ a)' failed: OOPS! Cannot find
   information for class Qualified "Data.Semigroup" "Semigroup" unsupported *)

Local Definition Foldable__Set__elem : forall {a},
                                         forall `{GHC.Base.Eq_ a}, a -> Set_ a -> bool :=
  fun {a} `{GHC.Base.Eq_ a} =>
    let go :=
      fix go arg_370__ arg_371__
            := let j_373__ :=
                 match arg_370__ , arg_371__ with
                   | _ , Tip => false
                   | x , Bin _ y l r => orb (x GHC.Base.== y) (orb (go x l) (go x r))
                 end in
               match arg_370__ , arg_371__ with
                 | arg , _ => if GHC.Prim.seq arg false : bool
                              then GHC.Err.undefined
                              else j_373__
               end in
    go.

Local Definition Foldable__Set__fold : forall {m},
                                         forall `{GHC.Base.Monoid m}, Set_ m -> m :=
  fun {m} `{GHC.Base.Monoid m} =>
    let go :=
      fix go arg_357__
            := let j_360__ :=
                 match arg_357__ with
                   | Bin _ k l r => GHC.Base.mappend (go l) (GHC.Base.mappend k (go r))
                   | _ => patternFailure
                 end in
               match arg_357__ with
                 | Tip => GHC.Base.mempty
                 | Bin num_358__ k _ _ => if num_358__ GHC.Base.== GHC.Num.fromInteger 1 : bool
                                          then k
                                          else j_360__
               end in
    go.

Local Definition Foldable__Set__foldMap : forall {m} {a},
                                            forall `{GHC.Base.Monoid m}, (a -> m) -> Set_ a -> m :=
  fun {m} {a} `{GHC.Base.Monoid m} =>
    fun f t =>
      let go :=
        fix go arg_363__
              := let j_366__ :=
                   match arg_363__ with
                     | Bin _ k l r => GHC.Base.mappend (go l) (GHC.Base.mappend (f k) (go r))
                     | _ => patternFailure
                   end in
                 match arg_363__ with
                   | Tip => GHC.Base.mempty
                   | Bin num_364__ k _ _ => if num_364__ GHC.Base.== GHC.Num.fromInteger 1 : bool
                                            then f k
                                            else j_366__
                 end in
      go t.

(* Translating `instance forall {a}, forall `{Data.Data.Data a} `{GHC.Base.Ord
   a}, Data.Data.Data (Data.Set.Base.Set_ a)' failed: OOPS! Cannot find information
   for class Qualified "Data.Data" "Data" unsupported *)

(* Translating `instance forall {a}, forall `{(GHC.Base.Ord a)}, GHC.Exts.IsList
   (Data.Set.Base.Set_ a)' failed: OOPS! Cannot find information for class
   Qualified "GHC.Exts" "IsList" unsupported *)

(* Translating `instance forall {a}, forall `{GHC.Show.Show a}, GHC.Show.Show
   (Data.Set.Base.Set_ a)' failed: OOPS! Cannot find information for class
   Qualified "GHC.Show" "Show" unsupported *)

(* Translating `instance forall {a}, forall `{GHC.Read.Read a} `{GHC.Base.Ord
   a}, GHC.Read.Read (Data.Set.Base.Set_ a)' failed: OOPS! Cannot find information
   for class Qualified "GHC.Read" "Read" unsupported *)

(* Translating `instance forall {a}, forall `{Control.DeepSeq.NFData a},
   Control.DeepSeq.NFData (Data.Set.Base.Set_ a)' failed: OOPS! Cannot find
   information for class Qualified "Control.DeepSeq" "NFData" unsupported *)

Definition delta : GHC.Num.Int :=
  GHC.Num.fromInteger 3.

Definition empty {a} : Set_ a :=
  Tip.

Definition findMax {a} : Set_ a -> a :=
  fix findMax arg_66__
        := match arg_66__ with
             | Bin _ x _ Tip => x
             | Bin _ _ _ r => findMax r
             | Tip => GHC.Err.error (GHC.Base.hs_string__
                                    "Set.findMax: empty set has no maximal element")
           end.

Definition findMin {a} : Set_ a -> a :=
  fix findMin arg_70__
        := match arg_70__ with
             | Bin _ x Tip _ => x
             | Bin _ _ l _ => findMin l
             | Tip => GHC.Err.error (GHC.Base.hs_string__
                                    "Set.findMin: empty set has no minimal element")
           end.

Definition foldl {a} {b} : (a -> b -> a) -> a -> Set_ b -> a :=
  fun f z =>
    let go :=
      fix go arg_43__ arg_44__
            := match arg_43__ , arg_44__ with
                 | z' , Tip => z'
                 | z' , Bin _ x l r => go (f (go z' l) x) r
               end in
    go z.

Definition foldlFB {a} {b} : (a -> b -> a) -> a -> Set_ b -> a :=
  foldl.

Definition toDescList {a} : Set_ a -> list a :=
  foldl (GHC.Base.flip cons) nil.

Local Definition Foldable__Set__foldl : forall {b} {a},
                                          (b -> a -> b) -> b -> Set_ a -> b :=
  fun {b} {a} => foldl.

Definition foldl' {a} {b} : (a -> b -> a) -> a -> Set_ b -> a :=
  fun f z =>
    let go :=
      fix go arg_36__ arg_37__
            := let j_39__ :=
                 match arg_36__ , arg_37__ with
                   | z' , Tip => z'
                   | z' , Bin _ x l r => go (f (go z' l) x) r
                 end in
               match arg_36__ , arg_37__ with
                 | arg , _ => if GHC.Prim.seq arg false : bool
                              then GHC.Err.undefined
                              else j_39__
               end in
    go z.

Local Definition Foldable__Set__sum : forall {a},
                                        forall `{GHC.Num.Num a}, Set_ a -> a :=
  fun {a} `{GHC.Num.Num a} => foldl' _GHC.Num.+_ (GHC.Num.fromInteger 0).

Local Definition Foldable__Set__product : forall {a},
                                            forall `{GHC.Num.Num a}, Set_ a -> a :=
  fun {a} `{GHC.Num.Num a} => foldl' _GHC.Num.*_ (GHC.Num.fromInteger 1).

Local Definition Foldable__Set__foldl' : forall {b} {a},
                                           (b -> a -> b) -> b -> Set_ a -> b :=
  fun {b} {a} => foldl'.

Definition foldr {a} {b} : (a -> b -> b) -> b -> Set_ a -> b :=
  fun f z =>
    let go :=
      fix go arg_56__ arg_57__
            := match arg_56__ , arg_57__ with
                 | z' , Tip => z'
                 | z' , Bin _ x l r => go (f x (go z' r)) l
               end in
    go z.

Definition foldrFB {a} {b} : (a -> b -> b) -> b -> Set_ a -> b :=
  foldr.

Definition toAscList {a} : Set_ a -> list a :=
  foldr cons nil.

Definition toList {a} : Set_ a -> list a :=
  toAscList.

Local Definition Foldable__Set__toList : forall {a}, Set_ a -> list a :=
  fun {a} => toList.

Definition elems {a} : Set_ a -> list a :=
  toAscList.

Local Definition Ord__Set__compare {inst_a} `{GHC.Base.Ord inst_a} : (Set_
                                                                     inst_a) -> (Set_ inst_a) -> comparison :=
  fun s1 s2 => GHC.Base.compare (toAscList s1) (toAscList s2).

Local Definition Ord__Set__op_zg__ {inst_a} `{GHC.Base.Ord inst_a} : (Set_
                                                                     inst_a) -> (Set_ inst_a) -> bool :=
  fun x y => _GHC.Base.==_ (Ord__Set__compare x y) Gt.

Local Definition Ord__Set__op_zgze__ {inst_a} `{GHC.Base.Ord inst_a} : (Set_
                                                                       inst_a) -> (Set_ inst_a) -> bool :=
  fun x y => _GHC.Base./=_ (Ord__Set__compare x y) Lt.

Local Definition Ord__Set__op_zl__ {inst_a} `{GHC.Base.Ord inst_a} : (Set_
                                                                     inst_a) -> (Set_ inst_a) -> bool :=
  fun x y => _GHC.Base.==_ (Ord__Set__compare x y) Lt.

Local Definition Ord__Set__op_zlze__ {inst_a} `{GHC.Base.Ord inst_a} : (Set_
                                                                       inst_a) -> (Set_ inst_a) -> bool :=
  fun x y => _GHC.Base./=_ (Ord__Set__compare x y) Gt.

Local Definition Ord__Set__max {inst_a} `{GHC.Base.Ord inst_a} : (Set_
                                                                 inst_a) -> (Set_ inst_a) -> (Set_ inst_a) :=
  fun x y => if Ord__Set__op_zlze__ x y : bool then y else x.

Local Definition Ord__Set__min {inst_a} `{GHC.Base.Ord inst_a} : (Set_
                                                                 inst_a) -> (Set_ inst_a) -> (Set_ inst_a) :=
  fun x y => if Ord__Set__op_zlze__ x y : bool then x else y.

Definition fold {a} {b} : (a -> b -> b) -> b -> Set_ a -> b :=
  foldr.

Local Definition Foldable__Set__foldr : forall {a} {b},
                                          (a -> b -> b) -> b -> Set_ a -> b :=
  fun {a} {b} => foldr.

Definition foldr' {a} {b} : (a -> b -> b) -> b -> Set_ a -> b :=
  fun f z =>
    let go :=
      fix go arg_49__ arg_50__
            := let j_52__ :=
                 match arg_49__ , arg_50__ with
                   | z' , Tip => z'
                   | z' , Bin _ x l r => go (f x (go z' r)) l
                 end in
               match arg_49__ , arg_50__ with
                 | arg , _ => if GHC.Prim.seq arg false : bool
                              then GHC.Err.undefined
                              else j_52__
               end in
    go z.

Local Definition Foldable__Set__foldr' : forall {a} {b},
                                           (a -> b -> b) -> b -> Set_ a -> b :=
  fun {a} {b} => foldr'.

Definition lookupGE {a} `{GHC.Base.Ord a} : a -> Set_ a -> option a :=
  let goJust :=
    fix goJust arg_78__ arg_79__ arg_80__
          := let j_88__ :=
               match arg_78__ , arg_79__ , arg_80__ with
                 | _ , best , Tip => Some best
                 | x , best , Bin _ y l r => let scrut_82__ := GHC.Base.compare x y in
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
                 | _ , Tip => None
                 | x , Bin _ y l r => let scrut_93__ := GHC.Base.compare x y in
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
                 | _ , best , Tip => Some best
                 | x , best , Bin _ y l r => let j_130__ := goJust x best r in
                                             if x GHC.Base.< y : bool
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
                 | _ , Tip => None
                 | x , Bin _ y l r => let j_137__ := goNothing x r in
                                      if x GHC.Base.< y : bool
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
                 | _ , best , Tip => Some best
                 | x , best , Bin _ y l r => let scrut_106__ := GHC.Base.compare x y in
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
                 | _ , Tip => None
                 | x , Bin _ y l r => let scrut_117__ := GHC.Base.compare x y in
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
                 | _ , best , Tip => Some best
                 | x , best , Bin _ y l r => let j_146__ := goJust x y r in
                                             if x GHC.Base.<= y : bool
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
                 | _ , Tip => None
                 | x , Bin _ y l r => let j_153__ := goJust x y r in
                                      if x GHC.Base.<= y : bool
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
             | _ , Tip => Tip
             | f , Bin sz x l r => Bin sz (f x) (mapMonotonic f l) (mapMonotonic f r)
           end.

Definition member {a} `{GHC.Base.Ord a} : a -> Set_ a -> bool :=
  let go :=
    fix go arg_158__ arg_159__
          := let j_165__ :=
               match arg_158__ , arg_159__ with
                 | _ , Tip => false
                 | x , Bin _ y l r => let scrut_160__ := GHC.Base.compare x y in
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
  fun a t => negb GHC.Base.$ member a t.

Definition node : GHC.Base.String :=
  GHC.Base.hs_string__ "+--".

Definition null {a} : Set_ a -> bool :=
  fun arg_353__ => match arg_353__ with | Tip => true | Bin _ _ _ _ => false end.

Local Definition Foldable__Set__null : forall {a}, Set_ a -> bool :=
  fun {a} => null.

Definition ordered {a} `{GHC.Base.Ord a} : Set_ a -> bool :=
  fun t =>
    let bounded :=
      fix bounded lo hi t'
            := match t' with
                 | Tip => true
                 | Bin _ x l r => andb (lo x) (andb (hi x) (andb (bounded lo (fun arg_0__ =>
                                                                               arg_0__ GHC.Base.< x) l) (bounded
                                                                 (fun arg_1__ => arg_1__ GHC.Base.> x) hi r)))
               end in
    bounded (GHC.Base.const true) (GHC.Base.const true) t.

Definition ratio : GHC.Num.Int :=
  GHC.Num.fromInteger 2.

Definition singleton {a} : a -> Set_ a :=
  fun x => Bin (GHC.Num.fromInteger 1) x Tip Tip.

Definition splitRoot {a} : Set_ a -> list (Set_ a) :=
  fun orig =>
    match orig with
      | Tip => nil
      | Bin _ v l r => cons l (cons (singleton v) (cons r nil))
    end.

Definition size {a} : Set_ a -> GHC.Num.Int :=
  fun arg_169__ =>
    match arg_169__ with
      | Tip => GHC.Num.fromInteger 0
      | Bin sz _ _ _ => sz
    end.

Definition validsize {a} : Set_ a -> bool :=
  fun t =>
    let realsize :=
      fix realsize t'
            := match t' with
                 | Tip => Some (GHC.Num.fromInteger 0)
                 | Bin sz _ l r => let scrut_345__ := pair (realsize l) (realsize r) in
                                   match scrut_345__ with
                                     | pair (Some n) (Some m) => if ((n GHC.Num.+ m) GHC.Num.+ GHC.Num.fromInteger 1)
                                                                    GHC.Base.== sz : bool
                                                                 then Some sz
                                                                 else None
                                     | _ => None
                                   end
               end in
    (realsize t GHC.Base.== Some (size t)).

Definition lookupIndex {a} `{GHC.Base.Ord a} : a -> Set_ a -> option
                                               GHC.Num.Int :=
  let go {a} `{GHC.Base.Ord a} : GHC.Num.Int -> a -> Set_ a -> option
                                 GHC.Num.Int :=
    fix go arg_188__ arg_189__ arg_190__
          := let j_197__ :=
               match arg_188__ , arg_189__ , arg_190__ with
                 | _ , _ , Tip => None
                 | idx , x , Bin _ kx l r => let scrut_191__ := GHC.Base.compare x kx in
                                             match scrut_191__ with
                                               | Lt => go idx x l
                                               | Gt => go ((idx GHC.Num.+ size l) GHC.Num.+ GHC.Num.fromInteger 1) x r
                                               | Eq => Some GHC.Base.$! (idx GHC.Num.+ size l)
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
                 | _ , _ , Tip => GHC.Err.error (GHC.Base.hs_string__
                                                "Set.findIndex: element is not in the set")
                 | idx , x , Bin _ kx l r => let scrut_176__ := GHC.Base.compare x kx in
                                             match scrut_176__ with
                                               | Lt => go idx x l
                                               | Gt => go ((idx GHC.Num.+ size l) GHC.Num.+ GHC.Num.fromInteger 1) x r
                                               | Eq => idx GHC.Num.+ size l
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
               | _ , Tip => GHC.Err.error (GHC.Base.hs_string__
                                          "Set.elemAt: index out of range")
               | i , Bin _ x l r => let sizeL := size l in
                                    let scrut_207__ := GHC.Base.compare i sizeL in
                                    match scrut_207__ with
                                      | Lt => elemAt i l
                                      | Gt => elemAt ((i GHC.Num.- sizeL) GHC.Num.- GHC.Num.fromInteger 1) r
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
    Bin ((size l GHC.Num.+ size r) GHC.Num.+ GHC.Num.fromInteger 1) x l r.

Definition balanced {a} : Set_ a -> bool :=
  fix balanced t
        := match t with
             | Tip => true
             | Bin _ _ l r => andb (orb ((size l GHC.Num.+ size r) GHC.Base.<=
                                        GHC.Num.fromInteger 1) (andb (size l GHC.Base.<= (delta GHC.Num.* size r)) (size
                                                                     r GHC.Base.<= (delta GHC.Num.* size l)))) (andb
                                   (balanced l) (balanced r))
           end.

Definition valid {a} `{GHC.Base.Ord a} : Set_ a -> bool :=
  fun t => andb (balanced t) (andb (ordered t) (validsize t)).

Definition balanceR {a} : a -> Set_ a -> Set_ a -> Set_ a :=
  fun x l r =>
    match l with
      | Tip => match r with
                 | Tip => Bin (GHC.Num.fromInteger 1) x Tip Tip
                 | Bin _ _ Tip Tip => Bin (GHC.Num.fromInteger 2) x Tip r
                 | Bin _ rx Tip (Bin _ _ _ _ as rr) => Bin (GHC.Num.fromInteger 3) rx (Bin
                                                                                      (GHC.Num.fromInteger 1) x Tip Tip)
                                                       rr
                 | Bin _ rx (Bin _ rlx _ _) Tip => Bin (GHC.Num.fromInteger 3) rlx (Bin
                                                                                   (GHC.Num.fromInteger 1) x Tip Tip)
                                                   (Bin (GHC.Num.fromInteger 1) rx Tip Tip)
                 | Bin rs rx (Bin rls rlx rll rlr as rl) (Bin rrs _ _ _ as rr) => let j_256__ :=
                                                                                    Bin (GHC.Num.fromInteger 1 GHC.Num.+
                                                                                        rs) rlx (Bin
                                                                                                (GHC.Num.fromInteger 1
                                                                                                GHC.Num.+ size rll) x
                                                                                                Tip rll) (Bin
                                                                                                         ((GHC.Num.fromInteger
                                                                                                         1 GHC.Num.+
                                                                                                         rrs) GHC.Num.+
                                                                                                         size rlr) rx
                                                                                                         rlr rr) in
                                                                                  if rls GHC.Base.< (ratio GHC.Num.*
                                                                                     rrs) : bool
                                                                                  then Bin (GHC.Num.fromInteger 1
                                                                                           GHC.Num.+ rs) rx (Bin
                                                                                                            (GHC.Num.fromInteger
                                                                                                            1 GHC.Num.+
                                                                                                            rls) x Tip
                                                                                                            rl) rr
                                                                                  else j_256__
               end
      | Bin ls _ _ _ => match r with
                          | Tip => Bin (GHC.Num.fromInteger 1 GHC.Num.+ ls) x l Tip
                          | Bin rs rx rl rr => let j_261__ :=
                                                 Bin ((GHC.Num.fromInteger 1 GHC.Num.+ ls) GHC.Num.+ rs) x l r in
                                               if rs GHC.Base.> (delta GHC.Num.* ls) : bool
                                               then let scrut_262__ := pair rl rr in
                                                    let j_264__ :=
                                                      match scrut_262__ with
                                                        | pair _ _ => GHC.Err.error (GHC.Base.hs_string__
                                                                                    "Failure in Data.Map.balanceR")
                                                      end in
                                                    match scrut_262__ with
                                                      | pair (Bin rls rlx rll rlr) (Bin rrs _ _ _) => let j_265__ :=
                                                                                                        Bin
                                                                                                        ((GHC.Num.fromInteger
                                                                                                        1 GHC.Num.+ ls)
                                                                                                        GHC.Num.+ rs)
                                                                                                        rlx (Bin
                                                                                                            ((GHC.Num.fromInteger
                                                                                                            1 GHC.Num.+
                                                                                                            ls)
                                                                                                            GHC.Num.+
                                                                                                            size rll) x
                                                                                                            l rll) (Bin
                                                                                                                   ((GHC.Num.fromInteger
                                                                                                                   1
                                                                                                                   GHC.Num.+
                                                                                                                   rrs)
                                                                                                                   GHC.Num.+
                                                                                                                   size
                                                                                                                   rlr)
                                                                                                                   rx
                                                                                                                   rlr
                                                                                                                   rr) in
                                                                                                      if rls GHC.Base.<
                                                                                                         (ratio
                                                                                                         GHC.Num.*
                                                                                                         rrs) : bool
                                                                                                      then Bin
                                                                                                           ((GHC.Num.fromInteger
                                                                                                           1 GHC.Num.+
                                                                                                           ls) GHC.Num.+
                                                                                                           rs) rx (Bin
                                                                                                                  ((GHC.Num.fromInteger
                                                                                                                  1
                                                                                                                  GHC.Num.+
                                                                                                                  ls)
                                                                                                                  GHC.Num.+
                                                                                                                  rls) x
                                                                                                                  l rl)
                                                                                                           rr
                                                                                                      else j_265__
                                                      | _ => j_264__
                                                    end
                                               else j_261__
                        end
    end.

Definition deleteFindMin {a} : Set_ a -> (a * Set_ a)%type :=
  fix deleteFindMin t
        := match t with
             | Bin _ x Tip r => pair x r
             | Bin _ x l r => match deleteFindMin l with
                                | pair xm l' => pair xm (balanceR x l' r)
                              end
             | Tip => pair (GHC.Err.error (GHC.Base.hs_string__
                                          "Set.deleteFindMin: can not return the minimal element of an empty set")) Tip
           end.

Definition minView {a} : Set_ a -> option (a * Set_ a)%type :=
  fun arg_337__ =>
    match arg_337__ with
      | Tip => None
      | x => Some (deleteFindMin x)
    end.

Definition deleteMin {a} : Set_ a -> Set_ a :=
  fix deleteMin arg_296__
        := match arg_296__ with
             | Bin _ _ Tip r => r
             | Bin _ x l r => balanceR x (deleteMin l) r
             | Tip => Tip
           end.

Definition insertMax {a} : a -> Set_ a -> Set_ a :=
  fix insertMax x t
        := match t with
             | Tip => singleton x
             | Bin _ y l r => balanceR y l (insertMax x r)
           end.

Definition balanceL {a} : a -> Set_ a -> Set_ a -> Set_ a :=
  fun x l r =>
    match r with
      | Tip => match l with
                 | Tip => Bin (GHC.Num.fromInteger 1) x Tip Tip
                 | Bin _ _ Tip Tip => Bin (GHC.Num.fromInteger 2) x l Tip
                 | Bin _ lx Tip (Bin _ lrx _ _) => Bin (GHC.Num.fromInteger 3) lrx (Bin
                                                                                   (GHC.Num.fromInteger 1) lx Tip Tip)
                                                   (Bin (GHC.Num.fromInteger 1) x Tip Tip)
                 | Bin _ lx (Bin _ _ _ _ as ll) Tip => Bin (GHC.Num.fromInteger 3) lx ll (Bin
                                                                                         (GHC.Num.fromInteger 1) x Tip
                                                                                         Tip)
                 | Bin ls lx (Bin lls _ _ _ as ll) (Bin lrs lrx lrl lrr as lr) => let j_219__ :=
                                                                                    Bin (GHC.Num.fromInteger 1 GHC.Num.+
                                                                                        ls) lrx (Bin
                                                                                                ((GHC.Num.fromInteger 1
                                                                                                GHC.Num.+ lls) GHC.Num.+
                                                                                                size lrl) lx ll lrl)
                                                                                    (Bin (GHC.Num.fromInteger 1
                                                                                         GHC.Num.+ size lrr) x lrr
                                                                                    Tip) in
                                                                                  if lrs GHC.Base.< (ratio GHC.Num.*
                                                                                     lls) : bool
                                                                                  then Bin (GHC.Num.fromInteger 1
                                                                                           GHC.Num.+ ls) lx ll (Bin
                                                                                                               (GHC.Num.fromInteger
                                                                                                               1
                                                                                                               GHC.Num.+
                                                                                                               lrs) x lr
                                                                                                               Tip)
                                                                                  else j_219__
               end
      | Bin rs _ _ _ => match l with
                          | Tip => Bin (GHC.Num.fromInteger 1 GHC.Num.+ rs) x Tip r
                          | Bin ls lx ll lr => let j_224__ :=
                                                 Bin ((GHC.Num.fromInteger 1 GHC.Num.+ ls) GHC.Num.+ rs) x l r in
                                               if ls GHC.Base.> (delta GHC.Num.* rs) : bool
                                               then let scrut_225__ := pair ll lr in
                                                    let j_227__ :=
                                                      match scrut_225__ with
                                                        | pair _ _ => GHC.Err.error (GHC.Base.hs_string__
                                                                                    "Failure in Data.Map.balanceL")
                                                      end in
                                                    match scrut_225__ with
                                                      | pair (Bin lls _ _ _) (Bin lrs lrx lrl lrr) => let j_228__ :=
                                                                                                        Bin
                                                                                                        ((GHC.Num.fromInteger
                                                                                                        1 GHC.Num.+ ls)
                                                                                                        GHC.Num.+ rs)
                                                                                                        lrx (Bin
                                                                                                            ((GHC.Num.fromInteger
                                                                                                            1 GHC.Num.+
                                                                                                            lls)
                                                                                                            GHC.Num.+
                                                                                                            size lrl) lx
                                                                                                            ll lrl) (Bin
                                                                                                                    ((GHC.Num.fromInteger
                                                                                                                    1
                                                                                                                    GHC.Num.+
                                                                                                                    rs)
                                                                                                                    GHC.Num.+
                                                                                                                    size
                                                                                                                    lrr)
                                                                                                                    x
                                                                                                                    lrr
                                                                                                                    r) in
                                                                                                      if lrs GHC.Base.<
                                                                                                         (ratio
                                                                                                         GHC.Num.*
                                                                                                         lls) : bool
                                                                                                      then Bin
                                                                                                           ((GHC.Num.fromInteger
                                                                                                           1 GHC.Num.+
                                                                                                           ls) GHC.Num.+
                                                                                                           rs) lx ll
                                                                                                           (Bin
                                                                                                           ((GHC.Num.fromInteger
                                                                                                           1 GHC.Num.+
                                                                                                           rs) GHC.Num.+
                                                                                                           lrs) x lr r)
                                                                                                      else j_228__
                                                      | _ => j_227__
                                                    end
                                               else j_224__
                        end
    end.

Definition deleteFindMax {a} : Set_ a -> (a * Set_ a)%type :=
  fix deleteFindMax t
        := match t with
             | Bin _ x l Tip => pair x l
             | Bin _ x l r => match deleteFindMax r with
                                | pair xm r' => pair xm (balanceL x l r')
                              end
             | Tip => pair (GHC.Err.error (GHC.Base.hs_string__
                                          "Set.deleteFindMax: can not return the maximal element of an empty set")) Tip
           end.

Definition maxView {a} : Set_ a -> option (a * Set_ a)%type :=
  fun arg_249__ =>
    match arg_249__ with
      | Tip => None
      | x => Some (deleteFindMax x)
    end.

Definition deleteMax {a} : Set_ a -> Set_ a :=
  fix deleteMax arg_236__
        := match arg_236__ with
             | Bin _ _ l Tip => l
             | Bin _ x l r => balanceL x l (deleteMax r)
             | Tip => Tip
           end.

Definition insert {a} `{GHC.Base.Ord a} : a -> Set_ a -> Set_ a :=
  let go {a} `{GHC.Base.Ord a} : a -> Set_ a -> Set_ a :=
    fix go arg_273__ arg_274__
          := let j_282__ :=
               match arg_273__ , arg_274__ with
                 | x , Tip => singleton x
                 | x , Bin sz y l r => let scrut_276__ := GHC.Base.compare x y in
                                       match scrut_276__ with
                                         | Lt => balanceL y (go x l) r
                                         | Gt => balanceR y l (go x r)
                                         | Eq => Bin sz x l r
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
             | Tip => singleton x
             | Bin _ y l r => balanceL y (insertMin x l) r
           end.

Definition insertR {a} `{GHC.Base.Ord a} : a -> Set_ a -> Set_ a :=
  let go {a} `{GHC.Base.Ord a} : a -> Set_ a -> Set_ a :=
    fix go arg_285__ arg_286__
          := let j_293__ :=
               match arg_285__ , arg_286__ with
                 | x , Tip => singleton x
                 | x , (Bin _ y l r as t) => let scrut_288__ := GHC.Base.compare x y in
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
      | Tip , r => r
      | l , Tip => l
      | l , r => let j_312__ :=
                   match deleteFindMin r with
                     | pair m r' => balanceL m l r'
                   end in
                 if size l GHC.Base.> size r : bool
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
                 | _ , Tip => Tip
                 | x , Bin _ y l r => let scrut_318__ := GHC.Base.compare x y in
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
                          | Tip => GHC.Err.error (GHC.Base.hs_string__ "Set.deleteAt: index out of range")
                          | Bin _ x l r => let sizeL := size l in
                                           let scrut_329__ := GHC.Base.compare i sizeL in
                                           match scrut_329__ with
                                             | Lt => balanceR x (deleteAt i l) r
                                             | Gt => balanceL x l (deleteAt ((i GHC.Num.- sizeL) GHC.Num.-
                                                                            GHC.Num.fromInteger 1) r)
                                             | Eq => glue l r
                                           end
                        end).

Local Definition Eq___Set__op_zeze__ {inst_a} `{GHC.Base.Eq_ inst_a} : (Set_
                                                                       inst_a) -> (Set_ inst_a) -> bool :=
  fun t1 t2 =>
    andb (size t1 GHC.Base.== size t2) (toAscList t1 GHC.Base.== toAscList t2).

Local Definition Eq___Set__op_zsze__ {inst_a} `{GHC.Base.Eq_ inst_a} : (Set_
                                                                       inst_a) -> (Set_ inst_a) -> bool :=
  fun x y => negb (Eq___Set__op_zeze__ x y).

Program Instance Eq___Set_ {a} `{GHC.Base.Eq_ a} : GHC.Base.Eq_ (Set_ a) :=
  fun _ k =>
    k {|GHC.Base.op_zeze____ := Eq___Set__op_zeze__ ;
      GHC.Base.op_zsze____ := Eq___Set__op_zsze__ |}.

Program Instance Ord__Set_ {a} `{GHC.Base.Ord a} : GHC.Base.Ord (Set_ a) :=
  fun _ k =>
    k {|GHC.Base.op_zl____ := Ord__Set__op_zl__ ;
      GHC.Base.op_zlze____ := Ord__Set__op_zlze__ ;
      GHC.Base.op_zg____ := Ord__Set__op_zg__ ;
      GHC.Base.op_zgze____ := Ord__Set__op_zgze__ ;
      GHC.Base.compare__ := Ord__Set__compare ;
      GHC.Base.max__ := Ord__Set__max ;
      GHC.Base.min__ := Ord__Set__min |}.

Local Definition Foldable__Set__length : forall {a}, Set_ a -> GHC.Num.Int :=
  fun {a} => size.

Program Instance Foldable__Set_ : Data.Foldable.Foldable Set_ := fun _ k =>
    k {|Data.Foldable.elem__ := fun {a} `{GHC.Base.Eq_ a} => Foldable__Set__elem ;
      Data.Foldable.fold__ := fun {m} `{GHC.Base.Monoid m} => Foldable__Set__fold ;
      Data.Foldable.foldMap__ := fun {m} {a} `{GHC.Base.Monoid m} =>
        Foldable__Set__foldMap ;
      Data.Foldable.foldl__ := fun {b} {a} => Foldable__Set__foldl ;
      Data.Foldable.foldl'__ := fun {b} {a} => Foldable__Set__foldl' ;
      Data.Foldable.foldr__ := fun {a} {b} => Foldable__Set__foldr ;
      Data.Foldable.foldr'__ := fun {a} {b} => Foldable__Set__foldr' ;
      Data.Foldable.length__ := fun {a} => Foldable__Set__length ;
      Data.Foldable.null__ := fun {a} => Foldable__Set__null ;
      Data.Foldable.product__ := fun {a} `{GHC.Num.Num a} => Foldable__Set__product ;
      Data.Foldable.sum__ := fun {a} `{GHC.Num.Num a} => Foldable__Set__sum ;
      Data.Foldable.toList__ := fun {a} => Foldable__Set__toList |}.

Definition trim {a} `{GHC.Base.Ord a} : MaybeS a -> MaybeS a -> Set_ a -> Set_
                                        a :=
  fun arg_11__ arg_12__ arg_13__ =>
    match arg_11__ , arg_12__ , arg_13__ with
      | NothingS , NothingS , t => t
      | JustS lx , NothingS , t => let greater :=
                                     fix greater arg_14__ arg_15__
                                           := let j_16__ := match arg_14__ , arg_15__ with | _ , t' => t' end in
                                              match arg_14__ , arg_15__ with
                                                | lo , Bin _ x _ r => if x GHC.Base.<= lo : bool
                                                                      then greater lo r
                                                                      else j_16__
                                                | _ , _ => j_16__
                                              end in
                                   greater lx t
      | NothingS , JustS hx , t => let lesser :=
                                     fix lesser arg_20__ arg_21__
                                           := let j_22__ := match arg_20__ , arg_21__ with | _ , t' => t' end in
                                              match arg_20__ , arg_21__ with
                                                | hi , Bin _ x l _ => if x GHC.Base.>= hi : bool
                                                                      then lesser hi l
                                                                      else j_22__
                                                | _ , _ => j_22__
                                              end in
                                   lesser hx t
      | JustS lx , JustS hx , t => let middle :=
                                     fix middle arg_26__ arg_27__ arg_28__
                                           := let j_29__ :=
                                                match arg_26__ , arg_27__ , arg_28__ with
                                                  | _ , _ , t' => t'
                                                end in
                                              let j_31__ :=
                                                match arg_26__ , arg_27__ , arg_28__ with
                                                  | lo , hi , Bin _ x l _ => if x GHC.Base.>= hi : bool
                                                                             then middle lo hi l
                                                                             else j_29__
                                                  | _ , _ , _ => j_29__
                                                end in
                                              match arg_26__ , arg_27__ , arg_28__ with
                                                | lo , hi , Bin _ x _ r => if x GHC.Base.<= lo : bool
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
     Gt Lt None Some andb bool comparison cons false list negb nil op_zt__ option orb
     pair true Data.Foldable.Foldable GHC.Base.Eq_ GHC.Base.Monoid GHC.Base.Ord
     GHC.Base.String GHC.Base.compare GHC.Base.const GHC.Base.flip GHC.Base.mappend
     GHC.Base.mempty GHC.Base.op_zd__ GHC.Base.op_zdzn__ GHC.Base.op_zeze__
     GHC.Base.op_zg__ GHC.Base.op_zgze__ GHC.Base.op_zl__ GHC.Base.op_zlze__
     GHC.Base.op_zsze__ GHC.Err.error GHC.Err.undefined GHC.Num.Int GHC.Num.Num
     GHC.Num.op_zm__ GHC.Num.op_zp__ GHC.Num.op_zt__ GHC.Prim.seq
*)
