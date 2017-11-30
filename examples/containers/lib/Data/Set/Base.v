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

Require Data.Bits.
Require Data.Foldable.
Require GHC.Base.
Require GHC.List.
Require GHC.Num.
Require GHC.Prim.
Import GHC.Base.Notations.
Import GHC.Num.Notations.

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

Local Definition Monoid__Set__mappend {inst_a} `{GHC.Base.Ord inst_a} : (Set_
                                                                        inst_a) -> (Set_ inst_a) -> (Set_ inst_a) :=
  _Data.Semigroup.<>_.

(* Translating `instance forall {a}, forall `{GHC.Base.Ord a},
   Data.Semigroup.Semigroup (Data.Set.Base.Set_ a)' failed: OOPS! Cannot find
   information for class Qualified "Data.Semigroup" "Semigroup" unsupported *)

(* Translating `instance Data.Foldable.Foldable Data.Set.Base.Set_' failed:
   Cannot find sig for Qualified "Data.Foldable" "minimum" unsupported *)

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
  Mk_Tip.

Local Definition Monoid__Set__mempty {inst_a} `{GHC.Base.Ord inst_a} : (Set_
                                                                       inst_a) :=
  empty.

Definition findMax {a} : Set_ a -> a :=
  fix findMax arg_83__
        := match arg_83__ with
             | Mk_Bin _ x _ Mk_Tip => x
             | Mk_Bin _ _ _ r => findMax r
             | Mk_Tip => GHC.Err.error (GHC.Base.hs_string__
                                       "Set.findMax: empty set has no maximal element")
           end.

Definition findMin {a} : Set_ a -> a :=
  fix findMin arg_87__
        := match arg_87__ with
             | Mk_Bin _ x Mk_Tip _ => x
             | Mk_Bin _ _ l _ => findMin l
             | Mk_Tip => GHC.Err.error (GHC.Base.hs_string__
                                       "Set.findMin: empty set has no minimal element")
           end.

Definition foldl {a} {b} : (a -> b -> a) -> a -> Set_ b -> a :=
  fun f z =>
    let go :=
      fix go arg_60__ arg_61__
            := match arg_60__ , arg_61__ with
                 | z' , Mk_Tip => z'
                 | z' , Mk_Bin _ x l r => go (f (go z' l) x) r
               end in
    go z.

Definition foldlFB {a} {b} : (a -> b -> a) -> a -> Set_ b -> a :=
  foldl.

Definition toDescList {a} : Set_ a -> list a :=
  foldl (GHC.Base.flip cons) nil.

Definition foldl' {a} {b} : (a -> b -> a) -> a -> Set_ b -> a :=
  fun f z =>
    let go :=
      fix go arg_53__ arg_54__
            := let j_56__ :=
                 match arg_53__ , arg_54__ with
                   | z' , Mk_Tip => z'
                   | z' , Mk_Bin _ x l r => go (f (go z' l) x) r
                 end in
               match arg_53__ , arg_54__ with
                 | arg , _ => if GHC.Prim.seq arg false : bool
                              then GHC.Err.undefined
                              else j_56__
               end in
    go z.

Definition foldr {a} {b} : (a -> b -> b) -> b -> Set_ a -> b :=
  fun f z =>
    let go :=
      fix go arg_73__ arg_74__
            := match arg_73__ , arg_74__ with
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

Program Instance Ord__Set_ {a} `{GHC.Base.Ord a} : GHC.Base.Ord (Set_ a) :=
  fun _ k =>
    k {|GHC.Base.op_zl____ := Ord__Set__op_zl__ ;
      GHC.Base.op_zlze____ := Ord__Set__op_zlze__ ;
      GHC.Base.op_zg____ := Ord__Set__op_zg__ ;
      GHC.Base.op_zgze____ := Ord__Set__op_zgze__ ;
      GHC.Base.compare__ := Ord__Set__compare ;
      GHC.Base.max__ := Ord__Set__max ;
      GHC.Base.min__ := Ord__Set__min |}.

Definition fold {a} {b} : (a -> b -> b) -> b -> Set_ a -> b :=
  foldr.

Definition foldr' {a} {b} : (a -> b -> b) -> b -> Set_ a -> b :=
  fun f z =>
    let go :=
      fix go arg_66__ arg_67__
            := let j_69__ :=
                 match arg_66__ , arg_67__ with
                   | z' , Mk_Tip => z'
                   | z' , Mk_Bin _ x l r => go (f x (go z' r)) l
                 end in
               match arg_66__ , arg_67__ with
                 | arg , _ => if GHC.Prim.seq arg false : bool
                              then GHC.Err.undefined
                              else j_69__
               end in
    go z.

Definition fromListConstr : Data.Data.Constr :=
  Data.Data.mkConstr setDataType (GHC.Base.hs_string__ "fromList") nil
  Data.Data.Prefix.

Definition setDataType : Data.Data.DataType :=
  Data.Data.mkDataType (GHC.Base.hs_string__ "Data.Set.Base.Set") (cons
                                                                  fromListConstr nil).

Definition lookupGE {a} `{GHC.Base.Ord a} : a -> Set_ a -> option a :=
  let goJust :=
    fix goJust arg_95__ arg_96__ arg_97__
          := let j_105__ :=
               match arg_95__ , arg_96__ , arg_97__ with
                 | _ , best , Mk_Tip => Some best
                 | x , best , Mk_Bin _ y l r => let scrut_99__ := GHC.Base.compare x y in
                                                match scrut_99__ with
                                                  | Lt => goJust x y l
                                                  | Eq => Some y
                                                  | Gt => goJust x best r
                                                end
               end in
             match arg_95__ , arg_96__ , arg_97__ with
               | arg , _ , _ => if GHC.Prim.seq arg false : bool
                                then GHC.Err.undefined
                                else j_105__
             end in
  let goNothing :=
    fix goNothing arg_108__ arg_109__
          := let j_116__ :=
               match arg_108__ , arg_109__ with
                 | _ , Mk_Tip => None
                 | x , Mk_Bin _ y l r => let scrut_110__ := GHC.Base.compare x y in
                                         match scrut_110__ with
                                           | Lt => goJust x y l
                                           | Eq => Some y
                                           | Gt => goNothing x r
                                         end
               end in
             match arg_108__ , arg_109__ with
               | arg , _ => if GHC.Prim.seq arg false : bool
                            then GHC.Err.undefined
                            else j_116__
             end in
  goNothing.

Definition lookupGT {a} `{GHC.Base.Ord a} : a -> Set_ a -> option a :=
  let goJust :=
    fix goJust arg_143__ arg_144__ arg_145__
          := let j_149__ :=
               match arg_143__ , arg_144__ , arg_145__ with
                 | _ , best , Mk_Tip => Some best
                 | x , best , Mk_Bin _ y l r => let j_147__ := goJust x best r in
                                                if x GHC.Base.< y : bool
                                                then goJust x y l
                                                else j_147__
               end in
             match arg_143__ , arg_144__ , arg_145__ with
               | arg , _ , _ => if GHC.Prim.seq arg false : bool
                                then GHC.Err.undefined
                                else j_149__
             end in
  let goNothing :=
    fix goNothing arg_152__ arg_153__
          := let j_156__ :=
               match arg_152__ , arg_153__ with
                 | _ , Mk_Tip => None
                 | x , Mk_Bin _ y l r => let j_154__ := goNothing x r in
                                         if x GHC.Base.< y : bool
                                         then goJust x y l
                                         else j_154__
               end in
             match arg_152__ , arg_153__ with
               | arg , _ => if GHC.Prim.seq arg false : bool
                            then GHC.Err.undefined
                            else j_156__
             end in
  goNothing.

Definition lookupLE {a} `{GHC.Base.Ord a} : a -> Set_ a -> option a :=
  let goJust :=
    fix goJust arg_119__ arg_120__ arg_121__
          := let j_129__ :=
               match arg_119__ , arg_120__ , arg_121__ with
                 | _ , best , Mk_Tip => Some best
                 | x , best , Mk_Bin _ y l r => let scrut_123__ := GHC.Base.compare x y in
                                                match scrut_123__ with
                                                  | Lt => goJust x best l
                                                  | Eq => Some y
                                                  | Gt => goJust x y r
                                                end
               end in
             match arg_119__ , arg_120__ , arg_121__ with
               | arg , _ , _ => if GHC.Prim.seq arg false : bool
                                then GHC.Err.undefined
                                else j_129__
             end in
  let goNothing :=
    fix goNothing arg_132__ arg_133__
          := let j_140__ :=
               match arg_132__ , arg_133__ with
                 | _ , Mk_Tip => None
                 | x , Mk_Bin _ y l r => let scrut_134__ := GHC.Base.compare x y in
                                         match scrut_134__ with
                                           | Lt => goNothing x l
                                           | Eq => Some y
                                           | Gt => goJust x y r
                                         end
               end in
             match arg_132__ , arg_133__ with
               | arg , _ => if GHC.Prim.seq arg false : bool
                            then GHC.Err.undefined
                            else j_140__
             end in
  goNothing.

Definition lookupLT {a} `{GHC.Base.Ord a} : a -> Set_ a -> option a :=
  let goJust :=
    fix goJust arg_159__ arg_160__ arg_161__
          := let j_165__ :=
               match arg_159__ , arg_160__ , arg_161__ with
                 | _ , best , Mk_Tip => Some best
                 | x , best , Mk_Bin _ y l r => let j_163__ := goJust x y r in
                                                if x GHC.Base.<= y : bool
                                                then goJust x best l
                                                else j_163__
               end in
             match arg_159__ , arg_160__ , arg_161__ with
               | arg , _ , _ => if GHC.Prim.seq arg false : bool
                                then GHC.Err.undefined
                                else j_165__
             end in
  let goNothing :=
    fix goNothing arg_168__ arg_169__
          := let j_172__ :=
               match arg_168__ , arg_169__ with
                 | _ , Mk_Tip => None
                 | x , Mk_Bin _ y l r => let j_170__ := goJust x y r in
                                         if x GHC.Base.<= y : bool
                                         then goNothing x l
                                         else j_170__
               end in
             match arg_168__ , arg_169__ with
               | arg , _ => if GHC.Prim.seq arg false : bool
                            then GHC.Err.undefined
                            else j_172__
             end in
  goNothing.

Definition mapMonotonic {a} {b} : (a -> b) -> Set_ a -> Set_ b :=
  fix mapMonotonic arg_79__ arg_80__
        := match arg_79__ , arg_80__ with
             | _ , Mk_Tip => Mk_Tip
             | f , Mk_Bin sz x l r => Mk_Bin sz (f x) (mapMonotonic f l) (mapMonotonic f r)
           end.

Definition member {a} `{GHC.Base.Ord a} : a -> Set_ a -> bool :=
  let go :=
    fix go arg_175__ arg_176__
          := let j_182__ :=
               match arg_175__ , arg_176__ with
                 | _ , Mk_Tip => false
                 | x , Mk_Bin _ y l r => let scrut_177__ := GHC.Base.compare x y in
                                         match scrut_177__ with
                                           | Lt => go x l
                                           | Gt => go x r
                                           | Eq => true
                                         end
               end in
             match arg_175__ , arg_176__ with
               | arg , _ => if GHC.Prim.seq arg false : bool
                            then GHC.Err.undefined
                            else j_182__
             end in
  go.

Definition notMember {a} `{GHC.Base.Ord a} : a -> Set_ a -> bool :=
  fun a t => negb GHC.Base.$ member a t.

Definition node : GHC.Base.String :=
  GHC.Base.hs_string__ "+--".

Definition showsBars : list GHC.Base.String -> GHC.Show.ShowS :=
  fun bars =>
    match bars with
      | nil => GHC.Base.id
      | _ => GHC.Show.showString (Data.Foldable.concat (GHC.List.reverse
                                                       (GHC.List.tail bars))) GHC.Base.∘ GHC.Show.showString node
    end.

Definition null {a} : Set_ a -> bool :=
  fun arg_576__ =>
    match arg_576__ with
      | Mk_Tip => true
      | Mk_Bin _ _ _ _ => false
    end.

Definition ordered {a} `{GHC.Base.Ord a} : Set_ a -> bool :=
  fun t =>
    let bounded :=
      fix bounded lo hi t'
            := match t' with
                 | Mk_Tip => true
                 | Mk_Bin _ x l r => andb (lo x) (andb (hi x) (andb (bounded lo (fun arg_0__ =>
                                                                                  arg_0__ GHC.Base.< x) l) (bounded
                                                                    (fun arg_1__ => arg_1__ GHC.Base.> x) hi r)))
               end in
    bounded (GHC.Base.const true) (GHC.Base.const true) t.

Definition ratio : GHC.Num.Int :=
  GHC.Num.fromInteger 2.

Definition showWide : bool -> list
                      GHC.Base.String -> GHC.Base.String -> GHC.Base.String :=
  fun wide bars =>
    if wide : bool
    then GHC.Show.showString (Data.Foldable.concat (GHC.List.reverse bars))
         GHC.Base.∘ GHC.Show.showString (GHC.Base.hs_string__ "|")
    else GHC.Base.id.

Definition singleton {a} : a -> Set_ a :=
  fun x => Mk_Bin (GHC.Num.fromInteger 1) x Mk_Tip Mk_Tip.

Definition splitRoot {a} : Set_ a -> list (Set_ a) :=
  fun orig =>
    match orig with
      | Mk_Tip => nil
      | Mk_Bin _ v l r => cons l (cons (singleton v) (cons r nil))
    end.

Definition size {a} : Set_ a -> GHC.Num.Int :=
  fun arg_186__ =>
    match arg_186__ with
      | Mk_Tip => GHC.Num.fromInteger 0
      | Mk_Bin sz _ _ _ => sz
    end.

Definition validsize {a} : Set_ a -> bool :=
  fun t =>
    let realsize :=
      fix realsize t'
            := match t' with
                 | Mk_Tip => Some (GHC.Num.fromInteger 0)
                 | Mk_Bin sz _ l r => let scrut_568__ := pair (realsize l) (realsize r) in
                                      match scrut_568__ with
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
    fix go arg_205__ arg_206__ arg_207__
          := let j_214__ :=
               match arg_205__ , arg_206__ , arg_207__ with
                 | _ , _ , Mk_Tip => None
                 | idx , x , Mk_Bin _ kx l r => let scrut_208__ := GHC.Base.compare x kx in
                                                match scrut_208__ with
                                                  | Lt => go idx x l
                                                  | Gt => go ((idx GHC.Num.+ size l) GHC.Num.+ GHC.Num.fromInteger 1) x
                                                          r
                                                  | Eq => Some GHC.Base.$! (idx GHC.Num.+ size l)
                                                end
               end in
             let j_216__ :=
               match arg_205__ , arg_206__ , arg_207__ with
                 | _ , arg , _ => if GHC.Prim.seq arg false : bool
                                  then GHC.Err.undefined
                                  else j_214__
               end in
             match arg_205__ , arg_206__ , arg_207__ with
               | arg , _ , _ => if GHC.Prim.seq arg false : bool
                                then GHC.Err.undefined
                                else j_216__
             end in
  go (GHC.Num.fromInteger 0).

Definition findIndex {a} `{GHC.Base.Ord a} : a -> Set_ a -> GHC.Num.Int :=
  let go {a} `{GHC.Base.Ord a} : GHC.Num.Int -> a -> Set_ a -> GHC.Num.Int :=
    fix go arg_189__ arg_190__ arg_191__
          := let j_199__ :=
               match arg_189__ , arg_190__ , arg_191__ with
                 | _ , _ , Mk_Tip => GHC.Err.error (GHC.Base.hs_string__
                                                   "Set.findIndex: element is not in the set")
                 | idx , x , Mk_Bin _ kx l r => let scrut_193__ := GHC.Base.compare x kx in
                                                match scrut_193__ with
                                                  | Lt => go idx x l
                                                  | Gt => go ((idx GHC.Num.+ size l) GHC.Num.+ GHC.Num.fromInteger 1) x
                                                          r
                                                  | Eq => idx GHC.Num.+ size l
                                                end
               end in
             let j_201__ :=
               match arg_189__ , arg_190__ , arg_191__ with
                 | _ , arg , _ => if GHC.Prim.seq arg false : bool
                                  then GHC.Err.undefined
                                  else j_199__
               end in
             match arg_189__ , arg_190__ , arg_191__ with
               | arg , _ , _ => if GHC.Prim.seq arg false : bool
                                then GHC.Err.undefined
                                else j_201__
             end in
  go (GHC.Num.fromInteger 0).

Definition elemAt {a} : GHC.Num.Int -> Set_ a -> a :=
  fix elemAt arg_220__ arg_221__
        := let j_229__ :=
             match arg_220__ , arg_221__ with
               | _ , Mk_Tip => GHC.Err.error (GHC.Base.hs_string__
                                             "Set.elemAt: index out of range")
               | i , Mk_Bin _ x l r => let sizeL := size l in
                                       let scrut_224__ := GHC.Base.compare i sizeL in
                                       match scrut_224__ with
                                         | Lt => elemAt i l
                                         | Gt => elemAt ((i GHC.Num.- sizeL) GHC.Num.- GHC.Num.fromInteger 1) r
                                         | Eq => x
                                       end
             end in
           match arg_220__ , arg_221__ with
             | arg , _ => if GHC.Prim.seq arg false : bool
                          then GHC.Err.undefined
                          else j_229__
           end.

Definition bin {a} : a -> Set_ a -> Set_ a -> Set_ a :=
  fun x l r =>
    Mk_Bin ((size l GHC.Num.+ size r) GHC.Num.+ GHC.Num.fromInteger 1) x l r.

Definition balanced {a} : Set_ a -> bool :=
  fix balanced t
        := match t with
             | Mk_Tip => true
             | Mk_Bin _ _ l r => andb (orb ((size l GHC.Num.+ size r) GHC.Base.<=
                                           GHC.Num.fromInteger 1) (andb (size l GHC.Base.<= (delta GHC.Num.* size r))
                                                                        (size r GHC.Base.<= (delta GHC.Num.* size l))))
                                      (andb (balanced l) (balanced r))
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
                      let j_273__ :=
                        Mk_Bin (GHC.Num.fromInteger 1 GHC.Num.+ rs) rlx (Mk_Bin (GHC.Num.fromInteger 1
                                                                                GHC.Num.+ size rll) x Mk_Tip rll)
                        (Mk_Bin ((GHC.Num.fromInteger 1 GHC.Num.+ rrs) GHC.Num.+ size rlr) rx rlr rr) in
                      if rls GHC.Base.< (ratio GHC.Num.* rrs) : bool
                      then Mk_Bin (GHC.Num.fromInteger 1 GHC.Num.+ rs) rx (Mk_Bin (GHC.Num.fromInteger
                                                                                  1 GHC.Num.+ rls) x Mk_Tip rl) rr
                      else j_273__
                  end
      | Mk_Bin ls _ _ _ => match r with
                             | Mk_Tip => Mk_Bin (GHC.Num.fromInteger 1 GHC.Num.+ ls) x l Mk_Tip
                             | Mk_Bin rs rx rl rr => let j_278__ :=
                                                       Mk_Bin ((GHC.Num.fromInteger 1 GHC.Num.+ ls) GHC.Num.+ rs) x l
                                                       r in
                                                     if rs GHC.Base.> (delta GHC.Num.* ls) : bool
                                                     then let scrut_279__ := pair rl rr in
                                                          let j_281__ :=
                                                            match scrut_279__ with
                                                              | pair _ _ => GHC.Err.error (GHC.Base.hs_string__
                                                                                          "Failure in Data.Map.balanceR")
                                                            end in
                                                          match scrut_279__ with
                                                            | pair (Mk_Bin rls rlx rll rlr) (Mk_Bin rrs _ _ _) =>
                                                              let j_282__ :=
                                                                Mk_Bin ((GHC.Num.fromInteger 1 GHC.Num.+ ls) GHC.Num.+
                                                                       rs) rlx (Mk_Bin ((GHC.Num.fromInteger 1 GHC.Num.+
                                                                                       ls) GHC.Num.+ size rll) x l rll)
                                                                (Mk_Bin ((GHC.Num.fromInteger 1 GHC.Num.+ rrs) GHC.Num.+
                                                                        size rlr) rx rlr rr) in
                                                              if rls GHC.Base.< (ratio GHC.Num.* rrs) : bool
                                                              then Mk_Bin ((GHC.Num.fromInteger 1 GHC.Num.+ ls)
                                                                          GHC.Num.+ rs) rx (Mk_Bin ((GHC.Num.fromInteger
                                                                                                   1 GHC.Num.+ ls)
                                                                                                   GHC.Num.+ rls) x l
                                                                                           rl) rr
                                                              else j_282__
                                                            | _ => j_281__
                                                          end
                                                     else j_278__
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
  fun arg_360__ =>
    match arg_360__ with
      | Mk_Tip => None
      | x => Some (deleteFindMin x)
    end.

Definition deleteMin {a} : Set_ a -> Set_ a :=
  fix deleteMin arg_313__
        := match arg_313__ with
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
                      let j_236__ :=
                        Mk_Bin (GHC.Num.fromInteger 1 GHC.Num.+ ls) lrx (Mk_Bin ((GHC.Num.fromInteger 1
                                                                                GHC.Num.+ lls) GHC.Num.+ size lrl) lx ll
                                                                        lrl) (Mk_Bin (GHC.Num.fromInteger 1 GHC.Num.+
                                                                                     size lrr) x lrr Mk_Tip) in
                      if lrs GHC.Base.< (ratio GHC.Num.* lls) : bool
                      then Mk_Bin (GHC.Num.fromInteger 1 GHC.Num.+ ls) lx ll (Mk_Bin
                                                                             (GHC.Num.fromInteger 1 GHC.Num.+ lrs) x lr
                                                                             Mk_Tip)
                      else j_236__
                  end
      | Mk_Bin rs _ _ _ => match l with
                             | Mk_Tip => Mk_Bin (GHC.Num.fromInteger 1 GHC.Num.+ rs) x Mk_Tip r
                             | Mk_Bin ls lx ll lr => let j_241__ :=
                                                       Mk_Bin ((GHC.Num.fromInteger 1 GHC.Num.+ ls) GHC.Num.+ rs) x l
                                                       r in
                                                     if ls GHC.Base.> (delta GHC.Num.* rs) : bool
                                                     then let scrut_242__ := pair ll lr in
                                                          let j_244__ :=
                                                            match scrut_242__ with
                                                              | pair _ _ => GHC.Err.error (GHC.Base.hs_string__
                                                                                          "Failure in Data.Map.balanceL")
                                                            end in
                                                          match scrut_242__ with
                                                            | pair (Mk_Bin lls _ _ _) (Mk_Bin lrs lrx lrl lrr) =>
                                                              let j_245__ :=
                                                                Mk_Bin ((GHC.Num.fromInteger 1 GHC.Num.+ ls) GHC.Num.+
                                                                       rs) lrx (Mk_Bin ((GHC.Num.fromInteger 1 GHC.Num.+
                                                                                       lls) GHC.Num.+ size lrl) lx ll
                                                                               lrl) (Mk_Bin ((GHC.Num.fromInteger 1
                                                                                            GHC.Num.+ rs) GHC.Num.+ size
                                                                                            lrr) x lrr r) in
                                                              if lrs GHC.Base.< (ratio GHC.Num.* lls) : bool
                                                              then Mk_Bin ((GHC.Num.fromInteger 1 GHC.Num.+ ls)
                                                                          GHC.Num.+ rs) lx ll (Mk_Bin
                                                                                              ((GHC.Num.fromInteger 1
                                                                                              GHC.Num.+ rs) GHC.Num.+
                                                                                              lrs) x lr r)
                                                              else j_245__
                                                            | _ => j_244__
                                                          end
                                                     else j_241__
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
  fun arg_266__ =>
    match arg_266__ with
      | Mk_Tip => None
      | x => Some (deleteFindMax x)
    end.

Definition deleteMax {a} : Set_ a -> Set_ a :=
  fix deleteMax arg_253__
        := match arg_253__ with
             | Mk_Bin _ _ l Mk_Tip => l
             | Mk_Bin _ x l r => balanceL x l (deleteMax r)
             | Mk_Tip => Mk_Tip
           end.

Definition insert {a} `{GHC.Base.Ord a} : a -> Set_ a -> Set_ a :=
  let go {a} `{GHC.Base.Ord a} : a -> Set_ a -> Set_ a :=
    fix go arg_290__ arg_291__
          := let j_299__ :=
               match arg_290__ , arg_291__ with
                 | x , Mk_Tip => singleton x
                 | x , Mk_Bin sz y l r => let scrut_293__ := GHC.Base.compare x y in
                                          match scrut_293__ with
                                            | Lt => balanceL y (go x l) r
                                            | Gt => balanceR y l (go x r)
                                            | Eq => Mk_Bin sz x l r
                                          end
               end in
             match arg_290__ , arg_291__ with
               | arg , _ => if GHC.Prim.seq arg false : bool
                            then GHC.Err.undefined
                            else j_299__
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
    fix go arg_302__ arg_303__
          := let j_310__ :=
               match arg_302__ , arg_303__ with
                 | x , Mk_Tip => singleton x
                 | x , (Mk_Bin _ y l r as t) => let scrut_305__ := GHC.Base.compare x y in
                                                match scrut_305__ with
                                                  | Lt => balanceL y (go x l) r
                                                  | Gt => balanceR y l (go x r)
                                                  | Eq => t
                                                end
               end in
             match arg_302__ , arg_303__ with
               | arg , _ => if GHC.Prim.seq arg false : bool
                            then GHC.Err.undefined
                            else j_310__
             end in
  go.

Definition link {a} : a -> Set_ a -> Set_ a -> Set_ a :=
  fix link arg_364__ arg_365__ arg_366__
        := match arg_364__ , arg_365__ , arg_366__ with
             | x , Mk_Tip , r => insertMin x r
             | x , l , Mk_Tip => insertMax x l
             | x , (Mk_Bin sizeL y ly ry as l) , (Mk_Bin sizeR z lz rz as r) =>
               let j_369__ := bin x l r in
               let j_370__ :=
                 if (delta GHC.Num.* sizeR) GHC.Base.< sizeL : bool
                 then balanceR y ly (link x ry r)
                 else j_369__ in
               if (delta GHC.Num.* sizeL) GHC.Base.< sizeR : bool
               then balanceL z (link x l lz) rz
               else j_370__
           end.

Definition filterGt {a} `{GHC.Base.Ord a} : MaybeS a -> Set_ a -> Set_ a :=
  fun arg_480__ arg_481__ =>
    match arg_480__ , arg_481__ with
      | Mk_NothingS , t => t
      | Mk_JustS b , t => let filter' :=
                            fix filter' arg_482__ arg_483__
                                  := match arg_482__ , arg_483__ with
                                       | _ , Mk_Tip => Mk_Tip
                                       | b' , Mk_Bin _ x l r => let scrut_484__ := GHC.Base.compare b' x in
                                                                match scrut_484__ with
                                                                  | Lt => link x (filter' b' l) r
                                                                  | Eq => r
                                                                  | Gt => filter' b' r
                                                                end
                                     end in
                          filter' b t
    end.

Definition filterLt {a} `{GHC.Base.Ord a} : MaybeS a -> Set_ a -> Set_ a :=
  fun arg_492__ arg_493__ =>
    match arg_492__ , arg_493__ with
      | Mk_NothingS , t => t
      | Mk_JustS b , t => let filter' :=
                            fix filter' arg_494__ arg_495__
                                  := match arg_494__ , arg_495__ with
                                       | _ , Mk_Tip => Mk_Tip
                                       | b' , Mk_Bin _ x l r => let scrut_496__ := GHC.Base.compare x b' in
                                                                match scrut_496__ with
                                                                  | Lt => link x l (filter' b' r)
                                                                  | Eq => l
                                                                  | Gt => filter' b' l
                                                                end
                                     end in
                          filter' b t
    end.

Definition fromDistinctAscList {a} : list a -> Set_ a :=
  fun arg_442__ =>
    match arg_442__ with
      | nil => Mk_Tip
      | cons x0 xs0 => let create :=
                         fix create arg_443__ arg_444__
                               := let j_454__ :=
                                    match arg_443__ , arg_444__ with
                                      | _ , nil => pair Mk_Tip nil
                                      | s , (cons x xs' as xs) => let j_452__ :=
                                                                    let scrut_446__ :=
                                                                      create (Data.Bits.shiftR s (GHC.Num.fromInteger
                                                                                               1)) xs in
                                                                    match scrut_446__ with
                                                                      | (pair _ nil as res) => res
                                                                      | pair l (cons y ys) => let scrut_447__ :=
                                                                                                create (Data.Bits.shiftR
                                                                                                       s
                                                                                                       (GHC.Num.fromInteger
                                                                                                       1)) ys in
                                                                                              match scrut_447__ with
                                                                                                | pair r zs => pair
                                                                                                               (link y l
                                                                                                               r) zs
                                                                                              end
                                                                    end in
                                                                  if s GHC.Base.== GHC.Num.fromInteger 1 : bool
                                                                  then pair (Mk_Bin (GHC.Num.fromInteger 1) x Mk_Tip
                                                                            Mk_Tip) xs'
                                                                  else j_452__
                                    end in
                                  match arg_443__ , arg_444__ with
                                    | arg , _ => if GHC.Prim.seq arg false : bool
                                                 then GHC.Err.undefined
                                                 else j_454__
                                  end in
                       let go :=
                         fix go arg_457__ arg_458__ arg_459__
                               := let j_464__ :=
                                    match arg_457__ , arg_458__ , arg_459__ with
                                      | _ , t , nil => t
                                      | s , l , cons x xs => let scrut_460__ := create s xs in
                                                             match scrut_460__ with
                                                               | pair r ys => go (Data.Bits.shiftL s
                                                                                                   (GHC.Num.fromInteger
                                                                                                   1)) (link x l r) ys
                                                             end
                                    end in
                                  match arg_457__ , arg_458__ , arg_459__ with
                                    | arg , _ , _ => if GHC.Prim.seq arg false : bool
                                                     then GHC.Err.undefined
                                                     else j_464__
                                  end in
                       go (GHC.Num.fromInteger 1 : GHC.Num.Int) (Mk_Bin (GHC.Num.fromInteger 1) x0
                                                                Mk_Tip Mk_Tip) xs0
    end.

Definition fromAscList {a} `{GHC.Base.Eq_ a} : list a -> Set_ a :=
  fun xs =>
    let combineEq' :=
      fix combineEq' arg_469__ arg_470__
            := match arg_469__ , arg_470__ with
                 | z , nil => cons z nil
                 | z , cons x xs' => let j_472__ := cons z (combineEq' x xs') in
                                     if z GHC.Base.== x : bool
                                     then combineEq' z xs'
                                     else j_472__
               end in
    let combineEq :=
      fun xs' =>
        match xs' with
          | nil => nil
          | cons x nil => cons x nil
          | cons x xx => combineEq' x xx
        end in
    fromDistinctAscList (combineEq xs).

Definition fromList {a} `{GHC.Base.Ord a} : list a -> Set_ a :=
  fun arg_401__ =>
    match arg_401__ with
      | nil => Mk_Tip
      | cons x nil => Mk_Bin (GHC.Num.fromInteger 1) x Mk_Tip Mk_Tip
      | cons x0 xs0 => let fromList' :=
                         fun t0 xs => let ins := fun t x => insert x t in foldl ins t0 xs in
                       let not_ordered :=
                         fun arg_405__ arg_406__ =>
                           match arg_405__ , arg_406__ with
                             | _ , nil => false
                             | x , cons y _ => x GHC.Base.>= y
                           end in
                       let create :=
                         fix create arg_409__ arg_410__
                               := let j_422__ :=
                                    match arg_409__ , arg_410__ with
                                      | _ , nil => pair (pair Mk_Tip nil) nil
                                      | s , (cons x xss as xs) => let j_420__ :=
                                                                    let scrut_412__ :=
                                                                      create (Data.Bits.shiftR s (GHC.Num.fromInteger
                                                                                               1)) xs in
                                                                    match scrut_412__ with
                                                                      | (pair (pair _ nil) _ as res) => res
                                                                      | pair (pair l (cons y nil)) zs => pair (pair
                                                                                                              (insertMax
                                                                                                              y l) nil)
                                                                                                              zs
                                                                      | pair (pair l (cons y yss as ys)) _ =>
                                                                        let j_417__ :=
                                                                          let scrut_414__ :=
                                                                            create (Data.Bits.shiftR s
                                                                                                     (GHC.Num.fromInteger
                                                                                                     1)) yss in
                                                                          match scrut_414__ with
                                                                            | pair (pair r zs) ws => pair (pair (link y
                                                                                                                l r) zs)
                                                                                                          ws
                                                                          end in
                                                                        if not_ordered y yss : bool
                                                                        then pair (pair l nil) ys
                                                                        else j_417__
                                                                    end in
                                                                  if s GHC.Base.== GHC.Num.fromInteger 1 : bool
                                                                  then if not_ordered x xss : bool
                                                                       then pair (pair (Mk_Bin (GHC.Num.fromInteger 1) x
                                                                                       Mk_Tip Mk_Tip) nil) xss
                                                                       else pair (pair (Mk_Bin (GHC.Num.fromInteger 1) x
                                                                                       Mk_Tip Mk_Tip) xss) nil
                                                                  else j_420__
                                    end in
                                  match arg_409__ , arg_410__ with
                                    | arg , _ => if GHC.Prim.seq arg false : bool
                                                 then GHC.Err.undefined
                                                 else j_422__
                                  end in
                       let go :=
                         fix go arg_425__ arg_426__ arg_427__
                               := let j_435__ :=
                                    match arg_425__ , arg_426__ , arg_427__ with
                                      | _ , t , nil => t
                                      | _ , t , cons x nil => insertMax x t
                                      | s , l , (cons x xss as xs) => let j_433__ :=
                                                                        let scrut_429__ := create s xss in
                                                                        match scrut_429__ with
                                                                          | pair (pair r ys) nil => go (Data.Bits.shiftL
                                                                                                       s
                                                                                                       (GHC.Num.fromInteger
                                                                                                       1)) (link x l r)
                                                                                                    ys
                                                                          | pair (pair r _) ys => fromList' (link x l r)
                                                                                                  ys
                                                                        end in
                                                                      if not_ordered x xss : bool
                                                                      then fromList' l xs
                                                                      else j_433__
                                    end in
                                  match arg_425__ , arg_426__ , arg_427__ with
                                    | arg , _ , _ => if GHC.Prim.seq arg false : bool
                                                     then GHC.Err.undefined
                                                     else j_435__
                                  end in
                       let j_438__ :=
                         go (GHC.Num.fromInteger 1 : GHC.Num.Int) (Mk_Bin (GHC.Num.fromInteger 1) x0
                                                                  Mk_Tip Mk_Tip) xs0 in
                       if not_ordered x0 xs0 : bool
                       then fromList' (Mk_Bin (GHC.Num.fromInteger 1) x0 Mk_Tip Mk_Tip) xs0
                       else j_438__
    end.

Definition map {b} {a} `{GHC.Base.Ord b} : (a -> b) -> Set_ a -> Set_ b :=
  fun f => fromList GHC.Base.∘ (GHC.Base.map f GHC.Base.∘ toList).

Definition split {a} `{GHC.Base.Ord a} : a -> Set_ a -> Set_ a * Set_ a :=
  fun x0 t0 =>
    let go :=
      fix go arg_530__ arg_531__
            := match arg_530__ , arg_531__ with
                 | _ , Mk_Tip => (pair Mk_Tip Mk_Tip)
                 | x , Mk_Bin _ y l r => let scrut_533__ := GHC.Base.compare x y in
                                         match scrut_533__ with
                                           | Lt => match go x l with
                                                     | pair lt gt => (pair lt (link y gt r))
                                                   end
                                           | Gt => match go x r with
                                                     | pair lt gt => (pair (link y l lt) gt)
                                                   end
                                           | Eq => (pair l r)
                                         end
               end in
    Data.Utils.StrictPair.toPair GHC.Base.$ go x0 t0.

Definition splitMember {a} `{GHC.Base.Ord a} : a -> Set_ a -> Set_ a * bool *
                                               Set_ a :=
  fix splitMember arg_543__ arg_544__
        := match arg_543__ , arg_544__ with
             | _ , Mk_Tip => pair (pair Mk_Tip false) Mk_Tip
             | x , Mk_Bin _ y l r => let scrut_546__ := GHC.Base.compare x y in
                                     match scrut_546__ with
                                       | Lt => match splitMember x l with
                                                 | pair (pair lt found) gt => let gt' := link y gt r in
                                                                              GHC.Prim.seq gt' (pair (pair lt found)
                                                                                                     gt')
                                               end
                                       | Gt => match splitMember x r with
                                                 | pair (pair lt found) gt => let lt' := link y l lt in
                                                                              GHC.Prim.seq lt' (pair (pair lt' found)
                                                                                                     gt)
                                               end
                                       | Eq => pair (pair l true) r
                                     end
           end.

Definition isSubsetOfX {a} `{GHC.Base.Ord a} : Set_ a -> Set_ a -> bool :=
  fix isSubsetOfX arg_557__ arg_558__
        := match arg_557__ , arg_558__ with
             | Mk_Tip , _ => true
             | _ , Mk_Tip => false
             | Mk_Bin _ x l r , t => match splitMember x t with
                                       | pair (pair lt found) gt => andb found (andb (isSubsetOfX l lt) (isSubsetOfX r
                                                                                     gt))
                                     end
           end.

Definition glue {a} : Set_ a -> Set_ a -> Set_ a :=
  fun arg_326__ arg_327__ =>
    match arg_326__ , arg_327__ with
      | Mk_Tip , r => r
      | l , Mk_Tip => l
      | l , r => let j_329__ :=
                   match deleteFindMin r with
                     | pair m r' => balanceL m l r'
                   end in
                 if size l GHC.Base.> size r : bool
                 then match deleteFindMax l with
                        | pair m l' => balanceR m l' r
                      end
                 else j_329__
    end.

Definition delete {a} `{GHC.Base.Ord a} : a -> Set_ a -> Set_ a :=
  let go {a} `{GHC.Base.Ord a} : a -> Set_ a -> Set_ a :=
    fix go arg_333__ arg_334__
          := let j_341__ :=
               match arg_333__ , arg_334__ with
                 | _ , Mk_Tip => Mk_Tip
                 | x , Mk_Bin _ y l r => let scrut_335__ := GHC.Base.compare x y in
                                         match scrut_335__ with
                                           | Lt => balanceR y (go x l) r
                                           | Gt => balanceL y l (go x r)
                                           | Eq => glue l r
                                         end
               end in
             match arg_333__ , arg_334__ with
               | arg , _ => if GHC.Prim.seq arg false : bool
                            then GHC.Err.undefined
                            else j_341__
             end in
  go.

Definition merge {a} : Set_ a -> Set_ a -> Set_ a :=
  fix merge arg_354__ arg_355__
        := match arg_354__ , arg_355__ with
             | Mk_Tip , r => r
             | l , Mk_Tip => l
             | (Mk_Bin sizeL x lx rx as l) , (Mk_Bin sizeR y ly ry as r) => let j_356__ :=
                                                                              glue l r in
                                                                            let j_357__ :=
                                                                              if (delta GHC.Num.* sizeR) GHC.Base.<
                                                                                 sizeL : bool
                                                                              then balanceR x lx (merge rx r)
                                                                              else j_356__ in
                                                                            if (delta GHC.Num.* sizeL) GHC.Base.<
                                                                               sizeR : bool
                                                                            then balanceL y (merge l ly) ry
                                                                            else j_357__
           end.

Definition filter {a} : (a -> bool) -> Set_ a -> Set_ a :=
  fix filter arg_386__ arg_387__
        := match arg_386__ , arg_387__ with
             | _ , Mk_Tip => Mk_Tip
             | p , Mk_Bin _ x l r => let j_388__ := merge (filter p l) (filter p r) in
                                     if p x : bool
                                     then link x (filter p l) (filter p r)
                                     else j_388__
           end.

Definition partition {a} : (a -> bool) -> Set_ a -> Set_ a * Set_ a :=
  fun p0 t0 =>
    let go :=
      fix go arg_391__ arg_392__
            := match arg_391__ , arg_392__ with
                 | _ , Mk_Tip => (pair Mk_Tip Mk_Tip)
                 | p , Mk_Bin _ x l r => let scrut_394__ := pair (go p l) (go p r) in
                                         match scrut_394__ with
                                           | pair (pair l1 l2) (pair r1 r2) => let j_395__ :=
                                                                                 pair (merge l1 r1) (link x l2 r2) in
                                                                               if p x : bool
                                                                               then pair (link x l1 r1) (merge l2 r2)
                                                                               else j_395__
                                         end
               end in
    Data.Utils.StrictPair.toPair GHC.Base.$ go p0 t0.

Definition deleteAt {a} : GHC.Num.Int -> Set_ a -> Set_ a :=
  fix deleteAt i t
        := GHC.Prim.seq i (match t with
                          | Mk_Tip => GHC.Err.error (GHC.Base.hs_string__
                                                    "Set.deleteAt: index out of range")
                          | Mk_Bin _ x l r => let sizeL := size l in
                                              let scrut_346__ := GHC.Base.compare i sizeL in
                                              match scrut_346__ with
                                                | Lt => balanceR x (deleteAt i l) r
                                                | Gt => balanceL x l (deleteAt ((i GHC.Num.- sizeL) GHC.Num.-
                                                                               GHC.Num.fromInteger 1) r)
                                                | Eq => glue l r
                                              end
                        end).

Definition isSubsetOf {a} `{GHC.Base.Ord a} : Set_ a -> Set_ a -> bool :=
  fun t1 t2 => andb (size t1 GHC.Base.<= size t2) (isSubsetOfX t1 t2).

Definition isProperSubsetOf {a} `{GHC.Base.Ord a} : Set_ a -> Set_ a -> bool :=
  fun s1 s2 => andb (size s1 GHC.Base.< size s2) (isSubsetOf s1 s2).

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

Definition trim {a} `{GHC.Base.Ord a} : MaybeS a -> MaybeS a -> Set_ a -> Set_
                                        a :=
  fun arg_28__ arg_29__ arg_30__ =>
    match arg_28__ , arg_29__ , arg_30__ with
      | Mk_NothingS , Mk_NothingS , t => t
      | Mk_JustS lx , Mk_NothingS , t => let greater :=
                                           fix greater arg_31__ arg_32__
                                                 := let j_33__ := match arg_31__ , arg_32__ with | _ , t' => t' end in
                                                    match arg_31__ , arg_32__ with
                                                      | lo , Mk_Bin _ x _ r => if x GHC.Base.<= lo : bool
                                                                               then greater lo r
                                                                               else j_33__
                                                      | _ , _ => j_33__
                                                    end in
                                         greater lx t
      | Mk_NothingS , Mk_JustS hx , t => let lesser :=
                                           fix lesser arg_37__ arg_38__
                                                 := let j_39__ := match arg_37__ , arg_38__ with | _ , t' => t' end in
                                                    match arg_37__ , arg_38__ with
                                                      | hi , Mk_Bin _ x l _ => if x GHC.Base.>= hi : bool
                                                                               then lesser hi l
                                                                               else j_39__
                                                      | _ , _ => j_39__
                                                    end in
                                         lesser hx t
      | Mk_JustS lx , Mk_JustS hx , t => let middle :=
                                           fix middle arg_43__ arg_44__ arg_45__
                                                 := let j_46__ :=
                                                      match arg_43__ , arg_44__ , arg_45__ with
                                                        | _ , _ , t' => t'
                                                      end in
                                                    let j_48__ :=
                                                      match arg_43__ , arg_44__ , arg_45__ with
                                                        | lo , hi , Mk_Bin _ x l _ => if x GHC.Base.>= hi : bool
                                                                                      then middle lo hi l
                                                                                      else j_46__
                                                        | _ , _ , _ => j_46__
                                                      end in
                                                    match arg_43__ , arg_44__ , arg_45__ with
                                                      | lo , hi , Mk_Bin _ x _ r => if x GHC.Base.<= lo : bool
                                                                                    then middle lo hi r
                                                                                    else j_48__
                                                      | _ , _ , _ => j_48__
                                                    end in
                                         middle lx hx t
    end.

Definition hedgeUnion {a} `{GHC.Base.Ord a} : MaybeS a -> MaybeS a -> Set_
                                              a -> Set_ a -> Set_ a :=
  fix hedgeUnion arg_504__ arg_505__ arg_506__ arg_507__
        := match arg_504__ , arg_505__ , arg_506__ , arg_507__ with
             | _ , _ , t1 , Mk_Tip => t1
             | blo , bhi , Mk_Tip , Mk_Bin _ x l r => link x (filterGt blo l) (filterLt bhi
                                                                              r)
             | _ , _ , t1 , Mk_Bin _ x Mk_Tip Mk_Tip => insertR x t1
             | blo , bhi , Mk_Bin _ x l r , t2 => let bmi := Mk_JustS x in
                                                  link x (hedgeUnion blo bmi l (trim blo bmi t2)) (hedgeUnion bmi bhi r
                                                                                                  (trim bmi bhi t2))
           end.

Definition union {a} `{GHC.Base.Ord a} : Set_ a -> Set_ a -> Set_ a :=
  fun arg_513__ arg_514__ =>
    match arg_513__ , arg_514__ with
      | Mk_Tip , t2 => t2
      | t1 , Mk_Tip => t1
      | t1 , t2 => hedgeUnion Mk_NothingS Mk_NothingS t1 t2
    end.

Definition unions {a} `{GHC.Base.Ord a} : list (Set_ a) -> Set_ a :=
  foldl union empty.

Local Definition Monoid__Set__mconcat {inst_a} `{GHC.Base.Ord inst_a} : list
                                                                        (Set_ inst_a) -> (Set_ inst_a) :=
  unions.

Program Instance Monoid__Set_ {a} `{GHC.Base.Ord a} : GHC.Base.Monoid (Set_
                                                                      a) := fun _ k =>
    k {|GHC.Base.mappend__ := Monoid__Set__mappend ;
      GHC.Base.mconcat__ := Monoid__Set__mconcat ;
      GHC.Base.mempty__ := Monoid__Set__mempty |}.

Definition hedgeDiff {a} `{GHC.Base.Ord a} : MaybeS a -> MaybeS a -> Set_
                                             a -> Set_ a -> Set_ a :=
  fix hedgeDiff arg_518__ arg_519__ arg_520__ arg_521__
        := match arg_518__ , arg_519__ , arg_520__ , arg_521__ with
             | _ , _ , Mk_Tip , _ => Mk_Tip
             | blo , bhi , Mk_Bin _ x l r , Mk_Tip => link x (filterGt blo l) (filterLt bhi
                                                                              r)
             | blo , bhi , t , Mk_Bin _ x l r => let bmi := Mk_JustS x in
                                                 merge (hedgeDiff blo bmi (trim blo bmi t) l) (hedgeDiff bmi bhi (trim
                                                                                                                 bmi bhi
                                                                                                                 t) r)
           end.

Definition difference {a} `{GHC.Base.Ord a} : Set_ a -> Set_ a -> Set_ a :=
  fun arg_526__ arg_527__ =>
    match arg_526__ , arg_527__ with
      | Mk_Tip , _ => Mk_Tip
      | t1 , Mk_Tip => t1
      | t1 , t2 => hedgeDiff Mk_NothingS Mk_NothingS t1 t2
    end.

Definition op_zrzr__ {a} `{GHC.Base.Ord a} : Set_ a -> Set_ a -> Set_ a :=
  fun m1 m2 => difference m1 m2.

Notation "'_\\_'" := (op_zrzr__).

Infix "\\" := (_\\_) (at level 99).

Definition hedgeInt {a} `{GHC.Base.Ord a} : MaybeS a -> MaybeS a -> Set_
                                            a -> Set_ a -> Set_ a :=
  fix hedgeInt arg_373__ arg_374__ arg_375__ arg_376__
        := match arg_373__ , arg_374__ , arg_375__ , arg_376__ with
             | _ , _ , _ , Mk_Tip => Mk_Tip
             | _ , _ , Mk_Tip , _ => Mk_Tip
             | blo , bhi , Mk_Bin _ x l r , t2 => let bmi := Mk_JustS x in
                                                  let r' := hedgeInt bmi bhi r (trim bmi bhi t2) in
                                                  let l' := hedgeInt blo bmi l (trim blo bmi t2) in
                                                  if member x t2 : bool
                                                  then link x l' r'
                                                  else merge l' r'
           end.

Definition intersection {a} `{GHC.Base.Ord a} : Set_ a -> Set_ a -> Set_ a :=
  fun arg_382__ arg_383__ =>
    match arg_382__ , arg_383__ with
      | Mk_Tip , _ => Mk_Tip
      | _ , Mk_Tip => Mk_Tip
      | t1 , t2 => hedgeInt Mk_NothingS Mk_NothingS t1 t2
    end.

Definition withBar : list GHC.Base.String -> list GHC.Base.String :=
  fun bars => cons (GHC.Base.hs_string__ "|  ") bars.

Definition withEmpty : list GHC.Base.String -> list GHC.Base.String :=
  fun bars => cons (GHC.Base.hs_string__ "   ") bars.

Definition showsTree {a} `{GHC.Show.Show a} : bool -> list
                                              GHC.Base.String -> list GHC.Base.String -> Set_ a -> GHC.Show.ShowS :=
  fix showsTree wide lbars rbars t
        := match t with
             | Mk_Tip => showsBars lbars GHC.Base.∘ GHC.Show.showString (GHC.Base.hs_string__
                                                                        "|")
             | Mk_Bin _ x Mk_Tip Mk_Tip => showsBars lbars GHC.Base.∘ (GHC.Show.shows x
                                           GHC.Base.∘ GHC.Show.showString (GHC.Base.hs_string__ ""))
             | Mk_Bin _ x l r => showsTree wide (withBar rbars) (withEmpty rbars) r
                                 GHC.Base.∘ (showWide wide rbars GHC.Base.∘ (showsBars lbars GHC.Base.∘
                                 (GHC.Show.shows x GHC.Base.∘ (GHC.Show.showString (GHC.Base.hs_string__ "")
                                 GHC.Base.∘ (showWide wide lbars GHC.Base.∘ showsTree wide (withEmpty lbars)
                                 (withBar lbars) l)))))
           end.

Definition showsTreeHang {a} `{GHC.Show.Show a} : bool -> list
                                                  GHC.Base.String -> Set_ a -> GHC.Show.ShowS :=
  fix showsTreeHang wide bars t
        := match t with
             | Mk_Tip => showsBars bars GHC.Base.∘ GHC.Show.showString (GHC.Base.hs_string__
                                                                       "|")
             | Mk_Bin _ x Mk_Tip Mk_Tip => showsBars bars GHC.Base.∘ (GHC.Show.shows x
                                           GHC.Base.∘ GHC.Show.showString (GHC.Base.hs_string__ ""))
             | Mk_Bin _ x l r => showsBars bars GHC.Base.∘ (GHC.Show.shows x GHC.Base.∘
                                 (GHC.Show.showString (GHC.Base.hs_string__ "") GHC.Base.∘ (showWide wide bars
                                 GHC.Base.∘ (showsTreeHang wide (withBar bars) l GHC.Base.∘ (showWide wide bars
                                 GHC.Base.∘ showsTreeHang wide (withEmpty bars) r)))))
           end.

Definition showTreeWith {a} `{GHC.Show.Show a} : bool -> bool -> Set_
                                                 a -> GHC.Base.String :=
  fun hang wide t =>
    let j_23__ := (showsTree wide nil nil t) (GHC.Base.hs_string__ "") in
    if hang : bool
    then (showsTreeHang wide nil t) (GHC.Base.hs_string__ "")
    else j_23__.

Definition showTree {a} `{GHC.Show.Show a} : Set_ a -> GHC.Base.String :=
  fun s => showTreeWith true false s.

Module Notations.
Notation "'_Data.Set.Base.\\_'" := (op_zrzr__).
Infix "Data.Set.Base.\\" := (_\\_) (at level 99).
End Notations.

(* Unbound variables:
     Gt Lt None Some andb bool comparison cons false list negb nil op_zt__ option orb
     pair setDataType true Data.Bits.shiftL Data.Bits.shiftR Data.Data.Constr
     Data.Data.DataType Data.Data.Prefix Data.Data.mkConstr Data.Data.mkDataType
     Data.Foldable.concat Data.Semigroup.op_zlzg__ Data.Utils.StrictPair.toPair
     GHC.Base.Eq_ GHC.Base.Monoid GHC.Base.Ord GHC.Base.String GHC.Base.compare
     GHC.Base.const GHC.Base.flip GHC.Base.id GHC.Base.map GHC.Base.op_z2218U__
     GHC.Base.op_zd__ GHC.Base.op_zdzn__ GHC.Base.op_zeze__ GHC.Base.op_zg__
     GHC.Base.op_zgze__ GHC.Base.op_zl__ GHC.Base.op_zlze__ GHC.Base.op_zsze__
     GHC.Err.error GHC.Err.undefined GHC.List.reverse GHC.List.tail GHC.Num.Int
     GHC.Num.op_zm__ GHC.Num.op_zp__ GHC.Num.op_zt__ GHC.Prim.seq GHC.Show.Show
     GHC.Show.ShowS GHC.Show.showString GHC.Show.shows
*)
