(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Coq.Program.Tactics.
Require Coq.Program.Wf.

(* Preamble *)

Require GHC.Base.

Module GHC.
  Module Err.
    Axiom undefined : forall {a}, a.
    Axiom error : forall {a}, GHC.Base.String -> a.
  End Err.
End GHC.

(* Converted imports: *)

Require Data.Bits.
Require Data.Foldable.
Require GHC.Base.
Require GHC.Num.
Require GHC.Prim.
Require Nat.
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
(* Midamble *)

Require Omega.

Ltac termination_by_omega :=
  Coq.Program.Tactics.program_simpl;
  simpl;Omega.omega.

Fixpoint set_size {a} (s : Set_ a) : nat :=
  match s with
  | Tip => 0
  | Bin _ _ s1 s2 => 1 + set_size s1 + set_size s2
  end.

(* Converted value declarations: *)

(* The Haskell code containes partial or untranslateable code, which needs the
   following *)

Axiom patternFailure : forall {a}, a.

Axiom unsafeFix : forall {a}, (a -> a) -> a.

(* Skipping instance Monoid__Set_ *)

(* Translating `instance forall {a}, forall `{GHC.Base.Ord a},
   Data.Semigroup.Semigroup (Data.Set.Base.Set_ a)' failed: OOPS! Cannot find
   information for class Qualified "Data.Semigroup" "Semigroup" unsupported *)

Local Definition Foldable__Set__elem : forall {a},
                                         forall `{GHC.Base.Eq_ a}, a -> Set_ a -> bool :=
  fun {a} `{GHC.Base.Eq_ a} =>
    let go :=
      fix go arg_0__ arg_1__
            := let j_3__ :=
                 match arg_0__ , arg_1__ with
                   | _ , Tip => false
                   | x , Bin _ y l r => orb (x GHC.Base.== y) (orb (go x l) (go x r))
                 end in
               match arg_0__ , arg_1__ with
                 | arg , _ => if GHC.Prim.seq arg false : bool
                              then GHC.Err.undefined
                              else j_3__
               end in
    go.

Local Definition Foldable__Set__fold : forall {m},
                                         forall `{GHC.Base.Monoid m}, Set_ m -> m :=
  fun {m} `{GHC.Base.Monoid m} =>
    let go :=
      fix go arg_0__
            := let j_3__ :=
                 match arg_0__ with
                   | Bin _ k l r => GHC.Base.mappend (go l) (GHC.Base.mappend k (go r))
                   | _ => patternFailure
                 end in
               match arg_0__ with
                 | Tip => GHC.Base.mempty
                 | Bin num_1__ k _ _ => if num_1__ GHC.Base.== GHC.Num.fromInteger 1 : bool
                                        then k
                                        else j_3__
               end in
    go.

Local Definition Foldable__Set__foldMap : forall {m} {a},
                                            forall `{GHC.Base.Monoid m}, (a -> m) -> Set_ a -> m :=
  fun {m} {a} `{GHC.Base.Monoid m} =>
    fun f t =>
      let go :=
        fix go arg_0__
              := let j_3__ :=
                   match arg_0__ with
                     | Bin _ k l r => GHC.Base.mappend (go l) (GHC.Base.mappend (f k) (go r))
                     | _ => patternFailure
                   end in
                 match arg_0__ with
                   | Tip => GHC.Base.mempty
                   | Bin num_1__ k _ _ => if num_1__ GHC.Base.== GHC.Num.fromInteger 1 : bool
                                          then f k
                                          else j_3__
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
  fix findMax arg_0__
        := match arg_0__ with
             | Bin _ x _ Tip => x
             | Bin _ _ _ r => findMax r
             | Tip => GHC.Err.error (GHC.Base.hs_string__
                                    "Set.findMax: empty set has no maximal element")
           end.

Definition findMin {a} : Set_ a -> a :=
  fix findMin arg_0__
        := match arg_0__ with
             | Bin _ x Tip _ => x
             | Bin _ _ l _ => findMin l
             | Tip => GHC.Err.error (GHC.Base.hs_string__
                                    "Set.findMin: empty set has no minimal element")
           end.

Definition foldl {a} {b} : (a -> b -> a) -> a -> Set_ b -> a :=
  fun f z =>
    let go :=
      fix go arg_0__ arg_1__
            := match arg_0__ , arg_1__ with
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
      fix go arg_0__ arg_1__
            := let j_3__ :=
                 match arg_0__ , arg_1__ with
                   | z' , Tip => z'
                   | z' , Bin _ x l r => go (f (go z' l) x) r
                 end in
               match arg_0__ , arg_1__ with
                 | arg , _ => if GHC.Prim.seq arg false : bool
                              then GHC.Err.undefined
                              else j_3__
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
      fix go arg_0__ arg_1__
            := match arg_0__ , arg_1__ with
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
      fix go arg_0__ arg_1__
            := let j_3__ :=
                 match arg_0__ , arg_1__ with
                   | z' , Tip => z'
                   | z' , Bin _ x l r => go (f x (go z' r)) l
                 end in
               match arg_0__ , arg_1__ with
                 | arg , _ => if GHC.Prim.seq arg false : bool
                              then GHC.Err.undefined
                              else j_3__
               end in
    go z.

Local Definition Foldable__Set__foldr' : forall {a} {b},
                                           (a -> b -> b) -> b -> Set_ a -> b :=
  fun {a} {b} => foldr'.

Definition lookupGE {a} `{GHC.Base.Ord a} : a -> Set_ a -> option a :=
  let goJust :=
    fix goJust arg_0__ arg_1__ arg_2__
          := let j_10__ :=
               match arg_0__ , arg_1__ , arg_2__ with
                 | _ , best , Tip => Some best
                 | x , best , Bin _ y l r => let scrut_4__ := GHC.Base.compare x y in
                                             match scrut_4__ with
                                               | Lt => goJust x y l
                                               | Eq => Some y
                                               | Gt => goJust x best r
                                             end
               end in
             match arg_0__ , arg_1__ , arg_2__ with
               | arg , _ , _ => if GHC.Prim.seq arg false : bool
                                then GHC.Err.undefined
                                else j_10__
             end in
  let goNothing :=
    fix goNothing arg_13__ arg_14__
          := let j_21__ :=
               match arg_13__ , arg_14__ with
                 | _ , Tip => None
                 | x , Bin _ y l r => let scrut_15__ := GHC.Base.compare x y in
                                      match scrut_15__ with
                                        | Lt => goJust x y l
                                        | Eq => Some y
                                        | Gt => goNothing x r
                                      end
               end in
             match arg_13__ , arg_14__ with
               | arg , _ => if GHC.Prim.seq arg false : bool
                            then GHC.Err.undefined
                            else j_21__
             end in
  goNothing.

Definition lookupGT {a} `{GHC.Base.Ord a} : a -> Set_ a -> option a :=
  let goJust :=
    fix goJust arg_0__ arg_1__ arg_2__
          := let j_6__ :=
               match arg_0__ , arg_1__ , arg_2__ with
                 | _ , best , Tip => Some best
                 | x , best , Bin _ y l r => let j_4__ := goJust x best r in
                                             if x GHC.Base.< y : bool
                                             then goJust x y l
                                             else j_4__
               end in
             match arg_0__ , arg_1__ , arg_2__ with
               | arg , _ , _ => if GHC.Prim.seq arg false : bool
                                then GHC.Err.undefined
                                else j_6__
             end in
  let goNothing :=
    fix goNothing arg_9__ arg_10__
          := let j_13__ :=
               match arg_9__ , arg_10__ with
                 | _ , Tip => None
                 | x , Bin _ y l r => let j_11__ := goNothing x r in
                                      if x GHC.Base.< y : bool
                                      then goJust x y l
                                      else j_11__
               end in
             match arg_9__ , arg_10__ with
               | arg , _ => if GHC.Prim.seq arg false : bool
                            then GHC.Err.undefined
                            else j_13__
             end in
  goNothing.

Definition lookupLE {a} `{GHC.Base.Ord a} : a -> Set_ a -> option a :=
  let goJust :=
    fix goJust arg_0__ arg_1__ arg_2__
          := let j_10__ :=
               match arg_0__ , arg_1__ , arg_2__ with
                 | _ , best , Tip => Some best
                 | x , best , Bin _ y l r => let scrut_4__ := GHC.Base.compare x y in
                                             match scrut_4__ with
                                               | Lt => goJust x best l
                                               | Eq => Some y
                                               | Gt => goJust x y r
                                             end
               end in
             match arg_0__ , arg_1__ , arg_2__ with
               | arg , _ , _ => if GHC.Prim.seq arg false : bool
                                then GHC.Err.undefined
                                else j_10__
             end in
  let goNothing :=
    fix goNothing arg_13__ arg_14__
          := let j_21__ :=
               match arg_13__ , arg_14__ with
                 | _ , Tip => None
                 | x , Bin _ y l r => let scrut_15__ := GHC.Base.compare x y in
                                      match scrut_15__ with
                                        | Lt => goNothing x l
                                        | Eq => Some y
                                        | Gt => goJust x y r
                                      end
               end in
             match arg_13__ , arg_14__ with
               | arg , _ => if GHC.Prim.seq arg false : bool
                            then GHC.Err.undefined
                            else j_21__
             end in
  goNothing.

Definition lookupLT {a} `{GHC.Base.Ord a} : a -> Set_ a -> option a :=
  let goJust :=
    fix goJust arg_0__ arg_1__ arg_2__
          := let j_6__ :=
               match arg_0__ , arg_1__ , arg_2__ with
                 | _ , best , Tip => Some best
                 | x , best , Bin _ y l r => let j_4__ := goJust x y r in
                                             if x GHC.Base.<= y : bool
                                             then goJust x best l
                                             else j_4__
               end in
             match arg_0__ , arg_1__ , arg_2__ with
               | arg , _ , _ => if GHC.Prim.seq arg false : bool
                                then GHC.Err.undefined
                                else j_6__
             end in
  let goNothing :=
    fix goNothing arg_9__ arg_10__
          := let j_13__ :=
               match arg_9__ , arg_10__ with
                 | _ , Tip => None
                 | x , Bin _ y l r => let j_11__ := goJust x y r in
                                      if x GHC.Base.<= y : bool
                                      then goNothing x l
                                      else j_11__
               end in
             match arg_9__ , arg_10__ with
               | arg , _ => if GHC.Prim.seq arg false : bool
                            then GHC.Err.undefined
                            else j_13__
             end in
  goNothing.

Definition mapMonotonic {a} {b} : (a -> b) -> Set_ a -> Set_ b :=
  fix mapMonotonic arg_0__ arg_1__
        := match arg_0__ , arg_1__ with
             | _ , Tip => Tip
             | f , Bin sz x l r => Bin sz (f x) (mapMonotonic f l) (mapMonotonic f r)
           end.

Definition member {a} `{GHC.Base.Ord a} : a -> Set_ a -> bool :=
  let go :=
    fix go arg_0__ arg_1__
          := let j_7__ :=
               match arg_0__ , arg_1__ with
                 | _ , Tip => false
                 | x , Bin _ y l r => let scrut_2__ := GHC.Base.compare x y in
                                      match scrut_2__ with
                                        | Lt => go x l
                                        | Gt => go x r
                                        | Eq => true
                                      end
               end in
             match arg_0__ , arg_1__ with
               | arg , _ => if GHC.Prim.seq arg false : bool
                            then GHC.Err.undefined
                            else j_7__
             end in
  go.

Definition notMember {a} `{GHC.Base.Ord a} : a -> Set_ a -> bool :=
  fun a t => negb GHC.Base.$ member a t.

Definition node : GHC.Base.String :=
  GHC.Base.hs_string__ "+--".

Definition null {a} : Set_ a -> bool :=
  fun arg_0__ => match arg_0__ with | Tip => true | Bin _ _ _ _ => false end.

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
  fun arg_0__ =>
    match arg_0__ with
      | Tip => GHC.Num.fromInteger 0
      | Bin sz _ _ _ => sz
    end.

Definition validsize {a} : Set_ a -> bool :=
  fun t =>
    let realsize :=
      fix realsize t'
            := match t' with
                 | Tip => Some (GHC.Num.fromInteger 0)
                 | Bin sz _ l r => let scrut_1__ := pair (realsize l) (realsize r) in
                                   match scrut_1__ with
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
    fix go arg_0__ arg_1__ arg_2__
          := let j_9__ :=
               match arg_0__ , arg_1__ , arg_2__ with
                 | _ , _ , Tip => None
                 | idx , x , Bin _ kx l r => let scrut_3__ := GHC.Base.compare x kx in
                                             match scrut_3__ with
                                               | Lt => go idx x l
                                               | Gt => go ((idx GHC.Num.+ size l) GHC.Num.+ GHC.Num.fromInteger 1) x r
                                               | Eq => Some GHC.Base.$! (idx GHC.Num.+ size l)
                                             end
               end in
             let j_11__ :=
               match arg_0__ , arg_1__ , arg_2__ with
                 | _ , arg , _ => if GHC.Prim.seq arg false : bool
                                  then GHC.Err.undefined
                                  else j_9__
               end in
             match arg_0__ , arg_1__ , arg_2__ with
               | arg , _ , _ => if GHC.Prim.seq arg false : bool
                                then GHC.Err.undefined
                                else j_11__
             end in
  go (GHC.Num.fromInteger 0).

Definition findIndex {a} `{GHC.Base.Ord a} : a -> Set_ a -> GHC.Num.Int :=
  let go {a} `{GHC.Base.Ord a} : GHC.Num.Int -> a -> Set_ a -> GHC.Num.Int :=
    fix go arg_0__ arg_1__ arg_2__
          := let j_10__ :=
               match arg_0__ , arg_1__ , arg_2__ with
                 | _ , _ , Tip => GHC.Err.error (GHC.Base.hs_string__
                                                "Set.findIndex: element is not in the set")
                 | idx , x , Bin _ kx l r => let scrut_4__ := GHC.Base.compare x kx in
                                             match scrut_4__ with
                                               | Lt => go idx x l
                                               | Gt => go ((idx GHC.Num.+ size l) GHC.Num.+ GHC.Num.fromInteger 1) x r
                                               | Eq => idx GHC.Num.+ size l
                                             end
               end in
             let j_12__ :=
               match arg_0__ , arg_1__ , arg_2__ with
                 | _ , arg , _ => if GHC.Prim.seq arg false : bool
                                  then GHC.Err.undefined
                                  else j_10__
               end in
             match arg_0__ , arg_1__ , arg_2__ with
               | arg , _ , _ => if GHC.Prim.seq arg false : bool
                                then GHC.Err.undefined
                                else j_12__
             end in
  go (GHC.Num.fromInteger 0).

Definition elemAt {a} : GHC.Num.Int -> Set_ a -> a :=
  fix elemAt arg_0__ arg_1__
        := let j_9__ :=
             match arg_0__ , arg_1__ with
               | _ , Tip => GHC.Err.error (GHC.Base.hs_string__
                                          "Set.elemAt: index out of range")
               | i , Bin _ x l r => let sizeL := size l in
                                    let scrut_4__ := GHC.Base.compare i sizeL in
                                    match scrut_4__ with
                                      | Lt => elemAt i l
                                      | Gt => elemAt ((i GHC.Num.- sizeL) GHC.Num.- GHC.Num.fromInteger 1) r
                                      | Eq => x
                                    end
             end in
           match arg_0__ , arg_1__ with
             | arg , _ => if GHC.Prim.seq arg false : bool
                          then GHC.Err.undefined
                          else j_9__
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
                 | Bin rs rx (Bin rls rlx rll rlr as rl) (Bin rrs _ _ _ as rr) => let j_4__ :=
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
                                                                                  else j_4__
               end
      | Bin ls _ _ _ => match r with
                          | Tip => Bin (GHC.Num.fromInteger 1 GHC.Num.+ ls) x l Tip
                          | Bin rs rx rl rr => let j_9__ :=
                                                 Bin ((GHC.Num.fromInteger 1 GHC.Num.+ ls) GHC.Num.+ rs) x l r in
                                               if rs GHC.Base.> (delta GHC.Num.* ls) : bool
                                               then let scrut_10__ := pair rl rr in
                                                    let j_12__ :=
                                                      match scrut_10__ with
                                                        | pair _ _ => GHC.Err.error (GHC.Base.hs_string__
                                                                                    "Failure in Data.Map.balanceR")
                                                      end in
                                                    match scrut_10__ with
                                                      | pair (Bin rls rlx rll rlr) (Bin rrs _ _ _) => let j_13__ :=
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
                                                                                                      else j_13__
                                                      | _ => j_12__
                                                    end
                                               else j_9__
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
  fun arg_0__ =>
    match arg_0__ with
      | Tip => None
      | x => Some (deleteFindMin x)
    end.

Definition deleteMin {a} : Set_ a -> Set_ a :=
  fix deleteMin arg_0__
        := match arg_0__ with
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
                 | Bin ls lx (Bin lls _ _ _ as ll) (Bin lrs lrx lrl lrr as lr) => let j_4__ :=
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
                                                                                  else j_4__
               end
      | Bin rs _ _ _ => match l with
                          | Tip => Bin (GHC.Num.fromInteger 1 GHC.Num.+ rs) x Tip r
                          | Bin ls lx ll lr => let j_9__ :=
                                                 Bin ((GHC.Num.fromInteger 1 GHC.Num.+ ls) GHC.Num.+ rs) x l r in
                                               if ls GHC.Base.> (delta GHC.Num.* rs) : bool
                                               then let scrut_10__ := pair ll lr in
                                                    let j_12__ :=
                                                      match scrut_10__ with
                                                        | pair _ _ => GHC.Err.error (GHC.Base.hs_string__
                                                                                    "Failure in Data.Map.balanceL")
                                                      end in
                                                    match scrut_10__ with
                                                      | pair (Bin lls _ _ _) (Bin lrs lrx lrl lrr) => let j_13__ :=
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
                                                                                                      else j_13__
                                                      | _ => j_12__
                                                    end
                                               else j_9__
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
  fun arg_0__ =>
    match arg_0__ with
      | Tip => None
      | x => Some (deleteFindMax x)
    end.

Definition deleteMax {a} : Set_ a -> Set_ a :=
  fix deleteMax arg_0__
        := match arg_0__ with
             | Bin _ _ l Tip => l
             | Bin _ x l r => balanceL x l (deleteMax r)
             | Tip => Tip
           end.

Definition insert {a} `{GHC.Base.Ord a} : a -> Set_ a -> Set_ a :=
  let go {a} `{GHC.Base.Ord a} : a -> Set_ a -> Set_ a :=
    fix go arg_0__ arg_1__
          := let j_9__ :=
               match arg_0__ , arg_1__ with
                 | x , Tip => singleton x
                 | x , Bin sz y l r => let scrut_3__ := GHC.Base.compare x y in
                                       match scrut_3__ with
                                         | Lt => balanceL y (go x l) r
                                         | Gt => balanceR y l (go x r)
                                         | Eq => Bin sz x l r
                                       end
               end in
             match arg_0__ , arg_1__ with
               | arg , _ => if GHC.Prim.seq arg false : bool
                            then GHC.Err.undefined
                            else j_9__
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
    fix go arg_0__ arg_1__
          := let j_8__ :=
               match arg_0__ , arg_1__ with
                 | x , Tip => singleton x
                 | x , (Bin _ y l r as t) => let scrut_3__ := GHC.Base.compare x y in
                                             match scrut_3__ with
                                               | Lt => balanceL y (go x l) r
                                               | Gt => balanceR y l (go x r)
                                               | Eq => t
                                             end
               end in
             match arg_0__ , arg_1__ with
               | arg , _ => if GHC.Prim.seq arg false : bool
                            then GHC.Err.undefined
                            else j_8__
             end in
  go.

Program Fixpoint link {a} (arg_0__ : a) (arg_1__ : Set_ a) (arg_2__ : Set_
                                                                      a) { measure (Nat.add (set_size arg_1__) (set_size
                                                                                            arg_2__)) } : Set_ a :=
match arg_0__ , arg_1__ , arg_2__ with
  | x , Tip , r => insertMin x r
  | x , l , Tip => insertMax x l
  | x , (Bin sizeL y ly ry as l) , (Bin sizeR z lz rz as r) => let j_5__ :=
                                                                 bin x l r in
                                                               let j_6__ :=
                                                                 if (delta GHC.Num.* sizeR) GHC.Base.< sizeL : bool
                                                                 then balanceR y ly (link x ry r)
                                                                 else j_5__ in
                                                               if (delta GHC.Num.* sizeL) GHC.Base.< sizeR : bool
                                                               then balanceL z (link x l lz) rz
                                                               else j_6__
end.
Solve Obligations with (termination_by_omega).

Definition filterGt {a} `{GHC.Base.Ord a} : MaybeS a -> Set_ a -> Set_ a :=
  fun arg_0__ arg_1__ =>
    match arg_0__ , arg_1__ with
      | NothingS , t => t
      | JustS b , t => let filter' :=
                         fix filter' arg_2__ arg_3__
                               := match arg_2__ , arg_3__ with
                                    | _ , Tip => Tip
                                    | b' , Bin _ x l r => let scrut_4__ := GHC.Base.compare b' x in
                                                          match scrut_4__ with
                                                            | Lt => link x (filter' b' l) r
                                                            | Eq => r
                                                            | Gt => filter' b' r
                                                          end
                                  end in
                       filter' b t
    end.

Definition filterLt {a} `{GHC.Base.Ord a} : MaybeS a -> Set_ a -> Set_ a :=
  fun arg_0__ arg_1__ =>
    match arg_0__ , arg_1__ with
      | NothingS , t => t
      | JustS b , t => let filter' :=
                         fix filter' arg_2__ arg_3__
                               := match arg_2__ , arg_3__ with
                                    | _ , Tip => Tip
                                    | b' , Bin _ x l r => let scrut_4__ := GHC.Base.compare x b' in
                                                          match scrut_4__ with
                                                            | Lt => link x l (filter' b' r)
                                                            | Eq => l
                                                            | Gt => filter' b' l
                                                          end
                                  end in
                       filter' b t
    end.

Definition fromDistinctAscList {a} : list a -> Set_ a :=
  fun arg_0__ =>
    match arg_0__ with
      | nil => Tip
      | cons x0 xs0 => let create :=
                         unsafeFix (fun create arg_1__ arg_2__ =>
                                     let j_12__ :=
                                       match arg_1__ , arg_2__ with
                                         | _ , nil => pair Tip nil
                                         | s , (cons x xs' as xs) => let j_10__ :=
                                                                       let scrut_4__ :=
                                                                         create (Data.Bits.shiftR s (GHC.Num.fromInteger
                                                                                                  1)) xs in
                                                                       match scrut_4__ with
                                                                         | (pair _ nil as res) => res
                                                                         | pair l (cons y ys) => let scrut_5__ :=
                                                                                                   create
                                                                                                   (Data.Bits.shiftR s
                                                                                                                     (GHC.Num.fromInteger
                                                                                                                     1))
                                                                                                   ys in
                                                                                                 match scrut_5__ with
                                                                                                   | pair r zs => pair
                                                                                                                  (link
                                                                                                                  y l r)
                                                                                                                  zs
                                                                                                 end
                                                                       end in
                                                                     if s GHC.Base.== GHC.Num.fromInteger 1 : bool
                                                                     then pair (Bin (GHC.Num.fromInteger 1) x Tip Tip)
                                                                               xs'
                                                                     else j_10__
                                       end in
                                     match arg_1__ , arg_2__ with
                                       | arg , _ => if GHC.Prim.seq arg false : bool
                                                    then GHC.Err.undefined
                                                    else j_12__
                                     end) in
                       let go :=
                         unsafeFix (fun go arg_15__ arg_16__ arg_17__ =>
                                     let j_22__ :=
                                       match arg_15__ , arg_16__ , arg_17__ with
                                         | _ , t , nil => t
                                         | s , l , cons x xs => let scrut_18__ := create s xs in
                                                                match scrut_18__ with
                                                                  | pair r ys => go (Data.Bits.shiftL s
                                                                                                      (GHC.Num.fromInteger
                                                                                                      1)) (link x l r)
                                                                                 ys
                                                                end
                                       end in
                                     match arg_15__ , arg_16__ , arg_17__ with
                                       | arg , _ , _ => if GHC.Prim.seq arg false : bool
                                                        then GHC.Err.undefined
                                                        else j_22__
                                     end) in
                       go (GHC.Num.fromInteger 1 : GHC.Num.Int) (Bin (GHC.Num.fromInteger 1) x0 Tip
                                                                Tip) xs0
    end.

Definition fromAscList {a} `{GHC.Base.Eq_ a} : list a -> Set_ a :=
  fun xs =>
    let combineEq' :=
      unsafeFix (fun combineEq' arg_0__ arg_1__ =>
                  match arg_0__ , arg_1__ with
                    | z , nil => cons z nil
                    | z , cons x xs' => let j_3__ := cons z (combineEq' x xs') in
                                        if z GHC.Base.== x : bool
                                        then combineEq' z xs'
                                        else j_3__
                  end) in
    let combineEq :=
      fun xs' =>
        match xs' with
          | nil => nil
          | cons x nil => cons x nil
          | cons x xx => combineEq' x xx
        end in
    fromDistinctAscList (combineEq xs).

Definition fromList {a} `{GHC.Base.Ord a} : list a -> Set_ a :=
  fun arg_0__ =>
    match arg_0__ with
      | nil => Tip
      | cons x nil => Bin (GHC.Num.fromInteger 1) x Tip Tip
      | cons x0 xs0 => let fromList' :=
                         fun t0 xs =>
                           let ins := fun t x => insert x t in Data.Foldable.foldl ins t0 xs in
                       let not_ordered :=
                         fun arg_4__ arg_5__ =>
                           match arg_4__ , arg_5__ with
                             | _ , nil => false
                             | x , cons y _ => x GHC.Base.>= y
                           end in
                       let create :=
                         unsafeFix (fun create arg_8__ arg_9__ =>
                                     let j_21__ :=
                                       match arg_8__ , arg_9__ with
                                         | _ , nil => pair (pair Tip nil) nil
                                         | s , (cons x xss as xs) => let j_19__ :=
                                                                       let scrut_11__ :=
                                                                         create (Data.Bits.shiftR s (GHC.Num.fromInteger
                                                                                                  1)) xs in
                                                                       match scrut_11__ with
                                                                         | (pair (pair _ nil) _ as res) => res
                                                                         | pair (pair l (cons y nil)) zs => pair (pair
                                                                                                                 (insertMax
                                                                                                                 y l)
                                                                                                                 nil) zs
                                                                         | pair (pair l (cons y yss as ys)) _ =>
                                                                           let j_16__ :=
                                                                             let scrut_13__ :=
                                                                               create (Data.Bits.shiftR s
                                                                                                        (GHC.Num.fromInteger
                                                                                                        1)) yss in
                                                                             match scrut_13__ with
                                                                               | pair (pair r zs) ws => pair (pair (link
                                                                                                                   y l
                                                                                                                   r)
                                                                                                                   zs)
                                                                                                             ws
                                                                             end in
                                                                           if not_ordered y yss : bool
                                                                           then pair (pair l nil) ys
                                                                           else j_16__
                                                                       end in
                                                                     if s GHC.Base.== GHC.Num.fromInteger 1 : bool
                                                                     then if not_ordered x xss : bool
                                                                          then pair (pair (Bin (GHC.Num.fromInteger 1) x
                                                                                          Tip Tip) nil) xss
                                                                          else pair (pair (Bin (GHC.Num.fromInteger 1) x
                                                                                          Tip Tip) xss) nil
                                                                     else j_19__
                                       end in
                                     match arg_8__ , arg_9__ with
                                       | arg , _ => if GHC.Prim.seq arg false : bool
                                                    then GHC.Err.undefined
                                                    else j_21__
                                     end) in
                       let go :=
                         unsafeFix (fun go arg_24__ arg_25__ arg_26__ =>
                                     let j_34__ :=
                                       match arg_24__ , arg_25__ , arg_26__ with
                                         | _ , t , nil => t
                                         | _ , t , cons x nil => insertMax x t
                                         | s , l , (cons x xss as xs) => let j_32__ :=
                                                                           let scrut_28__ := create s xss in
                                                                           match scrut_28__ with
                                                                             | pair (pair r ys) nil => go
                                                                                                       (Data.Bits.shiftL
                                                                                                       s
                                                                                                       (GHC.Num.fromInteger
                                                                                                       1)) (link x l r)
                                                                                                       ys
                                                                             | pair (pair r _) ys => fromList' (link x l
                                                                                                               r) ys
                                                                           end in
                                                                         if not_ordered x xss : bool
                                                                         then fromList' l xs
                                                                         else j_32__
                                       end in
                                     match arg_24__ , arg_25__ , arg_26__ with
                                       | arg , _ , _ => if GHC.Prim.seq arg false : bool
                                                        then GHC.Err.undefined
                                                        else j_34__
                                     end) in
                       let j_37__ :=
                         go (GHC.Num.fromInteger 1 : GHC.Num.Int) (Bin (GHC.Num.fromInteger 1) x0 Tip
                                                                  Tip) xs0 in
                       if not_ordered x0 xs0 : bool
                       then fromList' (Bin (GHC.Num.fromInteger 1) x0 Tip Tip) xs0
                       else j_37__
    end.

Definition map {b} {a} `{GHC.Base.Ord b} : (a -> b) -> Set_ a -> Set_ b :=
  fun f => fromList GHC.Base.∘ (GHC.Base.map f GHC.Base.∘ toList).

Definition split {a} `{GHC.Base.Ord a} : a -> Set_ a -> (Set_ a * Set_
                                         a)%type :=
  fun x0 t0 =>
    let go :=
      fix go arg_0__ arg_1__
            := match arg_0__ , arg_1__ with
                 | _ , Tip => (pair Tip Tip)
                 | x , Bin _ y l r => let scrut_3__ := GHC.Base.compare x y in
                                      match scrut_3__ with
                                        | Lt => match go x l with
                                                  | pair lt gt => (pair lt (link y gt r))
                                                end
                                        | Gt => match go x r with
                                                  | pair lt gt => (pair (link y l lt) gt)
                                                end
                                        | Eq => (pair l r)
                                      end
               end in
    id GHC.Base.$ go x0 t0.

Definition splitMember {a} `{GHC.Base.Ord a} : a -> Set_ a -> (Set_ a * bool *
                                               Set_ a)%type :=
  fix splitMember arg_0__ arg_1__
        := match arg_0__ , arg_1__ with
             | _ , Tip => pair (pair Tip false) Tip
             | x , Bin _ y l r => let scrut_3__ := GHC.Base.compare x y in
                                  match scrut_3__ with
                                    | Lt => match splitMember x l with
                                              | pair (pair lt found) gt => let gt' := link y gt r in
                                                                           GHC.Prim.seq gt' (pair (pair lt found) gt')
                                            end
                                    | Gt => match splitMember x r with
                                              | pair (pair lt found) gt => let lt' := link y l lt in
                                                                           GHC.Prim.seq lt' (pair (pair lt' found) gt)
                                            end
                                    | Eq => pair (pair l true) r
                                  end
           end.

Definition isSubsetOfX {a} `{GHC.Base.Ord a} : Set_ a -> Set_ a -> bool :=
  fix isSubsetOfX arg_0__ arg_1__
        := match arg_0__ , arg_1__ with
             | Tip , _ => true
             | _ , Tip => false
             | Bin _ x l r , t => match splitMember x t with
                                    | pair (pair lt found) gt => andb found (andb (isSubsetOfX l lt) (isSubsetOfX r
                                                                                  gt))
                                  end
           end.

Definition glue {a} : Set_ a -> Set_ a -> Set_ a :=
  fun arg_0__ arg_1__ =>
    match arg_0__ , arg_1__ with
      | Tip , r => r
      | l , Tip => l
      | l , r => let j_3__ :=
                   match deleteFindMin r with
                     | pair m r' => balanceL m l r'
                   end in
                 if size l GHC.Base.> size r : bool
                 then match deleteFindMax l with
                        | pair m l' => balanceR m l' r
                      end
                 else j_3__
    end.

Definition delete {a} `{GHC.Base.Ord a} : a -> Set_ a -> Set_ a :=
  let go {a} `{GHC.Base.Ord a} : a -> Set_ a -> Set_ a :=
    fix go arg_0__ arg_1__
          := let j_8__ :=
               match arg_0__ , arg_1__ with
                 | _ , Tip => Tip
                 | x , Bin _ y l r => let scrut_2__ := GHC.Base.compare x y in
                                      match scrut_2__ with
                                        | Lt => balanceR y (go x l) r
                                        | Gt => balanceL y l (go x r)
                                        | Eq => glue l r
                                      end
               end in
             match arg_0__ , arg_1__ with
               | arg , _ => if GHC.Prim.seq arg false : bool
                            then GHC.Err.undefined
                            else j_8__
             end in
  go.

Program Fixpoint merge {a} (arg_0__ : Set_ a) (arg_1__ : Set_
                                                         a) { measure (Nat.add (set_size arg_0__) (set_size
                                                                               arg_1__)) } : Set_ a :=
match arg_0__ , arg_1__ with
  | Tip , r => r
  | l , Tip => l
  | (Bin sizeL x lx rx as l) , (Bin sizeR y ly ry as r) => let j_2__ :=
                                                             glue l r in
                                                           let j_3__ :=
                                                             if (delta GHC.Num.* sizeR) GHC.Base.< sizeL : bool
                                                             then balanceR x lx (merge rx r)
                                                             else j_2__ in
                                                           if (delta GHC.Num.* sizeL) GHC.Base.< sizeR : bool
                                                           then balanceL y (merge l ly) ry
                                                           else j_3__
end.
Solve Obligations with (termination_by_omega).

Definition filter {a} : (a -> bool) -> Set_ a -> Set_ a :=
  fix filter arg_0__ arg_1__
        := match arg_0__ , arg_1__ with
             | _ , Tip => Tip
             | p , Bin _ x l r => let j_2__ := merge (filter p l) (filter p r) in
                                  if p x : bool
                                  then link x (filter p l) (filter p r)
                                  else j_2__
           end.

Definition partition {a} : (a -> bool) -> Set_ a -> (Set_ a * Set_ a)%type :=
  fun p0 t0 =>
    let go :=
      fix go arg_0__ arg_1__
            := match arg_0__ , arg_1__ with
                 | _ , Tip => (pair Tip Tip)
                 | p , Bin _ x l r => let scrut_3__ := pair (go p l) (go p r) in
                                      match scrut_3__ with
                                        | pair (pair l1 l2) (pair r1 r2) => let j_4__ :=
                                                                              pair (merge l1 r1) (link x l2 r2) in
                                                                            if p x : bool
                                                                            then pair (link x l1 r1) (merge l2 r2)
                                                                            else j_4__
                                      end
               end in
    id GHC.Base.$ go p0 t0.

Definition deleteAt {a} : GHC.Num.Int -> Set_ a -> Set_ a :=
  fix deleteAt i t
        := GHC.Prim.seq i (match t with
                          | Tip => GHC.Err.error (GHC.Base.hs_string__ "Set.deleteAt: index out of range")
                          | Bin _ x l r => let sizeL := size l in
                                           let scrut_2__ := GHC.Base.compare i sizeL in
                                           match scrut_2__ with
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
  fun arg_0__ arg_1__ arg_2__ =>
    match arg_0__ , arg_1__ , arg_2__ with
      | NothingS , NothingS , t => t
      | JustS lx , NothingS , t => let greater :=
                                     fix greater arg_3__ arg_4__
                                           := let j_5__ := match arg_3__ , arg_4__ with | _ , t' => t' end in
                                              match arg_3__ , arg_4__ with
                                                | lo , Bin _ x _ r => if x GHC.Base.<= lo : bool
                                                                      then greater lo r
                                                                      else j_5__
                                                | _ , _ => j_5__
                                              end in
                                   greater lx t
      | NothingS , JustS hx , t => let lesser :=
                                     fix lesser arg_9__ arg_10__
                                           := let j_11__ := match arg_9__ , arg_10__ with | _ , t' => t' end in
                                              match arg_9__ , arg_10__ with
                                                | hi , Bin _ x l _ => if x GHC.Base.>= hi : bool
                                                                      then lesser hi l
                                                                      else j_11__
                                                | _ , _ => j_11__
                                              end in
                                   lesser hx t
      | JustS lx , JustS hx , t => let middle :=
                                     fix middle arg_15__ arg_16__ arg_17__
                                           := let j_18__ :=
                                                match arg_15__ , arg_16__ , arg_17__ with
                                                  | _ , _ , t' => t'
                                                end in
                                              let j_20__ :=
                                                match arg_15__ , arg_16__ , arg_17__ with
                                                  | lo , hi , Bin _ x l _ => if x GHC.Base.>= hi : bool
                                                                             then middle lo hi l
                                                                             else j_18__
                                                  | _ , _ , _ => j_18__
                                                end in
                                              match arg_15__ , arg_16__ , arg_17__ with
                                                | lo , hi , Bin _ x _ r => if x GHC.Base.<= lo : bool
                                                                           then middle lo hi r
                                                                           else j_20__
                                                | _ , _ , _ => j_20__
                                              end in
                                   middle lx hx t
    end.

Definition hedgeUnion {a} `{GHC.Base.Ord a} : MaybeS a -> MaybeS a -> Set_
                                              a -> Set_ a -> Set_ a :=
  fix hedgeUnion arg_0__ arg_1__ arg_2__ arg_3__
        := match arg_0__ , arg_1__ , arg_2__ , arg_3__ with
             | _ , _ , t1 , Tip => t1
             | blo , bhi , Tip , Bin _ x l r => link x (filterGt blo l) (filterLt bhi r)
             | _ , _ , t1 , Bin _ x Tip Tip => insertR x t1
             | blo , bhi , Bin _ x l r , t2 => let bmi := JustS x in
                                               link x (hedgeUnion blo bmi l (trim blo bmi t2)) (hedgeUnion bmi bhi r
                                                                                               (trim bmi bhi t2))
           end.

Definition union {a} `{GHC.Base.Ord a} : Set_ a -> Set_ a -> Set_ a :=
  fun arg_0__ arg_1__ =>
    match arg_0__ , arg_1__ with
      | Tip , t2 => t2
      | t1 , Tip => t1
      | t1 , t2 => hedgeUnion NothingS NothingS t1 t2
    end.

Definition unions {a} `{GHC.Base.Ord a} : list (Set_ a) -> Set_ a :=
  Data.Foldable.foldl union empty.

Definition hedgeDiff {a} `{GHC.Base.Ord a} : MaybeS a -> MaybeS a -> Set_
                                             a -> Set_ a -> Set_ a :=
  fix hedgeDiff arg_0__ arg_1__ arg_2__ arg_3__
        := match arg_0__ , arg_1__ , arg_2__ , arg_3__ with
             | _ , _ , Tip , _ => Tip
             | blo , bhi , Bin _ x l r , Tip => link x (filterGt blo l) (filterLt bhi r)
             | blo , bhi , t , Bin _ x l r => let bmi := JustS x in
                                              merge (hedgeDiff blo bmi (trim blo bmi t) l) (hedgeDiff bmi bhi (trim bmi
                                                                                                              bhi t) r)
           end.

Definition difference {a} `{GHC.Base.Ord a} : Set_ a -> Set_ a -> Set_ a :=
  fun arg_0__ arg_1__ =>
    match arg_0__ , arg_1__ with
      | Tip , _ => Tip
      | t1 , Tip => t1
      | t1 , t2 => hedgeDiff NothingS NothingS t1 t2
    end.

Definition op_zrzr__ {a} `{GHC.Base.Ord a} : Set_ a -> Set_ a -> Set_ a :=
  fun m1 m2 => difference m1 m2.

Notation "'_\\_'" := (op_zrzr__).

Infix "\\" := (_\\_) (at level 99).

Definition hedgeInt {a} `{GHC.Base.Ord a} : MaybeS a -> MaybeS a -> Set_
                                            a -> Set_ a -> Set_ a :=
  fix hedgeInt arg_0__ arg_1__ arg_2__ arg_3__
        := match arg_0__ , arg_1__ , arg_2__ , arg_3__ with
             | _ , _ , _ , Tip => Tip
             | _ , _ , Tip , _ => Tip
             | blo , bhi , Bin _ x l r , t2 => let bmi := JustS x in
                                               let r' := hedgeInt bmi bhi r (trim bmi bhi t2) in
                                               let l' := hedgeInt blo bmi l (trim blo bmi t2) in
                                               if member x t2 : bool
                                               then link x l' r'
                                               else merge l' r'
           end.

Definition intersection {a} `{GHC.Base.Ord a} : Set_ a -> Set_ a -> Set_ a :=
  fun arg_0__ arg_1__ =>
    match arg_0__ , arg_1__ with
      | Tip , _ => Tip
      | _ , Tip => Tip
      | t1 , t2 => hedgeInt NothingS NothingS t1 t2
    end.

Definition withBar : list GHC.Base.String -> list GHC.Base.String :=
  fun bars => cons (GHC.Base.hs_string__ "|  ") bars.

Definition withEmpty : list GHC.Base.String -> list GHC.Base.String :=
  fun bars => cons (GHC.Base.hs_string__ "   ") bars.

Module Notations.
Notation "'_Data.Set.Base.\\_'" := (op_zrzr__).
Infix "Data.Set.Base.\\" := (_\\_) (at level 99).
End Notations.

(* Unbound variables:
     Eq Gt Lt None Some andb bool comparison cons false id list negb nil op_zt__
     option orb pair set_size true Data.Bits.shiftL Data.Bits.shiftR
     Data.Foldable.Foldable Data.Foldable.foldl GHC.Base.Eq_ GHC.Base.Monoid
     GHC.Base.Ord GHC.Base.String GHC.Base.compare GHC.Base.const GHC.Base.flip
     GHC.Base.map GHC.Base.mappend GHC.Base.mempty GHC.Base.op_z2218U__
     GHC.Base.op_zd__ GHC.Base.op_zdzn__ GHC.Base.op_zeze__ GHC.Base.op_zg__
     GHC.Base.op_zgze__ GHC.Base.op_zl__ GHC.Base.op_zlze__ GHC.Base.op_zsze__
     GHC.Err.error GHC.Err.undefined GHC.Num.Int GHC.Num.Num GHC.Num.op_zm__
     GHC.Num.op_zp__ GHC.Num.op_zt__ GHC.Prim.seq Nat.add
*)
