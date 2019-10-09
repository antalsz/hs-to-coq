(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Coq.Program.Tactics.
Require Coq.Program.Wf.

(* Preamble *)

Require Coq.ZArith.BinInt.
Import Coq.ZArith.BinInt.Z.

Require Data.Set.Internal.
Require GHC.Num.
Require Test.QuickCheck.Property.
Require SetProofs.

Instance Arbitrary_Set {a} `{Base.Eq_ a} `{Base.Ord a} : Test.QuickCheck.Property.Arbitrary (Data.Set.Internal.Set_ a) :=
  { arbitrary := Test.QuickCheck.Property.MkGen SetProofs.WF }.

Require GHC.Enum.
Notation enumFromTo := GHC.Enum.enumFromTo.

Coercion is_true : bool >-> Sortclass.
Coercion of_N : Coq.Numbers.BinNums.N >-> Coq.Numbers.BinNums.Z.

Class IsInt (a : Type) `{Integral a} `{Test.QuickCheck.Property.Arbitrary a} :=
  Mk_IsInt { fromIntF {f : Type -> Type} : f Coq.Numbers.BinNums.N -> f a }.

(* Converted imports: *)

Require Coq.Init.Datatypes.
Require Coq.Lists.List.
Require Coq.Numbers.BinNums.
Require Data.Either.
Require Data.Foldable.
Require Data.Functor.Identity.
Require Data.IntSet.Internal.
Require Data.OldList.
Require Data.Set.Internal.
Require GHC.Base.
Require GHC.Enum.
Require GHC.Err.
Require GHC.List.
Require GHC.Num.
Require GHC.Real.
Require GHC.Tuple.
Require Test.QuickCheck.Arbitrary.
Require Test.QuickCheck.Function.
Require Test.QuickCheck.Gen.
Require Test.QuickCheck.Property.
Import Data.OldList.Notations.
Import GHC.Base.Notations.
Import GHC.Num.Notations.
Import Test.QuickCheck.Property.Notations.

(* Converted type declarations: *)

Inductive TwoSets : Type
  := | Mk_TwoSets
   : (Data.Set.Internal.Set_ Coq.Numbers.BinNums.N) ->
     (Data.Set.Internal.Set_ Coq.Numbers.BinNums.N) -> TwoSets.

Inductive TwoLists a : Type := | Mk_TwoLists : list a -> list a -> TwoLists a.

Inductive Options2 : Type
  := | One2 : Options2
  |  Two2 : Options2
  |  Both2 : Options2.

Inductive OddEq a : Type := | Mk_OddEq : a -> bool -> OddEq a.

Arguments Mk_TwoLists {_} _ _.

Arguments Mk_OddEq {_} _ _.

Instance Default__Options2 : GHC.Err.Default Options2 :=
  GHC.Err.Build_Default _ One2.

(* Converted value declarations: *)

Definition toIntSet
   : Data.Set.Internal.Set_ Coq.Numbers.BinNums.N ->
     Data.IntSet.Internal.IntSet :=
  Data.IntSet.Internal.fromList GHC.Base.∘ Data.Set.Internal.toList.

Definition prop_take
   : Coq.Numbers.BinNums.N ->
     Data.Set.Internal.Set_ Coq.Numbers.BinNums.N -> Prop :=
  fun n xs =>
    let taken := Data.Set.Internal.take n xs in
    Data.Set.Internal.valid taken Test.QuickCheck.Property..&&.(**)
    (taken Test.QuickCheck.Property.===
     Data.Set.Internal.fromDistinctAscList (GHC.List.take n (Data.Set.Internal.toList
                                                             xs))).

Definition prop_splitRoot
   : Data.Set.Internal.Set_ Coq.Numbers.BinNums.N -> bool :=
  fun s =>
    let loop :=
      fun arg_0__ =>
        match arg_0__ with
        | nil => true
        | cons s1 rst =>
            Data.Foldable.null (Coq.Lists.List.flat_map (fun x =>
                                                           Coq.Lists.List.flat_map (fun y =>
                                                                                      if x GHC.Base.> y : bool
                                                                                      then cons (pair x y) nil else
                                                                                      nil) (Data.Set.Internal.toList
                                                                                    (Data.Set.Internal.unions rst)))
                                                        (Data.Set.Internal.toList s1))
        end in
    let ls := Data.Set.Internal.splitRoot s in
    andb (loop ls) (s GHC.Base.== Data.Set.Internal.unions ls).

Definition prop_splitMember
   : Data.Set.Internal.Set_ Coq.Numbers.BinNums.N ->
     Coq.Numbers.BinNums.N -> bool :=
  fun s i =>
    let 'pair (pair s1 t) s2 := Data.Set.Internal.splitMember i s in
    andb (Data.Foldable.all (fun arg_1__ => arg_1__ GHC.Base.< i)
          (Data.Set.Internal.toList s1)) (andb (Data.Foldable.all (fun arg_2__ =>
                                                                     arg_2__ GHC.Base.> i) (Data.Set.Internal.toList
                                                                                            s2)) (andb (t GHC.Base.==
                                                                                                        Data.Set.Internal.member
                                                                                                        i s)
                                                                                                       (Data.Set.Internal.delete
                                                                                                        i s GHC.Base.==
                                                                                                        Data.Set.Internal.union
                                                                                                        s1 s2))).

Definition prop_splitAt
   : Coq.Numbers.BinNums.N ->
     Data.Set.Internal.Set_ Coq.Numbers.BinNums.N -> Prop :=
  fun n xs =>
    let 'pair taken dropped := Data.Set.Internal.splitAt n xs in
    Data.Set.Internal.valid taken Test.QuickCheck.Property..&&.(**)
    (Data.Set.Internal.valid dropped Test.QuickCheck.Property..&&.(**)
     ((taken Test.QuickCheck.Property.=== Data.Set.Internal.take n xs)
      Test.QuickCheck.Property..&&.(**)
      (dropped Test.QuickCheck.Property.=== Data.Set.Internal.drop n xs))).

Definition prop_split
   : Data.Set.Internal.Set_ Coq.Numbers.BinNums.N ->
     Coq.Numbers.BinNums.N -> bool :=
  fun s i =>
    let 'pair s1 s2 := Data.Set.Internal.split i s in
    andb (Data.Foldable.all (fun arg_1__ => arg_1__ GHC.Base.< i)
          (Data.Set.Internal.toList s1)) (andb (Data.Foldable.all (fun arg_2__ =>
                                                                     arg_2__ GHC.Base.> i) (Data.Set.Internal.toList
                                                                                            s2))
                                               (Data.Set.Internal.delete i s GHC.Base.==
                                                Data.Set.Internal.union s1 s2)).

Definition prop_size : Data.Set.Internal.Set_ Coq.Numbers.BinNums.N -> bool :=
  fun s =>
    Data.Set.Internal.size s GHC.Base.==
    Data.Foldable.length (Data.Set.Internal.toList s).

Definition prop_powerSet
   : Data.Set.Internal.Set_ Coq.Numbers.BinNums.N -> Prop :=
  fun xs =>
    let fix lps arg_0__
              := match arg_0__ with
                 | nil => cons nil nil
                 | cons y ys =>
                     Coq.Init.Datatypes.app (GHC.Base.fmap (fun arg_2__ => cons y arg_2__) (lps ys))
                                            (lps ys)
                 end in
    let xs' := Data.Set.Internal.take #10 xs in
    let ps := Data.Set.Internal.powerSet xs' in
    let ps' :=
      (Data.Set.Internal.fromList GHC.Base.∘ GHC.Base.fmap Data.Set.Internal.fromList)
      (lps (Data.Set.Internal.toList xs')) in
    Data.Set.Internal.valid ps Test.QuickCheck.Property..&&.(**)
    (ps Test.QuickCheck.Property.=== ps').

Definition prop_partition
   : Data.Set.Internal.Set_ Coq.Numbers.BinNums.N ->
     Coq.Numbers.BinNums.N -> bool :=
  fun s i =>
    let 'pair s1 s2 := Data.Set.Internal.partition GHC.Real.odd s in
    andb (Data.Foldable.all GHC.Real.odd (Data.Set.Internal.toList s1)) (andb
          (Data.Foldable.all GHC.Real.even (Data.Set.Internal.toList s2)) (s GHC.Base.==
           Data.Set.Internal.union s1 s2)).

Definition prop_ord : TwoSets -> bool :=
  fun '(Mk_TwoSets s1 s2) =>
    GHC.Base.compare s1 s2 GHC.Base.==
    GHC.Base.compare (Data.Set.Internal.toList s1) (Data.Set.Internal.toList s2).

Definition prop_mapMonotonic
   : Data.Set.Internal.Set_ Coq.Numbers.BinNums.N -> Prop :=
  fun s =>
    Data.Set.Internal.mapMonotonic GHC.Base.id s Test.QuickCheck.Property.=== s.

Definition prop_map2
   : Test.QuickCheck.Function.Fun Coq.Numbers.BinNums.N Coq.Numbers.BinNums.N ->
     Test.QuickCheck.Function.Fun Coq.Numbers.BinNums.N Coq.Numbers.BinNums.N ->
     Data.Set.Internal.Set_ Coq.Numbers.BinNums.N -> Prop :=
  fun f g s =>
    Data.Set.Internal.map (Test.QuickCheck.Function.apply f) (Data.Set.Internal.map
                                                              (Test.QuickCheck.Function.apply g) s)
    Test.QuickCheck.Property.===
    Data.Set.Internal.map (Test.QuickCheck.Function.apply f GHC.Base.∘
                           Test.QuickCheck.Function.apply g) s.

Definition prop_map : Data.Set.Internal.Set_ Coq.Numbers.BinNums.N -> bool :=
  fun s => Data.Set.Internal.map GHC.Base.id s GHC.Base.== s.

Definition prop_isSubsetOf2 : TwoSets -> bool :=
  fun '(Mk_TwoSets a b) =>
    Data.Set.Internal.isSubsetOf a (Data.Set.Internal.union a b).

Definition prop_isSubsetOf : TwoSets -> bool :=
  fun '(Mk_TwoSets a b) =>
    Data.Set.Internal.isSubsetOf a b GHC.Base.==
    Data.IntSet.Internal.isSubsetOf (toIntSet a) (toIntSet b).

Definition prop_isProperSubsetOf2 : TwoSets -> bool :=
  fun '(Mk_TwoSets a b) =>
    let c := Data.Set.Internal.union a b in
    Data.Set.Internal.isProperSubsetOf a c GHC.Base.== (a GHC.Base./= c).

Definition prop_isProperSubsetOf : TwoSets -> bool :=
  fun '(Mk_TwoSets a b) =>
    Data.Set.Internal.isProperSubsetOf a b GHC.Base.==
    Data.IntSet.Internal.isProperSubsetOf (toIntSet a) (toIntSet b).

Definition prop_fromListDesc : list Coq.Numbers.BinNums.N -> Prop :=
  fun xs =>
    let sort_xs := GHC.List.reverse (Data.OldList.sort xs) in
    let nub_sort_xs := GHC.Base.map GHC.Err.head (Data.OldList.group sort_xs) in
    let t := Data.Set.Internal.fromList xs in
    (t Test.QuickCheck.Property.=== Data.Set.Internal.fromDescList sort_xs)
    Test.QuickCheck.Property..&&.(**)
    ((t Test.QuickCheck.Property.===
      Data.Set.Internal.fromDistinctDescList nub_sort_xs)
     Test.QuickCheck.Property..&&.(**)
     (t Test.QuickCheck.Property.===
      Data.Foldable.foldr Data.Set.Internal.insert Data.Set.Internal.empty xs)).

Definition prop_fromList : list Coq.Numbers.BinNums.N -> Prop :=
  fun xs =>
    let sort_xs := Data.OldList.sort xs in
    let nub_sort_xs := GHC.Base.map GHC.Err.head (Data.OldList.group sort_xs) in
    let t := Data.Set.Internal.fromList xs in
    (t Test.QuickCheck.Property.=== Data.Set.Internal.fromAscList sort_xs)
    Test.QuickCheck.Property..&&.(**)
    ((t Test.QuickCheck.Property.===
      Data.Set.Internal.fromDistinctAscList nub_sort_xs)
     Test.QuickCheck.Property..&&.(**)
     (t Test.QuickCheck.Property.===
      Data.Foldable.foldr Data.Set.Internal.insert Data.Set.Internal.empty xs)).

Definition prop_foldR' : Data.Set.Internal.Set_ Coq.Numbers.BinNums.N -> bool :=
  fun s =>
    Data.Set.Internal.foldr' cons nil s GHC.Base.== Data.Set.Internal.toList s.

Definition prop_foldR : Data.Set.Internal.Set_ Coq.Numbers.BinNums.N -> bool :=
  fun s =>
    Data.Set.Internal.foldr cons nil s GHC.Base.== Data.Set.Internal.toList s.

Definition prop_foldL' : Data.Set.Internal.Set_ Coq.Numbers.BinNums.N -> bool :=
  fun s =>
    Data.Set.Internal.foldl' (GHC.Base.flip cons) nil s GHC.Base.==
    Data.Foldable.foldl' (GHC.Base.flip cons) nil (Data.Set.Internal.toList s).

Definition prop_foldL : Data.Set.Internal.Set_ Coq.Numbers.BinNums.N -> bool :=
  fun s =>
    Data.Set.Internal.foldl (GHC.Base.flip cons) nil s GHC.Base.==
    Data.Foldable.foldl (GHC.Base.flip cons) nil (Data.Set.Internal.toList s).

Definition prop_filter
   : Data.Set.Internal.Set_ Coq.Numbers.BinNums.N ->
     Coq.Numbers.BinNums.N -> bool :=
  fun s i =>
    Data.Set.Internal.partition GHC.Real.odd s GHC.Base.==
    pair (Data.Set.Internal.filter GHC.Real.odd s) (Data.Set.Internal.filter
          GHC.Real.even s).

Definition prop_drop
   : Coq.Numbers.BinNums.N ->
     Data.Set.Internal.Set_ Coq.Numbers.BinNums.N -> Prop :=
  fun n xs =>
    let dropped := Data.Set.Internal.drop n xs in
    Data.Set.Internal.valid dropped Test.QuickCheck.Property..&&.(**)
    (dropped Test.QuickCheck.Property.===
     Data.Set.Internal.fromDistinctAscList (GHC.List.drop n (Data.Set.Internal.toList
                                                             xs))).

Definition prop_disjointUnion
   : Data.Set.Internal.Set_ Coq.Numbers.BinNums.N ->
     Data.Set.Internal.Set_ Coq.Numbers.BinNums.N -> Prop :=
  fun xs ys =>
    let du := Data.Set.Internal.disjointUnion xs ys in
    Data.Set.Internal.valid du Test.QuickCheck.Property..&&.(**)
    (du Test.QuickCheck.Property.===
     Data.Set.Internal.union (Data.Set.Internal.mapMonotonic Data.Either.Left xs)
     (Data.Set.Internal.mapMonotonic Data.Either.Right ys)).

Definition prop_disjoint
   : Data.Set.Internal.Set_ Coq.Numbers.BinNums.N ->
     Data.Set.Internal.Set_ Coq.Numbers.BinNums.N -> bool :=
  fun a b =>
    Data.Set.Internal.disjoint a b GHC.Base.==
    Data.Set.Internal.null (Data.Set.Internal.intersection a b).

Definition prop_cartesianProduct
   : Data.Set.Internal.Set_ Coq.Numbers.BinNums.N ->
     Data.Set.Internal.Set_ Coq.Numbers.BinNums.N -> Prop :=
  fun xs ys =>
    let cp := Data.Set.Internal.cartesianProduct xs ys in
    Data.Set.Internal.valid cp Test.QuickCheck.Property..&&.(**)
    (Data.Set.Internal.toList cp Test.QuickCheck.Property.===
     GHC.Base.liftA2 GHC.Tuple.pair2 (Data.Set.Internal.toList xs)
     (Data.Set.Internal.toList ys)).

Definition prop_UnionInsert
   : Coq.Numbers.BinNums.N ->
     Data.Set.Internal.Set_ Coq.Numbers.BinNums.N -> bool :=
  fun x t =>
    Data.Set.Internal.union t (Data.Set.Internal.singleton x) GHC.Base.==
    Data.Set.Internal.insert x t.

Definition prop_UnionComm : TwoSets -> bool :=
  fun '(Mk_TwoSets t1 t2) =>
    (Data.Set.Internal.union t1 t2 GHC.Base.== Data.Set.Internal.union t2 t1).

Definition prop_UnionBiased : TwoSets -> Prop :=
  fun '(Mk_TwoSets l r) =>
    let r' :=
      Data.Set.Internal.mapMonotonic (fun arg_1__ => Mk_OddEq arg_1__ true) r in
    let l' :=
      Data.Set.Internal.mapMonotonic (fun arg_3__ => Mk_OddEq arg_3__ false) l in
    Data.Set.Internal.union l' r' Test.QuickCheck.Property.===
    Data.Set.Internal.union l' (Data.Set.Internal.difference r' l').

Definition prop_UnionAssoc
   : Data.Set.Internal.Set_ Coq.Numbers.BinNums.N ->
     Data.Set.Internal.Set_ Coq.Numbers.BinNums.N ->
     Data.Set.Internal.Set_ Coq.Numbers.BinNums.N -> bool :=
  fun t1 t2 t3 =>
    Data.Set.Internal.union t1 (Data.Set.Internal.union t2 t3) GHC.Base.==
    Data.Set.Internal.union (Data.Set.Internal.union t1 t2) t3.

Definition prop_Single : Coq.Numbers.BinNums.N -> bool :=
  fun x =>
    (Data.Set.Internal.insert x Data.Set.Internal.empty GHC.Base.==
     Data.Set.Internal.singleton x).

Definition prop_Ordered : Prop :=
  Test.QuickCheck.Property.forAll (Test.QuickCheck.Gen.choose (pair #5 #100))
  (fun n =>
     let xs := GHC.Enum.enumFromTo #0 (n : Coq.Numbers.BinNums.N) in
     Data.Set.Internal.fromAscList xs Test.QuickCheck.Property.===
     Data.Set.Internal.fromList xs).

Definition prop_NotMember
   : list Coq.Numbers.BinNums.N -> Coq.Numbers.BinNums.N -> bool :=
  fun xs n =>
    let m := Data.Set.Internal.fromList xs in
    Data.Foldable.all (fun k =>
                         Data.Set.Internal.notMember k m GHC.Base.== (Data.Foldable.notElem k xs)) (cons
                                                                                                    n xs).

Definition prop_Member
   : list Coq.Numbers.BinNums.N -> Coq.Numbers.BinNums.N -> bool :=
  fun xs n =>
    let m := Data.Set.Internal.fromList xs in
    Data.Foldable.all (fun k =>
                         Data.Set.Internal.member k m GHC.Base.== (Data.Foldable.elem k xs)) (cons n xs).

Definition prop_List : list Coq.Numbers.BinNums.N -> bool :=
  fun xs =>
    (Data.OldList.sort (Data.OldList.nub xs) GHC.Base.==
     Data.Set.Internal.toList (Data.Set.Internal.fromList xs)).

Definition prop_IntBiased : TwoSets -> bool :=
  fun '(Mk_TwoSets l r) =>
    let r' :=
      Data.Set.Internal.mapMonotonic (fun arg_1__ => Mk_OddEq arg_1__ true) r in
    let l' :=
      Data.Set.Internal.mapMonotonic (fun arg_3__ => Mk_OddEq arg_3__ false) l in
    let l'r' := Data.Set.Internal.intersection l' r' in
    Data.Foldable.all (fun '(Mk_OddEq _ b) => negb b) l'r'.

Definition prop_Int
   : list Coq.Numbers.BinNums.N -> list Coq.Numbers.BinNums.N -> bool :=
  fun xs ys =>
    Data.Set.Internal.toAscList (Data.Set.Internal.intersection
                                 (Data.Set.Internal.fromList xs) (Data.Set.Internal.fromList ys)) GHC.Base.==
    Data.OldList.sort (Data.OldList.nub ((Data.OldList.intersect) (xs) (ys))).

Definition prop_InsertDelete
   : Coq.Numbers.BinNums.N ->
     Data.Set.Internal.Set_ Coq.Numbers.BinNums.N -> Prop :=
  fun k t =>
    negb (Data.Set.Internal.member k t) Test.QuickCheck.Property.==>
    (Data.Set.Internal.delete k (Data.Set.Internal.insert k t) GHC.Base.== t).

Definition prop_Diff
   : list Coq.Numbers.BinNums.N -> list Coq.Numbers.BinNums.N -> bool :=
  fun xs ys =>
    Data.Set.Internal.toAscList (Data.Set.Internal.difference
                                 (Data.Set.Internal.fromList xs) (Data.Set.Internal.fromList ys)) GHC.Base.==
    Data.OldList.sort (_Data.OldList.\\_ (Data.OldList.nub xs) (Data.OldList.nub
                                                                ys)).

Definition prop_DescendingOrdered : Prop :=
  Test.QuickCheck.Property.forAll (Test.QuickCheck.Gen.choose (pair #5 #100))
  (fun n =>
     let xs :=
       GHC.Enum.enumFromThenTo n (n GHC.Num.- #1) (#0 : Coq.Numbers.BinNums.N) in
     Data.Set.Internal.fromDescList xs Test.QuickCheck.Property.===
     Data.Set.Internal.fromList xs).

Definition prop_DescList : list Coq.Numbers.BinNums.N -> bool :=
  fun xs =>
    (GHC.List.reverse (Data.OldList.sort (Data.OldList.nub xs)) GHC.Base.==
     Data.Set.Internal.toDescList (Data.Set.Internal.fromList xs)).

Definition prop_AscDescList : list Coq.Numbers.BinNums.N -> bool :=
  fun xs =>
    let s := Data.Set.Internal.fromList xs in
    Data.Set.Internal.toAscList s GHC.Base.==
    GHC.List.reverse (Data.Set.Internal.toDescList s).

Definition positionFactor : Coq.Numbers.BinNums.N :=
  #1.

Definition isLeft {a} {b} : Data.Either.Either a b -> bool :=
  fun arg_0__ => match arg_0__ with | Data.Either.Left _ => true | _ => false end.

Definition prop_dropWhileAntitone
   : list (Data.Either.Either Coq.Numbers.BinNums.N Coq.Numbers.BinNums.N) ->
     Prop :=
  fun xs' =>
    let xs := Data.Set.Internal.fromList xs' in
    let tw := Data.Set.Internal.dropWhileAntitone isLeft xs in
    Data.Set.Internal.valid tw Test.QuickCheck.Property..&&.(**)
    (tw Test.QuickCheck.Property.===
     Data.Set.Internal.filter (negb GHC.Base.∘ isLeft) xs).

Definition prop_spanAntitone
   : list (Data.Either.Either Coq.Numbers.BinNums.N Coq.Numbers.BinNums.N) ->
     Prop :=
  fun xs' =>
    let xs := Data.Set.Internal.fromList xs' in
    let 'pair tw dw := Data.Set.Internal.spanAntitone isLeft xs in
    Data.Set.Internal.valid tw Test.QuickCheck.Property..&&.(**)
    (Data.Set.Internal.valid dw Test.QuickCheck.Property..&&.(**)
     ((tw Test.QuickCheck.Property.=== Data.Set.Internal.takeWhileAntitone isLeft xs)
      Test.QuickCheck.Property..&&.(**)
      (dw Test.QuickCheck.Property.===
       Data.Set.Internal.dropWhileAntitone isLeft xs))).

Definition prop_takeWhileAntitone
   : list (Data.Either.Either Coq.Numbers.BinNums.N Coq.Numbers.BinNums.N) ->
     Prop :=
  fun xs' =>
    let xs := Data.Set.Internal.fromList xs' in
    let tw := Data.Set.Internal.takeWhileAntitone isLeft xs in
    Data.Set.Internal.valid tw Test.QuickCheck.Property..&&.(**)
    (tw Test.QuickCheck.Property.=== Data.Set.Internal.filter isLeft xs).

Definition getOddEq {a} : OddEq a -> (a * bool)%type :=
  fun '(Mk_OddEq b a) => pair b a.

Definition prop_InsertBiased
   : Coq.Numbers.BinNums.N ->
     Data.Set.Internal.Set_ Coq.Numbers.BinNums.N -> bool :=
  fun k t =>
    let t' :=
      Data.Set.Internal.mapMonotonic (fun arg_0__ => Mk_OddEq arg_0__ false) t in
    let kt' := Data.Set.Internal.insert (Mk_OddEq k true) t' in
    let kt := Data.Set.Internal.mapMonotonic getOddEq kt' in
    Data.Set.Internal.member (pair k true) kt.

Definition gapRange : Coq.Numbers.BinNums.N :=
  #5.

Definition fromInt {a} `{IsInt a} : Coq.Numbers.BinNums.N -> a :=
  Data.Functor.Identity.runIdentity GHC.Base.∘
  (fromIntF GHC.Base.∘ Data.Functor.Identity.Mk_Identity).

Definition forValid {a} {b} `{IsInt a} `{Test.QuickCheck.Property.Testable b}
   : (Data.Set.Internal.Set_ a -> b) -> Prop :=
  fun f =>
    Test.QuickCheck.Property.forAll Test.QuickCheck.Arbitrary.arbitrary (fun t =>
                                                                           Test.QuickCheck.Property.classify
                                                                           (Data.Set.Internal.size t GHC.Base.== #0)
                                                                           (GHC.Base.hs_string__ "empty")
                                                                           (Test.QuickCheck.Property.classify (andb
                                                                                                               (Data.Set.Internal.size
                                                                                                                t
                                                                                                                GHC.Base.>
                                                                                                                #0)
                                                                                                               (Data.Set.Internal.size
                                                                                                                t
                                                                                                                GHC.Base.<=
                                                                                                                #10))
                                                                                                              (GHC.Base.hs_string__
                                                                                                               "small")
                                                                                                              (Test.QuickCheck.Property.classify
                                                                                                               (andb
                                                                                                                (Data.Set.Internal.size
                                                                                                                 t
                                                                                                                 GHC.Base.>
                                                                                                                 #10)
                                                                                                                (Data.Set.Internal.size
                                                                                                                 t
                                                                                                                 GHC.Base.<=
                                                                                                                 #64))
                                                                                                               (GHC.Base.hs_string__
                                                                                                                "medium")
                                                                                                               (Test.QuickCheck.Property.classify
                                                                                                                (Data.Set.Internal.size
                                                                                                                 t
                                                                                                                 GHC.Base.>
                                                                                                                 #64)
                                                                                                                (GHC.Base.hs_string__
                                                                                                                 "large")
                                                                                                                (f
                                                                                                                 t))))).

Definition forValidUnitTree {a} `{Test.QuickCheck.Property.Testable a}
   : (Data.Set.Internal.Set_ Coq.Numbers.BinNums.N -> a) -> Prop :=
  fun f => forValid f.

Definition prop_DeleteValid : Coq.Numbers.BinNums.N -> Prop :=
  fun k =>
    forValidUnitTree (fun t =>
                        Data.Set.Internal.valid (Data.Set.Internal.delete k (Data.Set.Internal.insert k
                                                                             t))).

Definition prop_DiffValid : Prop :=
  forValidUnitTree (fun t1 =>
                      forValidUnitTree (fun t2 =>
                                          Data.Set.Internal.valid (Data.Set.Internal.difference t1 t2))).

Definition prop_InsertValid : Coq.Numbers.BinNums.N -> Prop :=
  fun k =>
    forValidUnitTree (fun t =>
                        Data.Set.Internal.valid (Data.Set.Internal.insert k t)).

Definition prop_IntValid : Prop :=
  forValidUnitTree (fun t1 =>
                      forValidUnitTree (fun t2 =>
                                          Data.Set.Internal.valid (Data.Set.Internal.intersection t1 t2))).

Definition prop_Link : Coq.Numbers.BinNums.N -> Prop :=
  fun x =>
    forValidUnitTree (fun t =>
                        let 'pair l r := Data.Set.Internal.split x t in
                        Data.Set.Internal.valid (Data.Set.Internal.link x l r)).

Definition prop_Merge : Coq.Numbers.BinNums.N -> Prop :=
  fun x =>
    forValidUnitTree (fun t =>
                        let 'pair l r := Data.Set.Internal.split x t in
                        Data.Set.Internal.valid (Data.Set.Internal.merge l r)).

Definition prop_UnionValid : Prop :=
  forValidUnitTree (fun t1 =>
                      forValidUnitTree (fun t2 =>
                                          Data.Set.Internal.valid (Data.Set.Internal.union t1 t2))).

Definition prop_Valid : Prop :=
  forValidUnitTree (fun t => Data.Set.Internal.valid t).

(* Skipping all instances of class `GHC.Show.Show', including
   `SetProperties.Show__OddEq' *)

(* Skipping all instances of class `GHC.Show.Show', including
   `SetProperties.Show__TwoSets' *)

(* Skipping all instances of class `GHC.Enum.Bounded', including
   `SetProperties.Bounded__Options2' *)

(* Skipping all instances of class `GHC.Enum.Enum', including
   `SetProperties.Enum__Options2' *)

Local Definition Ord__OddEq_compare {inst_a} `{GHC.Base.Ord inst_a}
   : (OddEq inst_a) -> (OddEq inst_a) -> comparison :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | Mk_OddEq x _, Mk_OddEq y _ => GHC.Base.compare x y
    end.

Local Definition Ord__OddEq_op_zl__ {inst_a} `{GHC.Base.Ord inst_a}
   : (OddEq inst_a) -> (OddEq inst_a) -> bool :=
  fun x y => Ord__OddEq_compare x y GHC.Base.== Lt.

Local Definition Ord__OddEq_op_zlze__ {inst_a} `{GHC.Base.Ord inst_a}
   : (OddEq inst_a) -> (OddEq inst_a) -> bool :=
  fun x y => Ord__OddEq_compare x y GHC.Base./= Gt.

Local Definition Ord__OddEq_op_zg__ {inst_a} `{GHC.Base.Ord inst_a}
   : (OddEq inst_a) -> (OddEq inst_a) -> bool :=
  fun x y => Ord__OddEq_compare x y GHC.Base.== Gt.

Local Definition Ord__OddEq_op_zgze__ {inst_a} `{GHC.Base.Ord inst_a}
   : (OddEq inst_a) -> (OddEq inst_a) -> bool :=
  fun x y => Ord__OddEq_compare x y GHC.Base./= Lt.

Local Definition Ord__OddEq_max {inst_a} `{GHC.Base.Ord inst_a}
   : (OddEq inst_a) -> (OddEq inst_a) -> (OddEq inst_a) :=
  fun x y => if Ord__OddEq_op_zlze__ x y : bool then y else x.

Local Definition Ord__OddEq_min {inst_a} `{GHC.Base.Ord inst_a}
   : (OddEq inst_a) -> (OddEq inst_a) -> (OddEq inst_a) :=
  fun x y => if Ord__OddEq_op_zlze__ x y : bool then x else y.

Program Instance Ord__OddEq {a} `{GHC.Base.Ord a} : GHC.Base.Ord (OddEq a) :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zl____ := Ord__OddEq_op_zl__ ;
           GHC.Base.op_zlze____ := Ord__OddEq_op_zlze__ ;
           GHC.Base.op_zg____ := Ord__OddEq_op_zg__ ;
           GHC.Base.op_zgze____ := Ord__OddEq_op_zgze__ ;
           GHC.Base.compare__ := Ord__OddEq_compare ;
           GHC.Base.max__ := Ord__OddEq_max ;
           GHC.Base.min__ := Ord__OddEq_min |}.

Local Definition Eq___OddEq_op_zeze__ {inst_a} `{GHC.Base.Eq_ inst_a}
   : (OddEq inst_a) -> (OddEq inst_a) -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | Mk_OddEq x _, Mk_OddEq y _ => x GHC.Base.== y
    end.

Local Definition Eq___OddEq_op_zsze__ {inst_a} `{GHC.Base.Eq_ inst_a}
   : (OddEq inst_a) -> (OddEq inst_a) -> bool :=
  fun x y => negb (Eq___OddEq_op_zeze__ x y).

Program Instance Eq___OddEq {a} `{GHC.Base.Eq_ a} : GHC.Base.Eq_ (OddEq a) :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zeze____ := Eq___OddEq_op_zeze__ ;
           GHC.Base.op_zsze____ := Eq___OddEq_op_zsze__ |}.

(* Skipping all instances of class `Test.QuickCheck.Arbitrary.Arbitrary',
   including `SetProperties.Arbitrary__OddEq' *)

(* Skipping all instances of class `Test.QuickCheck.Arbitrary.Arbitrary',
   including `SetProperties.Arbitrary__Set_' *)

(* Skipping all instances of class `SetProperties.IsInt', including
   `SetProperties.IsInt__N' *)

(* Skipping all instances of class `SetProperties.MonadGen', including
   `SetProperties.MonadGen__StateT' *)

(* Skipping all instances of class `SetProperties.MonadGen', including
   `SetProperties.MonadGen__Gen' *)

(* Skipping all instances of class `Test.QuickCheck.Arbitrary.Arbitrary',
   including `SetProperties.Arbitrary__TwoSets' *)

(* Skipping all instances of class `Test.QuickCheck.Arbitrary.Arbitrary',
   including `SetProperties.Arbitrary__TwoLists' *)

(* Skipping all instances of class `Test.QuickCheck.Arbitrary.Arbitrary',
   including `SetProperties.Arbitrary__Options2' *)

(* External variables:
     Gt IsInt Lt Prop andb bool comparison cons false fromIntF list negb nil op_zt__
     pair true Coq.Init.Datatypes.app Coq.Lists.List.flat_map Coq.Numbers.BinNums.N
     Data.Either.Either Data.Either.Left Data.Either.Right Data.Foldable.all
     Data.Foldable.elem Data.Foldable.foldl Data.Foldable.foldl' Data.Foldable.foldr
     Data.Foldable.length Data.Foldable.notElem Data.Foldable.null
     Data.Functor.Identity.Mk_Identity Data.Functor.Identity.runIdentity
     Data.IntSet.Internal.IntSet Data.IntSet.Internal.fromList
     Data.IntSet.Internal.isProperSubsetOf Data.IntSet.Internal.isSubsetOf
     Data.OldList.group Data.OldList.intersect Data.OldList.nub
     Data.OldList.op_zrzr__ Data.OldList.sort Data.Set.Internal.Set_
     Data.Set.Internal.cartesianProduct Data.Set.Internal.delete
     Data.Set.Internal.difference Data.Set.Internal.disjoint
     Data.Set.Internal.disjointUnion Data.Set.Internal.drop
     Data.Set.Internal.dropWhileAntitone Data.Set.Internal.empty
     Data.Set.Internal.filter Data.Set.Internal.foldl Data.Set.Internal.foldl'
     Data.Set.Internal.foldr Data.Set.Internal.foldr' Data.Set.Internal.fromAscList
     Data.Set.Internal.fromDescList Data.Set.Internal.fromDistinctAscList
     Data.Set.Internal.fromDistinctDescList Data.Set.Internal.fromList
     Data.Set.Internal.insert Data.Set.Internal.intersection
     Data.Set.Internal.isProperSubsetOf Data.Set.Internal.isSubsetOf
     Data.Set.Internal.link Data.Set.Internal.map Data.Set.Internal.mapMonotonic
     Data.Set.Internal.member Data.Set.Internal.merge Data.Set.Internal.notMember
     Data.Set.Internal.null Data.Set.Internal.partition Data.Set.Internal.powerSet
     Data.Set.Internal.singleton Data.Set.Internal.size
     Data.Set.Internal.spanAntitone Data.Set.Internal.split Data.Set.Internal.splitAt
     Data.Set.Internal.splitMember Data.Set.Internal.splitRoot Data.Set.Internal.take
     Data.Set.Internal.takeWhileAntitone Data.Set.Internal.toAscList
     Data.Set.Internal.toDescList Data.Set.Internal.toList Data.Set.Internal.union
     Data.Set.Internal.unions Data.Set.Internal.valid GHC.Base.Eq_ GHC.Base.Ord
     GHC.Base.compare GHC.Base.compare__ GHC.Base.flip GHC.Base.fmap GHC.Base.id
     GHC.Base.liftA2 GHC.Base.map GHC.Base.max__ GHC.Base.min__ GHC.Base.op_z2218U__
     GHC.Base.op_zeze__ GHC.Base.op_zeze____ GHC.Base.op_zg__ GHC.Base.op_zg____
     GHC.Base.op_zgze____ GHC.Base.op_zl__ GHC.Base.op_zl____ GHC.Base.op_zlze__
     GHC.Base.op_zlze____ GHC.Base.op_zsze__ GHC.Base.op_zsze____
     GHC.Enum.enumFromThenTo GHC.Enum.enumFromTo GHC.Err.Build_Default
     GHC.Err.Default GHC.Err.head GHC.List.drop GHC.List.reverse GHC.List.take
     GHC.Num.fromInteger GHC.Num.op_zm__ GHC.Real.even GHC.Real.odd GHC.Tuple.pair2
     Test.QuickCheck.Arbitrary.arbitrary Test.QuickCheck.Function.Fun
     Test.QuickCheck.Function.apply Test.QuickCheck.Gen.choose
     Test.QuickCheck.Property.Testable Test.QuickCheck.Property.classify
     Test.QuickCheck.Property.forAll Test.QuickCheck.Property.op_zezeze__
     Test.QuickCheck.Property.op_zezezg__ Test.QuickCheck.Property.op_zizazazi__
*)
