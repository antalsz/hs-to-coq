(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Coq.Program.Tactics.
Require Coq.Program.Wf.

(* Preamble *)

Require Data.IntSet.Internal.
Require Test.QuickCheck.Property.
Require IntSetProofs.

Require String.
Import String.StringSyntax.

Instance Arbitrary_IntSet : Test.QuickCheck.Property.Arbitrary Data.IntSet.Internal.IntSet :=
  { arbitrary := Test.QuickCheck.Property.MkGen IntSetProofs.WF }.

Require GHC.Enum.
Notation enumFromTo := GHC.Enum.enumFromTo.

Coercion is_true : bool >-> Sortclass.

(* Converted imports: *)

Require Coq.Init.Datatypes.
Require Coq.Lists.List.
Require Coq.NArith.BinNat.
Require Coq.Numbers.BinNums.
Require Data.Bits.
Require Data.Foldable.
Require Data.IntSet.Internal.
Require Data.OldList.
Require Data.Set.Internal.
Require GHC.Base.
Require GHC.Enum.
Require GHC.List.
Require GHC.Num.
Require GHC.Real.
Require IntSetValidity.
Require Test.QuickCheck.Arbitrary.
Require Test.QuickCheck.Property.
Import Data.Bits.Notations.
Import Data.OldList.Notations.
Import GHC.Base.Notations.
Import GHC.Num.Notations.
Import Test.QuickCheck.Property.Notations.

(* No type declarations to convert. *)

(* Converted value declarations: *)

Definition toSet
   : Data.IntSet.Internal.IntSet ->
     Data.Set.Internal.Set_ Coq.Numbers.BinNums.N :=
  Data.Set.Internal.fromList GHC.Base.∘ Data.IntSet.Internal.toList.

(* Skipping definition `IntSetProperties.test_split' *)

(* Skipping definition `IntSetProperties.test_lookupLT' *)

(* Skipping definition `IntSetProperties.test_lookupLE' *)

(* Skipping definition `IntSetProperties.test_lookupGT' *)

(* Skipping definition `IntSetProperties.test_lookupGE' *)

(* Skipping definition `IntSetProperties.test_LookupSomething' *)

Definition prop_splitRoot : Data.IntSet.Internal.IntSet -> bool :=
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
                                                                                      nil) (Data.IntSet.Internal.toList
                                                                                    (Data.IntSet.Internal.unions rst)))
                                                        (Data.IntSet.Internal.toList s1))
        end in
    let ls := Data.IntSet.Internal.splitRoot s in
    andb (loop ls) (s GHC.Base.== Data.IntSet.Internal.unions ls).

Definition prop_splitMember
   : Data.IntSet.Internal.IntSet -> Coq.Numbers.BinNums.N -> Prop :=
  fun s i =>
    let 'pair (pair s1 t) s2 := Data.IntSet.Internal.splitMember i s in
    IntSetValidity.valid s1 Test.QuickCheck.Property..&&.(**)
    (IntSetValidity.valid s2 Test.QuickCheck.Property..&&.(**)
     (Data.Foldable.all (fun arg_1__ => arg_1__ GHC.Base.< i)
      (Data.IntSet.Internal.toList s1) Test.QuickCheck.Property..&&.(**)
      (Data.Foldable.all (fun arg_2__ => arg_2__ GHC.Base.> i)
       (Data.IntSet.Internal.toList s2) Test.QuickCheck.Property..&&.(**)
       ((t Test.QuickCheck.Property.=== Data.IntSet.Internal.member i s)
        Test.QuickCheck.Property..&&.(**)
        (Data.IntSet.Internal.delete i s Test.QuickCheck.Property.===
         Data.IntSet.Internal.union s1 s2))))).

Definition prop_split
   : Data.IntSet.Internal.IntSet -> Coq.Numbers.BinNums.N -> Prop :=
  fun s i =>
    let 'pair s1 s2 := Data.IntSet.Internal.split i s in
    IntSetValidity.valid s1 Test.QuickCheck.Property..&&.(**)
    (IntSetValidity.valid s2 Test.QuickCheck.Property..&&.(**)
     (Data.Foldable.all (fun arg_1__ => arg_1__ GHC.Base.< i)
      (Data.IntSet.Internal.toList s1) Test.QuickCheck.Property..&&.(**)
      (Data.Foldable.all (fun arg_2__ => arg_2__ GHC.Base.> i)
       (Data.IntSet.Internal.toList s2) Test.QuickCheck.Property..&&.(**)
       (Data.IntSet.Internal.delete i s Test.QuickCheck.Property.===
        Data.IntSet.Internal.union s1 s2)))).

Definition prop_size : Data.IntSet.Internal.IntSet -> Prop :=
  fun s =>
    let sz := Data.IntSet.Internal.size s in
    (sz Test.QuickCheck.Property.===
     Data.IntSet.Internal.foldl' (fun arg_1__ arg_2__ =>
                                    match arg_1__, arg_2__ with
                                    | i, _ => i GHC.Num.+ #1
                                    end) (#0 : Coq.Numbers.BinNums.N) s) Test.QuickCheck.Property..&&.(**)
    (sz Test.QuickCheck.Property.===
     Coq.NArith.BinNat.N.of_nat (Coq.Init.Datatypes.length
                                 (Data.IntSet.Internal.toList s))).

(* Skipping definition `IntSetProperties.prop_readShow' *)

Definition prop_partition
   : Data.IntSet.Internal.IntSet -> Coq.Numbers.BinNums.N -> Prop :=
  fun s i =>
    let 'pair s1 s2 := Data.IntSet.Internal.partition GHC.Real.odd s in
    IntSetValidity.valid s1 Test.QuickCheck.Property..&&.(**)
    (IntSetValidity.valid s2 Test.QuickCheck.Property..&&.(**)
     (Data.Foldable.all GHC.Real.odd (Data.IntSet.Internal.toList s1)
      Test.QuickCheck.Property..&&.(**)
      (Data.Foldable.all GHC.Real.even (Data.IntSet.Internal.toList s2)
       Test.QuickCheck.Property..&&.(**)
       (s Test.QuickCheck.Property.=== Data.IntSet.Internal.union s1 s2)))).

Definition prop_ord
   : Data.IntSet.Internal.IntSet -> Data.IntSet.Internal.IntSet -> bool :=
  fun s1 s2 =>
    GHC.Base.compare s1 s2 GHC.Base.==
    GHC.Base.compare (Data.IntSet.Internal.toList s1) (Data.IntSet.Internal.toList
                      s2).

(* Skipping definition `IntSetProperties.prop_minView' *)

(* Skipping definition `IntSetProperties.prop_maxView' *)

Definition prop_map : Data.IntSet.Internal.IntSet -> bool :=
  fun s => Data.IntSet.Internal.map GHC.Base.id s GHC.Base.== s.

Definition prop_isSubsetOf2
   : Data.IntSet.Internal.IntSet -> Data.IntSet.Internal.IntSet -> bool :=
  fun a b => Data.IntSet.Internal.isSubsetOf a (Data.IntSet.Internal.union a b).

Definition prop_isSubsetOf
   : Data.IntSet.Internal.IntSet -> Data.IntSet.Internal.IntSet -> bool :=
  fun a b =>
    Data.IntSet.Internal.isSubsetOf a b GHC.Base.==
    Data.Set.Internal.isSubsetOf (toSet a) (toSet b).

Definition prop_isProperSubsetOf2
   : Data.IntSet.Internal.IntSet -> Data.IntSet.Internal.IntSet -> bool :=
  fun a b =>
    let c := Data.IntSet.Internal.union a b in
    Data.IntSet.Internal.isProperSubsetOf a c GHC.Base.== (a GHC.Base./= c).

Definition prop_isProperSubsetOf
   : Data.IntSet.Internal.IntSet -> Data.IntSet.Internal.IntSet -> bool :=
  fun a b =>
    Data.IntSet.Internal.isProperSubsetOf a b GHC.Base.==
    Data.Set.Internal.isProperSubsetOf (toSet a) (toSet b).

(* Skipping definition `IntSetProperties.prop_fromList' *)

Definition prop_foldR' : Data.IntSet.Internal.IntSet -> bool :=
  fun s =>
    Data.IntSet.Internal.foldr' cons nil s GHC.Base.==
    Data.IntSet.Internal.toList s.

Definition prop_foldR : Data.IntSet.Internal.IntSet -> bool :=
  fun s =>
    Data.IntSet.Internal.foldr cons nil s GHC.Base.== Data.IntSet.Internal.toList s.

Definition prop_foldL' : Data.IntSet.Internal.IntSet -> bool :=
  fun s =>
    Data.IntSet.Internal.foldl' (GHC.Base.flip cons) nil s GHC.Base.==
    Data.Foldable.foldl' (GHC.Base.flip cons) nil (Data.IntSet.Internal.toList s).

Definition prop_foldL : Data.IntSet.Internal.IntSet -> bool :=
  fun s =>
    Data.IntSet.Internal.foldl (GHC.Base.flip cons) nil s GHC.Base.==
    Data.Foldable.foldl (GHC.Base.flip cons) nil (Data.IntSet.Internal.toList s).

(* Skipping definition `IntSetProperties.prop_findMin' *)

(* Skipping definition `IntSetProperties.prop_findMax' *)

Definition prop_filter
   : Data.IntSet.Internal.IntSet -> Coq.Numbers.BinNums.N -> Prop :=
  fun s i =>
    let evens := Data.IntSet.Internal.filter GHC.Real.even s in
    let odds := Data.IntSet.Internal.filter GHC.Real.odd s in
    let parts := Data.IntSet.Internal.partition GHC.Real.odd s in
    IntSetValidity.valid odds Test.QuickCheck.Property..&&.(**)
    (IntSetValidity.valid evens Test.QuickCheck.Property..&&.(**)
     (parts Test.QuickCheck.Property.=== pair odds evens)).

Definition prop_disjoint
   : Data.IntSet.Internal.IntSet -> Data.IntSet.Internal.IntSet -> bool :=
  fun a b =>
    Data.IntSet.Internal.disjoint a b GHC.Base.==
    Data.IntSet.Internal.null (Data.IntSet.Internal.intersection a b).

(* Skipping definition `IntSetProperties.prop_bitcount' *)

Definition prop_UnionInsert
   : Coq.Numbers.BinNums.N -> Data.IntSet.Internal.IntSet -> Prop :=
  fun x t =>
    let 't' := Data.IntSet.Internal.union t (Data.IntSet.Internal.singleton x) in
    IntSetValidity.valid t' Test.QuickCheck.Property..&&.(**)
    (t' Test.QuickCheck.Property.=== Data.IntSet.Internal.insert x t).

Definition prop_UnionComm
   : Data.IntSet.Internal.IntSet -> Data.IntSet.Internal.IntSet -> bool :=
  fun t1 t2 =>
    (Data.IntSet.Internal.union t1 t2 GHC.Base.== Data.IntSet.Internal.union t2 t1).

Definition prop_UnionAssoc
   : Data.IntSet.Internal.IntSet ->
     Data.IntSet.Internal.IntSet -> Data.IntSet.Internal.IntSet -> bool :=
  fun t1 t2 t3 =>
    Data.IntSet.Internal.union t1 (Data.IntSet.Internal.union t2 t3) GHC.Base.==
    Data.IntSet.Internal.union (Data.IntSet.Internal.union t1 t2) t3.

Definition prop_SingletonValid : Coq.Numbers.BinNums.N -> Prop :=
  fun x => IntSetValidity.valid (Data.IntSet.Internal.singleton x).

Definition prop_Single : Coq.Numbers.BinNums.N -> bool :=
  fun x =>
    (Data.IntSet.Internal.insert x Data.IntSet.Internal.empty GHC.Base.==
     Data.IntSet.Internal.singleton x).

Fixpoint prop_Prefix (arg_0__ : Data.IntSet.Internal.IntSet) : bool
           := match arg_0__ with
              | (Data.IntSet.Internal.Bin prefix msk left_ right_ as s) =>
                  andb (Data.Foldable.all (fun elem =>
                                             Data.IntSet.Internal.match_ elem prefix msk) (Data.IntSet.Internal.toList
                                                                                           s)) (andb (prop_Prefix left_)
                                                                                                     (prop_Prefix
                                                                                                      right_))
              | _ => true
              end.

(* Skipping definition `IntSetProperties.prop_Ordered' *)

Definition prop_NotMember
   : list Coq.Numbers.BinNums.N -> Coq.Numbers.BinNums.N -> bool :=
  fun xs n =>
    let m := Data.IntSet.Internal.fromList xs in
    Data.Foldable.all (fun k =>
                         Data.IntSet.Internal.notMember k m GHC.Base.== (Data.Foldable.notElem k xs))
    (cons n xs).

Definition prop_MemberFromList : list Coq.Numbers.BinNums.N -> bool :=
  fun xs =>
    let abs_xs :=
      Coq.Lists.List.flat_map (fun x =>
                                 if x GHC.Base./= #0 : bool then cons (GHC.Num.abs x) nil else
                                 nil) xs in
    let t := Data.IntSet.Internal.fromList abs_xs in
    andb (Data.Foldable.all (fun arg_2__ => Data.IntSet.Internal.member arg_2__ t)
          abs_xs) (Data.Foldable.all ((fun arg_3__ =>
                                         Data.IntSet.Internal.notMember arg_3__ t) GHC.Base.∘
                                      GHC.Num.negate) abs_xs).

Definition prop_Member
   : list Coq.Numbers.BinNums.N -> Coq.Numbers.BinNums.N -> bool :=
  fun xs n =>
    let m := Data.IntSet.Internal.fromList xs in
    Data.Foldable.all (fun k =>
                         Data.IntSet.Internal.member k m GHC.Base.== (Data.Foldable.elem k xs)) (cons n
                                                                                                      xs).

(* Skipping definition `IntSetProperties.prop_LookupLT' *)

(* Skipping definition `IntSetProperties.prop_LookupLE' *)

(* Skipping definition `IntSetProperties.prop_LookupGT' *)

(* Skipping definition `IntSetProperties.prop_LookupGE' *)

Definition prop_List : list Coq.Numbers.BinNums.N -> bool :=
  fun xs =>
    (Data.OldList.sort (Data.OldList.nub xs) GHC.Base.==
     Data.IntSet.Internal.toAscList (Data.IntSet.Internal.fromList xs)).

Definition prop_LeftRight : Data.IntSet.Internal.IntSet -> bool :=
  fun arg_0__ =>
    match arg_0__ with
    | Data.IntSet.Internal.Bin _ msk left_ right_ =>
        andb (Data.Foldable.and (Coq.Lists.List.flat_map (fun x =>
                                                            cons ((x Data.Bits..&.(**) msk) GHC.Base.== #0) nil)
                                                         (Data.IntSet.Internal.toList left_))) (Data.Foldable.and
              (Coq.Lists.List.flat_map (fun x =>
                                          cons ((x Data.Bits..&.(**) msk) GHC.Base.== msk) nil)
                                       (Data.IntSet.Internal.toList right_)))
    | _ => true
    end.

Definition prop_Int
   : list Coq.Numbers.BinNums.N -> list Coq.Numbers.BinNums.N -> Prop :=
  fun xs ys =>
    let 't := Data.IntSet.Internal.intersection (Data.IntSet.Internal.fromList xs)
                (Data.IntSet.Internal.fromList ys) in
    IntSetValidity.valid t Test.QuickCheck.Property..&&.(**)
    (Data.IntSet.Internal.toAscList t Test.QuickCheck.Property.===
     Data.OldList.sort (Data.OldList.nub ((Data.OldList.intersect) (xs) (ys)))).

Definition prop_InsertIntoEmptyValid : Coq.Numbers.BinNums.N -> Prop :=
  fun x =>
    IntSetValidity.valid (Data.IntSet.Internal.insert x Data.IntSet.Internal.empty).

Definition prop_InsertDelete
   : Coq.Numbers.BinNums.N -> Data.IntSet.Internal.IntSet -> Prop :=
  fun k t =>
    negb (Data.IntSet.Internal.member k t) Test.QuickCheck.Property.==>
    (let 't' := Data.IntSet.Internal.delete k (Data.IntSet.Internal.insert k t) in
     IntSetValidity.valid t' Test.QuickCheck.Property..&&.(**)
     (t' Test.QuickCheck.Property.=== t)).

Definition prop_EmptyValid : Prop :=
  IntSetValidity.valid Data.IntSet.Internal.empty.

Definition prop_Diff
   : list Coq.Numbers.BinNums.N -> list Coq.Numbers.BinNums.N -> Prop :=
  fun xs ys =>
    let 't := Data.IntSet.Internal.difference (Data.IntSet.Internal.fromList xs)
                (Data.IntSet.Internal.fromList ys) in
    IntSetValidity.valid t Test.QuickCheck.Property..&&.(**)
    (Data.IntSet.Internal.toAscList t Test.QuickCheck.Property.===
     Data.OldList.sort (_Data.OldList.\\_ (Data.OldList.nub xs) (Data.OldList.nub
                                                                 ys))).

Definition prop_DescList : list Coq.Numbers.BinNums.N -> bool :=
  fun xs =>
    (GHC.List.reverse (Data.OldList.sort (Data.OldList.nub xs)) GHC.Base.==
     Data.IntSet.Internal.toDescList (Data.IntSet.Internal.fromList xs)).

Definition prop_AscDescList : list Coq.Numbers.BinNums.N -> bool :=
  fun xs =>
    let s := Data.IntSet.Internal.fromList xs in
    Data.IntSet.Internal.toAscList s GHC.Base.==
    GHC.List.reverse (Data.IntSet.Internal.toDescList s).

Definition powersOf2 : Data.IntSet.Internal.IntSet :=
  Data.IntSet.Internal.fromList (Coq.Lists.List.flat_map (fun i =>
                                                            cons (Coq.NArith.BinNat.N.pow #2 i) nil)
                                                         (GHC.Enum.enumFromTo #0 #63)).

Fixpoint prop_MaskPow2 (arg_0__ : Data.IntSet.Internal.IntSet) : bool
           := match arg_0__ with
              | Data.IntSet.Internal.Bin _ msk left_ right_ =>
                  andb (Data.IntSet.Internal.member msk powersOf2) (andb (prop_MaskPow2 left_)
                                                                         (prop_MaskPow2 right_))
              | _ => true
              end.

(* Skipping definition `IntSetProperties.main' *)

Definition forValid {a} `{Test.QuickCheck.Property.Testable a}
   : (Data.IntSet.Internal.IntSet -> a) -> Prop :=
  fun f =>
    Test.QuickCheck.Property.forAll Test.QuickCheck.Arbitrary.arbitrary (fun t =>
                                                                           Test.QuickCheck.Property.classify
                                                                           (Data.IntSet.Internal.size t GHC.Base.== #0)
                                                                           (GHC.Base.hs_string__ "empty")
                                                                           (Test.QuickCheck.Property.classify (andb
                                                                                                               (Data.IntSet.Internal.size
                                                                                                                t
                                                                                                                GHC.Base.>
                                                                                                                #0)
                                                                                                               (Data.IntSet.Internal.size
                                                                                                                t
                                                                                                                GHC.Base.<=
                                                                                                                #10))
                                                                                                              (GHC.Base.hs_string__
                                                                                                               "small")
                                                                                                              (Test.QuickCheck.Property.classify
                                                                                                               (andb
                                                                                                                (Data.IntSet.Internal.size
                                                                                                                 t
                                                                                                                 GHC.Base.>
                                                                                                                 #10)
                                                                                                                (Data.IntSet.Internal.size
                                                                                                                 t
                                                                                                                 GHC.Base.<=
                                                                                                                 #64))
                                                                                                               (GHC.Base.hs_string__
                                                                                                                "medium")
                                                                                                               (Test.QuickCheck.Property.classify
                                                                                                                (Data.IntSet.Internal.size
                                                                                                                 t
                                                                                                                 GHC.Base.>
                                                                                                                 #64)
                                                                                                                (GHC.Base.hs_string__
                                                                                                                 "large")
                                                                                                                (f
                                                                                                                 t))))).

Definition forValidUnitTree {a} `{Test.QuickCheck.Property.Testable a}
   : (Data.IntSet.Internal.IntSet -> a) -> Prop :=
  fun f => forValid f.

Definition prop_Valid : Prop :=
  forValidUnitTree (fun t => IntSetValidity.valid t).

(* Skipping all instances of class `Test.QuickCheck.Arbitrary.Arbitrary',
   including `IntSetProperties.Arbitrary__IntSet' *)

(* External variables:
     Prop andb bool cons list negb nil pair true Coq.Init.Datatypes.length
     Coq.Lists.List.flat_map Coq.NArith.BinNat.N.of_nat Coq.NArith.BinNat.N.pow
     Coq.Numbers.BinNums.N Data.Bits.op_zizazi__ Data.Foldable.all Data.Foldable.and
     Data.Foldable.elem Data.Foldable.foldl Data.Foldable.foldl'
     Data.Foldable.notElem Data.Foldable.null Data.IntSet.Internal.Bin
     Data.IntSet.Internal.IntSet Data.IntSet.Internal.delete
     Data.IntSet.Internal.difference Data.IntSet.Internal.disjoint
     Data.IntSet.Internal.empty Data.IntSet.Internal.filter
     Data.IntSet.Internal.foldl Data.IntSet.Internal.foldl'
     Data.IntSet.Internal.foldr Data.IntSet.Internal.foldr'
     Data.IntSet.Internal.fromList Data.IntSet.Internal.insert
     Data.IntSet.Internal.intersection Data.IntSet.Internal.isProperSubsetOf
     Data.IntSet.Internal.isSubsetOf Data.IntSet.Internal.map
     Data.IntSet.Internal.match_ Data.IntSet.Internal.member
     Data.IntSet.Internal.notMember Data.IntSet.Internal.null
     Data.IntSet.Internal.partition Data.IntSet.Internal.singleton
     Data.IntSet.Internal.size Data.IntSet.Internal.split
     Data.IntSet.Internal.splitMember Data.IntSet.Internal.splitRoot
     Data.IntSet.Internal.toAscList Data.IntSet.Internal.toDescList
     Data.IntSet.Internal.toList Data.IntSet.Internal.union
     Data.IntSet.Internal.unions Data.OldList.intersect Data.OldList.nub
     Data.OldList.op_zrzr__ Data.OldList.sort Data.Set.Internal.Set_
     Data.Set.Internal.fromList Data.Set.Internal.isProperSubsetOf
     Data.Set.Internal.isSubsetOf GHC.Base.compare GHC.Base.flip GHC.Base.id
     GHC.Base.op_z2218U__ GHC.Base.op_zeze__ GHC.Base.op_zg__ GHC.Base.op_zl__
     GHC.Base.op_zlze__ GHC.Base.op_zsze__ GHC.Enum.enumFromTo GHC.List.reverse
     GHC.Num.abs GHC.Num.fromInteger GHC.Num.negate GHC.Num.op_zp__ GHC.Real.even
     GHC.Real.odd IntSetValidity.valid Test.QuickCheck.Arbitrary.arbitrary
     Test.QuickCheck.Property.Testable Test.QuickCheck.Property.classify
     Test.QuickCheck.Property.forAll Test.QuickCheck.Property.op_zezeze__
     Test.QuickCheck.Property.op_zezezg__ Test.QuickCheck.Property.op_zizazazi__
*)
