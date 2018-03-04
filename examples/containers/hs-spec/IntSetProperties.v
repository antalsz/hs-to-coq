(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Coq.Program.Tactics.
Require Coq.Program.Wf.

(* Preamble *)

From mathcomp Require Import ssreflect ssrbool.
Set Bullet Behavior "Strict Subproofs".

Require Coq.ZArith.BinInt.
Local Notation Zpow := Coq.ZArith.BinInt.Z.pow.
Local Notation Zle  := Coq.ZArith.BinInt.Z.le.

Require GHC.Enum.
Notation enumFromTo := GHC.Enum.enumFromTo.

Require GHC.Base.
Import GHC.Base.Notations.

Require GHC.Num.

Require IntSetProofs.

Record Gen a := MkGen { unGen : a -> Prop }.
Arguments MkGen {_} _.
Arguments unGen {_} _ _.

Class Arbitrary (a : Type) := { arbitrary : Gen a }.

Class Propable (a : Type) := { toProp : a -> Prop }.


Definition forAll {a prop} `{Propable prop} (g : Gen a) (p : a -> prop) : Prop :=
  forall (x : a), unGen g x -> toProp (p x).
Arguments forAll {_ _ _} / _ _.


Instance Propable_Prop : Propable Prop :=
  { toProp := id }.

Instance Propable_bool : Propable bool :=
  { toProp := is_true }.

Instance Propable_unit : Propable unit :=
  { toProp := fun _ => True }.

Instance Propable_fn {a prop} `{Arbitrary a} `{Propable prop} : Propable (a -> prop) :=
  { toProp := forAll arbitrary }.


Definition implies {prop} `{Propable prop} (c : bool) (p : prop) : Prop :=
  if c then toProp p else True.
Infix ".==>." := implies (at level 99).

Definition andp {prop1 prop2} `{Propable prop1} `{Propable prop2} (p1 : prop1) (p2 : prop2) : Prop :=
  toProp p1 /\ toProp p2.
Infix ".&&." := andp (at level 99).

Definition orp {prop1 prop2} `{Propable prop1} `{Propable prop2} (p1 : prop1) (p2 : prop2) : Prop :=
  toProp p1 \/ toProp p2.
Infix ".||." := orp (at level 99).


Definition choose {a} `{GHC.Base.Ord a} (range : a * a) : Gen a :=
  MkGen (fun x => (fst range GHC.Base.<= x) && (x GHC.Base.<= snd range)).


Definition skip_classify {prop} `{Propable prop} (_ : bool) (_ : GHC.Base.String) : prop -> Prop :=
  toProp.


Instance Arbitrary_bool : Arbitrary bool :=
  { arbitrary := MkGen xpredT }.

Instance Arbitrary_Int : Arbitrary GHC.Num.Int :=
  { arbitrary := MkGen (fun x => Zle 0 x) }. (* For IntSet *)

Instance Arbitrary_list {a} `{Arbitrary a} : Arbitrary (list a) :=
  { arbitrary := MkGen (Coq.Lists.List.Forall (unGen arbitrary)) }.

Instance Arbitrary_IntSet : Arbitrary Data.IntSet.Internal.IntSet :=
  { arbitrary := MkGen IntSetProofs.WF }.

(* Converted imports: *)

Require Coq.Lists.List.
Require Data.Bits.
Require Data.Foldable.
Require Data.IntSet.Internal.
Require Data.OldList.
Require Data.Set.Internal.
Require GHC.Base.
Require GHC.List.
Require GHC.Num.
Require GHC.Real.
Require IntSetValidity.
Import Data.Bits.Notations.
Import Data.OldList.Notations.
Import GHC.Base.Notations.
Import GHC.Num.Notations.

(* No type declarations to convert. *)
(* Converted value declarations: *)

(* Translating `instance Test.QuickCheck.Arbitrary.Arbitrary
   Data.IntSet.Internal.IntSet' failed: OOPS! Cannot find information for class
   Qualified "Test.QuickCheck.Arbitrary" "Arbitrary" unsupported *)

Definition forValid {a} `{Propable a}
   : (Data.IntSet.Internal.IntSet -> a) -> Prop :=
  fun f =>
    forAll arbitrary GHC.Base.$
    (fun t =>
       skip_classify (Data.IntSet.Internal.size t GHC.Base.== #0) (GHC.Base.hs_string__
                                                                   "empty") GHC.Base.$
       (skip_classify (andb (Data.IntSet.Internal.size t GHC.Base.> #0)
                            (Data.IntSet.Internal.size t GHC.Base.<= #10)) (GHC.Base.hs_string__ "small")
        GHC.Base.$
        (skip_classify (andb (Data.IntSet.Internal.size t GHC.Base.> #10)
                             (Data.IntSet.Internal.size t GHC.Base.<= #64)) (GHC.Base.hs_string__ "medium")
         GHC.Base.$
         (skip_classify (Data.IntSet.Internal.size t GHC.Base.> #64)
          (GHC.Base.hs_string__ "large") GHC.Base.$
          f t)))).

Definition forValidUnitTree {a} `{Propable a}
   : (Data.IntSet.Internal.IntSet -> a) -> Prop :=
  fun f => forValid f.

Definition prop_Valid : Prop :=
  forValidUnitTree GHC.Base.$ (fun t => IntSetValidity.valid t).

Definition powersOf2 : Data.IntSet.Internal.IntSet :=
  Data.IntSet.Internal.fromList (Coq.Lists.List.flat_map (fun i =>
                                                            cons (Zpow #2 i) nil) (enumFromTo #0 #63)).

Definition prop_MaskPow2 : Data.IntSet.Internal.IntSet -> bool :=
  fix prop_MaskPow2 arg_0__
        := match arg_0__ with
           | Data.IntSet.Internal.Bin _ msk left_ right_ =>
               andb (Data.IntSet.Internal.member msk powersOf2) (andb (prop_MaskPow2 left_)
                                                                      (prop_MaskPow2 right_))
           | _ => true
           end.

Definition prop_AscDescList : list GHC.Num.Int -> bool :=
  fun xs =>
    let s := Data.IntSet.Internal.fromList xs in
    Data.IntSet.Internal.toAscList s GHC.Base.==
    GHC.List.reverse (Data.IntSet.Internal.toDescList s).

Definition prop_DescList : list GHC.Num.Int -> bool :=
  fun xs =>
    (GHC.List.reverse (Data.OldList.sort (Data.OldList.nub xs)) GHC.Base.==
     Data.IntSet.Internal.toDescList (Data.IntSet.Internal.fromList xs)).

Definition prop_Diff : list GHC.Num.Int -> list GHC.Num.Int -> Prop :=
  fun xs ys =>
    let 't := Data.IntSet.Internal.difference (Data.IntSet.Internal.fromList xs)
                (Data.IntSet.Internal.fromList ys) in
    IntSetValidity.valid t .&&.(**)
    (Data.IntSet.Internal.toAscList t GHC.Base.==
     Data.OldList.sort (_Data.OldList.\\_ (Data.OldList.nub xs) (Data.OldList.nub
                                                                 ys))).

Definition prop_EmptyValid : Prop :=
  IntSetValidity.valid Data.IntSet.Internal.empty.

Definition prop_InsertDelete
   : GHC.Num.Int -> Data.IntSet.Internal.IntSet -> Prop :=
  fun k t =>
    negb (Data.IntSet.Internal.member k t) .==>.(**)
    (let 't' := Data.IntSet.Internal.delete k (Data.IntSet.Internal.insert k t) in
     IntSetValidity.valid t' .&&.(**) (t' GHC.Base.== t)).

Definition prop_InsertIntoEmptyValid : GHC.Num.Int -> Prop :=
  fun x =>
    IntSetValidity.valid (Data.IntSet.Internal.insert x Data.IntSet.Internal.empty).

Definition prop_Int : list GHC.Num.Int -> list GHC.Num.Int -> Prop :=
  fun xs ys =>
    let 't := Data.IntSet.Internal.intersection (Data.IntSet.Internal.fromList xs)
                (Data.IntSet.Internal.fromList ys) in
    IntSetValidity.valid t .&&.(**)
    (Data.IntSet.Internal.toAscList t GHC.Base.==
     Data.OldList.sort (Data.OldList.nub ((Data.OldList.intersect) (xs) (ys)))).

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

Definition prop_List : list GHC.Num.Int -> bool :=
  fun xs =>
    (Data.OldList.sort (Data.OldList.nub xs) GHC.Base.==
     Data.IntSet.Internal.toAscList (Data.IntSet.Internal.fromList xs)).

Definition prop_Member : list GHC.Num.Int -> GHC.Num.Int -> bool :=
  fun xs n =>
    let m := Data.IntSet.Internal.fromList xs in
    Data.Foldable.all (fun k =>
                         Data.IntSet.Internal.member k m GHC.Base.== (Data.Foldable.elem k xs)) (cons n
                                                                                                      xs).

Definition prop_MemberFromList : list GHC.Num.Int -> bool :=
  fun xs =>
    let abs_xs :=
      Coq.Lists.List.flat_map (fun x =>
                                 if x GHC.Base./= #0 : bool
                                 then cons (GHC.Num.abs x) nil
                                 else nil) xs in
    let t := Data.IntSet.Internal.fromList abs_xs in
    andb (Data.Foldable.all (fun arg_2__ => Data.IntSet.Internal.member arg_2__ t)
          abs_xs) (Data.Foldable.all ((fun arg_3__ =>
                                         Data.IntSet.Internal.notMember arg_3__ t) GHC.Base.∘
                                      GHC.Num.negate) abs_xs).

Definition prop_NotMember : list GHC.Num.Int -> GHC.Num.Int -> bool :=
  fun xs n =>
    let m := Data.IntSet.Internal.fromList xs in
    Data.Foldable.all (fun k =>
                         Data.IntSet.Internal.notMember k m GHC.Base.== (Data.Foldable.notElem k xs))
    (cons n xs).

Definition prop_Prefix : Data.IntSet.Internal.IntSet -> bool :=
  fix prop_Prefix arg_0__
        := match arg_0__ with
           | (Data.IntSet.Internal.Bin prefix msk left_ right_ as s) =>
               andb (Data.Foldable.all (fun elem =>
                                          Data.IntSet.Internal.match_ elem prefix msk) (Data.IntSet.Internal.toList s))
                    (andb (prop_Prefix left_) (prop_Prefix right_))
           | _ => true
           end.

Definition prop_Single : GHC.Num.Int -> bool :=
  fun x =>
    (Data.IntSet.Internal.insert x Data.IntSet.Internal.empty GHC.Base.==
     Data.IntSet.Internal.singleton x).

Definition prop_SingletonValid : GHC.Num.Int -> Prop :=
  fun x => IntSetValidity.valid (Data.IntSet.Internal.singleton x).

Definition prop_UnionAssoc
   : Data.IntSet.Internal.IntSet ->
     Data.IntSet.Internal.IntSet -> Data.IntSet.Internal.IntSet -> bool :=
  fun t1 t2 t3 =>
    Data.IntSet.Internal.union t1 (Data.IntSet.Internal.union t2 t3) GHC.Base.==
    Data.IntSet.Internal.union (Data.IntSet.Internal.union t1 t2) t3.

Definition prop_UnionComm
   : Data.IntSet.Internal.IntSet -> Data.IntSet.Internal.IntSet -> bool :=
  fun t1 t2 =>
    (Data.IntSet.Internal.union t1 t2 GHC.Base.== Data.IntSet.Internal.union t2 t1).

Definition prop_UnionInsert
   : GHC.Num.Int -> Data.IntSet.Internal.IntSet -> Prop :=
  fun x t =>
    let 't' := Data.IntSet.Internal.union t (Data.IntSet.Internal.singleton x) in
    IntSetValidity.valid t' .&&.(**)
    (t' GHC.Base.== Data.IntSet.Internal.insert x t).

Definition prop_disjoint
   : Data.IntSet.Internal.IntSet -> Data.IntSet.Internal.IntSet -> bool :=
  fun a b =>
    Data.IntSet.Internal.disjoint a b GHC.Base.==
    Data.IntSet.Internal.null (Data.IntSet.Internal.intersection a b).

Definition prop_filter : Data.IntSet.Internal.IntSet -> GHC.Num.Int -> Prop :=
  fun s i =>
    let evens := Data.IntSet.Internal.filter GHC.Real.even s in
    let odds := Data.IntSet.Internal.filter GHC.Real.odd s in
    let parts := Data.IntSet.Internal.partition GHC.Real.odd s in
    IntSetValidity.valid odds .&&.(**)
    (IntSetValidity.valid evens .&&.(**) (parts GHC.Base.== pair odds evens)).

Definition prop_foldL : Data.IntSet.Internal.IntSet -> bool :=
  fun s =>
    Data.IntSet.Internal.foldl (GHC.Base.flip cons) nil s GHC.Base.==
    Data.Foldable.foldl (GHC.Base.flip cons) nil (Data.IntSet.Internal.toList s).

Definition prop_foldL' : Data.IntSet.Internal.IntSet -> bool :=
  fun s =>
    Data.IntSet.Internal.foldl' (GHC.Base.flip cons) nil s GHC.Base.==
    Data.Foldable.foldl' (GHC.Base.flip cons) nil (Data.IntSet.Internal.toList s).

Definition prop_foldR : Data.IntSet.Internal.IntSet -> bool :=
  fun s =>
    Data.IntSet.Internal.foldr cons nil s GHC.Base.== Data.IntSet.Internal.toList s.

Definition prop_foldR' : Data.IntSet.Internal.IntSet -> bool :=
  fun s =>
    Data.IntSet.Internal.foldr' cons nil s GHC.Base.==
    Data.IntSet.Internal.toList s.

Definition prop_isProperSubsetOf2
   : Data.IntSet.Internal.IntSet -> Data.IntSet.Internal.IntSet -> bool :=
  fun a b =>
    let c := Data.IntSet.Internal.union a b in
    Data.IntSet.Internal.isProperSubsetOf a c GHC.Base.== (a GHC.Base./= c).

Definition prop_isSubsetOf2
   : Data.IntSet.Internal.IntSet -> Data.IntSet.Internal.IntSet -> bool :=
  fun a b => Data.IntSet.Internal.isSubsetOf a (Data.IntSet.Internal.union a b).

Definition prop_map : Data.IntSet.Internal.IntSet -> bool :=
  fun s => Data.IntSet.Internal.map GHC.Base.id s GHC.Base.== s.

Definition prop_ord
   : Data.IntSet.Internal.IntSet -> Data.IntSet.Internal.IntSet -> bool :=
  fun s1 s2 =>
    GHC.Base.compare s1 s2 GHC.Base.==
    GHC.Base.compare (Data.IntSet.Internal.toList s1) (Data.IntSet.Internal.toList
                      s2).

Definition prop_partition
   : Data.IntSet.Internal.IntSet -> GHC.Num.Int -> Prop :=
  fun s i =>
    let 'pair s1 s2 := Data.IntSet.Internal.partition GHC.Real.odd s in
    IntSetValidity.valid s1 .&&.(**)
    (IntSetValidity.valid s2 .&&.(**)
     (Data.Foldable.all GHC.Real.odd (Data.IntSet.Internal.toList s1) .&&.(**)
      (Data.Foldable.all GHC.Real.even (Data.IntSet.Internal.toList s2) .&&.(**)
       (s GHC.Base.== Data.IntSet.Internal.union s1 s2)))).

Definition prop_size : Data.IntSet.Internal.IntSet -> Prop :=
  fun s =>
    let sz := Data.IntSet.Internal.size s in
    (sz GHC.Base.==
     Data.IntSet.Internal.foldl' (fun arg_1__ arg_2__ =>
                                    match arg_1__, arg_2__ with
                                    | i, _ => i GHC.Num.+ #1
                                    end) (#0 : GHC.Num.Int) s) .&&.(**)
    (sz GHC.Base.== Data.Foldable.length (Data.IntSet.Internal.toList s)).

Definition prop_split : Data.IntSet.Internal.IntSet -> GHC.Num.Int -> Prop :=
  fun s i =>
    let 'pair s1 s2 := Data.IntSet.Internal.split i s in
    IntSetValidity.valid s1 .&&.(**)
    (IntSetValidity.valid s2 .&&.(**)
     (Data.Foldable.all (fun arg_1__ => arg_1__ GHC.Base.< i)
      (Data.IntSet.Internal.toList s1) .&&.(**)
      (Data.Foldable.all (fun arg_2__ => arg_2__ GHC.Base.> i)
       (Data.IntSet.Internal.toList s2) .&&.(**)
       (Data.IntSet.Internal.delete i s GHC.Base.==
        Data.IntSet.Internal.union s1 s2)))).

Definition prop_splitMember
   : Data.IntSet.Internal.IntSet -> GHC.Num.Int -> Prop :=
  fun s i =>
    let 'pair (pair s1 t) s2 := Data.IntSet.Internal.splitMember i s in
    IntSetValidity.valid s1 .&&.(**)
    (IntSetValidity.valid s2 .&&.(**)
     (Data.Foldable.all (fun arg_1__ => arg_1__ GHC.Base.< i)
      (Data.IntSet.Internal.toList s1) .&&.(**)
      (Data.Foldable.all (fun arg_2__ => arg_2__ GHC.Base.> i)
       (Data.IntSet.Internal.toList s2) .&&.(**)
       ((t GHC.Base.== Data.IntSet.Internal.member i s) .&&.(**)
        (Data.IntSet.Internal.delete i s GHC.Base.==
         Data.IntSet.Internal.union s1 s2))))).

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
                                                                                      then cons (pair x y) nil
                                                                                      else nil)
                                                                                   (Data.IntSet.Internal.toList
                                                                                    (Data.IntSet.Internal.unions rst)))
                                                        (Data.IntSet.Internal.toList s1))
        end in
    let ls := Data.IntSet.Internal.splitRoot s in
    andb (loop ls) (s GHC.Base.== Data.IntSet.Internal.unions ls).

Definition toSet
   : Data.IntSet.Internal.IntSet -> Data.Set.Internal.Set_ GHC.Num.Int :=
  Data.Set.Internal.fromList GHC.Base.∘ Data.IntSet.Internal.toList.

Definition prop_isSubsetOf
   : Data.IntSet.Internal.IntSet -> Data.IntSet.Internal.IntSet -> bool :=
  fun a b =>
    Data.IntSet.Internal.isSubsetOf a b GHC.Base.==
    Data.Set.Internal.isSubsetOf (toSet a) (toSet b).

Definition prop_isProperSubsetOf
   : Data.IntSet.Internal.IntSet -> Data.IntSet.Internal.IntSet -> bool :=
  fun a b =>
    Data.IntSet.Internal.isProperSubsetOf a b GHC.Base.==
    Data.Set.Internal.isProperSubsetOf (toSet a) (toSet b).

(* Unbound variables:
     Prop Propable Zpow andb arbitrary bool cons enumFromTo forAll list negb nil
     op_zizazazi__ op_zizezezgzi__ pair skip_classify true Coq.Lists.List.flat_map
     Data.Bits.op_zizazi__ Data.Foldable.all Data.Foldable.and Data.Foldable.elem
     Data.Foldable.foldl Data.Foldable.foldl' Data.Foldable.length
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
     GHC.Base.op_z2218U__ GHC.Base.op_zd__ GHC.Base.op_zeze__ GHC.Base.op_zg__
     GHC.Base.op_zl__ GHC.Base.op_zlze__ GHC.Base.op_zsze__ GHC.List.reverse
     GHC.Num.Int GHC.Num.abs GHC.Num.fromInteger GHC.Num.negate GHC.Num.op_zp__
     GHC.Real.even GHC.Real.odd IntSetValidity.valid
*)
