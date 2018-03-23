(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Coq.Program.Tactics.
Require Coq.Program.Wf.

(* Preamble *)

Require BitTerminationProofs.

(* Converted imports: *)

Require Coq.Init.Peano.
Require Coq.NArith.BinNat.
Require Coq.Numbers.BinNums.
Require Data.Bits.
Require Data.Foldable.
Require Data.Maybe.
Require Data.Semigroup.
Require Data.Tuple.
Require GHC.Base.
Require GHC.Num.
Require GHC.Wf.
Require Utils.Containers.Internal.BitUtil.
Import Data.Bits.Notations.
Import Data.Semigroup.Notations.
Import GHC.Base.Notations.
Import GHC.Num.Notations.

(* Converted type declarations: *)

Definition Prefix :=
  Coq.Numbers.BinNums.N.

Definition Nat :=
  Coq.Numbers.BinNums.N.

Definition Mask :=
  Coq.Numbers.BinNums.N.

Definition Key :=
  Coq.Numbers.BinNums.N%type.

Definition BitMap :=
  Coq.Numbers.BinNums.N.

Inductive IntSet : Type
  := Bin : Prefix -> Mask -> IntSet -> IntSet -> IntSet
  |  Tip : Prefix -> BitMap -> IntSet
  |  Nil : IntSet.

Inductive Stack : Type
  := Push : Prefix -> IntSet -> Stack -> Stack
  |  Nada : Stack.
(* Midamble *)

(** Additional definitions for termination proof *)

Fixpoint size_nat (t : IntSet) : nat :=
  match t with
  | Bin _ _ l r => S (size_nat l + size_nat r)%nat
  | Tip _ bm => 0
  | Nil => 0
  end.

Require Omega.
Ltac termination_by_omega :=
  Coq.Program.Tactics.program_simpl;
  simpl;Omega.omega.


Require Import Coq.NArith.NArith.
(* Z.ones 6 = 64-1 *)
(* Definition suffixBitMask := Coq.NArith.BinNat.N.ones 6%N. *)

(* Converted value declarations: *)

(* Translating `instance Data__IntSet' failed: OOPS! Cannot find information for
   class Qualified "Data.Data" "Data" unsupported *)

(* Translating `instance IsList__IntSet' failed: OOPS! Cannot find information
   for class Qualified "GHC.Exts" "IsList" unsupported *)

(* Translating `instance Show__IntSet' failed: OOPS! Cannot find information for
   class Qualified "GHC.Show" "Show" unsupported *)

(* Translating `instance Read__IntSet' failed: OOPS! Cannot find information for
   class Qualified "GHC.Read" "Read" unsupported *)

(* Translating `instance NFData__IntSet' failed: OOPS! Cannot find information
   for class Qualified "Control.DeepSeq" "NFData" unsupported *)

Definition bin : Prefix -> Mask -> IntSet -> IntSet -> IntSet :=
  fun arg_0__ arg_1__ arg_2__ arg_3__ =>
    match arg_0__, arg_1__, arg_2__, arg_3__ with
    | _, _, l, Nil => l
    | _, _, Nil, r => r
    | p, m, l, r => Bin p m l r
    end.

Definition bitmapOfSuffix : Coq.Numbers.BinNums.N -> BitMap :=
  fun s => Utils.Containers.Internal.BitUtil.shiftLL #1 s.

Definition branchMask : Prefix -> Prefix -> Mask :=
  fun p1 p2 =>
    Coq.NArith.BinNat.N.pow 2 (Coq.NArith.BinNat.N.log2 (Coq.NArith.BinNat.N.lxor p1
                                                                                  p2)).

Definition empty : IntSet :=
  Nil.

Local Definition Monoid__IntSet_mempty : IntSet :=
  empty.

Definition equal : IntSet -> IntSet -> bool :=
  fix equal arg_0__ arg_1__
        := match arg_0__, arg_1__ with
           | Bin p1 m1 l1 r1, Bin p2 m2 l2 r2 =>
               andb (m1 GHC.Base.== m2) (andb (p1 GHC.Base.== p2) (andb (equal l1 l2) (equal r1
                                                                         r2)))
           | Tip kx1 bm1, Tip kx2 bm2 => andb (kx1 GHC.Base.== kx2) (bm1 GHC.Base.== bm2)
           | Nil, Nil => true
           | _, _ => false
           end.

Local Definition Eq___IntSet_op_zeze__ : IntSet -> IntSet -> bool :=
  fun t1 t2 => equal t1 t2.

Definition indexOfTheOnlyBit :=
  fun x => Coq.NArith.BinNat.N.log2 x.

Definition lowestBitSet : Nat -> Coq.Numbers.BinNums.N :=
  fun x => indexOfTheOnlyBit (Utils.Containers.Internal.BitUtil.lowestBitMask x).

Definition unsafeFindMin : IntSet -> option Key :=
  fix unsafeFindMin arg_0__
        := match arg_0__ with
           | Nil => None
           | Tip kx bm => Some (_GHC.Num.+_ kx (lowestBitSet bm))
           | Bin _ _ l _ => unsafeFindMin l
           end.

Definition highestBitSet : Nat -> Coq.Numbers.BinNums.N :=
  fun x => indexOfTheOnlyBit (Utils.Containers.Internal.BitUtil.highestBitMask x).

Definition unsafeFindMax : IntSet -> option Key :=
  fix unsafeFindMax arg_0__
        := match arg_0__ with
           | Nil => None
           | Tip kx bm => Some (_GHC.Num.+_ kx (highestBitSet bm))
           | Bin _ _ _ r => unsafeFindMax r
           end.

Program Definition foldlBits {a}
           : Coq.Numbers.BinNums.N ->
             (a -> Coq.Numbers.BinNums.N -> a) -> a -> Nat -> a :=
          fun prefix f z bitmap =>
            let go :=
              GHC.Wf.wfFix2 Coq.Init.Peano.lt (fun arg_0__ arg_1__ =>
                               Coq.NArith.BinNat.N.to_nat arg_0__) _ (fun arg_0__ arg_1__ go =>
                               match arg_0__, arg_1__ with
                               | num_2__, acc =>
                                   if Bool.Sumbool.sumbool_of_bool (num_2__ GHC.Base.== #0) then acc else
                                   match arg_0__, arg_1__ with
                                   | bm, acc =>
                                       let 'bitmask := Utils.Containers.Internal.BitUtil.lowestBitMask bm in
                                       let 'bi := indexOfTheOnlyBit bitmask in
                                       go (Data.Bits.xor bm bitmask) (f acc (_GHC.Num.+_ prefix bi))
                                   end
                               end) in
            go bitmap z.
Solve Obligations with (BitTerminationProofs.termination_foldl).

Definition foldl {a} : (a -> Key -> a) -> a -> IntSet -> a :=
  fun f z =>
    let fix go arg_0__ arg_1__
              := match arg_0__, arg_1__ with
                 | z', Nil => z'
                 | z', Tip kx bm => foldlBits kx f z' bm
                 | z', Bin _ _ l r => go (go z' l) r
                 end in
    fun t =>
      match t with
      | Bin _ m l r => if m GHC.Base.< #0 : bool then go (go z r) l else go (go z l) r
      | _ => go z t
      end.

Definition foldlFB {a} : (a -> Key -> a) -> a -> IntSet -> a :=
  foldl.

Definition toDescList : IntSet -> list Key :=
  foldl (GHC.Base.flip cons) nil.

Program Definition foldl'Bits {a}
           : Coq.Numbers.BinNums.N ->
             (a -> Coq.Numbers.BinNums.N -> a) -> a -> Nat -> a :=
          fun prefix f z bitmap =>
            let go :=
              GHC.Wf.wfFix2 Coq.Init.Peano.lt (fun arg_0__ arg_1__ =>
                               Coq.NArith.BinNat.N.to_nat arg_0__) _ (fun arg_0__ arg_1__ go =>
                               match arg_0__, arg_1__ with
                               | num_2__, acc =>
                                   if Bool.Sumbool.sumbool_of_bool (num_2__ GHC.Base.== #0) then acc else
                                   match arg_0__, arg_1__ with
                                   | bm, acc =>
                                       let 'bitmask := Utils.Containers.Internal.BitUtil.lowestBitMask bm in
                                       let 'bi := indexOfTheOnlyBit bitmask in
                                       go (Data.Bits.xor bm bitmask) (f acc (_GHC.Num.+_ prefix bi))
                                   end
                               end) in
            go bitmap z.
Solve Obligations with (BitTerminationProofs.termination_foldl).

Definition foldl' {a} : (a -> Key -> a) -> a -> IntSet -> a :=
  fun f z =>
    let fix go arg_0__ arg_1__
              := match arg_0__, arg_1__ with
                 | z', Nil => z'
                 | z', Tip kx bm => foldl'Bits kx f z' bm
                 | z', Bin _ _ l r => go (go z' l) r
                 end in
    fun t =>
      match t with
      | Bin _ m l r => if m GHC.Base.< #0 : bool then go (go z r) l else go (go z l) r
      | _ => go z t
      end.

Definition maskW : Nat -> Nat -> Prefix :=
  fun i m => Coq.NArith.BinNat.N.ldiff i (2 * m - 1 % N).

Definition mask : Coq.Numbers.BinNums.N -> Mask -> Prefix :=
  fun i m => maskW (i) (m).

Definition match_ : Coq.Numbers.BinNums.N -> Prefix -> Mask -> bool :=
  fun i p m => (mask i m) GHC.Base.== p.

Definition nomatch : Coq.Numbers.BinNums.N -> Prefix -> Mask -> bool :=
  fun i p m => (mask i m) GHC.Base./= p.

Definition nequal : IntSet -> IntSet -> bool :=
  fix nequal arg_0__ arg_1__
        := match arg_0__, arg_1__ with
           | Bin p1 m1 l1 r1, Bin p2 m2 l2 r2 =>
               orb (m1 GHC.Base./= m2) (orb (p1 GHC.Base./= p2) (orb (nequal l1 l2) (nequal r1
                                                                      r2)))
           | Tip kx1 bm1, Tip kx2 bm2 => orb (kx1 GHC.Base./= kx2) (bm1 GHC.Base./= bm2)
           | Nil, Nil => false
           | _, _ => true
           end.

Local Definition Eq___IntSet_op_zsze__ : IntSet -> IntSet -> bool :=
  fun t1 t2 => nequal t1 t2.

Program Instance Eq___IntSet : GHC.Base.Eq_ IntSet :=
  fun _ k =>
    k {| GHC.Base.op_zeze____ := Eq___IntSet_op_zeze__ ;
         GHC.Base.op_zsze____ := Eq___IntSet_op_zsze__ |}.

Definition null : IntSet -> bool :=
  fun arg_0__ => match arg_0__ with | Nil => true | _ => false end.

Definition revNat : Nat -> Nat :=
  fun x1 =>
    let 'x2 := ((Utils.Containers.Internal.BitUtil.shiftRL x1 #1) Data.Bits..&.(**)
                  #6148914691236517205) Data.Bits..|.(**)
                 (Utils.Containers.Internal.BitUtil.shiftLL (x1 Data.Bits..&.(**)
                                                             #6148914691236517205) #1) in
    let 'x3 := ((Utils.Containers.Internal.BitUtil.shiftRL x2 #2) Data.Bits..&.(**)
                  #3689348814741910323) Data.Bits..|.(**)
                 (Utils.Containers.Internal.BitUtil.shiftLL (x2 Data.Bits..&.(**)
                                                             #3689348814741910323) #2) in
    let 'x4 := ((Utils.Containers.Internal.BitUtil.shiftRL x3 #4) Data.Bits..&.(**)
                  #1085102592571150095) Data.Bits..|.(**)
                 (Utils.Containers.Internal.BitUtil.shiftLL (x3 Data.Bits..&.(**)
                                                             #1085102592571150095) #4) in
    let 'x5 := ((Utils.Containers.Internal.BitUtil.shiftRL x4 #8) Data.Bits..&.(**)
                  #71777214294589695) Data.Bits..|.(**)
                 (Utils.Containers.Internal.BitUtil.shiftLL (x4 Data.Bits..&.(**)
                                                             #71777214294589695) #8) in
    let 'x6 := ((Utils.Containers.Internal.BitUtil.shiftRL x5 #16) Data.Bits..&.(**)
                  #281470681808895) Data.Bits..|.(**)
                 (Utils.Containers.Internal.BitUtil.shiftLL (x5 Data.Bits..&.(**)
                                                             #281470681808895) #16) in
    (Utils.Containers.Internal.BitUtil.shiftRL x6 #32) Data.Bits..|.(**)
    (Utils.Containers.Internal.BitUtil.shiftLL x6 #32).

Definition revNatSafe n :=
  Coq.NArith.BinNat.N.modulo (revNat n) (Coq.NArith.BinNat.N.pow 2 64).

Program Definition foldrBits {a}
           : Coq.Numbers.BinNums.N ->
             (Coq.Numbers.BinNums.N -> a -> a) -> a -> Nat -> a :=
          fun prefix f z bitmap =>
            let go :=
              GHC.Wf.wfFix2 Coq.Init.Peano.lt (fun arg_0__ arg_1__ =>
                               Coq.NArith.BinNat.N.to_nat arg_0__) _ (fun arg_0__ arg_1__ go =>
                               match arg_0__, arg_1__ with
                               | num_2__, acc =>
                                   if Bool.Sumbool.sumbool_of_bool (num_2__ GHC.Base.== #0) then acc else
                                   match arg_0__, arg_1__ with
                                   | bm, acc =>
                                       let 'bitmask := Utils.Containers.Internal.BitUtil.lowestBitMask bm in
                                       let 'bi := indexOfTheOnlyBit bitmask in
                                       go (Data.Bits.xor bm bitmask) ((f (_GHC.Num.-_ (prefix GHC.Num.+
                                                                                       (#64 GHC.Num.- #1)) bi)) acc)
                                   end
                               end) in
            go (revNatSafe bitmap) z.
Solve Obligations with (BitTerminationProofs.termination_foldl).

Definition foldr {b} : (Key -> b -> b) -> b -> IntSet -> b :=
  fun f z =>
    let fix go arg_0__ arg_1__
              := match arg_0__, arg_1__ with
                 | z', Nil => z'
                 | z', Tip kx bm => foldrBits kx f z' bm
                 | z', Bin _ _ l r => go (go z' r) l
                 end in
    fun t =>
      match t with
      | Bin _ m l r => if m GHC.Base.< #0 : bool then go (go z l) r else go (go z r) l
      | _ => go z t
      end.

Definition foldrFB {b} : (Key -> b -> b) -> b -> IntSet -> b :=
  foldr.

Definition toAscList : IntSet -> list Key :=
  foldr cons nil.

Definition toList : IntSet -> list Key :=
  toAscList.

Definition elems : IntSet -> list Key :=
  toAscList.

Local Definition Ord__IntSet_compare : IntSet -> IntSet -> comparison :=
  fun s1 s2 => GHC.Base.compare (toAscList s1) (toAscList s2).

Local Definition Ord__IntSet_op_zg__ : IntSet -> IntSet -> bool :=
  fun x y => _GHC.Base.==_ (Ord__IntSet_compare x y) Gt.

Local Definition Ord__IntSet_op_zgze__ : IntSet -> IntSet -> bool :=
  fun x y => _GHC.Base./=_ (Ord__IntSet_compare x y) Lt.

Local Definition Ord__IntSet_op_zl__ : IntSet -> IntSet -> bool :=
  fun x y => _GHC.Base.==_ (Ord__IntSet_compare x y) Lt.

Local Definition Ord__IntSet_op_zlze__ : IntSet -> IntSet -> bool :=
  fun x y => _GHC.Base./=_ (Ord__IntSet_compare x y) Gt.

Local Definition Ord__IntSet_max : IntSet -> IntSet -> IntSet :=
  fun x y => if Ord__IntSet_op_zlze__ x y : bool then y else x.

Local Definition Ord__IntSet_min : IntSet -> IntSet -> IntSet :=
  fun x y => if Ord__IntSet_op_zlze__ x y : bool then x else y.

Program Instance Ord__IntSet : GHC.Base.Ord IntSet :=
  fun _ k =>
    k {| GHC.Base.op_zl____ := Ord__IntSet_op_zl__ ;
         GHC.Base.op_zlze____ := Ord__IntSet_op_zlze__ ;
         GHC.Base.op_zg____ := Ord__IntSet_op_zg__ ;
         GHC.Base.op_zgze____ := Ord__IntSet_op_zgze__ ;
         GHC.Base.compare__ := Ord__IntSet_compare ;
         GHC.Base.max__ := Ord__IntSet_max ;
         GHC.Base.min__ := Ord__IntSet_min |}.

Definition fold {b} : (Key -> b -> b) -> b -> IntSet -> b :=
  foldr.

Program Definition foldr'Bits {a}
           : Coq.Numbers.BinNums.N ->
             (Coq.Numbers.BinNums.N -> a -> a) -> a -> Nat -> a :=
          fun prefix f z bitmap =>
            let go :=
              GHC.Wf.wfFix2 Coq.Init.Peano.lt (fun arg_0__ arg_1__ =>
                               Coq.NArith.BinNat.N.to_nat arg_0__) _ (fun arg_0__ arg_1__ go =>
                               match arg_0__, arg_1__ with
                               | num_2__, acc =>
                                   if Bool.Sumbool.sumbool_of_bool (num_2__ GHC.Base.== #0) then acc else
                                   match arg_0__, arg_1__ with
                                   | bm, acc =>
                                       let 'bitmask := Utils.Containers.Internal.BitUtil.lowestBitMask bm in
                                       let 'bi := indexOfTheOnlyBit bitmask in
                                       go (Data.Bits.xor bm bitmask) ((f (_GHC.Num.-_ (prefix GHC.Num.+
                                                                                       (#64 GHC.Num.- #1)) bi)) acc)
                                   end
                               end) in
            go (revNatSafe bitmap) z.
Solve Obligations with (BitTerminationProofs.termination_foldl).

Definition foldr' {b} : (Key -> b -> b) -> b -> IntSet -> b :=
  fun f z =>
    let fix go arg_0__ arg_1__
              := match arg_0__, arg_1__ with
                 | z', Nil => z'
                 | z', Tip kx bm => foldr'Bits kx f z' bm
                 | z', Bin _ _ l r => go (go z' r) l
                 end in
    fun t =>
      match t with
      | Bin _ m l r => if m GHC.Base.< #0 : bool then go (go z l) r else go (go z r) l
      | _ => go z t
      end.

Definition shorter : Mask -> Mask -> bool :=
  fun m1 m2 => (m1) GHC.Base.> (m2).

Definition size : IntSet -> Coq.Numbers.BinNums.N :=
  let fix go arg_0__ arg_1__
            := match arg_0__, arg_1__ with
               | acc, Bin _ _ l r => go (go acc l) r
               | acc, Tip _ bm =>
                   acc GHC.Num.+ Utils.Containers.Internal.BitUtil.bitcount #0 bm
               | acc, Nil => acc
               end in
  go #0.

Definition splitRoot : IntSet -> list IntSet :=
  fun arg_0__ =>
    match arg_0__ with
    | Nil => nil
    | (Tip _ _ as x) => cons x nil
    | Bin _ m l r =>
        if m GHC.Base.< #0 : bool then cons r (cons l nil) else
        cons l (cons r nil)
    end.

Definition suffixBitMask :=
  Coq.NArith.BinNat.N.ones 6.

Definition suffixOf : Coq.Numbers.BinNums.N -> Coq.Numbers.BinNums.N :=
  fun x => x Data.Bits..&.(**) suffixBitMask.

Definition bitmapOf : Coq.Numbers.BinNums.N -> BitMap :=
  fun x => bitmapOfSuffix (suffixOf x).

Definition prefixOf : Coq.Numbers.BinNums.N -> Prefix :=
  fun x => Coq.NArith.BinNat.N.ldiff x suffixBitMask.

Definition singleton : Key -> IntSet :=
  fun x => Tip (prefixOf x) (bitmapOf x).

Definition tip : Prefix -> BitMap -> IntSet :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | _, num_2__ =>
        if num_2__ GHC.Base.== #0 : bool then Nil else
        match arg_0__, arg_1__ with
        | kx, bm => Tip kx bm
        end
    end.

Definition filter : (Key -> bool) -> IntSet -> IntSet :=
  fix filter predicate t
        := let bitPred :=
             fun kx bm bi =>
               if predicate (kx GHC.Num.+ bi) : bool
               then bm Data.Bits..|.(**) bitmapOfSuffix bi else
               bm in
           match t with
           | Bin p m l r => bin p m (filter predicate l) (filter predicate r)
           | Tip kx bm => tip kx (foldl'Bits #0 (bitPred kx) #0 bm)
           | Nil => Nil
           end.

Definition maxView : IntSet -> option (Key * IntSet)%type :=
  fun t =>
    let fix go arg_0__
              := match arg_0__ with
                 | Bin p m l r => let 'pair result r' := go r in pair result (bin p m l r')
                 | Tip kx bm =>
                     let 'bi := highestBitSet bm in
                     pair (kx GHC.Num.+ bi) (tip kx (Data.Bits.xor bm (bm Data.Bits..&.(**)
                                                                    bitmapOfSuffix bi)))
                 | Nil => pair (0 % N) Nil
                 end in
    let j_12__ := Some (go t) in
    match t with
    | Nil => None
    | Bin p m l r =>
        if m GHC.Base.< #0 : bool
        then let 'pair result l' := go l in
             Some (pair result (bin p m l' r)) else
        j_12__
    | _ => j_12__
    end.

Definition deleteMax : IntSet -> IntSet :=
  Data.Maybe.maybe Nil Data.Tuple.snd GHC.Base.∘ maxView.

Definition minView : IntSet -> option (Key * IntSet)%type :=
  fun t =>
    let fix go arg_0__
              := match arg_0__ with
                 | Bin p m l r => let 'pair result l' := go l in pair result (bin p m l' r)
                 | Tip kx bm =>
                     let 'bi := lowestBitSet bm in
                     pair (kx GHC.Num.+ bi) (tip kx (Data.Bits.xor bm (bm Data.Bits..&.(**)
                                                                    bitmapOfSuffix bi)))
                 | Nil => pair (0 % N) Nil
                 end in
    let j_12__ := Some (go t) in
    match t with
    | Nil => None
    | Bin p m l r =>
        if m GHC.Base.< #0 : bool
        then let 'pair result r' := go r in
             Some (pair result (bin p m l r')) else
        j_12__
    | _ => j_12__
    end.

Definition deleteMin : IntSet -> IntSet :=
  Data.Maybe.maybe Nil Data.Tuple.snd GHC.Base.∘ minView.

Definition partition : (Key -> bool) -> IntSet -> (IntSet * IntSet)%type :=
  fun predicate0 t0 =>
    let fix go predicate t
              := let bitPred :=
                   fun kx bm bi =>
                     if predicate (kx GHC.Num.+ bi) : bool
                     then bm Data.Bits..|.(**) bitmapOfSuffix bi else
                     bm in
                 match t with
                 | Bin p m l r =>
                     let 'pair r1 r2 := go predicate r in
                     let 'pair l1 l2 := go predicate l in
                     pair (bin p m l1 r1) (bin p m l2 r2)
                 | Tip kx bm =>
                     let bm1 := foldl'Bits #0 (bitPred kx) #0 bm in
                     pair (tip kx bm1) (tip kx (Data.Bits.xor bm bm1))
                 | Nil => (pair Nil Nil)
                 end in
    id (go predicate0 t0).

Definition zero : Coq.Numbers.BinNums.N -> Mask -> bool :=
  fun i m => ((i) Data.Bits..&.(**) (m)) GHC.Base.== #0.

Definition subsetCmp : IntSet -> IntSet -> comparison :=
  fix subsetCmp arg_0__ arg_1__
        := match arg_0__, arg_1__ with
           | (Bin p1 m1 l1 r1 as t1), Bin p2 m2 l2 r2 =>
               let subsetCmpEq :=
                 match pair (subsetCmp l1 l2) (subsetCmp r1 r2) with
                 | pair Gt _ => Gt
                 | pair _ Gt => Gt
                 | pair Eq Eq => Eq
                 | _ => Lt
                 end in
               let subsetCmpLt :=
                 if nomatch p1 p2 m2 : bool then Gt else
                 if zero p1 m2 : bool then subsetCmp t1 l2 else
                 subsetCmp t1 r2 in
               if shorter m1 m2 : bool then Gt else
               if shorter m2 m1 : bool
               then match subsetCmpLt with
                    | Gt => Gt
                    | _ => Lt
                    end else
               if p1 GHC.Base.== p2 : bool then subsetCmpEq else
               Gt
           | _, _ =>
               match arg_0__, arg_1__ with
               | Bin _ _ _ _, _ => Gt
               | Tip kx1 bm1, Tip kx2 bm2 =>
                   if kx1 GHC.Base./= kx2 : bool then Gt else
                   if bm1 GHC.Base.== bm2 : bool then Eq else
                   if Data.Bits.xor bm1 (bm1 Data.Bits..&.(**) bm2) GHC.Base.== #0 : bool
                   then Lt else
                   Gt
               | (Tip kx _ as t1), Bin p m l r =>
                   if nomatch kx p m : bool then Gt else
                   if zero kx m : bool then match subsetCmp t1 l with | Gt => Gt | _ => Lt end else
                   match subsetCmp t1 r with
                   | Gt => Gt
                   | _ => Lt
                   end
               | Tip _ _, Nil => Gt
               | Nil, Nil => Eq
               | Nil, _ => Lt
               end
           end.

Definition isProperSubsetOf : IntSet -> IntSet -> bool :=
  fun t1 t2 => match subsetCmp t1 t2 with | Lt => true | _ => false end.

Definition isSubsetOf : IntSet -> IntSet -> bool :=
  fix isSubsetOf arg_0__ arg_1__
        := match arg_0__, arg_1__ with
           | (Bin p1 m1 l1 r1 as t1), Bin p2 m2 l2 r2 =>
               if shorter m1 m2 : bool then false else
               if shorter m2 m1 : bool
               then andb (match_ p1 p2 m2) (if zero p1 m2 : bool
                          then isSubsetOf t1 l2
                          else isSubsetOf t1 r2) else
               andb (p1 GHC.Base.== p2) (andb (isSubsetOf l1 l2) (isSubsetOf r1 r2))
           | _, _ =>
               match arg_0__, arg_1__ with
               | Bin _ _ _ _, _ => false
               | Tip kx1 bm1, Tip kx2 bm2 =>
                   andb (kx1 GHC.Base.== kx2) (Data.Bits.xor bm1 (bm1 Data.Bits..&.(**) bm2)
                         GHC.Base.==
                         #0)
               | (Tip kx _ as t1), Bin p m l r =>
                   if nomatch kx p m : bool then false else
                   if zero kx m : bool then isSubsetOf t1 l else
                   isSubsetOf t1 r
               | Tip _ _, Nil => false
               | Nil, _ => true
               end
           end.

Program Fixpoint disjoint (arg_0__ : IntSet) (arg_1__ : IntSet)
                          {measure (size_nat arg_0__ + size_nat arg_1__)} : bool
                   := match arg_0__, arg_1__ with
                      | (Bin p1 m1 l1 r1 as t1), (Bin p2 m2 l2 r2 as t2) =>
                          let disjoint2 :=
                            if Bool.Sumbool.sumbool_of_bool (nomatch p1 p2 m2) then true else
                            if Bool.Sumbool.sumbool_of_bool (zero p1 m2) then disjoint t1 l2 else
                            disjoint t1 r2 in
                          let disjoint1 :=
                            if Bool.Sumbool.sumbool_of_bool (nomatch p2 p1 m1) then true else
                            if Bool.Sumbool.sumbool_of_bool (zero p2 m1) then disjoint l1 t2 else
                            disjoint r1 t2 in
                          if Bool.Sumbool.sumbool_of_bool (shorter m1 m2) then disjoint1 else
                          if Bool.Sumbool.sumbool_of_bool (shorter m2 m1) then disjoint2 else
                          if Bool.Sumbool.sumbool_of_bool (p1 GHC.Base.== p2)
                          then andb (disjoint l1 l2) (disjoint r1 r2) else
                          true
                      | (Bin _ _ _ _ as t1), Tip kx2 bm2 =>
                          let fix disjointBM arg_11__
                                    := match arg_11__ with
                                       | Bin p1 m1 l1 r1 =>
                                           if Bool.Sumbool.sumbool_of_bool (nomatch kx2 p1 m1) then true else
                                           if Bool.Sumbool.sumbool_of_bool (zero kx2 m1) then disjointBM l1 else
                                           disjointBM r1
                                       | Tip kx1 bm1 =>
                                           if Bool.Sumbool.sumbool_of_bool (kx1 GHC.Base.== kx2)
                                           then (bm1 Data.Bits..&.(**) bm2) GHC.Base.== #0 else
                                           true
                                       | Nil => true
                                       end in
                          disjointBM t1
                      | Bin _ _ _ _, Nil => true
                      | Tip kx1 bm1, t2 =>
                          let fix disjointBM arg_18__
                                    := match arg_18__ with
                                       | Bin p2 m2 l2 r2 =>
                                           if Bool.Sumbool.sumbool_of_bool (nomatch kx1 p2 m2) then true else
                                           if Bool.Sumbool.sumbool_of_bool (zero kx1 m2) then disjointBM l2 else
                                           disjointBM r2
                                       | Tip kx2 bm2 =>
                                           if Bool.Sumbool.sumbool_of_bool (kx1 GHC.Base.== kx2)
                                           then (bm1 Data.Bits..&.(**) bm2) GHC.Base.== #0 else
                                           true
                                       | Nil => true
                                       end in
                          disjointBM t2
                      | Nil, _ => true
                      end.
Solve Obligations with (termination_by_omega).

Definition link : Prefix -> IntSet -> Prefix -> IntSet -> IntSet :=
  fun p1 t1 p2 t2 =>
    let m := branchMask p1 p2 in
    let p := mask p1 m in if zero p1 m : bool then Bin p m t1 t2 else Bin p m t2 t1.

Definition insertBM : Prefix -> BitMap -> IntSet -> IntSet :=
  fix insertBM arg_0__ arg_1__ arg_2__
        := match arg_0__, arg_1__, arg_2__ with
           | kx, bm, (Bin p m l r as t) =>
               if nomatch kx p m : bool then link kx (Tip kx bm) p t else
               if zero kx m : bool then Bin p m (insertBM kx bm l) r else
               Bin p m l (insertBM kx bm r)
           | kx, bm, (Tip kx' bm' as t) =>
               if kx' GHC.Base.== kx : bool then Tip kx' (bm Data.Bits..|.(**) bm') else
               link kx (Tip kx bm) kx' t
           | kx, bm, Nil => Tip kx bm
           end.

Definition insert : Key -> IntSet -> IntSet :=
  fun x => insertBM (prefixOf x) (bitmapOf x).

Definition fromList : list Key -> IntSet :=
  fun xs => let ins := fun t x => insert x t in Data.Foldable.foldl ins empty xs.

Definition map : (Key -> Key) -> IntSet -> IntSet :=
  fun f => fromList GHC.Base.∘ (GHC.Base.map f GHC.Base.∘ toList).

Program Fixpoint union (arg_0__ : IntSet) (arg_1__ : IntSet) {measure (size_nat
                        arg_0__ +
                        size_nat arg_1__)} : IntSet
                   := match arg_0__, arg_1__ with
                      | (Bin p1 m1 l1 r1 as t1), (Bin p2 m2 l2 r2 as t2) =>
                          let union2 :=
                            if Bool.Sumbool.sumbool_of_bool (nomatch p1 p2 m2) then link p1 t1 p2 t2 else
                            if Bool.Sumbool.sumbool_of_bool (zero p1 m2)
                            then Bin p2 m2 (union t1 l2) r2 else
                            Bin p2 m2 l2 (union t1 r2) in
                          let union1 :=
                            if Bool.Sumbool.sumbool_of_bool (nomatch p2 p1 m1) then link p1 t1 p2 t2 else
                            if Bool.Sumbool.sumbool_of_bool (zero p2 m1)
                            then Bin p1 m1 (union l1 t2) r1 else
                            Bin p1 m1 l1 (union r1 t2) in
                          if Bool.Sumbool.sumbool_of_bool (shorter m1 m2) then union1 else
                          if Bool.Sumbool.sumbool_of_bool (shorter m2 m1) then union2 else
                          if Bool.Sumbool.sumbool_of_bool (p1 GHC.Base.== p2)
                          then Bin p1 m1 (union l1 l2) (union r1 r2) else
                          link p1 t1 p2 t2
                      | (Bin _ _ _ _ as t), Tip kx bm => insertBM kx bm t
                      | (Bin _ _ _ _ as t), Nil => t
                      | Tip kx bm, t => insertBM kx bm t
                      | Nil, t => t
                      end.
Solve Obligations with (termination_by_omega).

Definition unions : list IntSet -> IntSet :=
  fun xs => Data.Foldable.foldl union empty xs.

Local Definition Monoid__IntSet_mconcat : list IntSet -> IntSet :=
  unions.

Local Definition Semigroup__IntSet_op_zlzg__ : IntSet -> IntSet -> IntSet :=
  union.

Program Instance Semigroup__IntSet : Data.Semigroup.Semigroup IntSet :=
  fun _ k => k {| Data.Semigroup.op_zlzg____ := Semigroup__IntSet_op_zlzg__ |}.

Local Definition Monoid__IntSet_mappend : IntSet -> IntSet -> IntSet :=
  _Data.Semigroup.<>_.

Program Instance Monoid__IntSet : GHC.Base.Monoid IntSet :=
  fun _ k =>
    k {| GHC.Base.mappend__ := Monoid__IntSet_mappend ;
         GHC.Base.mconcat__ := Monoid__IntSet_mconcat ;
         GHC.Base.mempty__ := Monoid__IntSet_mempty |}.

Definition lookupGE : Key -> IntSet -> option Key :=
  fun x t =>
    let fix go arg_0__ arg_1__
              := match arg_0__, arg_1__ with
                 | def, Bin p m l r =>
                     if nomatch x p m : bool
                     then if x GHC.Base.< p : bool
                          then unsafeFindMin l
                          else unsafeFindMin def else
                     if zero x m : bool then go r l else
                     go def r
                 | def, Tip kx bm =>
                     let maskGE :=
                       (Coq.NArith.BinNat.N.ldiff (Coq.NArith.BinNat.N.ones (64 % N))
                                                  (Coq.NArith.BinNat.N.pred (bitmapOf x))) Data.Bits..&.(**)
                       bm in
                     if prefixOf x GHC.Base.< kx : bool
                     then Some (_GHC.Num.+_ kx (lowestBitSet bm)) else
                     if andb (prefixOf x GHC.Base.== kx) (maskGE GHC.Base./= #0) : bool
                     then Some (_GHC.Num.+_ kx (lowestBitSet maskGE)) else
                     unsafeFindMin def
                 | def, Nil => unsafeFindMin def
                 end in
    let j_12__ := go Nil t in
    match t with
    | Bin _ m l r =>
        if m GHC.Base.< #0 : bool
        then if x GHC.Base.>= #0 : bool
             then go Nil l
             else go l r else
        j_12__
    | _ => j_12__
    end.

Definition lookupGT : Key -> IntSet -> option Key :=
  fun x t =>
    let fix go arg_0__ arg_1__
              := match arg_0__, arg_1__ with
                 | def, Bin p m l r =>
                     if nomatch x p m : bool
                     then if x GHC.Base.< p : bool
                          then unsafeFindMin l
                          else unsafeFindMin def else
                     if zero x m : bool then go r l else
                     go def r
                 | def, Tip kx bm =>
                     let maskGT :=
                       (Coq.NArith.BinNat.N.ldiff (Coq.NArith.BinNat.N.ones (64 % N))
                                                  (Coq.NArith.BinNat.N.pred (Utils.Containers.Internal.BitUtil.shiftLL
                                                                             (bitmapOf x) #1))) Data.Bits..&.(**)
                       bm in
                     if prefixOf x GHC.Base.< kx : bool
                     then Some (_GHC.Num.+_ kx (lowestBitSet bm)) else
                     if andb (prefixOf x GHC.Base.== kx) (maskGT GHC.Base./= #0) : bool
                     then Some (_GHC.Num.+_ kx (lowestBitSet maskGT)) else
                     unsafeFindMin def
                 | def, Nil => unsafeFindMin def
                 end in
    let j_12__ := go Nil t in
    match t with
    | Bin _ m l r =>
        if m GHC.Base.< #0 : bool
        then if x GHC.Base.>= #0 : bool
             then go Nil l
             else go l r else
        j_12__
    | _ => j_12__
    end.

Definition lookupLE : Key -> IntSet -> option Key :=
  fun x t =>
    let fix go arg_0__ arg_1__
              := match arg_0__, arg_1__ with
                 | def, Bin p m l r =>
                     if nomatch x p m : bool
                     then if x GHC.Base.< p : bool
                          then unsafeFindMax def
                          else unsafeFindMax r else
                     if zero x m : bool then go def l else
                     go l r
                 | def, Tip kx bm =>
                     let maskLE :=
                       ((Utils.Containers.Internal.BitUtil.shiftLL (bitmapOf x) #1) GHC.Num.- #1)
                       Data.Bits..&.(**)
                       bm in
                     if prefixOf x GHC.Base.> kx : bool
                     then Some (_GHC.Num.+_ kx (highestBitSet bm)) else
                     if andb (prefixOf x GHC.Base.== kx) (maskLE GHC.Base./= #0) : bool
                     then Some (_GHC.Num.+_ kx (highestBitSet maskLE)) else
                     unsafeFindMax def
                 | def, Nil => unsafeFindMax def
                 end in
    let j_12__ := go Nil t in
    match t with
    | Bin _ m l r =>
        if m GHC.Base.< #0 : bool
        then if x GHC.Base.>= #0 : bool
             then go r l
             else go Nil r else
        j_12__
    | _ => j_12__
    end.

Definition lookupLT : Key -> IntSet -> option Key :=
  fun x t =>
    let fix go arg_0__ arg_1__
              := match arg_0__, arg_1__ with
                 | def, Bin p m l r =>
                     if nomatch x p m : bool
                     then if x GHC.Base.< p : bool
                          then unsafeFindMax def
                          else unsafeFindMax r else
                     if zero x m : bool then go def l else
                     go l r
                 | def, Tip kx bm =>
                     let maskLT := (bitmapOf x GHC.Num.- #1) Data.Bits..&.(**) bm in
                     if prefixOf x GHC.Base.> kx : bool
                     then Some (_GHC.Num.+_ kx (highestBitSet bm)) else
                     if andb (prefixOf x GHC.Base.== kx) (maskLT GHC.Base./= #0) : bool
                     then Some (_GHC.Num.+_ kx (highestBitSet maskLT)) else
                     unsafeFindMax def
                 | def, Nil => unsafeFindMax def
                 end in
    let j_12__ := go Nil t in
    match t with
    | Bin _ m l r =>
        if m GHC.Base.< #0 : bool
        then if x GHC.Base.>= #0 : bool
             then go r l
             else go Nil r else
        j_12__
    | _ => j_12__
    end.

Definition member : Key -> IntSet -> bool :=
  fun x =>
    let fix go arg_0__
              := match arg_0__ with
                 | Bin p m l r =>
                     if nomatch x p m : bool then false else
                     if zero x m : bool then go l else
                     go r
                 | Tip y bm =>
                     andb (prefixOf x GHC.Base.== y) ((bitmapOf x Data.Bits..&.(**) bm) GHC.Base./=
                           #0)
                 | Nil => false
                 end in
    go.

Definition notMember : Key -> IntSet -> bool :=
  fun k => negb GHC.Base.∘ member k.

Definition split : Key -> IntSet -> (IntSet * IntSet)%type :=
  fun x t =>
    let fix go arg_0__ arg_1__
              := match arg_0__, arg_1__ with
                 | x', (Bin p m l r as t') =>
                     if match_ x' p m : bool
                     then if zero x' m : bool
                          then let 'pair lt gt := go x' l in
                               pair lt (union gt r)
                          else let 'pair lt gt := go x' r in
                               pair (union lt l) gt else
                     if x' GHC.Base.< p : bool
                     then (pair Nil t')
                     else (pair t' Nil)
                 | x', (Tip kx' bm as t') =>
                     let lowerBitmap := bitmapOf x' GHC.Num.- #1 in
                     let higherBitmap :=
                       Coq.NArith.BinNat.N.ldiff (Coq.NArith.BinNat.N.ones (64 % N)) (lowerBitmap
                                                  GHC.Num.+
                                                  bitmapOf x') in
                     if kx' GHC.Base.> x' : bool then (pair Nil t') else
                     if kx' GHC.Base.< prefixOf x' : bool then (pair t' Nil) else
                     pair (tip kx' (bm Data.Bits..&.(**) lowerBitmap)) (tip kx' (bm Data.Bits..&.(**)
                                                                                 higherBitmap))
                 | _, Nil => (pair Nil Nil)
                 end in
    let j_21__ := let 'pair lt gt := go x t in pair lt gt in
    match t with
    | Bin _ m l r =>
        if m GHC.Base.< #0 : bool
        then if x GHC.Base.>= #0 : bool
             then let 'pair lt gt := go x l in
                  let 'lt' := union lt r in
                  pair lt' gt
             else let 'pair lt gt := go x r in
                  let 'gt' := union gt l in
                  pair lt gt' else
        j_21__
    | _ => j_21__
    end.

Definition splitMember : Key -> IntSet -> (IntSet * bool * IntSet)%type :=
  fun x t =>
    let fix go arg_0__ arg_1__
              := match arg_0__, arg_1__ with
                 | x', (Bin p m l r as t') =>
                     if match_ x' p m : bool
                     then if zero x' m : bool
                          then let 'pair (pair lt fnd) gt := go x' l in
                               pair (pair lt fnd) (union gt r)
                          else let 'pair (pair lt fnd) gt := go x' r in
                               pair (pair (union lt l) fnd) gt else
                     if x' GHC.Base.< p : bool
                     then pair (pair Nil false) t'
                     else pair (pair t' false) Nil
                 | x', (Tip kx' bm as t') =>
                     let bitmapOfx' := bitmapOf x' in
                     let lowerBitmap := bitmapOfx' GHC.Num.- #1 in
                     let higherBitmap :=
                       Coq.NArith.BinNat.N.ldiff (Coq.NArith.BinNat.N.ones (64 % N)) (lowerBitmap
                                                  GHC.Num.+
                                                  bitmapOfx') in
                     if kx' GHC.Base.> x' : bool then pair (pair Nil false) t' else
                     if kx' GHC.Base.< prefixOf x' : bool then pair (pair t' false) Nil else
                     let 'gt := tip kx' (bm Data.Bits..&.(**) higherBitmap) in
                     let 'found := (bm Data.Bits..&.(**) bitmapOfx') GHC.Base./= #0 in
                     let 'lt := tip kx' (bm Data.Bits..&.(**) lowerBitmap) in
                     pair (pair lt found) gt
                 | _, Nil => pair (pair Nil false) Nil
                 end in
    let j_22__ := go x t in
    match t with
    | Bin _ m l r =>
        if m GHC.Base.< #0 : bool
        then if x GHC.Base.>= #0 : bool
             then let 'pair (pair lt fnd) gt := go x l in
                  let 'lt' := union lt r in
                  pair (pair lt' fnd) gt
             else let 'pair (pair lt fnd) gt := go x r in
                  let 'gt' := union gt l in
                  pair (pair lt fnd) gt' else
        j_22__
    | _ => j_22__
    end.

Definition deleteBM : Prefix -> BitMap -> IntSet -> IntSet :=
  fix deleteBM arg_0__ arg_1__ arg_2__
        := match arg_0__, arg_1__, arg_2__ with
           | kx, bm, (Bin p m l r as t) =>
               if nomatch kx p m : bool then t else
               if zero kx m : bool then bin p m (deleteBM kx bm l) r else
               bin p m l (deleteBM kx bm r)
           | kx, bm, (Tip kx' bm' as t) =>
               if kx' GHC.Base.== kx : bool
               then tip kx (Data.Bits.xor bm' (bm' Data.Bits..&.(**) bm)) else
               t
           | _, _, Nil => Nil
           end.

Definition delete : Key -> IntSet -> IntSet :=
  fun x => deleteBM (prefixOf x) (bitmapOf x).

Program Fixpoint difference (arg_0__ : IntSet) (arg_1__ : IntSet)
                            {measure (size_nat arg_0__ + size_nat arg_1__)} : IntSet
                   := match arg_0__, arg_1__ with
                      | (Bin p1 m1 l1 r1 as t1), (Bin p2 m2 l2 r2 as t2) =>
                          let difference2 :=
                            if Bool.Sumbool.sumbool_of_bool (nomatch p1 p2 m2) then t1 else
                            if Bool.Sumbool.sumbool_of_bool (zero p1 m2) then difference t1 l2 else
                            difference t1 r2 in
                          let difference1 :=
                            if Bool.Sumbool.sumbool_of_bool (nomatch p2 p1 m1) then t1 else
                            if Bool.Sumbool.sumbool_of_bool (zero p2 m1)
                            then bin p1 m1 (difference l1 t2) r1 else
                            bin p1 m1 l1 (difference r1 t2) in
                          if Bool.Sumbool.sumbool_of_bool (shorter m1 m2) then difference1 else
                          if Bool.Sumbool.sumbool_of_bool (shorter m2 m1) then difference2 else
                          if Bool.Sumbool.sumbool_of_bool (p1 GHC.Base.== p2)
                          then bin p1 m1 (difference l1 l2) (difference r1 r2) else
                          t1
                      | (Bin _ _ _ _ as t), Tip kx bm => deleteBM kx bm t
                      | (Bin _ _ _ _ as t), Nil => t
                      | (Tip kx bm as t1), t2 =>
                          let fix differenceTip arg_12__
                                    := match arg_12__ with
                                       | Bin p2 m2 l2 r2 =>
                                           if Bool.Sumbool.sumbool_of_bool (nomatch kx p2 m2) then t1 else
                                           if Bool.Sumbool.sumbool_of_bool (zero kx m2) then differenceTip l2 else
                                           differenceTip r2
                                       | Tip kx2 bm2 =>
                                           if Bool.Sumbool.sumbool_of_bool (kx GHC.Base.== kx2)
                                           then tip kx (Data.Bits.xor bm (bm Data.Bits..&.(**) bm2)) else
                                           t1
                                       | Nil => t1
                                       end in
                          differenceTip t2
                      | Nil, _ => Nil
                      end.
Solve Obligations with (termination_by_omega).

Definition op_zrzr__ : IntSet -> IntSet -> IntSet :=
  fun m1 m2 => difference m1 m2.

Notation "'_\\_'" := (op_zrzr__).

Infix "\\" := (_\\_) (at level 99).

Program Fixpoint intersection (arg_0__ : IntSet) (arg_1__ : IntSet)
                              {measure (size_nat arg_0__ + size_nat arg_1__)} : IntSet
                   := match arg_0__, arg_1__ with
                      | (Bin p1 m1 l1 r1 as t1), (Bin p2 m2 l2 r2 as t2) =>
                          let intersection2 :=
                            if Bool.Sumbool.sumbool_of_bool (nomatch p1 p2 m2) then Nil else
                            if Bool.Sumbool.sumbool_of_bool (zero p1 m2) then intersection t1 l2 else
                            intersection t1 r2 in
                          let intersection1 :=
                            if Bool.Sumbool.sumbool_of_bool (nomatch p2 p1 m1) then Nil else
                            if Bool.Sumbool.sumbool_of_bool (zero p2 m1) then intersection l1 t2 else
                            intersection r1 t2 in
                          if Bool.Sumbool.sumbool_of_bool (shorter m1 m2) then intersection1 else
                          if Bool.Sumbool.sumbool_of_bool (shorter m2 m1) then intersection2 else
                          if Bool.Sumbool.sumbool_of_bool (p1 GHC.Base.== p2)
                          then bin p1 m1 (intersection l1 l2) (intersection r1 r2) else
                          Nil
                      | (Bin _ _ _ _ as t1), Tip kx2 bm2 =>
                          let fix intersectBM arg_11__
                                    := match arg_11__ with
                                       | Bin p1 m1 l1 r1 =>
                                           if Bool.Sumbool.sumbool_of_bool (nomatch kx2 p1 m1) then Nil else
                                           if Bool.Sumbool.sumbool_of_bool (zero kx2 m1) then intersectBM l1 else
                                           intersectBM r1
                                       | Tip kx1 bm1 =>
                                           if Bool.Sumbool.sumbool_of_bool (kx1 GHC.Base.== kx2)
                                           then tip kx1 (bm1 Data.Bits..&.(**) bm2) else
                                           Nil
                                       | Nil => Nil
                                       end in
                          intersectBM t1
                      | Bin _ _ _ _, Nil => Nil
                      | Tip kx1 bm1, t2 =>
                          let fix intersectBM arg_18__
                                    := match arg_18__ with
                                       | Bin p2 m2 l2 r2 =>
                                           if Bool.Sumbool.sumbool_of_bool (nomatch kx1 p2 m2) then Nil else
                                           if Bool.Sumbool.sumbool_of_bool (zero kx1 m2) then intersectBM l2 else
                                           intersectBM r2
                                       | Tip kx2 bm2 =>
                                           if Bool.Sumbool.sumbool_of_bool (kx1 GHC.Base.== kx2)
                                           then tip kx1 (bm1 Data.Bits..&.(**) bm2) else
                                           Nil
                                       | Nil => Nil
                                       end in
                          intersectBM t2
                      | Nil, _ => Nil
                      end.
Solve Obligations with (termination_by_omega).

Module Notations.
Notation "'_Data.IntSet.Internal.\\_'" := (op_zrzr__).
Infix "Data.IntSet.Internal.\\" := (_\\_) (at level 99).
End Notations.

(* Unbound variables:
     Bool.Sumbool.sumbool_of_bool Eq Gt Lt N None Some andb bool comparison cons
     false id list negb nil op_zm__ op_zp__ op_zt__ op_zv__ option orb pair size_nat
     true Coq.Init.Peano.lt Coq.NArith.BinNat.N.ldiff Coq.NArith.BinNat.N.log2
     Coq.NArith.BinNat.N.lxor Coq.NArith.BinNat.N.modulo Coq.NArith.BinNat.N.ones
     Coq.NArith.BinNat.N.pow Coq.NArith.BinNat.N.pred Coq.NArith.BinNat.N.to_nat
     Coq.Numbers.BinNums.N Data.Bits.op_zizazi__ Data.Bits.op_zizbzi__ Data.Bits.xor
     Data.Foldable.foldl Data.Maybe.maybe Data.Semigroup.Semigroup
     Data.Semigroup.op_zlzg__ Data.Tuple.snd GHC.Base.Eq_ GHC.Base.Monoid
     GHC.Base.Ord GHC.Base.compare GHC.Base.flip GHC.Base.map GHC.Base.op_z2218U__
     GHC.Base.op_zeze__ GHC.Base.op_zg__ GHC.Base.op_zgze__ GHC.Base.op_zl__
     GHC.Base.op_zsze__ GHC.Num.fromInteger GHC.Num.op_zm__ GHC.Num.op_zp__
     GHC.Wf.wfFix2 Utils.Containers.Internal.BitUtil.bitcount
     Utils.Containers.Internal.BitUtil.highestBitMask
     Utils.Containers.Internal.BitUtil.lowestBitMask
     Utils.Containers.Internal.BitUtil.shiftLL
     Utils.Containers.Internal.BitUtil.shiftRL
*)
