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
Require Data.Bits.
Require Data.Foldable.
Require Data.Maybe.
Require Data.Tuple.
Require GHC.Base.
Require GHC.Err.
Require GHC.Num.
Require GHC.Wf.
Require IntWord.
Import Data.Bits.Notations.
Import GHC.Base.Notations.
Import GHC.Num.Notations.

(* Converted type declarations: *)

Definition Prefix :=
  IntWord.Int%type.

Definition Nat :=
  IntWord.Word%type.

Definition Mask :=
  IntWord.Int%type.

Definition Key :=
  IntWord.Int%type.

Definition BitMap :=
  IntWord.Word%type.

Inductive IntSet : Type
  := | Bin : Prefix -> Mask -> IntSet -> IntSet -> IntSet
  |  Tip : Prefix -> BitMap -> IntSet
  |  Nil : IntSet.

Inductive Stack : Type
  := | Push : Prefix -> IntSet -> Stack -> Stack
  |  Nada : Stack.

Instance Default__IntSet : GHC.Err.Default IntSet :=
  GHC.Err.Build_Default _ Nil.

Instance Default__Stack : GHC.Err.Default Stack := GHC.Err.Build_Default _ Nada.

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

(* Converted value declarations: *)

Definition tip : Prefix -> BitMap -> IntSet :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | _, num_2__ =>
        if num_2__ GHC.Base.== #0 : bool then Nil else
        match arg_0__, arg_1__ with
        | kx, bm => Tip kx bm
        end
    end.

Definition suffixBitMask : IntWord.Int :=
  #63.

Definition suffixOf : IntWord.Int -> IntWord.Int :=
  fun x => x Data.Bits..&.(**) suffixBitMask.

Definition splitRoot : IntSet -> list IntSet :=
  fun arg_0__ =>
    match arg_0__ with
    | Nil => nil
    | (Tip _ _ as x) => cons x nil
    | Bin _ m l r =>
        if m GHC.Base.< #0 : bool then cons r (cons l nil) else
        cons l (cons r nil)
    end.

Definition size : IntSet -> IntWord.Int :=
  let fix go arg_0__ arg_1__
            := match arg_0__, arg_1__ with
               | acc, Bin _ _ l r => go (go acc l) r
               | acc, Tip _ bm => acc GHC.Num.+ IntWord.bitcount #0 bm
               | acc, Nil => acc
               end in
  go #0.

Definition revNat : Nat -> Nat :=
  fun x1 =>
    let 'x2 := ((IntWord.shiftRWord x1 #1) Data.Bits..&.(**) #6148914691236517205)
                 Data.Bits..|.(**)
                 (IntWord.shiftLWord (x1 Data.Bits..&.(**) #6148914691236517205) #1) in
    let 'x3 := ((IntWord.shiftRWord x2 #2) Data.Bits..&.(**) #3689348814741910323)
                 Data.Bits..|.(**)
                 (IntWord.shiftLWord (x2 Data.Bits..&.(**) #3689348814741910323) #2) in
    let 'x4 := ((IntWord.shiftRWord x3 #4) Data.Bits..&.(**) #1085102592571150095)
                 Data.Bits..|.(**)
                 (IntWord.shiftLWord (x3 Data.Bits..&.(**) #1085102592571150095) #4) in
    let 'x5 := ((IntWord.shiftRWord x4 #8) Data.Bits..&.(**) #71777214294589695)
                 Data.Bits..|.(**)
                 (IntWord.shiftLWord (x4 Data.Bits..&.(**) #71777214294589695) #8) in
    let 'x6 := ((IntWord.shiftRWord x5 #16) Data.Bits..&.(**) #281470681808895)
                 Data.Bits..|.(**)
                 (IntWord.shiftLWord (x5 Data.Bits..&.(**) #281470681808895) #16) in
    (IntWord.shiftRWord x6 #32) Data.Bits..|.(**) (IntWord.shiftLWord x6 #32).

Definition prefixBitMask : IntWord.Int :=
  Data.Bits.complement suffixBitMask.

Definition prefixOf : IntWord.Int -> Prefix :=
  fun x => x Data.Bits..&.(**) prefixBitMask.

Definition null : IntSet -> bool :=
  fun arg_0__ => match arg_0__ with | Nil => true | _ => false end.

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

Definition natFromInt :=
  IntWord.wordFromInt.

Definition shorter : Mask -> Mask -> bool :=
  fun m1 m2 => (natFromInt m1) GHC.Base.> (natFromInt m2).

Definition zero : IntWord.Int -> Mask -> bool :=
  fun i m => ((natFromInt i) Data.Bits..&.(**) (natFromInt m)) GHC.Base.== #0.

Definition lowestBitMask : Nat -> Nat :=
  fun x => x Data.Bits..&.(**) GHC.Num.negate x.

Definition intFromNat :=
  IntWord.intFromWord.

Definition maskW : Nat -> Nat -> Prefix :=
  fun i m =>
    intFromNat (i Data.Bits..&.(**)
                (Data.Bits.xor (Data.Bits.complement (m GHC.Num.- #1)) m)).

Definition mask : IntWord.Int -> Mask -> Prefix :=
  fun i m => maskW (natFromInt i) (natFromInt m).

Definition match_ : IntWord.Int -> Prefix -> Mask -> bool :=
  fun i p m => (mask i m) GHC.Base.== p.

Definition nomatch : IntWord.Int -> Prefix -> Mask -> bool :=
  fun i p m => (mask i m) GHC.Base./= p.

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
                   andb (kx1 GHC.Base.== kx2) ((bm1 Data.Bits..&.(**) Data.Bits.complement bm2)
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
                   if (bm1 Data.Bits..&.(**) Data.Bits.complement bm2) GHC.Base.== #0 : bool
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

Definition indexOfTheOnlyBit :=
  IntWord.indexOfTheOnlyBit.

Definition lowestBitSet : Nat -> IntWord.Int :=
  fun x => indexOfTheOnlyBit (lowestBitMask x).

Definition unsafeFindMin : IntSet -> option Key :=
  fix unsafeFindMin arg_0__
        := match arg_0__ with
           | Nil => None
           | Tip kx bm => Some (kx GHC.Num.+ lowestBitSet bm)
           | Bin _ _ l _ => unsafeFindMin l
           end.

Definition highestBitSet : Nat -> IntWord.Int :=
  fun x => indexOfTheOnlyBit (IntWord.highestBitMask x).

Definition unsafeFindMax : IntSet -> option Key :=
  fix unsafeFindMax arg_0__
        := match arg_0__ with
           | Nil => None
           | Tip kx bm => Some (kx GHC.Num.+ highestBitSet bm)
           | Bin _ _ _ r => unsafeFindMax r
           end.

Program Definition foldrBits {a}
           : IntWord.Int -> (IntWord.Int -> a -> a) -> a -> Nat -> a :=
          fun prefix f z bitmap =>
            let go :=
              GHC.Wf.wfFix2 Coq.Init.Peano.lt (fun arg_0__ arg_1__ =>
                               IntWord.wordTonat arg_0__) _ (fun arg_0__ arg_1__ go =>
                               match arg_0__, arg_1__ with
                               | num_2__, acc =>
                                   if Bool.Sumbool.sumbool_of_bool (num_2__ GHC.Base.== #0) then acc else
                                   match arg_0__, arg_1__ with
                                   | bm, acc =>
                                       let bitmask := lowestBitMask bm in
                                       let bi := indexOfTheOnlyBit bitmask in
                                       go (Data.Bits.xor bm bitmask) ((f ((prefix GHC.Num.+ (#64 GHC.Num.- #1))
                                                                          GHC.Num.-
                                                                          bi)) acc)
                                   end
                               end) in
            go (revNat bitmap) z.
Admit Obligations.

Program Definition foldr'Bits {a}
           : IntWord.Int -> (IntWord.Int -> a -> a) -> a -> Nat -> a :=
          fun prefix f z bitmap =>
            let go :=
              GHC.Wf.wfFix2 Coq.Init.Peano.lt (fun arg_0__ arg_1__ =>
                               IntWord.wordTonat arg_0__) _ (fun arg_0__ arg_1__ go =>
                               match arg_0__, arg_1__ with
                               | num_2__, acc =>
                                   if Bool.Sumbool.sumbool_of_bool (num_2__ GHC.Base.== #0) then acc else
                                   match arg_0__, arg_1__ with
                                   | bm, acc =>
                                       let bitmask := lowestBitMask bm in
                                       let bi := indexOfTheOnlyBit bitmask in
                                       go (Data.Bits.xor bm bitmask) ((f ((prefix GHC.Num.+ (#64 GHC.Num.- #1))
                                                                          GHC.Num.-
                                                                          bi)) acc)
                                   end
                               end) in
            go (revNat bitmap) z.
Admit Obligations.

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

Program Definition foldlBits {a}
           : IntWord.Int -> (a -> IntWord.Int -> a) -> a -> Nat -> a :=
          fun prefix f z bitmap =>
            let go :=
              GHC.Wf.wfFix2 Coq.Init.Peano.lt (fun arg_0__ arg_1__ =>
                               IntWord.wordTonat arg_0__) _ (fun arg_0__ arg_1__ go =>
                               match arg_0__, arg_1__ with
                               | num_2__, acc =>
                                   if Bool.Sumbool.sumbool_of_bool (num_2__ GHC.Base.== #0) then acc else
                                   match arg_0__, arg_1__ with
                                   | bm, acc =>
                                       let bitmask := lowestBitMask bm in
                                       let bi := indexOfTheOnlyBit bitmask in
                                       go (Data.Bits.xor bm bitmask) (f acc (prefix GHC.Num.+ bi))
                                   end
                               end) in
            go bitmap z.
Admit Obligations.

Program Definition foldl'Bits {a}
           : IntWord.Int -> (a -> IntWord.Int -> a) -> a -> Nat -> a :=
          fun prefix f z bitmap =>
            let go :=
              GHC.Wf.wfFix2 Coq.Init.Peano.lt (fun arg_0__ arg_1__ =>
                               IntWord.wordTonat arg_0__) _ (fun arg_0__ arg_1__ go =>
                               match arg_0__, arg_1__ with
                               | num_2__, acc =>
                                   if Bool.Sumbool.sumbool_of_bool (num_2__ GHC.Base.== #0) then acc else
                                   match arg_0__, arg_1__ with
                                   | bm, acc =>
                                       let bitmask := lowestBitMask bm in
                                       let bi := indexOfTheOnlyBit bitmask in
                                       go (Data.Bits.xor bm bitmask) (f acc (prefix GHC.Num.+ bi))
                                   end
                               end) in
            go bitmap z.
Admit Obligations.

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

Definition fold {b} : (Key -> b -> b) -> b -> IntSet -> b :=
  foldr.

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

Definition empty : IntSet :=
  Nil.

Definition elems : IntSet -> list Key :=
  toAscList.

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

Definition branchMask : Prefix -> Prefix -> Mask :=
  fun p1 p2 =>
    intFromNat (IntWord.highestBitMask (Data.Bits.xor (natFromInt p1) (natFromInt
                                                       p2))).

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

Definition unions {f} `{Data.Foldable.Foldable f} : f IntSet -> IntSet :=
  fun xs => Data.Foldable.foldl' union empty xs.

Definition bitmapOfSuffix : IntWord.Int -> BitMap :=
  fun s => IntWord.shiftLWord #1 s.

Definition bitmapOf : IntWord.Int -> BitMap :=
  fun x => bitmapOfSuffix (suffixOf x).

Definition insert : Key -> IntSet -> IntSet :=
  fun x => insertBM (prefixOf x) (bitmapOf x).

Definition fromList : list Key -> IntSet :=
  fun xs => let ins := fun t x => insert x t in Data.Foldable.foldl' ins empty xs.

Definition map : (Key -> Key) -> IntSet -> IntSet :=
  fun f => fromList GHC.Base.∘ (GHC.Base.map f GHC.Base.∘ toList).

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
                     let maskGE := (GHC.Num.negate (bitmapOf x)) Data.Bits..&.(**) bm in
                     if prefixOf x GHC.Base.< kx : bool then Some (kx GHC.Num.+ lowestBitSet bm) else
                     if andb (prefixOf x GHC.Base.== kx) (maskGE GHC.Base./= #0) : bool
                     then Some (kx GHC.Num.+ lowestBitSet maskGE) else
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
                       (GHC.Num.negate (IntWord.shiftLWord (bitmapOf x) #1)) Data.Bits..&.(**) bm in
                     if prefixOf x GHC.Base.< kx : bool then Some (kx GHC.Num.+ lowestBitSet bm) else
                     if andb (prefixOf x GHC.Base.== kx) (maskGT GHC.Base./= #0) : bool
                     then Some (kx GHC.Num.+ lowestBitSet maskGT) else
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
                       ((IntWord.shiftLWord (bitmapOf x) #1) GHC.Num.- #1) Data.Bits..&.(**) bm in
                     if prefixOf x GHC.Base.> kx : bool
                     then Some (kx GHC.Num.+ highestBitSet bm) else
                     if andb (prefixOf x GHC.Base.== kx) (maskLE GHC.Base./= #0) : bool
                     then Some (kx GHC.Num.+ highestBitSet maskLE) else
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
                     then Some (kx GHC.Num.+ highestBitSet bm) else
                     if andb (prefixOf x GHC.Base.== kx) (maskLT GHC.Base./= #0) : bool
                     then Some (kx GHC.Num.+ highestBitSet maskLT) else
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

Definition singleton : Key -> IntSet :=
  fun x => Tip (prefixOf x) (bitmapOf x).

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
                     let higherBitmap := Data.Bits.complement (lowerBitmap GHC.Num.+ bitmapOf x') in
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
                  let lt' := union lt r in pair lt' gt
             else let 'pair lt gt := go x r in
                  let gt' := union gt l in pair lt gt' else
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
                     let higherBitmap := Data.Bits.complement (lowerBitmap GHC.Num.+ bitmapOfx') in
                     if kx' GHC.Base.> x' : bool then pair (pair Nil false) t' else
                     if kx' GHC.Base.< prefixOf x' : bool then pair (pair t' false) Nil else
                     let gt := tip kx' (bm Data.Bits..&.(**) higherBitmap) in
                     let found := (bm Data.Bits..&.(**) bitmapOfx') GHC.Base./= #0 in
                     let lt := tip kx' (bm Data.Bits..&.(**) lowerBitmap) in pair (pair lt found) gt
                 | _, Nil => pair (pair Nil false) Nil
                 end in
    let j_22__ := go x t in
    match t with
    | Bin _ m l r =>
        if m GHC.Base.< #0 : bool
        then if x GHC.Base.>= #0 : bool
             then let 'pair (pair lt fnd) gt := go x l in
                  let lt' := union lt r in pair (pair lt' fnd) gt
             else let 'pair (pair lt fnd) gt := go x r in
                  let gt' := union gt l in pair (pair lt fnd) gt' else
        j_22__
    | _ => j_22__
    end.

Definition bin : Prefix -> Mask -> IntSet -> IntSet -> IntSet :=
  fun arg_0__ arg_1__ arg_2__ arg_3__ =>
    match arg_0__, arg_1__, arg_2__, arg_3__ with
    | _, _, l, Nil => l
    | _, _, Nil, r => r
    | p, m, l, r => Bin p m l r
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
               then tip kx (bm' Data.Bits..&.(**) Data.Bits.complement bm) else
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
                                           then tip kx (bm Data.Bits..&.(**) Data.Bits.complement bm2) else
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

Definition maxView : IntSet -> option (Key * IntSet)%type :=
  fun t =>
    let fix go arg_0__
              := match arg_0__ with
                 | Bin p m l r => let 'pair result r' := go r in pair result (bin p m l r')
                 | Tip kx bm =>
                     let 'bi := highestBitSet bm in
                     pair (kx GHC.Num.+ bi) (tip kx (bm Data.Bits..&.(**)
                                                     Data.Bits.complement (bitmapOfSuffix bi)))
                 | Nil => GHC.Err.error (GHC.Base.hs_string__ "maxView Nil")
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
                     pair (kx GHC.Num.+ bi) (tip kx (bm Data.Bits..&.(**)
                                                     Data.Bits.complement (bitmapOfSuffix bi)))
                 | Nil => GHC.Err.error (GHC.Base.hs_string__ "minView Nil")
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

(* Skipping all instances of class `Control.DeepSeq.NFData', including
   `Data.IntSet.InternalWord.NFData__IntSet' *)

(* Skipping all instances of class `GHC.Read.Read', including
   `Data.IntSet.InternalWord.Read__IntSet' *)

(* Skipping all instances of class `GHC.Show.Show', including
   `Data.IntSet.InternalWord.Show__IntSet' *)

Local Definition Ord__IntSet_compare : IntSet -> IntSet -> comparison :=
  fun s1 s2 => GHC.Base.compare (toAscList s1) (toAscList s2).

Local Definition Ord__IntSet_op_zl__ : IntSet -> IntSet -> bool :=
  fun x y => Ord__IntSet_compare x y GHC.Base.== Lt.

Local Definition Ord__IntSet_op_zlze__ : IntSet -> IntSet -> bool :=
  fun x y => Ord__IntSet_compare x y GHC.Base./= Gt.

Local Definition Ord__IntSet_op_zg__ : IntSet -> IntSet -> bool :=
  fun x y => Ord__IntSet_compare x y GHC.Base.== Gt.

Local Definition Ord__IntSet_op_zgze__ : IntSet -> IntSet -> bool :=
  fun x y => Ord__IntSet_compare x y GHC.Base./= Lt.

Local Definition Ord__IntSet_max : IntSet -> IntSet -> IntSet :=
  fun x y => if Ord__IntSet_op_zlze__ x y : bool then y else x.

Local Definition Ord__IntSet_min : IntSet -> IntSet -> IntSet :=
  fun x y => if Ord__IntSet_op_zlze__ x y : bool then x else y.

Local Definition Eq___IntSet_op_zeze__ : IntSet -> IntSet -> bool :=
  fun t1 t2 => equal t1 t2.

Local Definition Eq___IntSet_op_zsze__ : IntSet -> IntSet -> bool :=
  fun t1 t2 => nequal t1 t2.

Program Instance Eq___IntSet : GHC.Base.Eq_ IntSet :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zeze____ := Eq___IntSet_op_zeze__ ;
           GHC.Base.op_zsze____ := Eq___IntSet_op_zsze__ |}.

Program Instance Ord__IntSet : GHC.Base.Ord IntSet :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zl____ := Ord__IntSet_op_zl__ ;
           GHC.Base.op_zlze____ := Ord__IntSet_op_zlze__ ;
           GHC.Base.op_zg____ := Ord__IntSet_op_zg__ ;
           GHC.Base.op_zgze____ := Ord__IntSet_op_zgze__ ;
           GHC.Base.compare__ := Ord__IntSet_compare ;
           GHC.Base.max__ := Ord__IntSet_max ;
           GHC.Base.min__ := Ord__IntSet_min |}.

(* Skipping all instances of class `Data.Data.Data', including
   `Data.IntSet.InternalWord.Data__IntSet' *)

Local Definition Semigroup__IntSet_op_zlzlzgzg__ : IntSet -> IntSet -> IntSet :=
  union.

Program Instance Semigroup__IntSet : GHC.Base.Semigroup IntSet :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zlzlzgzg____ := Semigroup__IntSet_op_zlzlzgzg__ |}.

Local Definition Monoid__IntSet_mappend : IntSet -> IntSet -> IntSet :=
  _GHC.Base.<<>>_.

Local Definition Monoid__IntSet_mconcat : list IntSet -> IntSet :=
  unions.

Local Definition Monoid__IntSet_mempty : IntSet :=
  empty.

Program Instance Monoid__IntSet : GHC.Base.Monoid IntSet :=
  fun _ k__ =>
    k__ {| GHC.Base.mappend__ := Monoid__IntSet_mappend ;
           GHC.Base.mconcat__ := Monoid__IntSet_mconcat ;
           GHC.Base.mempty__ := Monoid__IntSet_mempty |}.

(* Skipping all instances of class `GHC.Exts.IsList', including
   `Data.IntSet.InternalWord.IsList__IntSet' *)

Module Notations.
Notation "'_Data.IntSet.InternalWord.\\_'" := (op_zrzr__).
Infix "Data.IntSet.InternalWord.\\" := (_\\_) (at level 99).
End Notations.

(* External variables:
     Bool.Sumbool.sumbool_of_bool Eq Gt Lt None Some andb bool comparison cons false
     id list negb nil op_zp__ op_zt__ option orb pair size_nat true Coq.Init.Peano.lt
     Data.Bits.complement Data.Bits.op_zizazi__ Data.Bits.op_zizbzi__ Data.Bits.xor
     Data.Foldable.Foldable Data.Foldable.foldl' Data.Maybe.maybe Data.Tuple.snd
     GHC.Base.Eq_ GHC.Base.Monoid GHC.Base.Ord GHC.Base.Semigroup GHC.Base.compare
     GHC.Base.compare__ GHC.Base.flip GHC.Base.map GHC.Base.mappend__ GHC.Base.max__
     GHC.Base.mconcat__ GHC.Base.mempty__ GHC.Base.min__ GHC.Base.op_z2218U__
     GHC.Base.op_zeze__ GHC.Base.op_zeze____ GHC.Base.op_zg__ GHC.Base.op_zg____
     GHC.Base.op_zgze__ GHC.Base.op_zgze____ GHC.Base.op_zl__ GHC.Base.op_zl____
     GHC.Base.op_zlze____ GHC.Base.op_zlzlzgzg__ GHC.Base.op_zlzlzgzg____
     GHC.Base.op_zsze__ GHC.Base.op_zsze____ GHC.Err.Build_Default GHC.Err.Default
     GHC.Err.error GHC.Num.fromInteger GHC.Num.negate GHC.Num.op_zm__ GHC.Num.op_zp__
     GHC.Wf.wfFix2 IntWord.Int IntWord.Word IntWord.bitcount IntWord.highestBitMask
     IntWord.indexOfTheOnlyBit IntWord.intFromWord IntWord.shiftLWord
     IntWord.shiftRWord IntWord.wordFromInt IntWord.wordTonat
*)
