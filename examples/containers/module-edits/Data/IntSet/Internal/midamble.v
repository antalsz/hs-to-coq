
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


Require Import Coq.ZArith.ZArith.
(* Z.ones 6 = 64-1 *)
Definition suffixBitMask : GHC.Num.Int := (Coq.ZArith.BinInt.Z.ones 6%Z).

(* This is a revised version of minView that passes the totality checker.
   But, it is less efficient. Would be good if we could define a version that
   is closer to the original, but that requires a precondition about the
   validity of the IntSet. *)

Definition indexOfTheOnlyBit :=
  fun x => Coq.ZArith.BinInt.Z.of_N (Coq.NArith.BinNat.N.log2 x).

Definition lowestBitSet : Nat -> GHC.Num.Int :=
  fun x => indexOfTheOnlyBit (Utils.Containers.Internal.BitUtil.lowestBitMask x).

Definition highestBitSet : Nat -> GHC.Num.Int :=
  fun x => indexOfTheOnlyBit (Utils.Containers.Internal.BitUtil.highestBitMask x).

Definition bitmapOfSuffix : GHC.Num.Int -> BitMap :=
  fun s => Utils.Containers.Internal.BitUtil.shiftLL #1 s.

Definition bin : Prefix -> Mask -> IntSet -> IntSet -> IntSet :=
  fun arg_0__ arg_1__ arg_2__ arg_3__ =>
    match arg_0__, arg_1__, arg_2__, arg_3__ with
    | _, _, l, Nil => l
    | _, _, Nil, r => r
    | p, m, l, r => Bin p m l r
    end.
Definition tip : Prefix -> BitMap -> IntSet :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | _, num_2__ =>
        if num_2__ GHC.Base.== #0 : bool
        then Nil
        else match arg_0__, arg_1__ with
             | kx, bm => Tip kx bm
             end
    end.

Definition minView_Manual : IntSet -> option (Key * IntSet)%type :=
  fun t =>
    let fix go arg_0__
              := match arg_0__ with
                 | Bin p m l r => 
                   match go l with 
                     | Some (pair result l') => Some (pair result (bin p m l' r))
                     | None => None
                   end
                 | Tip kx bm =>
                     let 'bi := lowestBitSet bm in
                     Some (pair (kx GHC.Num.+ bi) (tip kx (Data.Bits.xor bm (bm Data.Bits..&.(**)
                                                                    bitmapOfSuffix bi))))
                 | Nil => None
                 end in
    let j_12__ := go t in
    match t with
    | Nil => None
    | Bin p m l r =>
        if m GHC.Base.< #0 : bool
        then match go r with 
             | Some (pair result r') =>  Some (pair result (bin p m l r'))
             | None => None
             end
        else j_12__
    | _ => j_12__
    end.

Definition maxView_Manual : IntSet -> option (Key * IntSet)%type :=
  fun t =>
    let fix go arg_0__
              := match arg_0__ with
                 | Bin p m l r => match go r with 
                                   | Some (pair result r') => Some (pair result (bin p m l r'))
                                   | None => None
                                 end
                 | Tip kx bm =>
                     let 'bi := highestBitSet bm in
                     Some (pair (kx GHC.Num.+ bi) (tip kx (Data.Bits.xor bm (bm Data.Bits..&.(**)
                                                                    bitmapOfSuffix bi))))
                 | Nil => None
                 end in
    let j_12__ := go t in
    match t with
    | Nil => None
    | Bin p m l r =>
        if m GHC.Base.< #0 : bool
        then match go l with 
             | Some (pair result l') => Some (pair result (bin p m l' r))
             | None => None
             end
        else j_12__
    | _ => j_12__
    end.  

