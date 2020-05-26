(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Coq.Program.Tactics.
Require Coq.Program.Wf.

(* Converted imports: *)

Require Coq.Numbers.BinNums.
Require Data.Bits.
Require Data.Foldable.
Require Data.IntSet.Internal.
Require GHC.Base.
Require GHC.Num.
Import Data.Bits.Notations.
Import GHC.Base.Notations.
Import GHC.Num.Notations.

(* No type declarations to convert. *)

(* Converted value declarations: *)

Definition validTipPrefix : Data.IntSet.Internal.Prefix -> bool :=
  fun p => (#63 Data.Bits..&.(**) p) GHC.Base.== #0.

Fixpoint tipsValid (t : Data.IntSet.Internal.IntSet) : bool
           := match t with
              | Data.IntSet.Internal.Nil => true
              | (Data.IntSet.Internal.Tip p b as tip) => validTipPrefix p
              | Data.IntSet.Internal.Bin _ _ l r => andb (tipsValid l) (tipsValid r)
              end.

Definition nilNeverChildOfBin : Data.IntSet.Internal.IntSet -> bool :=
  fun t =>
    let fix noNilInSet t'
              := match t' with
                 | Data.IntSet.Internal.Nil => false
                 | Data.IntSet.Internal.Tip _ _ => true
                 | Data.IntSet.Internal.Bin _ _ l' r' => andb (noNilInSet l') (noNilInSet r')
                 end in
    match t with
    | Data.IntSet.Internal.Nil => true
    | Data.IntSet.Internal.Tip _ _ => true
    | Data.IntSet.Internal.Bin _ _ l r => andb (noNilInSet l) (noNilInSet r)
    end.

Fixpoint maskRespected (t : Data.IntSet.Internal.IntSet) : bool
           := match t with
              | Data.IntSet.Internal.Nil => true
              | Data.IntSet.Internal.Tip _ _ => true
              | Data.IntSet.Internal.Bin _ binMask l r =>
                  andb (Data.Foldable.all (fun x => Data.IntSet.Internal.zero x binMask)
                        (Data.IntSet.Internal.elems l)) (andb (Data.Foldable.all (fun x =>
                                                                                    negb (Data.IntSet.Internal.zero x
                                                                                          binMask))
                                                               (Data.IntSet.Internal.elems r)) (andb (maskRespected l)
                                                                                                     (maskRespected r)))
              end.

Fixpoint maskPowerOfTwo (t : Data.IntSet.Internal.IntSet) : bool
           := match t with
              | Data.IntSet.Internal.Nil => true
              | Data.IntSet.Internal.Tip _ _ => true
              | Data.IntSet.Internal.Bin _ m l r =>
                  andb (Utils.Containers.Internal.BitUtil.bitcount #0 (m) GHC.Base.== #1) (andb
                        (maskPowerOfTwo l) (maskPowerOfTwo r))
              end.

Fixpoint commonPrefix (t : Data.IntSet.Internal.IntSet) : bool
           := let sharedPrefix
               : Data.IntSet.Internal.Prefix -> Coq.Numbers.BinNums.N -> bool :=
                fun p a => p GHC.Base.== (p Data.Bits..&.(**) a) in
              match t with
              | Data.IntSet.Internal.Nil => true
              | Data.IntSet.Internal.Tip _ _ => true
              | (Data.IntSet.Internal.Bin p _ l r as b) =>
                  andb (Data.Foldable.all (sharedPrefix p) (Data.IntSet.Internal.elems b)) (andb
                        (commonPrefix l) (commonPrefix r))
              end.

Definition valid : Data.IntSet.Internal.IntSet -> bool :=
  fun t =>
    andb (nilNeverChildOfBin t) (andb (maskPowerOfTwo t) (andb (commonPrefix t)
                                                               (andb (maskRespected t) (tipsValid t)))).

(* External variables:
     andb bool false negb true Coq.Numbers.BinNums.N Data.Bits.op_zizazi__
     Data.Foldable.all Data.IntSet.Internal.Bin Data.IntSet.Internal.IntSet
     Data.IntSet.Internal.Nil Data.IntSet.Internal.Prefix Data.IntSet.Internal.Tip
     Data.IntSet.Internal.elems Data.IntSet.Internal.zero GHC.Base.op_zeze__
     GHC.Num.fromInteger Utils.Containers.Internal.BitUtil.bitcount
*)
