Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Coq.Program.Tactics.
Require Coq.Program.Wf.

(* Preamble *)

Require GHC.Base.
Require GHC.Enum.
Require GHC.Err.
Require Data.Either.
Require Utils.Containers.Internal.PtrEquality.

Require Import mathcomp.ssreflect.ssreflect.

Extraction Blacklist Prelude.
Extraction Language Haskell.

Set Warnings "-extraction-reserved-identifier".

Extract Inductive bool => "Prelude.Bool" ["Prelude.True" "Prelude.False" ].
Extract Inductive comparison => "Prelude.Ordering" ["Prelude.EQ" "Prelude.LT" "Prelude.GT"].
Extract Inductive list => "[]" ["[]" "(:)"].
Extract Inductive option => "Prelude.Maybe" [ "Prelude.Just" "Prelude.Nothing"].
Extract Inductive prod => "(,)" ["(,)"].
Extract Inductive Either.Either => "Prelude.Either" [ "Prelude.Left" "Prelude.Right" ].

Require Import Data.Set.Internal.

Extract Constant PtrEquality.ptrEq => "\ x y -> Prelude.False".
Extract Constant PtrEquality.hetPtrEq => "\ x y -> Prelude.False".
Extract Constant Base.errorWithoutStackTrace => "errorWithoutStackTrace".
Extract Constant GHC.Err.patternFailure => "(\d -> Prelude.error ""patternFailure"")".
Extract Constant GHC.DeferredFix.deferredFix => "(\d f -> let r = f r in r)".

(*
-- I'm trying to convert Z to Int, but this does not work. 
Require Import GHC.Num.
Extract Constant Num.Int => "Prelude.Int".
Extract Constant Num.Num_Int__ => "Prelude.undefined".
Require GHC.Char.
Extract Constant Char.Char => "Prelude.Char".
Extract Constant Char.hs_char__ => "Prelude.undefined".
Extract Constant Char.chr => "Prelude.undefined".
Extract Constant Char.ord => "Prelude.undefined".
Require Import GHC.Base.
Extract Constant Base.Eq_Int___ => "Prelude.undefined".
Extract Constant Base.Ord_Int___ => "Prelude.undefined".
Extract Constant Base.Eq_Char___ => "Prelude.undefined".
Extract Constant Base.Ord_Char___ => "Prelude.undefined". *)

(** Eq *)

Extraction Implicit eq_rect   [ x y ].
Extraction Implicit eq_rect_r [ x y ].
Extraction Implicit eq_rec    [ x y ].
Extraction Implicit eq_rec_r  [ x y ].

Extract Inlined Constant eq_rect   => "Prelude.id".
Extract Inlined Constant eq_rect_r => "Prelude.id".
Extract Inlined Constant eq_rec    => "Prelude.id".
Extract Inlined Constant eq_rec_r  => "Prelude.id".

(** Ord *)

Extract Inductive comparison =>
  "Prelude.Ordering" ["Prelude.EQ" "Prelude.LT" "Prelude.GT"].

(** Int *)

Extract Inductive Datatypes.nat => "Prelude.Integer"
  ["(0 :: Prelude.Integer)" "Prelude.succ"]
  "(\fO fS n -> if n Prelude.<= 0 then fO () else fS (Prelude.pred n))".

Extract Inlined Constant EqNat.beq_nat         => "((Prelude.==) :: Prelude.Integer -> Prelude.Integer -> Prelude.Bool)".
Extract Inlined Constant Compare_dec.le_lt_dec => "((Prelude.<=) :: Prelude.Integer -> Prelude.Integer -> Prelude.Bool)".
Extract Inlined Constant Compare_dec.le_gt_dec => "(Prelude.>)".
Extract Inlined Constant Compare_dec.le_dec    => "((Prelude.<=) :: Prelude.Integer -> Prelude.Integer -> Prelude.Bool)".
Extract Inlined Constant Compare_dec.lt_dec    => "(Prelude.<)".
Extract Inlined Constant Compare_dec.leb       => "((Prelude.<=) :: Prelude.Integer -> Prelude.Integer -> Prelude.Bool)".

Extract Inlined Constant plus  => "(Prelude.+)".
Extract Inlined Constant minus => "(Prelude.-)".
Extract Inlined Constant mult  => "(Prelude.* )".
Extract Inlined Constant pred  => "(Prelude.pred :: Prelude.Integer -> Prelude.Integer)".
Extract Inlined Constant min   => "Prelude.min".
Extract Inlined Constant max   => "(Prelude.max :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer)".

(** N *)

Require Import Coq.NArith.NArith.

Extract Inductive N => "Prelude.Integer" [ "0" "(\x -> x)" ]
  "(\fO fS n -> if n Prelude.== 0 then fO () else fS n)".

Extract Inlined Constant N.add       => "(Prelude.+)".
Extract Inlined Constant N.sub       => "(Prelude.-)".
Extract Inlined Constant N.mul       => "(Prelude.*)".
Extract Inlined Constant N.max       => "Prelude.max".
Extract Inlined Constant N.min       => "Prelude.min".

Extract Constant N.div =>
  "(\n m -> if m Prelude.== 0 then 0 else Prelude.div n m)".
Extract Constant N.modulo =>
  "(\n m -> if m Prelude.== 0 then 0 else Prelude.mod n m)".

(** Z, positive, Q *)

Require Import Coq.ZArith.ZArith.
Require Import Coq.QArith.QArith.

Extract Inductive positive => "Prelude.Integer" [
  "(\x -> 2 Prelude.* x Prelude.+ 1)"
  "(\x -> 2 Prelude.* x)"
  "1" ]
  "(\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n then fI (n `Prelude.div` 2)
                                    else fO (n `Prelude.div` 2))".

Extract Inductive Z => "Prelude.Integer" [ "0" "(\x -> x)" "Prelude.negate" ]
  "(\fO fP fN n -> if n Prelude.== 0 then fO () else
                   if n Prelude.> 0 then fP n else fN (Prelude.negate n))".

Extract Inlined Constant Z.add       => "(Prelude.+)".
Extract Inlined Constant Z.sub       => "(Prelude.-)".
Extract Inlined Constant Z.mul       => "(Prelude.*)".
Extract Inlined Constant Z.max       => "Prelude.max".
Extract Inlined Constant Z.min       => "Prelude.min".
Extract Inlined Constant Z_ge_lt_dec => "(Prelude.>=)".
Extract Inlined Constant Z_gt_le_dec => "(Prelude.>)".

Extract Constant Z.div =>
  "(\n m -> if m Prelude.== 0 then 0 else Prelude.div n m)".
Extract Constant Z.modulo =>
  "(\n m -> if m Prelude.== 0 then 0 else Prelude.mod n m)".

Extract Inductive Q => "(GHC.Real.Ratio Prelude.Integer)" [ "(GHC.Real.:%)" ].

Extract Inlined Constant Qplus  => "(Prelude.+)".
Extract Inlined Constant Qminus => "(Prelude.-)".
Extract Inlined Constant Qmult  => "(Prelude.*)".

Extract Constant Qdiv =>
  "(\n m -> if m Prelude.== 0 then 0 else n Prelude./ m)".

(** Bool *)

Extract Inductive bool    => "Prelude.Bool" ["Prelude.True" "Prelude.False"].
Extract Inductive sumbool => "Prelude.Bool" ["Prelude.True" "Prelude.False"].

(* Extract Inlined Constant Equality.bool_beq => "((Prelude.==) :: Prelude.Bool -> Prelude.Bool -> Prelude.Bool)". *)
Extract Inlined Constant Bool.bool_dec     => "((Prelude.==) :: Prelude.Bool -> Prelude.Bool -> Prelude.Bool)".

Extract Inlined Constant Sumbool.sumbool_of_bool => "".

Extract Inlined Constant negb => "Prelude.not".
Extract Inlined Constant orb  => "(Prelude.||)".
Extract Inlined Constant andb => "(Prelude.&&)".

(** Maybe *)

Extract Inductive option => "Prelude.Maybe" ["Prelude.Just" "Prelude.Nothing"].
Extract Inductive sumor  => "Prelude.Maybe" ["Prelude.Just" "Prelude.Nothing"].

(** Either *)

Extract Inductive sum => "Prelude.Either" ["Prelude.Left" "Prelude.Right"].

(** List *)

Extract Inductive list => "[]" ["[]" "(:)"].

Extract Inlined Constant app             => "(Prelude.++)".
Extract Inlined Constant List.map        => "Prelude.map".
Extract         Constant List.fold_left  => "\f l z -> Prelude.foldl f z l".
Extract Inlined Constant List.fold_right => "Prelude.foldr".
Extract Inlined Constant List.find       => "Prelude.find".
Extract Inlined Constant List.length     => "coq_Foldable__list_length".

(** Tuple *)

Extract Inductive prod => "(,)" ["(,)"].
Extract Inductive sigT => "(,)" ["(,)"].

Extract Inlined Constant fst    => "Prelude.fst".
Extract Inlined Constant snd    => "Prelude.snd".
Extract Inlined Constant projT1 => "Prelude.fst".
Extract Inlined Constant projT2 => "Prelude.snd".

Extract Inlined Constant proj1_sig => "".

(** Unit *)

Extract Inductive unit => "()" ["()"].

(** String *)

Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.

Extract Inductive string => "Prelude.String" ["[]" "(:)"].
Extract Inductive ascii  => "Prelude.Char" ["HString.asciiToChar"]
  "HString.foldChar".

Extract Inlined Constant ascii_of_nat => "Data.Char.chr".
Extract Inlined Constant nat_of_ascii => "Data.Char.ord".
Extract Inlined Constant ascii_of_N   => "Data.Char.chr".
Extract Inlined Constant ascii_of_pos => "Data.Char.chr".

Recursive Extraction Library Internal.

Extraction Blacklist Internal.

Require Import Data.IntSet.Internal.
Recursive Extraction Library Internal.





