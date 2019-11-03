(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Coq.Program.Tactics.
Require Coq.Program.Wf.

(* Converted imports: *)

Require Import Data.Foldable.
Require Import GHC.Base.
Require Import GHC.Char.
Require Import GHC.Num.
Require Import GHC.Unicode.

Require Import Types.

(* No type declarations to convert. *)

(* Converted value declarations: *)

Definition simpleFoldCountFile : String -> (Int * Int * Int)%type :=
  fun s =>
    let go
     : (Int * Int * Int * bool)%type -> Char -> (Int * Int * Int * bool)%type :=
      fun arg_0__ arg_1__ =>
        match arg_0__, arg_1__ with
        | pair (pair (pair cs ws) ls) wasSpace, c =>
            let addWord :=
              if wasSpace : bool then fromInteger 0 else
              if isSpace c : bool then fromInteger 1 else
              fromInteger 0 in
            let addLine :=
              if c == newline : bool then fromInteger 1 else
              fromInteger 0 in
            pair (pair (pair (cs + fromInteger 1) (ws + addWord)) (ls + addLine)) (isSpace
                  c)
        end in
    let 'pair (pair (pair cs ws) ls) _ := foldl' go (pair (pair (pair (fromInteger
                                                                       0) (fromInteger 0)) (fromInteger 0)) false) s in
    pair (pair cs ws) ls.

(* External variables:
     Char Int String bool false foldl' fromInteger isSpace op_zeze__ op_zp__ op_zt__
     pair
*)
