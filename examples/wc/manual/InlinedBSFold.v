(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Coq.Program.Tactics.
Require Coq.Program.Wf.

(* Converted imports: *)

Require BL.
Require Import GHC.Base.
Require Import GHC.Char.
Require Import GHC.Num.
Require GHC.Unicode.
Require Types.

(* No type declarations to convert. *)

(* Converted value declarations: *)

Definition go
   : (Int * Int * Int * bool)%type -> Char -> (Int * Int * Int * bool)%type :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | pair (pair (pair cs ws) ls) wasSpace, c =>
        let addWord :=
          if wasSpace : bool then fromInteger 0 else
          if GHC.Unicode.isSpace c : bool then fromInteger 1 else
          fromInteger 0 in
        let addLine :=
          if c == Types.newline : bool then fromInteger 1 else
          fromInteger 0 in
        pair (pair (pair (cs + fromInteger 1) (ws + addWord)) (ls + addLine))
             (GHC.Unicode.isSpace c)
    end.

Definition countFile : BL.ByteString -> (Int * Int * Int)%type :=
  fun s =>
    let 'pair (pair (pair cs ws) ls) _ := BL.foldl' go (pair (pair (pair
                                                                    (fromInteger 0) (fromInteger 0)) (fromInteger 0))
                                                             false) s in
    pair (pair cs ws) ls.

(* External variables:
     Char Int bool false fromInteger op_zeze__ op_zp__ op_zt__ pair BL.ByteString
     BL.foldl' GHC.Unicode.isSpace
*)
