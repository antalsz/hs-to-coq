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
Require Import Data.Functor.
Require Import Data.Traversable.
Require Import GHC.Base.
Require Import GHC.Char.
Require Import GHC.Num.
Require Import GHC.Unicode.
Require IO.
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

Definition simpleFold : list String -> IO.IO (list (String * Counts)%type) :=
  fun paths =>
    for_ paths (fun fp =>
                  ((fromTuple ∘ simpleFoldCountFile) <$> IO.readFile fp) >>=
                  (fun count => return_ (pair fp count))).

(* External variables:
     Char Counts Int String bool false foldl' for_ fromInteger fromTuple isSpace list
     op_z2218U__ op_zeze__ op_zgzgze__ op_zlzdzg__ op_zp__ op_zt__ pair return_ IO.IO
     IO.readFile
*)
