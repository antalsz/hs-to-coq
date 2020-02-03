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
Require Data.OldList.
Require Import Data.Traversable.
Require Import GHC.Base.
Require IO.
Require Import Types.

(* No type declarations to convert. *)

(* Midamble *)

Fixpoint length {a} (xs : list a) : Int :=
  match xs with 
  | nil => # 0
  | cons _ ys => (1 + (length ys))%Z
  end.

(* Converted value declarations: *)

Definition stupidCountFile : String -> Counts :=
  fun s =>
    fromTuple (pair (pair (length s) (length (Data.OldList.words s))) (length
                     (Data.OldList.lines s))).

Definition stupid : list String -> IO.IO (list (String * Counts)%type) :=
  fun paths =>
    for_ paths (fun fp =>
                  (stupidCountFile <$> IO.readFile fp) >>=
                  (fun count => return_ (pair fp count))).

(* External variables:
     Counts String for_ fromTuple length list op_zgzgze__ op_zlzdzg__ op_zt__ pair
     return_ Data.OldList.lines Data.OldList.words IO.IO IO.readFile
*)
