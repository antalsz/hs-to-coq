(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Coq.Program.Tactics.
Require Coq.Program.Wf.

(* Converted imports: *)

Require Data.Foldable.
Require Err.
Require GHC.Base.
Require GHC.DeferredFix.
Require GHC.List.

(* Converted type declarations: *)

Inductive Queue a : Type := | MkQueue : list a -> list a -> Queue a.

Arguments MkQueue {_} _ _.

(* Converted value declarations: *)

Definition queuePut {a} : a -> Queue a -> Queue a :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | item, MkQueue ins outs => MkQueue (cons item ins) outs
    end.

Definition queuePutList {a} : list a -> Queue a -> Queue a :=
  fun xs q => Data.Foldable.foldl' (GHC.Base.flip queuePut) q xs.

Definition queueGet {a} `{Err.Default (a * Queue a)} : Queue a -> a * Queue a :=
  GHC.DeferredFix.deferredFix1 (fun queueGet (arg_0__ : Queue a) =>
                                  match arg_0__ with
                                  | MkQueue ins (cons item rest) => pair item (MkQueue ins rest)
                                  | MkQueue ins nil => queueGet (MkQueue nil (GHC.List.reverse ins))
                                  end).

Definition queueEmpty {a} : Queue a -> bool :=
  fun '(MkQueue ins outs) =>
    andb (Data.Foldable.null ins) (Data.Foldable.null outs).

Definition mkQueue {a} : Queue a :=
  MkQueue nil nil.

(* External variables:
     andb bool cons list nil op_zt__ pair Data.Foldable.foldl' Data.Foldable.null
     Err.Default GHC.Base.flip GHC.DeferredFix.deferredFix1 GHC.List.reverse
*)
