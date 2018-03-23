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
