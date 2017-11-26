Require Import Data.OldList.

(* -------------------------------------------------------------------- *)

(* Haskell-Coq equivalence *)

Require Coq.Lists.List.

Theorem hs_coq_partition {A} (p : A -> bool) (l : list A) :
  partition p l = Coq.Lists.List.partition p l.
Proof.
  unfold partition; induction l; simpl; auto.
Qed.
