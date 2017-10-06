Require Import GHC.List.

(* -------------------------------------------------------------------- *)

(* Haskell-Coq equivalence *)

Require Coq.Lists.List.

Theorem hs_coq_filter {A} (p : A -> bool) (l : list A) :
  filter p l = Coq.Lists.List.filter p l.
Proof.
  induction l; simpl; auto.
  destruct (p _); f_equal; auto.
Qed.
