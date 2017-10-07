Require Import Data.Foldable.

Require Import Proofs.GHC.Base.

(* -------------------------------------------------------------------- *)

(* Haskell-Coq equivalence *)

Require Coq.Lists.List.

Theorem hs_coq_foldr_list {A B} (f : A -> B -> B) (z : B) (l : list A) :
  foldr f z l = Coq.Lists.List.fold_right f z l.
Proof. apply hs_coq_foldr_base. Qed.
