Require Import GHC.Base.
Require Data.Tuple.

Theorem hs_coq_tuple_fst {A B} (t : A * B) :
  Tuple.fst t = fst t.
Proof. reflexivity. Qed.

Theorem hs_coq_tuple_snd {A B} (t : A * B) :
  Tuple.snd t = snd t.
Proof. reflexivity. Qed.
