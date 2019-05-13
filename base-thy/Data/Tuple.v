Require Import GHC.Base.
Require Data.Tuple.

Theorem hs_coq_tuple_fst {A B} (t : A * B) :
  Tuple.fst t = fst t.
Proof. reflexivity. Qed.

Theorem hs_coq_tuple_snd {A B} (t : A * B) :
  Tuple.snd t = snd t.
Proof. reflexivity. Qed.

Lemma fst_pair A B (x:A) (y:B) : Tuple.fst (x,y) = x.
Proof. simpl. reflexivity. Qed.
Hint Rewrite fst_pair : hs_simpl.
Lemma snd_pair A B (x:A) (y:B) : Tuple.snd (x,y) = y.
Proof. simpl. reflexivity. Qed.
Hint Rewrite snd_pair : hs_simpl.
