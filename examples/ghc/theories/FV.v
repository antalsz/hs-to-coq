Require Import FV.

Lemma union_empty_l : forall fv, FV.unionFV FV.emptyFV fv = fv.
Proof. reflexivity. Qed.

Lemma union_empty_r : forall fv, FV.unionFV fv FV.emptyFV = fv.
Proof. reflexivity. Qed.
