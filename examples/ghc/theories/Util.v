Require Util.
Require Import Coq.Lists.List.
Import ListNotations.
Require GHC.List.

Require GHC.Base.
Import GHC.Base.ManualNotations.

Lemma map_unzip : forall (a b c : Type)( f : a -> b * c) xs, 
  Util.mapAndUnzip f xs = List.unzip (map f xs).
Proof.
  induction xs; simpl; auto.
  destruct Util.mapAndUnzip.
  destruct List.unzip.
  destruct (f a0).
  inversion IHxs.
  auto.
Qed.
