Require Import List.
Require Import FunctionalExtensionality.

Require Import LogExtInd.

Require Import GHC.Base.
Require Import Proofs.Freer.

Ltac destruct_units :=
  repeat match goal with
         | [x : unit |- _] => destruct x
         | [H : forall (x : unit), _ |- _] => specialize (H tt)
         end.

Fixpoint count_Vis {A} (m : OutputExt A) : nat :=
  match m with
  | Ret _ => 0
  | Vis (Out c) f => 1 + (count_Vis (f tt))
  end.

Lemma count_Vis_is_length_collect : forall m,
    count_Vis m = length (collect m).
Proof.
  intros. induction m.
  - destruct_units. reflexivity.
  - simpl. destruct e. destruct_units.
    assert (length (collect (Vis (Out c) f)) = S (length (collect (f tt)))).
    { unfold collect, interp_ext.
    cbv. 
    unfold collect, length, interp_ext.
Admitted.
     
Lemma collect_bind_dist : forall m1 m2,
    collect (m1 >> m2) = collect m1 ++ collect m2.
Proof.
  induction m1.
  - intros m2. destruct_units. simpl.
    replace (Ret tt) with (@return_ OutputExt _ _ _ _ tt) by reflexivity.
    replace (return_ tt >> m2) with (return_ tt >>= (fun _ => m2)) by reflexivity.
    rewrite monad_left_id. reflexivity.
  - intros. destruct e. 
Admitted.

Lemma length_bind : forall m1 m2,
    length (collect (m1 >> m2)) = length (collect (m2 >> m1)).
Proof.
  induction m1.
  - destruct m2.
    + destruct r, u. reflexivity.
    + destruct r.
      replace (Ret tt) with (@return_ OutputExt _ _ _ _ tt) by reflexivity.
      replace (return_ tt >> Vis l f) with (return_ tt >>= (fun _ => Vis l f)) by reflexivity.
      replace (Vis l f >> return_ tt) with (Vis l f >>= return_).
      rewrite monad_left_id, monad_right_id. reflexivity.
      * destruct l. cbn. f_equal. apply functional_extensionality. intros. destruct x.
        f_equal. apply functional_extensionality. intros x. destruct x. reflexivity.
  - intros m2. destruct e. specialize (H tt).
Admitted.
