Require Import List.
Import ListNotations.
Require Import DList.

Section Tests.
  Variable T : Type.

  Goal forall (a b : T), toList (append (singleton a) (singleton b)) = [a; b].
  Proof. reflexivity. Qed.

  Goal forall (a : T) b, toList (cons_ a b) = a :: (toList b).
  Proof. intros. destruct b. reflexivity. Qed.

  Goal forall (a b c : DList T),
      append (append a b) c = append a (append b c).
  Proof.
    intros. destruct a; destruct b; destruct c. reflexivity. Qed.
  
  Goal forall (a b : DList T),
      length (toList (append a b)) = length (toList (append b a)).
  Proof.
    intros. destruct a; destruct b.
    simpl. unfold Base.op_z2218U__. f_equal.
    (** Cannot prove this directly at this point. *)
  Abort.
End Tests.    
