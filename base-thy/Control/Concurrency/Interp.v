Require Import GHC.MVar.
Require Import Control.Concurrent.MVar.
Require Import GHC.Num.

Require Import Streams Arith.

Open Scope N_scope.

Record heap :=
  { max_loc : Word;
    content : Word -> option Word }.

Definition empty_heap :=
  {| max_loc := #0;
     content := fun _ => None |}.

Definition prog := IO unit.

Inductive stopFlag :=
| Unexpected
| Blocked
| Finished.

Program Definition interp (p : prog) (h : heap) : (stopFlag + (prog * heap)) :=
  match p with
  | GHC.IO.Ret m => inl Finished
  | GHC.IO.Vis eff k => _
  end.
Next Obligation.
  destruct eff eqn:Heff.
  - destruct h.
    remember (max_loc0 + 1) as max_loc1. right.
    exact (k (MkMV max_loc1),
           {| max_loc := max_loc1;
              content := fun n => if (n =? max_loc0) then None else content0 n
           |}).
  - destruct m.
    destruct (content h loc) eqn:Hcontent.
    + destruct (@decode A _ w) eqn:Hdecode.
      * right. destruct h.
        exact (k a,
               {| max_loc := max_loc0;
                  content := fun n => if n =? loc then None else content0 n
               |}).
      * left. exact Unexpected.
    + left. exact Blocked.
  - destruct m.
    destruct (content h loc) eqn:Hcontent.
    + destruct (@decode A _ w) eqn:Hdecode.
      * right. exact (k a, h).
      * left. exact Unexpected.
    + left. exact Blocked.
  - destruct m.
    destruct (content h loc) eqn:Hcontent.
    + left. exact Blocked.
    + right. destruct h.
      exact (k tt,
             {| max_loc := max_loc0;
                content := fun n => if n =? loc then (Some (encode a))  else content0 n
             |}).
  - destruct m.
    destruct (content h loc) eqn:Hcontent.
    + destruct (@decode A _ w) eqn:Hdecode.
      * right. destruct h.
        exact (k (Some a),
               {| max_loc := max_loc0;
                  content := fun n => if n =? loc then None else content0 n
               |}).
      * left. exact Unexpected.
    + right. exact (k None, h).
  - destruct m.
    destruct (content h loc) eqn:Hcontent.
    + destruct (@decode A _ w) eqn:Hdecode.
      * right. exact (k (Some a), h).
      * left. exact Unexpected.
    + right. exact (k None, h).
  - destruct m.
    destruct (content h loc) eqn:Hcontent.
    + right. exact (k false, h).
    + right. destruct h.
      exact (k true,
             {| max_loc := max_loc0;
                content := fun n => if n =? loc then (Some (encode a))  else content0 n
             |}).
  - destruct m.
    destruct (content h loc) eqn:Hcontent.
    + right. exact (k false, h).
    + right. exact (k true, h).
Defined.

Inductive safe_single_prog_on_heap (p : prog) (h : heap) : Prop :=
| SafeFinished (_ : interp p h = inl Finished)
| SafeRunning : forall p' h', interp p h = inr (p', h') ->
                         safe_single_prog_on_heap p' h' ->
                         safe_single_prog_on_heap p h.

Definition safe_single_prog (p : prog) : Prop :=
  safe_single_prog_on_heap p empty_heap.

Inductive deadlock_single_prog_on_heap (p : prog) (h : heap) : Prop :=
| DeadlockBlocked (_ : interp p h = inl Blocked)
| DeadlockRunning : forall p' h', interp p h = inr (p', h') ->
                             deadlock_single_prog_on_heap p' h' ->
                             deadlock_single_prog_on_heap p h.

Definition deadlock_single_prog (p : prog) : Prop :=
  deadlock_single_prog_on_heap p empty_heap.

Lemma deadlock_unsafe' : forall p h,
    deadlock_single_prog_on_heap p h -> ~ safe_single_prog_on_heap p h.
Proof.
  induction 1. 
  - inversion 1; subst; rewrite H1 in H; discriminate.
  - inversion 1; rewrite H2 in H.
    + discriminate.
    + inversion H; subst. contradiction.
Qed.

Lemma deadlock_unsafe : forall p,
    deadlock_single_prog p -> ~ safe_single_prog p.
Proof.
  intro p. apply deadlock_unsafe'.
Qed.
