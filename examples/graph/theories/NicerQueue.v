Require Import Data.Graph.Inductive.Internal.Queue.
Require Import Coq.Lists.List.
Require Import Foldable.
Require Import GHC.DeferredFix.
Require Import Omega.

Section Queue.

Variable a : Type.

(*Tactics*)
Lemma reverse_equiv: forall (l: list a),
  List.reverse l = rev_append l nil.
Proof.
  intros. induction l; unfold List.reverse; simpl; try(reflexivity); try(apply IHl).
Qed.

Ltac unfold_null := unfold null in *; unfold Foldable__list in *; simpl in *;
 unfold Foldable.Foldable__list_null in *; unfold List.null in *.

Ltac rewrite_rev:= rewrite reverse_equiv; rewrite rev_append_rev; simpl.

Definition toList (q: Queue a) : list a :=
  match q with
  | MkQueue x y => y ++ rev x
  end.

Lemma toList_empty: toList mkQueue = nil.
Proof.
  auto.
Qed.

Lemma toList_queuePut : forall q x, toList (queuePut x q) = toList q ++ (x :: nil).
Proof.
  intros.  unfold queuePut. destruct q. simpl. intuition.
Qed.

Lemma toList_queuePutList: forall q l, toList (queuePutList l q) = toList q ++ l.
Proof.
  intros. unfold queuePutList. (* unfold toList. *) unfold Base.flip. unfold foldl'. unfold Foldable__list.
  simpl. unfold Foldable.Foldable__list_foldl'. unfold Base.foldl'. unfold id. generalize dependent q. 
  induction l; intros; simpl.
  - rewrite app_nil_r; reflexivity.
  - rewrite IHl. rewrite toList_queuePut. rewrite <- app_assoc. reflexivity.
Qed.

Lemma toList_queueEmpty: forall q, queueEmpty q = true <-> toList q = nil.
Proof.
  intros. unfold queueEmpty. unfold_null. destruct q. unfold toList. destruct l; simpl.
  destruct l0. split; intros; reflexivity. split; intro H; inversion H.
  split; intros H. inversion H. destruct l0. destruct (rev l).
  simpl in H. inversion H. simpl in H. inversion H. simpl in H. inversion H. 
Qed.

(** ** Specification for QueueGet **)
(* This is nontrivial because the queueGet function in the library is not only
  nonterminating for empty queues but also recurses on a queue of the same size in the recursive case. To get
  around this restriction and prove that a measure is decreasing, we use a strange measure that actually does
  decrease **)

(*Recursion does from MkQueue x nil -> MkQueue nil x, so this measure does decrease for a nonempty queue*)
Definition queue_size' (q : Queue a) := match q with
  | MkQueue x y => (2 * Datatypes.length x) + (Datatypes.length y) 
  end.

(*Prove that this is well-formed*)

Definition queue_order q1 q2 := queue_size' q1 < queue_size' q2.

Lemma queue_order_wf': forall x, forall q, queue_size' q <= x -> Acc queue_order q.
Proof.
  intros. unfold queue_order. generalize dependent q. induction x; intros. 
  - apply Acc_intro. intros. assert (queue_size' y < 0) by omega. omega.
  - intros. apply Acc_intro. intros. apply IHx. omega.
Defined.  

Lemma queue_order_wf : well_founded queue_order.
Proof.
   red; intro; eapply queue_order_wf'; eauto.
Defined.

(* Total version of betterQueueGet that makes it easier to reason about. It has the same type but we don't
    need to worry about deferredFix once we prove the following lemma*)

Definition flip_queue (q: Queue a) : Queue a :=
  match q with
  | MkQueue (x :: xs) nil => MkQueue nil (rev (x :: xs))
  | MkQueue _ _ => q
  end.

Definition betterQueueGet (q: Queue a) (x : a) : (a * Queue a) :=
   match (flip_queue q) with
  | MkQueue l (x :: xs) => (x, MkQueue l xs)
  | MkQueue _ _ => (x, MkQueue nil nil)
  end.

Instance Queue__Default {a} : GHC.Err.Default (Data.Graph.Inductive.Internal.Queue.Queue a) :=
  { default := Data.Graph.Inductive.Internal.Queue.MkQueue nil nil }.

Lemma queueGet_def: forall q x `{Default a}, queueEmpty q = false -> queueGet q = betterQueueGet q x.
Proof.
  intros. unfold queueGet. unfold deferredFix1. destruct q. destruct l0. destruct l. simpl in H0. inversion H0. 
  - remember (MkQueue (a0 :: l) nil) as q. rewrite (deferredFix_eq_on _ (fun x => queueEmpty x = false) 
  (fun x y => queue_size' x < queue_size' y)).
    + rewrite Heqq. rewrite_rev. 
     rewrite (deferredFix_eq_on _ (fun x => queueEmpty x = false) 
  (fun x y => queue_size' x < queue_size' y)).
    * destruct (rev l) eqn : R. simpl. unfold betterQueueGet. simpl. rewrite R. simpl. reflexivity.
      simpl. unfold betterQueueGet. simpl. rewrite R. simpl. rewrite app_nil_r. reflexivity.
    * apply queue_order_wf.
    * unfold recurses_on. intros. destruct x0. destruct l1. destruct l0. simpl in H1. inversion H1. 
      apply H2. simpl. rewrite_rev. unfold_null. 
      destruct (rev l0);  reflexivity.
      simpl. rewrite_rev. rewrite app_nil_r. rewrite app_length. simpl.  rewrite rev_length. omega. 
      reflexivity.
    * simpl. unfold_null. destruct (rev l); reflexivity.
    + apply queue_order_wf.
    + unfold recurses_on. intros. destruct x0. destruct l1. apply H2. unfold queueEmpty in H1. 
      unfold queueEmpty. simpl. unfold_null.
      destruct l0. intuition. rewrite_rev. 
      destruct (rev l0); reflexivity. simpl. destruct l0. unfold queueEmpty in H1; unfold_null. inversion H1.
      simpl. rewrite_rev. rewrite app_nil_r. rewrite app_length; rewrite rev_length. simpl. omega. reflexivity.
     + apply H0.
  - rewrite (deferredFix_eq_on _ (fun x => queueEmpty x = false) 
  (fun x y => queue_size' x < queue_size' y)).
    + unfold betterQueueGet. simpl. destruct l; reflexivity.
    + apply queue_order_wf.
    + unfold recurses_on. intros. destruct x0. destruct l1. destruct l2. unfold queueEmpty in H1.
      unfold_null. inversion H1. reflexivity. destruct l2. apply H2. unfold queueEmpty. unfold_null.
      rewrite_rev. destruct (rev l1); reflexivity. rewrite_rev. rewrite app_nil_r. rewrite app_length.
      rewrite rev_length. simpl. omega. reflexivity.
    + assumption.
Qed.

(*Now, the specification we want*)

Lemma toList_queueGet: forall q x l `{Err.Default a} , toList q = x :: l -> fst (queueGet q) = x
  /\ toList (snd (queueGet q)) = l.
Proof.
  intros. assert (queueEmpty q = false). destruct (queueEmpty q) eqn : E. rewrite toList_queueEmpty in E.
  rewrite E in H0. inversion H0. reflexivity. rewrite (queueGet_def q x). destruct q. destruct l1; simpl.
  - unfold betterQueueGet; simpl. destruct l0 eqn : L. simpl in H0. inversion H0.
    destruct (rev l0) eqn : R; simpl. rewrite L in R. simpl in R. destruct (rev l1); inversion R.
    simpl in H0. rewrite H0. simpl. split; try(rewrite app_nil_r); reflexivity.
  - unfold betterQueueGet; simpl. simpl in H0. inversion H0; subst.
    destruct l0; simpl; split; try(rewrite app_nil_r); try(reflexivity).
  - assumption.
Qed.

End Queue.
