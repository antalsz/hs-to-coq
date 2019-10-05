Require Import GHC.DeferredFix.
Require Import Data.Graph.Inductive.Query.BFS.
Require Import Coq.Lists.List.
Require Import Data.Graph.Inductive.Internal.Queue.
Require Import NicerQueue.
Require Import Equations.Equations.
Require Import Crush.
Require Import Data.Graph.Inductive.Graph.
Require Import Coq.Bool.Bool.

(*Helpers*)
Definition null {a} (l: list a) :=
  match l with
  | nil => true
  | _ => false
  end.

(*Function to pop off queue satisfying given predicate*)
Fixpoint pop_list {a} (l: list a) (p: a -> bool) :=
  match l with
  | nil => nil
  | x :: xs => if (p x) then pop_list xs p else l
  end.

Definition pop_queue {a} (q: Queue.Queue a) (p: a -> bool) : Queue.Queue a :=
  queuePutList (pop_list (toList _ q) p) mkQueue.

(*Prove that first elt of queue satisfies predicate, prove for lists*)
Lemma pop_list_split: forall {a} (l : list a) p,
 exists l1, l1 ++ (pop_list l p) = l /\ (forall x, In x l1 -> p x = true).
Proof.
  intros. induction l.
  - exists nil. split; crush.
  - simpl. destruct (p a0) eqn : B. destruct IHl. exists (a0 :: x). split. simpl. destruct H. rewrite <- H at 2.
    reflexivity.
    intros. simpl in H0. destruct H0. subst. assumption. apply H. assumption.
    exists nil. split. reflexivity. intros. destruct H.
Qed.

Lemma pop_split_fst: forall {a} (l: list a) p h t,
  pop_list l p = t :: h -> p t = false.
Proof.
  intros. induction l. simpl in H. inversion H. simpl in H. destruct (p a0) eqn : B.
  apply IHl. apply H. inversion H; subst; assumption.
Qed.

(* Inductive relation*)
Section Ind.

Context {a : Type} {b : Type} { gr : Type -> Type -> Type} {Hgraph : Graph.Graph gr} {Hlaw : Graph.LawfulGraph gr}.

Definition state : Type := (gr a b) * list (Graph.Path) * RootPath.RTree.

Definition get_graph (s: state) :=
  match s with
  | (g, _, _) => g
  end.

Definition get_queue (s: state) :=
  match s with
  | (_, q, _) => q
end.

Definition get_paths (s: state) :=
  match s with
  | (_, _, p) => p
  end.

Definition vertex_in (g: gr a b) (v: Graph.Node) : bool :=
  match (Graph.match_ v g) with | (None, _) => true | _ => false end.

Definition in_graph (g : gr a b) (p: Graph.Path) : bool := 
  match p with
  | nil => true
  | v :: xs => vertex_in g v  end. 

Inductive bfs_step : state -> state -> Prop :=
  | bfs_find: forall g l r (p: Graph.Path) (q' : list Graph.Path) c g' (v : Graph.Node) tl,
    pop_list l (in_graph g) = p :: q' ->
    p = v :: tl ->
    Graph.match_ v g = (Some c, g') ->
    bfs_step (g, l, r) (g', q' ++ (List.map (fun x => cons x p) (Graph.suc' c)), r ++ (p :: nil)).

Definition start (g : gr a b) (v: Graph.Node) : state := (g, ((v :: nil) :: nil), nil).

Inductive valid : state -> Node -> Prop :=
  | v_start : forall g v, vertex_in g v = true -> valid (start g v) v
  | v_step : forall s s' v, valid s' v -> bfs_step s' s -> valid s v.

(*From Software Foundations*)
Definition relation (X : Type) := X -> X -> Prop.

Inductive multi {X : Type} (R : relation X) : relation X :=
  | multi_refl : forall (x : X), multi R x x
  | multi_step : forall (x y z : X),
                    R x y ->
                    multi R y z ->
                    multi R x z.

Theorem multi_R : forall (X : Type) (R : relation X) (x y : X),
    R x y -> (multi R) x y.
Proof.
  intros X R x y H.
  apply multi_step with y. apply H. apply multi_refl.
Qed.

Theorem multi_trans :
  forall (X : Type) (R : relation X) (x y z : X),
      multi R x y ->
      multi R y z ->
      multi R x z.
Proof.
  intros X R x y z G H.
  induction G.
    - (* multi_refl *) assumption.
    - (* multi_step *)
      apply multi_step with y. assumption.
      apply IHG. assumption.
Qed.


Definition bfs_multi (s1 s2 : state):= multi (bfs_step) s1 s2.

Lemma multi_valid: forall s1 s2 v,
  valid s1 v ->
  bfs_multi s1 s2 ->
  valid s2 v.
Proof.
  intros. induction H0. assumption. apply IHmulti. eapply v_step. apply H. assumption.
Qed.

Definition bfs_measure s := (BinInt.Z.abs_nat(Graph.noNodes (get_graph s))).

Lemma step_decr_measure: forall s s',
  bfs_step s s' ->
  bfs_measure s' < bfs_measure s.
Proof.
  intros. inversion H; unfold bfs_measure; simpl.
  eapply match_decr_size. symmetry. apply H2.
Qed.



Definition next_state (s: state) : state :=
  match s with
  | (g, q, r) =>
    let qnew := pop_list q (in_graph g) in
    (*So it is same order as in haskell version*)
    if (null qnew) then s else if (Graph.isEmpty g) then s else
    match qnew with
    (*impossible*)
    | nil => s
    | ((v :: tl) as p) :: q' => 
      match (Graph.match_ v g) with
       (*impossible*)
       | (None, _) => s
       | (Some c, g') => (g', q' ++ (List.map (fun x => cons x p) (Graph.suc' c)), r ++ (p :: nil))
      end
    (*impossible*)
    | (nil :: q') => s
    end
  end.

Definition done (s: state) : bool :=
  null (pop_list (get_queue s) (in_graph (get_graph s))) || (Graph.isEmpty (get_graph s)).

(*Every path we create has at least 1 element (v)*)
Lemma path_nonempty: forall s v,
  valid s v ->
  ~ In nil (get_paths s).
Proof.
  intros. intro. induction H.
  - simpl in H0. destruct H0.
  - inversion H1; subst.
    + apply in_app_or in H0. destruct H0. apply IHvalid; simpl; assumption. simpl in H0. 
      destruct H0. inversion H0. inversion H0.
Qed.

Lemma queue_path_nonempty: forall s v,
  valid s v ->
  ~ In nil (get_queue s).
Proof.
  intros. intro. induction H.
  - simpl in H0. destruct H0. inversion H0. destruct H0.
  - inversion H1; subst.
    apply in_app_or in H0. destruct H0. simpl in IHvalid.
     pose proof (pop_list_split l (in_graph g)). destruct H3 as [l']. destruct H3.
    rewrite H2 in H3. apply IHvalid. rewrite <- H3. apply in_or_app. right.
    simpl. right. assumption. 
    assert (forall l, ~In nil (map (fun x : Node => x :: v0 :: tl) l)). { intros.
    induction l0. simpl. auto. simpl. intro. destruct H3. inversion H3.
    contradiction. } eapply H3. apply H0.
Qed.


Lemma next_step: forall s v, valid s v -> done s = false -> bfs_step s (next_state s).
Proof.
  intros. destruct s. destruct p as [g q]. simpl. unfold done in H0; simpl in H0.
  rewrite Bool.orb_false_iff in H0. destruct H0. rewrite H0. rewrite H1.
  destruct (pop_list q (in_graph g)) eqn : Q. inversion H0. 
  simpl in H0. 
  (*prove p = nil case impossible*)
  destruct p eqn : P. pose proof (pop_list_split q (in_graph g)). destruct H2 as [l'].
  destruct H2. rewrite Q in H2.  pose proof (queue_path_nonempty (g, q, r) v). 
  apply H4 in H. simpl in H. rewrite <- H2 in H. exfalso. apply H. apply in_or_app. right.
  simpl. left. reflexivity. destruct (match_ n g) eqn : M. assert (Q' := Q).
  apply pop_split_fst in Q. simpl in Q. unfold vertex_in in Q. rewrite M in Q.
  destruct m. eapply bfs_find. apply Q'. reflexivity. apply M. inversion Q.
Qed. 

Lemma not_true: forall b,
  b <> true -> b = false.
Proof.
  intros. destruct b0; [contradiction | reflexivity].
Qed.

(*The big one - a tail recursive version of BFS we want to prove equivalent to both the inductive version as well
  as the Haskell one - Equations gives nice rewrite rules and elimination rules to prove things with this
  definition more easily*)
Equations bfs_tail (s: state) v (H: valid s v) : state by wf (bfs_measure s) lt :=
  bfs_tail s v H := if bool_dec (done s) true then s else (bfs_tail (next_state s) v _).
Next Obligation.
eapply v_step. apply H. eapply next_step. apply H. apply not_true; assumption. 
Defined.
Next Obligation.
apply step_decr_measure. eapply next_step. apply H. apply not_true; assumption.
Defined.

(*Prove valid and done*)
Lemma bfs_tail_done: forall s v (H: valid s v),
  done (bfs_tail s v H) = true.
Proof.
  intros. apply bfs_tail_elim. intros. destruct (bool_dec (done s0) true) eqn : ?.
  apply e. apply H1.
Qed.

Lemma bfs_tail_multi: forall s v (H: valid s v),
  bfs_multi s (bfs_tail s v H).
Proof.
  intros. apply bfs_tail_elim. intros. destruct (bool_dec (done s0) true) eqn : ?.
  - apply multi_refl.
  - eapply multi_step. eapply next_step. apply H0. apply not_true; assumption. apply H1.
Qed. 

(*Next step: try to prove this is equivalent to Haskell BFS, then can just work with this version/ valid states*)
End Ind.