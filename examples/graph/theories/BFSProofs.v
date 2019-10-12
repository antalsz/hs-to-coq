Require Import GHC.DeferredFix.
Require Import Data.Graph.Inductive.Query.BFS.
Require Import Coq.Lists.List.
Require Import Data.Graph.Inductive.Internal.Queue.
Require Import NicerQueue.
Require Import Equations.Equations.
Require Import Crush.
Require Import Data.Graph.Inductive.Graph.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.SetoidList.
Require Import Omega.
Require Import Wellfounded.
Require Import Coq.Relations.Relation_Operators.
Require Import Coq.Lists.ListDec.

Require Import CoLoR.Util.Relation.Lexico.
Require Import CoLoR.Util.Relation.SN.

Require Import Coq.FSets.FMapList.
Require Import Coq.FSets.FMapInterface.
Require Import Coq.Structures.OrderedTypeEx.

Module M := FMapList.Make(N_as_OT).


(*Helpers*)
Definition null {a} (l: list a) :=
  match l with
  | nil => true
  | _ => false
  end.

Ltac simplify' := try(rewrite andb_diag in *); try(rewrite andb_true_iff in *); try(rewrite negb_true_iff in *);
  try(rewrite andb_false_iff in *); try(rewrite negb_false_iff in *); intuition.

Ltac destruct_all :=
repeat(match goal with
            |[H: (exists _, _) |- _] => destruct H
            |[H: _ /\ _ |- _] => destruct H 
            end; try(rewrite andb_true_iff in *)).

(*Ltac for solving statements of the form: In x l, where l may be many lists appended together*) 
Ltac solve_in :=
  match goal with
  | [ H : _ |- In ?x (?l ++ ?r)] => apply in_or_app; solve_in
  | [ H : _ |- In ?x ?s \/ In ?x ?s'] => (right; solve_in) + (left; solve_in) 
  | [ H : _ |- In ?x (?x :: ?l)] => simpl; left; reflexivity
  | [H : _ |- In ?x (?a :: ?l)] => simpl; right; solve_in
  | [ H : _ |- _ ] => try(reflexivity); assumption
end. 

Lemma in_split_app_fst: forall (A: Type) (l: list A) (x: A),
  (forall x y : A, {x = y} + {x <> y}) ->
  In x l ->
  exists l1 l2, l = l1 ++ (x :: l2) /\ forall y, In y l1 -> y <> x.
Proof.
  intros. induction l.
  - inversion H.
  - destruct (X x a). subst. exists nil. exists l. split. reflexivity. intros. inversion H0.
    simpl in H. destruct H. subst. contradiction.  apply IHl in H. destruct_all.
    exists (a :: x0). exists x1. split. rewrite H. reflexivity. intros. intro. subst.
    simpl in H1. destruct H1. subst. contradiction. apply H0 in H. contradiction.
Qed.

Lemma no_no_dup: forall (A: Type) (l: list A),
  (forall x y : A, {x = y} + {x <> y}) ->
  ~(NoDup l) <-> (exists w l1 l2 l3, l = l1 ++ w :: l2 ++ w :: l3).
Proof.
  intros. split; intros.
  - induction l.
    + assert (@NoDup A nil). constructor. contradiction.
    + destruct (NoDup_dec X l).
      * assert (In a l). destruct (In_dec X a l). apply i.
        assert (NoDup (a :: l)). constructor. apply n0. apply n. contradiction.
        apply in_split_app_fst in H0. destruct_all. exists a. exists nil. exists x. exists x0.
        rewrite H0. reflexivity. apply X.
      * apply IHl in n. destruct_all. exists x. exists (a :: x0). exists x1. exists x2. rewrite H0.
        reflexivity.
  -  intro. destruct_all.  subst. induction x0; simpl in *.
    + rewrite NoDup_cons_iff in H0. destruct_all. apply H.
    solve_in.
    + simpl in H0. rewrite NoDup_cons_iff in H0. destruct_all. apply IHx0. apply H0.
Qed.


(*
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
*)
(* Inductive relation*)
Section Ind.

Context {a : Type} {b : Type} { gr : Type -> Type -> Type} {Hgraph : Graph.Graph gr} {Hlaw : Graph.LawfulGraph gr}.

Section Lex.

(*Well formed lexicographic measure - maybe put in own section*)
Definition natNodes (g : gr a b) := (BinInt.Z.abs_nat(Graph.noNodes g)).

Definition natNodes_lt x y := natNodes x < natNodes y.
Definition natNodes_eq x y := natNodes x = natNodes y.
Definition list_length_lt {a} (x y : list a) := length x < length y.
Definition queue_length_lt  {a} (x y : Queue a) := list_length_lt (toList _ x) (toList _ y).

Definition bf_measure_list (a: Type) := 
  transp (lex (transp natNodes_lt) natNodes_eq (transp  (@list_length_lt a))).

Definition bf_measure_queue (a: Type) :=
  transp (lex (transp natNodes_lt) natNodes_eq (transp (@queue_length_lt a))).

Definition f_nat_lt {a} (f: a -> nat) x y := f x < f y.

Lemma f_nat_lt_acc: forall {a} (f: a -> nat) x n, f x <= n -> Acc (f_nat_lt f) x.
Proof.
  intros. generalize dependent x. induction n; auto.
  - intros. apply Acc_intro. intros. unfold f_nat_lt in *. omega.
  - unfold f_nat_lt in *. intros. apply Acc_intro. intros. apply IHn. omega.
Qed.

Lemma f_nat_lt_wf: forall {a} (f: a -> nat), well_founded (f_nat_lt f).
Proof.
  red. intro. intro. intro. eapply f_nat_lt_acc. eauto.
Qed.


Lemma wf_bf_measure_list : forall a,  WF (transp (bf_measure_list a)).
Proof.
  intros. eapply WF_lex.
  - apply wf_transp_WF. unfold transp. 
    pose proof (f_nat_lt_wf (natNodes)). unfold f_nat_lt in H. unfold natNodes_lt. apply H.
  - apply wf_transp_WF. unfold transp.
    pose proof (f_nat_lt_wf (@length a0)). unfold f_nat_lt in H. unfold natNodes_lt. apply H.
  - unfold Transitive. intros. unfold natNodes_eq in *. omega.
  - unfold inclusion. unfold RelUtil.compose. intros.
    unfold transp in *. unfold natNodes_lt in *. unfold natNodes_eq in *. destruct H. omega.
Qed.

Lemma well_founded_bf_measure_list: forall a, well_founded (bf_measure_list a).
Proof. 
  intros.
  apply WF_transp_wf. apply wf_bf_measure_list.
Qed.

Lemma wf_bf_measure_queue : forall a, WF (transp (bf_measure_queue a)).
Proof.
  intros.
  eapply WF_lex.
  - apply wf_transp_WF. unfold transp. 
    pose proof (f_nat_lt_wf (natNodes)). unfold f_nat_lt in H. unfold natNodes_lt. apply H.
  - apply wf_transp_WF. unfold transp.
    pose proof (f_nat_lt_wf (fun x => length (toList a0 x))). unfold f_nat_lt in H. unfold queue_length_lt.
    unfold list_length_lt. apply H.
  - unfold Transitive. intros. unfold natNodes_eq in *. omega.
  - unfold inclusion. unfold RelUtil.compose. intros.
    unfold transp in *. unfold natNodes_lt in *. unfold natNodes_eq in *. destruct H. omega.
Qed.

Lemma well_founded_bf_measure_queue: forall a, well_founded (bf_measure_queue a).
Proof.
  intros.
  apply WF_transp_wf. apply wf_bf_measure_queue.
Qed.




End Lex.

Definition state : Type := (gr a b) * (list (Node * Num.Int)) * (list (Node * Num.Int)) * nat * (M.t nat).
  

Definition get_graph (s: state) :=
  match s with
  | (g, _, _, _, _) => g
  end.

Definition get_queue (s: state) :=
  match s with
  | (_, q, _, _, _) => q
end.

Definition get_dists (s: state) :=
  match s with
  | (_, _, d, _, _) => d
  end.

Definition get_time (s: state) :=
  match s with
  | (_, _, _, t, _) => t
  end.

Definition get_times (s: state) :=
  match s with
  |(_, _, _, _, t) => t
  end.

Definition vertex_in (g: gr a b) (v: Graph.Node) : bool :=
  match (Graph.match_ v g) with | (None, _) => false | _ => true end.

Inductive bfs_step : state -> state -> Prop :=
  | bfs_find: forall g d n t v j vs c g',
      isEmpty g = false ->
      match_ v g = (Some c, g') ->
      bfs_step (g, (v, j) :: vs, d, n, t) (g', (vs ++ suci c (Num.op_zp__ j (Num.fromInteger 1))),
        d ++ (v,j) :: nil, n + 1, (M.add v (n+1) t))
  | bfs_skip: forall g d n t v j vs g',
      isEmpty g = false ->
      match_ v g = (None, g') ->
      bfs_step (g, (v, j) :: vs, d, n, t) (g', vs, d, n, t).

Definition start (g : gr a b) (v: Graph.Node) : state := (g, ((v, Num.fromInteger 0) :: nil), nil, 0, @M.empty nat).

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

Definition done (s: state) := null (get_queue s) || isEmpty (get_graph s).

(*Proof of correctness of bfs. Later, we prove equivalence between this inductive formulation and leveln,
  allowing us to prove the correctness of this instead*)
Section Correctness.

(*Lots of stuff about paths here - TODO: move to separate file*)
Section Path.

(*Inductive and Fixpoint definitions for a path between two vertices. The Fixpoint instance proves that this is
  decidable, and we prove their equivalence*)
Inductive path : (gr a b) -> Node -> Node -> (list Node) -> Prop :=
  | p_start: forall g u v, eIn g u v = true -> path g u v nil
  | p_step: forall g u v w l, 
     path g u w l ->
     eIn g w v = true ->
     path g u v (w :: l) .

Fixpoint path_list (g: gr a b) (u v: Node) (l: list Node) : bool :=
  match l with
  | nil => eIn g u v
  | x :: tl => eIn g x v && path_list g u x tl
  end.

Lemma path_list_equiv: forall g u v l,
  path g u v l <-> path_list g u v l = true.
Proof.
  intros. split; intros.
  - induction H.
    + simpl. assumption.
    + simpl. rewrite andb_true_iff. split; assumption.
  - generalize dependent v. induction l; intros; simpl.
    + apply p_start. simpl in H. assumption.
    + simpl in *. rewrite andb_true_iff in H. destruct H. apply p_step. apply IHl. assumption.
      assumption.
Qed.

(*Some useful results about [path]*)
Lemma path_app: forall g u v a l1 l2,
  path_list g u v (l1 ++ a :: l2) = true <->
  path_list g a v l1 = true /\ path_list g u a l2 = true.
Proof.
  intros. split; intros. generalize dependent v. generalize dependent l2. induction l1; intros.
  - simpl in H. simpl. rewrite andb_true_iff in H. apply H.
  - simpl in *. simplify'; apply IHl1 in H1; destruct H1; assumption.
  - destruct_all. generalize dependent v. generalize dependent a0. revert l2. induction l1; intros; simpl in *;
    simplify'.
Qed.

Lemma path_remove_cycle: forall g u v w l1 l2 l3,
  path_list g u v (l1 ++ w :: l2 ++ w :: l3) = true ->
  path_list g u v (l1 ++ w :: l3) = true.
Proof.
  intros. apply path_app in H. destruct_all. apply path_app in H0. destruct_all.
  apply path_app. simplify'.
Qed.

(*If there is a path, then there is a path with no duplicates*)
Lemma path_no_dups: forall g u v l,
  path_list g u v l = true ->
  exists l1, path_list g u v l1 = true /\ NoDup l1 /\ ~In u l1 /\  ~In v l1 /\ 
  (forall x, In x l1 -> In x l). 
  Proof.
    intros. induction l using (well_founded_induction
                       (wf_inverse_image _ nat _ (@length _)
                          PeanoNat.Nat.lt_wf_0)).
    destruct (NoDup_dec (N.eq_dec) l).
    - destruct (In_dec N.eq_dec u l).
      + eapply in_split_app_fst in i. destruct_all. clear H2. subst.
        apply path_app in H. destruct H. specialize (H0 x). destruct H0 as [l]. 
        rewrite app_length. simpl. assert (forall n m, n < n + S(m)) by (intros; omega). apply H0.
        apply H. exists l. simplify'. apply N.eq_dec.
      + destruct (In_dec N.eq_dec v l).
        * eapply in_split_app_fst in i. destruct_all; subst. clear H2. apply path_app in H.
          destruct H. specialize (H0 x0). destruct H0 as [l]. rewrite app_length. simpl.
          assert (forall n m, n < m + S(n)) by (intros; omega). apply H0. apply H1. exists l.
          simplify'. apply N.eq_dec.
        * exists l. simplify'.
    - rewrite no_no_dup in n. destruct_all. subst. 
      apply path_remove_cycle in H. specialize (H0 (x0 ++ x :: x2)). destruct H0 as [l].
      repeat(rewrite app_length; simpl). omega. apply H. exists l. simplify'. apply H5 in H4.
      apply in_app_or in H4. destruct H4. apply in_or_app. left. apply H4. simpl in H4.
      destruct H4. subst. solve_in. solve_in. apply N.eq_dec.
Qed.

Lemma path_implies_in_graph: forall g u v l,
  path_list g u v l = true ->
  vIn g u = true /\ vIn g v = true /\ (forall x, In x l -> vIn g x = true).
Proof.
  intros. generalize dependent v. induction l; intros; simpl in H.
  - apply edges_valid in H. simplify'.
  - rewrite andb_true_iff in H. destruct H. apply IHl in H0. apply edges_valid in H. crush.
Qed. 


(*We want a function to get the distance between two nodes. This is a horribly inefficient function to help do this*)
(*A terrible function to find if a path of length <= n between two vertices exists*)
Fixpoint path_of_length (g: gr a b) (u v : Node) (n: nat) {struct n} : bool :=
  match n with
  | 0 => eIn g u v
  | S(m) => if eIn g u v then true else
  fold_right (fun x t => if path_of_length g u x m && eIn g x v then true else t) false 
  (nodeList g)
  end.

Lemma path_of_length_implies_path: forall g u v n,
  path_of_length g u v n = true -> exists l, path_list g u v l = true /\ length l <= n.
Proof.
  intros. generalize dependent v. induction n; intros.
  - simpl in H. exists nil. split. simpl. assumption. simpl. omega.
  - simpl in H. destruct (eIn g u v) eqn : ?.
    exists nil. split. simpl. assumption. simpl. omega.
    assert (forall l, fold_right
      (fun (x : Node) (t : bool) => if path_of_length g u x n && eIn g x v then true else t) false
      l = true-> exists x, In x l /\ path_of_length g u x n = true /\ eIn g x v = true). {
      intros. induction l; simpl in *.
      * inversion H0.
      * destruct (path_of_length g u a0 n && eIn g a0 v) eqn : ?.
        -- exists a0. split. left. reflexivity. rewrite andb_true_iff in Heqb1. apply Heqb1.
        -- apply IHl in H0. destruct H0. exists x. destruct H0. split. right. assumption.
           apply H1. } 
      apply H0 in H. clear H0. destruct H. destruct H. destruct H0. apply IHn in H0.
      destruct H0. destruct H0. exists (x :: x0). split. simpl. rewrite andb_true_iff. crush. simpl. omega.
Qed.

Lemma path_of_size_implies_function: forall g u v l n,
  length l <= n ->
  path_list g u v l = true -> path_of_length g u v n = true.
Proof.
  intros. generalize dependent v. revert u. generalize dependent n. induction l; simpl in *; intros.
  - destruct n. simpl. apply H0. simpl. rewrite H0. reflexivity.
  - simplify. destruct n. omega. assert (length l <= n) by omega. clear H.
    simpl. destruct (eIn g u v) eqn : ?. reflexivity.
      assert (forall a l', In a l' ->
      path_of_length g u a n = true ->
      eIn g a v = true ->
      fold_right
  (fun (x : Node) (t : bool) => if path_of_length g u x n && eIn g x v then true else t)
  false l' = true). { intros. induction l'; simpl in *.
  - destruct H.
  - destruct H. subst. rewrite H3. rewrite H2. simpl. reflexivity. apply IHl' in H. 
    destruct (path_of_length g u a2 n && eIn g a2 v). reflexivity. apply H. }
    apply (H a0). assert (vIn g a0 = true). { rewrite andb_true_iff in H0.
    destruct H0. apply edges_valid in H0. apply H0. } unfold vIn in H2.
    unfold mem in H2. destruct (in_dec N.eq_dec a0 (nodeList g)) eqn : ?. assumption.
    rewrite Heqs in H2. inversion H2. apply IHl. apply H1. simplify'. simplify'.
Qed.

(*If there is a path, then there is a path at most as large as the number of vertices in the graph (because
  there is a path with no duplicates and every vertex is in the graph*)
Lemma path_shorter_than_graph_size: forall g u v l,
  path_list g u v l = true ->
  exists l', path_list g u v l' = true /\ length l' <= length(nodeList g).
Proof.
  intros. apply path_no_dups in H. destruct_all. 
  assert (forall a, In a x -> In a (nodeList g)). intros.
  apply path_implies_in_graph in H. destruct_all. apply H6 in H4. unfold vIn in H4.
  unfold mem in H4. destruct (in_dec N.eq_dec a0 (nodeList g)) eqn : ?. assumption.
  rewrite Heqs in H4. inversion H4. 
  exists x. split. apply H. eapply NoDup_incl_length. apply H0. unfold incl. apply H4.
Qed.

(*By the above lemma, we can simply define distance by repeatedly checking if there is a list with 
  the given distance*)
Definition distance (g: gr a b) (u v : Node) : option nat :=
  fold_right (fun x acc => if path_of_length g u v x then Some x else acc) None (seq 0 (natNodes g + 1)).

Lemma distance_none: forall g u v,
  distance g u v = None <-> (forall l, path_list g u v l = false).
Proof.
  intros.  assert (A: forall l, fold_right (fun (x : nat) (acc : option nat) => 
    if path_of_length g u v x then Some x else acc) None l = None <->
    (forall x, In x l -> path_of_length g u v x = false)). { intros. split; intros; induction l; simpl in *.
    destruct H0. destruct H0. subst. destruct (path_of_length g u v x) eqn : ?. inversion H.
    reflexivity. apply IHl. destruct (path_of_length g u v a0) eqn : ?. inversion H.
    apply H. assumption. reflexivity. destruct (path_of_length g u v a0) eqn : ?.
    specialize (H a0). rewrite H in Heqb0. inversion Heqb0. left. reflexivity.
    apply IHl. intros. apply H. right. assumption. } 
     split; intros.
  - unfold distance in H. 
    assert (forall x, In x (seq 0 (natNodes g + 1)) -> path_of_length g u v x = false). { intros.
    eapply A. apply H. assumption. } clear H. clear A.
    destruct (path_list g u v l) eqn : P.
    + apply path_shorter_than_graph_size in P. destruct P. destruct H.
      assert (path_of_length g u v (length x) = true). eapply path_of_size_implies_function.
      reflexivity. assumption. 
      assert (In (length x) (seq 0 (natNodes g + 1))). apply in_seq. split. omega. simpl.
      assert (length (nodeList g) = natNodes g). unfold natNodes. rewrite noNodes_def. 
      unfold nodeList. unfold ulabNodes. apply map_length. omega. 
      apply H0 in H3. rewrite H3 in H2. inversion H2.
    + reflexivity.
  - unfold distance. apply A. intros. destruct (path_of_length g u v x) eqn : ?.
    + apply path_of_length_implies_path in Heqb0. destruct Heqb0. destruct H1. rewrite H in H1.
      inversion H1.
    + reflexivity.
Qed.

Lemma seq_pred: forall start len h t n l,
  seq start len = (h :: t) ++ S n :: l ->
  In n (h :: t).
Proof.
  intros. generalize dependent h. revert t. revert start0. induction len; intros.
  - simpl. simpl in H. inversion H.
  - simpl in H. inversion H. subst. destruct t.
    simpl in H2. simpl. destruct len. simpl in H2. inversion H2. simpl in H2. inversion H2. subst. left. reflexivity.
    apply IHlen in H2. solve_in.
Qed.

Lemma seq_split: forall start len l1 x l2,
  seq start len = l1 ++ x :: l2 ->
  (forall y, In y l1 -> y < x) /\ (forall y, In y l2 -> y > x).
Proof.
  intros. generalize dependent start0. revert l1. revert x. revert l2. induction len; intros; simpl in H.
  - assert (l1 = nil). destruct l1; inversion H. subst.
    simpl in H. inversion H.
  - destruct l1. simpl in H. inversion H. destruct l2.
     split; intros. destruct H0. rewrite H2 in H0. destruct H0.
     specialize (IHlen l2 n nil (S(start0))). subst. simpl in IHlen. apply IHlen in H2.
     split; intros. destruct H0. rewrite in_seq in H0. omega.
     inversion H; subst. specialize (IHlen l2 x l1 (S(n)) H2). split; intros. simpl in H0.
     destruct H0. subst. assert (In x (seq (S(y)) len)). rewrite H2. solve_in. rewrite in_seq in H0.
      omega. destruct IHlen. apply H1. assumption. apply IHlen. apply H0.
Qed.

(*This actually computes the shortest path*)
Lemma distance_some: forall g u v n,
  distance g u v = Some n <->
  (exists l, path g u v l /\ length l = n) /\ (forall l, length l < n -> path_list g u v l = false).
Proof.
  intros. unfold distance.
  assert (forall l, 
  fold_right (fun (x : nat) (acc : option nat) => if path_of_length g u v x then Some x else acc) None
  l = Some n <-> (exists l1 l2, l = l1 ++ n :: l2 /\ (forall y, In y l1 -> path_of_length g u v y = false) /\
  path_of_length g u v n = true)). { intros. induction l; split; intros; simpl in *.
  - inversion H.
  - destruct_all. destruct x; inversion H.
  - destruct (path_of_length g u v a0) eqn : ?.
    + inversion H; subst. exists nil. exists l. split. simpl. reflexivity. split; intros.
      destruct H0. assumption.
    + apply IHl in H. destruct H. exists (a0 :: x). destruct_all.
      exists x0. split. rewrite H. simpl. reflexivity.
      split; intros. simpl in H2. destruct H2. subst. assumption. apply H0. assumption.
      assumption.
  - destruct_all. destruct (path_of_length g u v a0) eqn : ?. destruct x.
    + inversion H; subst. reflexivity.
    + simpl in H0. inversion H; subst. specialize (H0 n0). rewrite H0 in Heqb0. inversion Heqb0.
      left. reflexivity.
    + destruct x. inversion H; subst. rewrite Heqb0 in H1. inversion H1.
      inversion H; subst. apply IHl. exists x. exists x0. simplify'. }
  rewrite H. clear H. split; intros; destruct_all.
  - apply path_of_length_implies_path in H1. split. setoid_rewrite path_list_equiv. 
    destruct  H1. destruct H1. assert (length x1 = n \/ length x1 < n) by omega. destruct H3.
    exists x1. split. assumption. assumption. 
    destruct x. simpl in H. assert (natNodes g + 1 = S(natNodes g)) by omega. rewrite H4 in H.
    simpl in H. inversion H; subst. omega. 
    destruct n. omega. assert (length x1 <= n) by omega. 
    apply (path_of_size_implies_function _ _ _ _ _ H4) in H1.
    rewrite H0 in H1. inversion H1. apply seq_pred in H. apply H.
    intros. assert (In (length l) (seq 0 (natNodes g + 1))). { rewrite in_seq.
    assert (In n (seq 0 (natNodes g + 1))). rewrite H. solve_in. rewrite in_seq in H3.
    omega. } rewrite H in H3. apply seq_split in H.
    destruct H. apply in_app_or in H3. destruct H3. 
    destruct (path_list g u v l) eqn : ?. eapply path_of_size_implies_function in Heqb0.
    rewrite (H0 (length l)) in Heqb0. inversion Heqb0.
    assumption. omega. reflexivity. simpl in H3. destruct H3. omega.
    apply H4 in H3. omega.
  - assert (n <= (natNodes g)). { assert (n <= natNodes g \/ n > natNodes g) by omega. destruct H2.
    assumption. rewrite path_list_equiv in H. apply path_shorter_than_graph_size in H.
    destruct H. destruct H. rewrite H0 in H. inversion H. unfold nodeList in H3.
    unfold ulabNodes in H3. rewrite map_length in H3. rewrite <- noNodes_def in H3.
    unfold natNodes in H2. omega. }
    pose proof (in_split_app_fst _ (seq 0 (natNodes g + 1)) n Nat.eq_dec).
    assert (In n (seq 0 (natNodes g + 1))). rewrite in_seq. omega.
    apply H3 in H4. clear H3. destruct_all. exists x0. exists x1. split. assumption.
    apply seq_split in H3. split; intros.
    destruct H3. destruct (path_of_length g u v y) eqn : ?.
    apply path_of_length_implies_path in Heqb0. destruct Heqb0.
    destruct H7. rewrite H0 in H7. inversion H7. apply H3 in H5. omega. reflexivity.
    eapply path_of_size_implies_function. assert (length x <= n) by omega. apply H5.
    rewrite <- path_list_equiv. assumption.
Qed. 


(*Next step lemma 22.1 of CLRS*)

End Path.

End Correctness.

Section Equiv.

Instance need_this_for_equations : WellFounded (bf_measure_list (Node * Num.Int)).
Proof.
  unfold WellFounded. apply well_founded_bf_measure_list.
Defined.

Lemma match_none_size: forall g v g',
  match_ v g = (None, g') -> natNodes g = natNodes g'.
Proof.
  intros. pose proof (match_remain_none g). erewrite H0. reflexivity. apply H.
Qed.  

Equations bfs_tail (s: state) : state by wf (get_graph s, get_queue s) (bf_measure_list (Node * Num.Int)) :=
  bfs_tail (g, nil, x, y, z) => (g, nil, x, y, z);
  bfs_tail (g, (v, j) :: vs, d, n, t) => if (isEmpty g) then  (g, (v, j) :: vs, d, n, t) else
      match (match_ v g) as y return ((match_ v g = y) -> _) with
      | (Some c, g') => fun H: (match_ v g) = (Some c, g') => 
        bfs_tail (g', (vs ++ suci c (Num.op_zp__ j (Num.fromInteger 1))), d ++ (v,j) :: nil, n + 1, M.add v (n+1) t)
      | (None, g') => fun H: (match_ v g) = (None, g') => bfs_tail (g', vs, d, n, t)
      end (eq_refl).
Next Obligation.
unfold bf_measure_list. unfold transp. apply lex1. unfold natNodes_lt. eapply match_decr_size. symmetry. apply H.
Defined.
Next Obligation.
unfold bf_measure_list. unfold transp. apply lex2. unfold natNodes_eq. eapply match_none_size. apply H. unfold list_length_lt.
simpl. omega.
Defined.

Definition expand_bfs_tail := 
fun s : gr a b * list (Node * Num.Int) * list (Node * Num.Int) * nat * M.t nat =>
let (p, t) := s in
(let (p0, n) := p in
 fun t0 : M.t nat =>
 (let (p1, l) := p0 in
  fun (n0 : nat) (t1 : M.t nat) =>
  (let (g, l0) := p1 in
   fun (l1 : list (Node * Num.Int)) (n1 : nat) (t2 : M.t nat) =>
   match l0 with
   | nil => fun (l2 : list (Node * Num.Int)) (n2 : nat) (t3 : M.t nat) => (g, nil, l2, n2, t3)
   | p2 :: l2 =>
       fun (l3 : list (Node * Num.Int)) (n2 : nat) (t3 : M.t nat) =>
       (let (n3, i) := p2 in
        fun (l4 l5 : list (Node * Num.Int)) (n4 : nat) (t4 : M.t nat) =>
        if isEmpty g
        then (g, (n3, i) :: l4, l5, n4, t4)
        else
         (let
            (m, g') as y
             return (match_ n3 g = y -> gr a b * list (Node * Num.Int) * list (Node * Num.Int) * nat * M.t nat) :=
            match_ n3 g in
          match
            m as m0
            return
              (match_ n3 g = (m0, g') -> gr a b * list (Node * Num.Int) * list (Node * Num.Int) * nat * M.t nat)
          with
          | Some c =>
              fun _ : match_ n3 g = (Some c, g') =>
              bfs_tail
                (g', l4 ++ suci c (Num.op_zp__ i (Num.fromInteger 1)), l5 ++ (n3, i) :: nil, 
                n4 + 1, M.add n3 (n4 + 1) t4)
          | None => fun _ : match_ n3 g = (None, g') => bfs_tail (g', l4, l5, n4, t4)
          end) eq_refl) l2 l3 n2 t3
   end l1 n1 t2) l n0 t1) n t0) t.

Lemma unfold_bfs_tail: forall s,
  bfs_tail s = expand_bfs_tail s.
Proof.
  intros. unfold expand_bfs_tail. apply bfs_tail_elim; intros; reflexivity.
Qed.

(*Want to prove this is valid, done and equivalent to other*)
Lemma bfs_tail_multi: forall s,
  bfs_multi s (bfs_tail s).
Proof.
  intros. destruct s as [r t]. destruct r as [r n]. destruct r as [r d].
  generalize dependent d. revert n. revert t. 
   induction (r) using (well_founded_induction (well_founded_bf_measure_list (Node * Num.Int))).
  intros.
  destruct r as [g q]. rewrite unfold_bfs_tail. simpl. destruct q eqn : Q.
  - apply multi_refl.
  - destruct p as [v j]. destruct (isEmpty g) eqn : E.
    + apply multi_refl.
    + destruct (match_ v g) eqn : M. destruct m eqn : M'.
      *  eapply multi_step. apply bfs_find. assumption. apply M. apply H. unfold bf_measure_list.
         unfold transp. apply lex1. unfold natNodes_lt. eapply match_decr_size. symmetry. apply M.
      * eapply multi_step. apply bfs_skip. assumption. apply M. apply H. unfold bf_measure_list.
        unfold transp. apply lex2. unfold natNodes_eq. eapply match_none_size; eassumption.
        unfold list_length_lt. simpl. omega.
Qed.  

Lemma bfs_tail_done: forall s,
  done (bfs_tail s) = true.
Proof.
  intros. unfold done. destruct s as [r t]. destruct r as [r n]. destruct r as [r d].
  generalize dependent d. revert n. revert t. 
   induction (r) using (well_founded_induction (well_founded_bf_measure_list (Node * Num.Int))).
  intros.
  destruct r as [g q]. rewrite unfold_bfs_tail. simpl. destruct q eqn : Q.
  - simpl. reflexivity.
  - destruct p. simpl. destruct (isEmpty g) eqn : G. simpl. assumption.
    destruct (match_ n0 g) eqn : M. destruct m; simpl.
    apply H. unfold bf_measure_list. unfold transp. apply lex1. unfold natNodes_lt. eapply match_decr_size;
    symmetry; eassumption. apply H. unfold bf_measure_list. unfold transp. apply lex2.
    unfold natNodes_eq. eapply match_none_size. eassumption. unfold list_length_lt. simpl. omega.
Qed. 

(*Equivalence of 2 versions - TODO: prove leveln and leveln' equivalent (proof is basically what I did before*)
Equations leveln' (x: (gr a b) * (list (Node * Num.Int))) : list (Node * Num.Int) by wf x (bf_measure_list (Node * Num.Int)) :=
  leveln' (g, nil) := nil;
  leveln' (g, (v,j) :: vs) := if (isEmpty g) then nil else
                                match (match_ v g) as y return ((match_ v g = y) -> _ ) with
                                | (Some c, g') => fun H : (match_ v g) = (Some c, g') => (v,j) :: leveln' (g', (vs ++ suci c (Num.op_zp__ j (Num.fromInteger 1))))
                                | (None, g') => fun H: (match_ v g) = (None, g') => leveln' (g', vs)
                                 end (eq_refl).
Next Obligation.
unfold bf_measure_list. unfold transp. apply lex1. unfold natNodes_lt. eapply match_decr_size. symmetry. apply H.
Defined.
Next Obligation.
unfold bf_measure_list. unfold transp. apply lex2. unfold natNodes_eq. eapply match_none_size. apply H. unfold list_length_lt.
simpl. omega.
Defined.

Definition expand_leveln' := 
fun x : gr a b * list (Node * Num.Int) =>
let (g, l) := x in
match l with
| nil => nil
| p :: l0 =>
    (let (n, i) := p in
     fun l1 : list (Node * Num.Int) =>
     if isEmpty g
     then nil
     else
      (let (m, g') as y return (match_ n g = y -> list (Node * Num.Int)) := match_ n g in
       match m as m0 return (match_ n g = (m0, g') -> list (Node * Num.Int)) with
       | Some c =>
           fun _ : match_ n g = (Some c, g') =>
           (n, i) :: leveln' (g', l1 ++ suci c (Num.op_zp__ i (Num.fromInteger 1)))
       | None => fun _ : match_ n g = (None, g') => leveln' (g', l1)
       end) eq_refl) l0
end.

Lemma unfold_leveln': forall x,
  leveln' x = expand_leveln' x.
Proof.
  intros. unfold expand_leveln'. apply leveln'_elim. reflexivity. reflexivity.
Qed.

Lemma leveln_tail_equiv: forall x l n t,
  get_dists (bfs_tail (x, l, n, t)) = l ++ leveln' x.
Proof.
  intros x. 
  induction (x) using (well_founded_induction (well_founded_bf_measure_list (Node * Num.Int))).
  intros. rewrite unfold_leveln'. rewrite unfold_bfs_tail. simpl. unfold expand_leveln'.
  destruct x as [g q]. simpl. destruct q eqn : Q.
  - simpl. rewrite app_nil_r. reflexivity.
  - destruct p as [v j]. destruct (isEmpty g) eqn : G. 
    + simpl. rewrite app_nil_r. reflexivity.
    + destruct (match_ v g) eqn : M. destruct m.
      * remember (g0, l0 ++ suci c (j + 1)%Z) as x. rewrite H. rewrite <- app_assoc. simpl.
        reflexivity. unfold bf_measure_list.  unfold transp. simpl. destruct x. apply lex1.
        unfold natNodes_lt. eapply match_decr_size. symmetry. inversion Heqx; subst. apply M.
      * rewrite H. reflexivity. unfold bf_measure_list. unfold transp. apply lex2.
        unfold natNodes_eq. eapply match_none_size. apply M. unfold list_length_lt. simpl. omega.
Qed. 

(*Need to wait until I prove equivalence of leveln and leveln', but easy from there*)
Theorem level_tail_equiv: forall v g,
  get_dists (bfs_tail (start g v)) = level v g.
Proof.
Abort.

End Equiv.

(*BFS with paths - come back to this*)

Section WithPath.

Instance also_need_this_for_equations : WellFounded (bf_measure_list (Path)).
Proof.
  unfold WellFounded. apply well_founded_bf_measure_list.
Defined.

Equations bf_list (x : (gr a b) * (list Path)) : RootPath.RTree by wf x (bf_measure_list Path) :=
  bf_list (g, nil) := nil;
  bf_list (g, (nil :: q')) := if (isEmpty g) then nil else GHC.Err.patternFailure;
  bf_list (g, ((v :: t) :: q')) := let p:= v :: t in  if (isEmpty g) then nil else
      match (match_ v g) as y return ((match_ v g = y) -> _) with
                        | (Some c, g') => fun H : (match_ v g) = (Some c, g') => p :: (bf_list (g', (q' ++ map (fun x => x :: p)  (suc' c))))
                        | (None, g') => fun H : (match_ v g) = (None, g') => ( bf_list (g', q'))
                        end (eq_refl)

  
.
Next Obligation.
unfold bf_measure_list. unfold transp. apply lex1. unfold natNodes_lt. eapply match_decr_size. symmetry. apply H.
Defined.
Next Obligation.
unfold bf_measure_list. unfold transp. apply lex2. unfold natNodes_eq. eapply match_none_size. apply H.
unfold list_length_lt. simpl. omega.
Defined.




(*NOTE: need to resolve this, working with this for now bc of issue with lazy evaluation vs strict*)
(*TODO: Add to midable before I resolve the issue with hs-toc-qo*)
(*only difference is that we check if the queue is empty BEFORE calling queueGet*)
(*
Definition bf_strict : Queue Path -> gr a b -> RootPath.RTree :=
deferredFix2
  (fun (bf : Queue Path -> gr a b -> list Path) (q : Queue Path) (g : gr a b) =>
   if queueEmpty q || isEmpty g : bool
       then nil else 
   let (p, q') := queueGet q in
   match p with
   | nil => patternFailure
   | v :: _ =>
        let (m, g') := match_ v g in
        match m with
        | Some c => p :: bf (queuePutList (Base.map (fun arg_2__ : Node => arg_2__ :: p) (suc' c)) q') g'
        | None => bf q' g'
        end
   end).
*)

(*TODO: NOTE: I changed the order ot the arguments to make the proofs MUCH easier (lex requires that
  graph comes first, and I can use the same well-founded proof for both*)
(*
Definition flip {a} {b} (x: a * b) : b * a :=
  match x with
  | (y, z) => (z, y)
  end.

Lemma wf_flip: forall {a b : Type} (f: (a * b) -> (a * b) -> Prop),
  well_founded f -> well_founded (fun x y => f (flip x) (flip y)).
Proof.
  intros. unfold well_founded in *. intros. 
  apply Acc_intro. intros. specialize (H (flip y) (flip a1)). specialize (H (flip y)).
*)

Definition bf_strict' :  gr a b -> Queue Path -> RootPath.RTree :=
deferredFix2
  (fun (bf : gr a b ->  Queue Path ->  list Path)  (g : gr a b) (q : Queue Path) =>
   if queueEmpty q || isEmpty g : bool
       then nil else 
   let (p, q') := queueGet q in
   match p with
   | nil => patternFailure
   | v :: _ =>
        let (m, g') := match_ v g in
        match m with
        | Some c => p :: bf g' (queuePutList (Base.map (fun arg_2__ : Node => arg_2__ :: p) (suc' c)) q')
        | None => bf g' q'
        end
   end).


(*test*)
Definition bf_list_unfold' := 
fun x : gr a b * list Path =>
let (g, l) := x in
match l with
| nil => nil
| p :: l0 =>
    match p with
    | nil => fun _ : list Path => if isEmpty g then nil else patternFailure
    | n :: l1 =>
        fun l2 : list Path =>
        if isEmpty g
        then nil
        else
         (let (m, g') as y return (match_ n g = y -> list (list Node)) := match_ n g in
          match m as m0 return (match_ n g = (m0, g') -> list (list Node)) with
          | Some c =>
              fun _ : match_ n g = (Some c, g') =>
              (n :: l1) :: bf_list (g', l2 ++ map (fun x0 : Node => x0 :: n :: l1) (suc' c))
          | None => fun _ : match_ n g = (None, g') => bf_list (g', l2)
          end) eq_refl
    end l0
end.

Lemma bf_list_unfold'_equiv: forall x,
  bf_list_unfold' x = bf_list x.
Proof.
  intros. unfold bf_list_unfold'. apply bf_list_elim; try(reflexivity).
Qed.

Lemma bf_list_equiv: forall (x: (gr a b) * (Queue Path)), 
  bf_strict'  (fst x) (snd x) = bf_list ((fst x), (toList _ (snd x))).
Proof.
  intros. unfold bf_strict'. rewrite <- bf_list_unfold'_equiv. simpl.
  induction (x) as [y IH] using (well_founded_induction (well_founded_bf_measure_queue (Path))). 
  destruct y as [g q]. simpl. unfold deferredFix2 in *. unfold curry in *.
  rewrite (deferredFix_eq_on _ (fun x => True) ( (bf_measure_queue (Path)) )).
  - simpl. destruct (toList _ q) eqn : Q.  
    + simpl. assert (queueEmpty q = true). rewrite toList_queueEmpty. assumption. rewrite H.
      simpl. reflexivity.
    + simpl. assert (queueEmpty q = false). destruct (queueEmpty q) eqn : ?. rewrite toList_queueEmpty in Heqb0.
      rewrite Heqb0 in Q. inversion Q. reflexivity. rewrite H. simpl.
      destruct (isEmpty g) eqn : GE. destruct p; reflexivity.
      destruct (queueGet q) eqn : QG.
      pose proof (toList_queueGet _ _ _ _ Q). rewrite QG in H0. simpl in H0. destruct H0; subst.
      destruct p. reflexivity. destruct (match_ n g) eqn : M. destruct m.
      * specialize (IH (g0, 
        queuePutList (Base.map (fun arg_2__ : Node => arg_2__ :: n :: p) (suc' c)) q0)). simpl in IH.
        rewrite IH. simpl. rewrite <- bf_list_unfold'_equiv. simpl.
        rewrite toList_queuePutList. reflexivity.
        unfold bf_measure_queue. unfold transp. apply lex1. unfold natNodes_lt. eapply match_decr_size.
        symmetry. apply M.
      * specialize (IH (g0, q0)). rewrite IH. simpl. rewrite <- bf_list_unfold'_equiv. simpl.
        reflexivity. unfold bf_measure_queue. unfold transp. apply lex2. unfold natNodes_eq.
        eapply match_none_size. apply M. unfold queue_length_lt. unfold list_length_lt.
        rewrite Q. simpl. omega.
  -  eapply well_founded_bf_measure_queue.
  - unfold recurses_on. intros. unfold uncurry. destruct x. destruct (queueEmpty q0) eqn : ?.
    reflexivity. destruct (isEmpty g1) eqn : ?. reflexivity. simpl. destruct (queueGet q0) eqn : ?.
    destruct p. reflexivity. destruct (match_ n g1) eqn : ?. destruct m.
    rewrite H0. reflexivity. apply I. unfold bf_measure_queue. unfold transp. apply lex1.
    unfold natNodes_lt. eapply match_decr_size. symmetry. apply Heqd. apply H0. apply I.
    unfold bf_measure_queue. unfold transp. apply lex2. unfold natNodes_eq. eapply match_none_size.
    apply Heqd. unfold queue_length_lt. unfold list_length_lt. 
    destruct (toList Path q0) eqn : ?. rewrite <- toList_queueEmpty in Heql. rewrite Heql in Heqb0.
    inversion Heqb0. eapply toList_queueGet in Heql. rewrite Heqp in Heql. simpl in Heql. destruct Heql; subst.
    simpl. omega.
  - apply I.
Qed.

(*Finally, the result we want (mostly - TODO NEED to figure out order stuff*)
Lemma bf_list_equiv': forall (g: gr a b) (q: Queue Path),
  bf_strict' g q = bf_list (g,(toList _ q)).
Proof.
  intros. pose proof (bf_list_equiv (g, q)). simpl in H. assumption.
Qed. 

Lemma contrapositive: forall (P Q : Prop), (P -> Q) -> (~Q -> ~P).
Proof.
  tauto.
Qed. 
(*probably dont need this*)
Lemma bf_list_unroll: forall (g: gr a b) (l: list Path) n p t,
  l = (n :: p) :: t ->
  vIn g n = false ->
  bf_list (g, l) = bf_list (g, t).
Proof.
  intros. rewrite <- bf_list_unfold'_equiv at 1. simpl.
  rewrite H. destruct (isEmpty g) eqn : G.
  rewrite <- bf_list_unfold'_equiv. simpl. destruct t. reflexivity.
  destruct l0. rewrite G. reflexivity. rewrite G. reflexivity.
  destruct (match_ n g) eqn : M. destruct m.
  - pose proof (match_in g n). destruct H1. apply contrapositive in H1.
    exfalso. apply H1. exists c. exists g0. assumption. intro. rewrite H3 in H0. inversion H0.
  - pose proof (match_remain_none g n g0 M). subst. reflexivity.
Qed.

End WithPath.

(*Equivalence*)

(*Steps:
1. show we can unwrap BFS if first in queue not in graph
2. show we can unwrap to pop_list
3. equivalence of lists and queues
4. then can unwarp deferredFix and prove termination
5. need something about the paths, tail vs regular recursive*)

(*Next step: try to prove this is equivalent to Haskell BFS, then can just work with this version/ valid states*)
End Ind.