Require Import Data.Graph.Inductive.Graph.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import Helper.
Require Import Wellfounded.
Require Import Coq.Lists.ListDec.
Require Import Coq.NArith.BinNat.
Require Import Omega.
Require Import Crush.

(*Lots of stuff about paths here*)
Section Path.

Context {a : Type} {b : Type} { gr : Type -> Type -> Type} {Hgraph : Graph.Graph gr} {Hlaw : Graph.LawfulGraph gr}.

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
  - simplify'. destruct n. omega. assert (length l <= n) by omega. clear H.
    simpl. destruct (eIn g u v) eqn : ?. reflexivity.
      assert (forall a l', In a l' ->
      path_of_length g u a n = true ->
      eIn g a v = true ->
      fold_right
  (fun (x : Node) (t : bool) => if path_of_length g u x n && eIn g x v then true else t)
  false l' = true). { intros. induction l'; simpl in *.
  - destruct H.
  - destruct H. subst. rewrite H3. simpl. rewrite H4. simpl. reflexivity. apply IHl' in H. 
    destruct (path_of_length g u a2 n && eIn g a2 v). reflexivity. apply H. }
    apply (H a0). assert (vIn g a0 = true). { apply edges_valid in H1. apply H1. } unfold vIn in H3.
    unfold mem in H3. match goal with | [H: (if ?x then _ else _) = _  |- _] => destruct x eqn : ? end.
    assumption. inversion H3.  apply IHl. assumption. simplify'. simplify'.
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
  unfold mem in H4.  match goal with | [H: (if ?x then _ else _) = _  |- _] => destruct x eqn : ? end.
  assumption. inversion H4. 
  exists x. split. apply H. eapply NoDup_incl_length. apply H0. unfold incl. apply H4.
Qed.

Definition natNodes (g : gr a b) := (BinInt.Z.abs_nat(Graph.noNodes g)).

(*By the above lemma, we can simply define distance by repeatedly checking if there is a list with 
  the given distance*)
Definition distance (g: gr a b) (u v : Node) : option nat :=
  if (N.eq_dec u v) then (Some 0) else
  fold_right (fun x acc => if path_of_length g u v x then Some (x + 1) else acc) None (seq 0 (natNodes g + 1)).

Lemma distance_none: forall g u v,
  distance g u v = None <-> (forall l, path_list g u v l = false) /\ u <> v.
Proof.
  intros.  assert (A: forall l, fold_right (fun (x : nat) (acc : option nat) => 
    if path_of_length g u v x then Some (x + 1) else acc) None l = None <->
    (forall x, In x l -> path_of_length g u v x = false)). { intros. split; intros; induction l; simpl in *.
    destruct H0. destruct H0. subst. destruct (path_of_length g u v x) eqn : ?. inversion H.
    reflexivity. apply IHl. destruct (path_of_length g u v a0) eqn : ?. inversion H.
    apply H. assumption. reflexivity. destruct (path_of_length g u v a0) eqn : ?.
    specialize (H a0). rewrite H in Heqb0. inversion Heqb0. left. reflexivity.
    apply IHl. intros. apply H. right. assumption. } 
     split; intros.
  - unfold distance in H. destruct (N.eq_dec u v). inversion H. split. intros. 
    assert (forall x, In x (seq 0 (natNodes g + 1)) -> path_of_length g u v x = false). { intros.
    eapply A.  apply H. assumption. } clear H. clear A.
    destruct (path_list g u v l) eqn : P.
    + apply path_shorter_than_graph_size in P. destruct P. destruct H.
      assert (path_of_length g u v (length x) = true). eapply path_of_size_implies_function.
      reflexivity. assumption. 
      assert (In (length x) (seq 0 (natNodes g + 1))). apply in_seq. split. omega. simpl.
      assert (length (nodeList g) = natNodes g). unfold natNodes. rewrite noNodes_def. 
      unfold nodeList. unfold ulabNodes. apply map_length. omega. 
      apply H0 in H3. rewrite H3 in H2. inversion H2.
    + reflexivity.
    + assumption.
  - unfold distance. destruct (N.eq_dec u v). subst. destruct H. contradiction.
    apply A. intros. destruct (path_of_length g u v x) eqn : ?.
    + apply path_of_length_implies_path in Heqb0. destruct Heqb0. destruct H1. destruct H. rewrite H in H1.
      inversion H1.
    + reflexivity.
Qed.

Lemma seq_pred: forall start len h t n l,
  seq start len = (h :: t) ++ S n :: l ->
  In n (h :: t).
Proof.
  intros. generalize dependent h. revert t. revert start. induction len; intros.
  - simpl. simpl in H. inversion H.
  - simpl in H. inversion H. subst. destruct t.
    simpl in H2. simpl. destruct len. simpl in H2. inversion H2. simpl in H2. inversion H2. subst. left. reflexivity.
    apply IHlen in H2. solve_in.
Qed.

Lemma seq_split: forall start len l1 x l2,
  seq start len = l1 ++ x :: l2 ->
  (forall y, In y l1 -> y < x) /\ (forall y, In y l2 -> y > x).
Proof.
  intros. generalize dependent start. revert l1. revert x. revert l2. induction len; intros; simpl in H.
  - assert (l1 = nil). destruct l1; inversion H. subst.
    simpl in H. inversion H.
  - destruct l1. simpl in H. inversion H. destruct l2.
     split; intros. destruct H0. rewrite H2 in H0. destruct H0.
     specialize (IHlen l2 n nil (S(start))). subst. simpl in IHlen. apply IHlen in H2.
     split; intros. destruct H0. rewrite in_seq in H0. omega.
     inversion H; subst. specialize (IHlen l2 x l1 (S(n)) H2). split; intros. simpl in H0.
     destruct H0. subst. assert (In x (seq (S(y)) len)). rewrite H2. solve_in. rewrite in_seq in H0.
      omega. destruct IHlen. apply H1. assumption. apply IHlen. apply H0.
Qed.

Lemma distance_neq: forall g u v n,
  u <> v ->
  distance g u v = Some n ->
  n > 0.
Proof.
  intros. unfold distance in H0. destruct (N.eq_dec u v). subst. contradiction.
  induction (seq 0 (natNodes g + 1)).
  - simpl in H0. inversion H0.
  - simpl in H0. destruct (path_of_length g u v a0) eqn : ?. inversion H0; subst; omega.
    apply IHl. assumption.
Qed.
  

(*This actually computes the shortest path*)
Lemma distance_some: forall g u v n,
  distance g u v = Some n <->
  ((u = v /\ n = 0)) \/ (n > 0 /\ u <> v /\ (exists l, path g u v l /\ length l = (n - 1)) /\ (forall l, length l < (n - 1) -> path_list g u v l = false)).
Proof.
  intros. 
  assert (forall l n, 
  fold_right (fun (x : nat) (acc : option nat) => if path_of_length g u v x then Some (x +1) else acc) None
  l = Some (n + 1) <-> (exists l1 l2, l = l1 ++ n :: l2 /\ (forall y, In y l1 -> path_of_length g u v y = false) /\
  path_of_length g u v n  = true)). { intros. induction l; split; intros; simpl in *.
  - inversion H.
  - destruct_all. destruct x; inversion H.
  - destruct (path_of_length g u v a0) eqn : ?. 
    + inversion H; subst. exists nil. exists l. split. simpl. 
      assert (a0 = n0) by omega. subst. reflexivity. split; intros.
      destruct H0. assert (a0 = n0). omega. subst. assumption. 
    + apply IHl in H. destruct H. exists (a0 :: x). destruct_all.
      exists x0. split. rewrite H. simpl. reflexivity.
      split; intros. simpl in H2. destruct H2. subst. assumption. apply H0. assumption.
      assumption.
  - destruct_all. destruct (path_of_length g u v a0) eqn : ?. destruct x.
    + inversion H; subst. reflexivity. 
    + simpl in H0. inversion H; subst. specialize (H0 n1). rewrite H0 in Heqb0. inversion Heqb0.
      left. reflexivity.
    + destruct x. inversion H; subst. rewrite Heqb0 in H1. inversion H1.
      inversion H; subst. apply IHl. exists x. exists x0. simplify'. }
   destruct (N.eq_dec u v).
   - unfold distance. subst. destruct (N.eq_dec v v ). 
    split; intros. inversion H0. subst. left. split; reflexivity. 
   destruct H0. destruct H0; subst; reflexivity. destruct_all; contradiction. contradiction.
  - split; intros. pose proof (distance_neq _ _ _ _ n0 H0). assert (exists m, m + 1 = n). {
    exists (n - 1). omega. } destruct H2 as [m]. subst.
    right. unfold distance in H0. destruct (N.eq_dec u v). inversion H0. 
    rewrite <- H3 in H1. exfalso. omega.  
    rewrite H in H0. destruct_all. clear H. split; try(assumption). split; try(assumption).
    apply path_of_length_implies_path in H3. split. setoid_rewrite path_list_equiv. 
    destruct  H3. destruct H. assert (length x1 = m \/ length x1 < m) by omega. destruct H4.
    exists x1. split. assumption. omega.  
    destruct x. simpl in H. assert (natNodes g + 1 = S(natNodes g)) by omega. rewrite H5 in H0.
    simpl in H0. inversion H0; subst. omega. 
    destruct m. omega. assert (length x1 <= m) by omega. assert (A:=H). 
    apply (path_of_size_implies_function _ _ _ _ _ H5) in H. exists x1.
    split. assumption. rewrite H2 in H. inversion H.
    pose proof seq_pred. eapply H6. apply H0.
    intros.   assert (In (length l) (seq 0 (natNodes g + 1))). { rewrite in_seq.
    assert (In m (seq 0 (natNodes g + 1))). rewrite H0. solve_in. rewrite in_seq in H4.
    omega. } rewrite H0 in H4. apply seq_split in H0. 
    destruct H0. apply in_app_or in H4. destruct H4. 
    destruct (path_list g u v l) eqn : ?. eapply path_of_size_implies_function in Heqb0.
    rewrite (H2 (length l)) in Heqb0. inversion Heqb0.
    assumption. omega. reflexivity. simpl in H4. destruct H4. omega.
    apply H5 in H4. omega. destruct H0. destruct H0; contradiction. destruct_all.
    assert (exists m, m + 1 = n). exists (n-1). omega. destruct H5 as [m]. subst.
    assert (length x = m ) by omega. clear H4. unfold distance. destruct (N.eq_dec u v). subst. contradiction.
    clear n. rewrite H. 
    assert (m <= (natNodes g)). { assert (m <= natNodes g \/ m > natNodes g) by omega. destruct H4.
    assumption. rewrite path_list_equiv in H2. apply path_shorter_than_graph_size in H2.
    destruct H2. destruct H2. rewrite H3 in H2. inversion H2. unfold nodeList in H6.
    unfold ulabNodes in H6. rewrite map_length in H6. rewrite <- noNodes_def in H6.
    unfold natNodes in H4. omega. }
    pose proof (in_split_app_fst _ (seq 0 (natNodes g + 1)) m Nat.eq_dec).
    assert (In m (seq 0 (natNodes g + 1))). rewrite in_seq. omega.
    apply H6 in H7. clear H6. destruct_all. exists x0. exists x1. split. assumption.
    apply seq_split in H6. split; intros.
    destruct H6. destruct (path_of_length g u v y) eqn : ?.
    apply path_of_length_implies_path in Heqb0. destruct Heqb0.
    destruct H10. rewrite H3 in H10. inversion H10. apply H6 in H8. omega. reflexivity.
    eapply path_of_size_implies_function. assert (length x <= m) by omega. apply H8.
    rewrite <- path_list_equiv. assumption.
Qed.

(* Key property of shortest paths - if u -> v is a shortest path passing through w, 
  then the length is the shortest path from u to w + the shortest path from w to v (plus 1)*)
Definition shortest_path g u v l :=
  path_list g u v l = true /\ (forall l', length l' < length l -> path_list g u v l' = false). 

Lemma shortest_path_transitive: forall g u v l w l' l'',
  shortest_path g u v l ->
  In w l ->
  shortest_path g u w l' ->
  shortest_path g w v l'' ->
  length l = length l' + length l'' + 1.
Proof.
  intros. unfold shortest_path in *. destruct_all.
  assert (length l < length l' + length l'' + 1 \/
  length l > length l' + length l'' + 1 \/ length l = length l' + length l'' + 1) by omega.
  destruct H6. apply in_split_app_fst in H0. destruct_all.
  rewrite H0 in H. apply path_app in H. destruct H.
  assert (length l = length x + length x0 + 1). rewrite H0. rewrite app_length.
  simpl. omega. rewrite H9 in H6. 
  assert (length x + length x0 < length l' + length l'') by omega. clear H6. clear H9.
  assert (length x < length l'' \/ length x0 < length l') by omega. destruct H6.
  rewrite H3 in H. inversion H. assumption.
  rewrite H4 in H8. inversion H8. assumption. apply N.eq_dec.
  destruct H6. assert (path_list g u v (l'' ++ w :: l') = true).
  rewrite path_app. split; assumption. rewrite H5 in H7.
  inversion H7. rewrite app_length. simpl. omega. assumption.
Qed.

(*Decidability of [path]*)

Lemma path_equiv: forall g u v,
  (exists l, path g u v l) <-> path_of_length g u v (length(nodeList g)) = true.
Proof.
  intros. split; intros.
  - setoid_rewrite path_list_equiv in H. destruct H. apply path_shorter_than_graph_size in H.
    destruct_all. eapply path_of_size_implies_function. apply H0. apply H.
  - setoid_rewrite path_list_equiv. pose proof (path_of_length_implies_path _ _ _ _ H).
    destruct_all. exists x. assumption. 
Qed.

Lemma path_dec: forall g u v,
  {exists l, path g u v l} + {~exists l, path g u v l}.
Proof.
  intros. destruct (path_of_length g u v (length(nodeList g))) eqn : ?.
  left. apply path_equiv; assumption.
  right. intro. apply path_equiv in H. rewrite H in Heqb0. inversion Heqb0.
Qed.

End Path. 
