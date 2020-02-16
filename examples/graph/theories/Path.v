Require Import Data.Graph.Inductive.Graph.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import Helper.
Require Import Wellfounded.
Require Import Coq.Lists.ListDec.
Require Import Coq.NArith.BinNat.
Require Import Omega.
Require Import Crush.
Require Import WeightedGraphs.
Import GHC.Num.Notations.


(*Lots of stuff about paths here*)
Section Path.

Context {a : Type} {b : Type} { gr : Type -> Type -> Type} {Hgraph : Graph.Graph gr} {Hlaw : Graph.LawfulGraph gr}.

Inductive path': (gr a b) -> Node -> Node -> (list Node) -> Prop :=
  | p_single: forall g v, vIn g v = true -> path' g v v (v :: nil)
  | p_multi: forall g u v v' l,
      path' g u v' l ->
      eIn g v' v = true ->
      path' g u v (v :: l).

(** Useful results about paths **)

(*The last element in a path is the end vertex*)
Lemma path_fst: forall g u v a l,
  path' g u v (a :: l) ->
  a = v.
Proof.
  intros. inversion H; subst; reflexivity.
Qed.

Lemma path_lst: forall g u v l,
  path' g u v l ->
  exists l1, l = l1 ++ u :: nil.
Proof.
  intros. induction H; subst.
  - exists nil; reflexivity.
  - destruct IHpath'. subst. exists (v :: x). reflexivity.
Qed. 

(*Any subpath of a path is also a valid path*)
Lemma path_app: forall g u v a l1 l2,
  path' g u v (l1 ++ a :: l2) <->
  path' g a v (l1 ++ a :: nil)/\ path' g u a (a :: l2).
Proof.
  intros. split; intros. generalize dependent v. generalize dependent l2. induction l1; intros.
  - simpl in H. inversion H; subst. simpl. split; assumption. simpl. split.
    + constructor. eapply edges_valid. apply H6.
    + assumption.
  - simpl in *. inversion H; subst.
    + destruct l1; inversion H5.
    + apply IHl1 in H5. destruct H5. split; try assumption. econstructor. apply H0. assumption.
  - destruct_all. generalize dependent v. generalize dependent a0. revert l2. induction l1; intros.
    + simpl in H. inversion H; subst. simpl. assumption. inversion H6.
    + simpl. simpl in H. assert (a0 = v) by (apply path_fst in H; assumption). subst.
      inversion H; subst.
      * destruct l1; inversion H1.
      * econstructor. apply IHl1. assumption. apply H2. assumption.
Qed. 

(*If there is a path that includes a cycle, there is also a valid path without that cycle*)
Lemma path_remove_cycle: forall g u v w l1 l2 l3,
  path' g u v (l1 ++ w :: l2 ++ w :: l3) ->
  path' g u v (l1 ++ w :: l3).
Proof.
  intros. apply path_app in H. destruct_all. inversion H0; subst. destruct l2; inversion H1.
  apply path_app in H2. destruct_all.
  apply path_app. simplify'.
Qed.

(*TODO: Move to helper*)
Ltac solve_assume := repeat(split; try(intros); try(assumption); try(reflexivity)).

Ltac solve_in :=
  match goal with
  | [ H : _ |- In ?x (?l ++ ?r)] => apply in_or_app; solve_in
  | [ H : _ |- In ?x ?s \/ In ?x ?s'] => first [ left; solve_in | right; solve_in ] 
  | [ H : _ |- In ?x (?x :: ?l)] => simpl; left; reflexivity
  | [ H : _ |- In ?x (?a :: ?l)] => simpl; right; solve_in
  | [ H : _ |- _ ] => try(reflexivity); assumption
end. 

Ltac destruct_if :=
  match goal with 
    | [H: (if ?b then _ else _) = _ |- _] => destruct b
    | [H: _ |- (if ?b then _ else _) = _ ] => destruct b
    end. 

(*If there is a path from u to v, then there is a path that contains no duplicates*)
Lemma path_no_dups: forall g u v l,
  path' g u v l ->
  exists l1, path' g u v l1 /\ NoDup l1 /\
  (forall x, In x l1 -> In x l).
  Proof.
    intros. induction l using (well_founded_induction
                       (wf_inverse_image _ nat _ (@length _)
                          PeanoNat.Nat.lt_wf_0)).
    destruct (NoDup_dec (N.eq_dec) l).
    - exists l. solve_assume.
    - rewrite no_no_dup in n. destruct_all. subst. 
      apply path_remove_cycle in H. specialize (H0 (x0 ++ x :: x2)). destruct H0 as [l].
      repeat(rewrite app_length; simpl). omega. apply H. exists l. destruct_all; solve_assume.
      apply H2 in H3. apply in_app_or in H3. destruct H3. solve_in. simpl in H3; solve_in.
      apply N.eq_dec.
Qed.

(*Every vertex in a path is in the graph*)
Lemma path_implies_in_graph: forall g u v l,
  path' g u v l ->
  vIn g u = true /\ vIn g v = true /\ (forall x, In x l -> vIn g x = true).
Proof.
  intros. induction H.
  - simplify'. inversion H0; subst. assumption. inversion H1.
  - destruct_all. solve_assume. eapply edges_valid. apply H0. simpl in H4.
    destruct H4; subst. eapply edges_valid. apply H0. apply H3; assumption.
Qed. 

Section AllPaths.

(*Find all u-v paths from a given vertex of length n*)
Fixpoint paths_of_length (g: gr a b) (u v : Node) (n : nat) : list (list Node) :=
  match n with
  | O => nil
  | S(O) => if N.eq_dec u v then if vIn g v then (v :: nil) :: nil else nil else nil
  | S(m) => fold_right (fun x t => match (paths_of_length g u x m) with
                                    | nil => t
                                    | l => if (eIn g x v) then (map (fun y => v :: y) l) ++ t else t
                                    end) nil (nodeList g)
  end.

Fixpoint All {T} (P: T -> Prop) (ls : list T) : Prop :=
  match ls with
    | nil => True
    | cons h t => P h /\ All P t
  end.

(*This function finds paths of correct length*)
Lemma paths_of_length_n: forall g u v n,
  forall l, In l (paths_of_length g u v n) -> length l = n.
Proof.
  intros. destruct n. simpl in H. destruct H. generalize dependent u. revert v. revert l. induction n; intros.
  - simpl in H. destruct (N.eq_dec u v). subst. destruct (vIn g v). simpl in H. destruct H.
    subst. simpl. reflexivity. destruct H. inversion H. inversion H.
  - remember (S(n)) as m. simpl in H. rewrite Heqm in H. rewrite <- Heqm in H. induction (nodeList g).
    simpl in H. destruct H. simpl in H. destruct (paths_of_length g u a0 m) eqn : P. apply IHl0. apply H.
    destruct (eIn g a0 v) eqn : E. simpl in H. destruct H. subst. simpl. erewrite IHn. reflexivity.
    rewrite P. left. reflexivity. apply in_app_or in H. destruct H. rewrite in_map_iff in H.
    destruct_all. subst. simpl. erewrite IHn. reflexivity. rewrite P. right. assumption.
    apply IHl0. apply H. apply IHl0. apply H.
Qed.

(*This function finds valid paths*)
Lemma paths_of_length_are_paths: forall g u v n,
  (forall l, In l (paths_of_length g u v n) -> path' g u v l).
Proof.
  intros. destruct n. simpl in H. destruct H. generalize dependent u. revert v. revert l.
  induction n; intros.
  - simpl in H. destruct (N.eq_dec u v). subst. destruct (vIn g v) eqn : V. simpl in H.
    destruct H. subst. constructor. assumption. destruct H. inversion H. inversion H.
  - remember (S(n)) as m. simpl in H. rewrite Heqm in H. rewrite <- Heqm in H.
   assert (forall l' l, (forall v', In v' l' -> vIn g v' = true) ->
    In l
      (fold_right
         (fun (x : Node) (t : list (list Node)) =>
          match paths_of_length g u x m with
          | nil => t
          | l0 :: l1 => if eIn g x v then (v :: l0) :: map (fun y : list Node => v :: y) l1 ++ t else t
          end) nil l') -> path' g u v l). { intros. induction l'. simpl in H1. destruct H1.
      simpl in H1. destruct (paths_of_length g u a0 m) eqn : P. apply IHl'. 
      intros. apply H0. right. assumption. apply H1. destruct (eIn g a0 v) eqn : E. simpl in H1.
      destruct H1. subst. eapply p_multi. apply IHn. rewrite P. left. reflexivity. assumption.
      apply in_app_or in H1. destruct H1. rewrite in_map_iff in H1. destruct_all. subst.
      eapply p_multi. apply IHn. rewrite P. right. assumption. assumption. apply IHl'. intros.
      apply H0. right. assumption. apply H1. apply IHl'. intros. apply H0. right. assumption.
      apply H1. } (apply (H0 (nodeList g))). intros. unfold vIn. unfold mem. destruct_if. reflexivity.
      contradiction. apply H.
Qed.
(*
Lemma in_path': forall u v l,
  path' g u v l ->
  vIn g u = true /\ vIn g v = true.
Proof.
  intros. remember g as g0. induction H; subst. split; assumption.
  eapply edges_valid in H0. destruct_all. split. apply IHpath'. reflexivity. assumption. assumption.
  assumption.
Qed.
*)

(*This function finds all paths of length n from u to v*)
Lemma paths_of_length_appear: forall g u v n l,
  path' g u v l /\ length l = n -> In l (paths_of_length g u v n).
Proof.
  intros. generalize dependent v. revert u. revert n. induction l; simpl in *; intros; destruct_all.
  - subst. inversion H.
  - destruct n. omega. assert (length l = n) by omega. clear H0. remember n as n'. inversion H.  subst.
    simpl. destruct (N.eq_dec a0 a0). rewrite H5. left. reflexivity. contradiction. subst.
    simpl. destruct (length l) eqn : L. destruct l. inversion H6. simpl in L. inversion L.
    assert (forall a v'' l', In a l' ->
      In l (paths_of_length g u a (S n)) ->
      eIn g a v'' = true ->
      In (v'' :: l)
  (fold_right
     (fun (x : Node) (t : list (list Node)) =>
      match paths_of_length g u x (S n) with
      | nil => t
      | l0 :: l1 => if eIn g x v'' then (v'' :: l0) :: map (fun y : list Node => v'' :: y) l1 ++ t else t
      end) nil l')). { intros. induction l'. inversion H0. simpl in H0. destruct (N.eq_dec a2 a1). subst. 
      unfold fold_right. destruct (paths_of_length g u a1 (S n)) eqn : P.
      inversion H1.  rewrite H2. simpl in H1. destruct H1. subst. left. reflexivity.
      right. apply in_or_app. left. rewrite in_map_iff. exists l. split. reflexivity. assumption.
      destruct H0. subst. contradiction. 
      unfold fold_right. destruct (paths_of_length g u a2 (S n)) eqn : P.
      apply IHl'. assumption. destruct (eIn g a2 v'') eqn :  simpl. right.
      apply in_or_app. right. apply IHl'. assumption. apply IHl'. assumption. }
      apply (H0 v'). apply edges_valid in H7. unfold vIn in H7. destruct H7.
      unfold mem in H1. destruct_if. assumption. inversion H1.
      apply IHl. split. assumption. reflexivity. assumption.
Qed.

(*What we want to say: This function defines all of the paths from u to v of length n*)
Lemma paths_of_length_def: forall g u v n l,
  In l (paths_of_length g u v n) <-> path' g u v l /\ length l = n.
Proof.
  intros. split; intros.
  - split. eapply paths_of_length_are_paths. apply H.
    eapply paths_of_length_n. apply H.
  - eapply paths_of_length_appear. apply H.
Qed.

(*If there is a path, then there is a path at most as large as the number of vertices in the graph (because
  there is a path with no duplicates and every vertex is in the graph*)
Lemma path_shorter_than_graph_size: forall g u v l,
  path' g u v l ->
  exists l', path' g u v l' /\ length l' <= length(nodeList g).
Proof.
  intros. apply path_no_dups in H. destruct_all. 
  assert (forall a, In a x -> In a (nodeList g)). intros.
  apply path_implies_in_graph in H. destruct_all. apply H4 in H2. unfold vIn in H2.
  unfold mem in H2.  match goal with | [H: (if ?x then _ else _) = _  |- _] => destruct x eqn : ? end.
  assumption. inversion H2. 
  exists x. split. apply H. eapply NoDup_incl_length. apply H0. unfold incl. apply H2.
Qed.

Definition natNodes (g : gr a b) := (BinInt.Z.abs_nat(Graph.noNodes g)).

(*By the above lemma, we can simply define distance by repeatedly checking if there is a list with 
  the given distance*)
Definition distance_list (l: list nat) (g: gr a b) (u v : Node) : option nat :=
  (*if (N.eq_dec u v) then if vIn g v then (Some 0) else None else*)
  fold_right (fun x acc => match paths_of_length g u v x with
                            | nil => acc
                            | _ => Some x
                           end) None l.

Definition distance := fun g => distance_list (seq 0 (natNodes g + 1)) g.


(*[distance_list] is none iff there is no path of size <= n*)
Lemma distance_list_none: forall l g u v,
  distance_list l g u v = None <-> (forall x, In x l -> paths_of_length g u v x = nil).
Proof.
  intros. induction l; simpl.
  - split; auto; intros. destruct H0.
  - split; intros.
    + destruct H0. subst. destruct (paths_of_length g u v x) eqn : E. reflexivity.
      inversion H. destruct (paths_of_length g u v a0). apply IHl in H0. assumption.
      assumption. inversion H.
    + destruct (paths_of_length g u v a0) eqn : E. 
      apply IHl. intros. apply H. right. assumption. 
      rewrite H in E. inversion E. auto.
Qed.

(*distance returns None iff u and v are not connected*)
Lemma distance_none: forall g u v,
  distance g u v = None <-> (forall l, ~path' g u v l).
Proof.
  intros. unfold distance; split; intros.
  - rewrite distance_list_none in H. intro.
    apply path_shorter_than_graph_size in H0.
    destruct_all.
    specialize (H (length x)).
    assert (paths_of_length g u v (length x) = nil). apply H.
    apply in_seq. simpl. split. omega. unfold natNodes. rewrite noNodes_def. unfold nodeList in H1.
    unfold ulabNodes in H1. rewrite map_length in H1.
    assert (forall n m, n <= m -> n < m + 1). intros. omega. apply H2. assumption.
    pose proof (paths_of_length_def g u v (length x) x). 
    destruct H3. rewrite H2 in H4. simpl in H4. apply H4. solve_assume.
  - rewrite distance_list_none. intros. destruct (paths_of_length g u v x) eqn : P.
    + reflexivity.
    + pose proof (paths_of_length_def g u v x l). destruct H1.
      assert (In l (paths_of_length g u v x)). rewrite P. solve_in.
      apply H1 in H3. destruct_all. exfalso. eapply H. apply H3.
Qed. 

Require Import Coq.Sorting.Sorted.

(*Helper lemma for some case*)
Lemma distance_list_some: forall l g u v n,
  StronglySorted Nat.le l ->
  distance_list l g u v = Some n ->
  In n l /\ paths_of_length g u v n <> nil /\ (forall x p, In x l -> path' g u v p -> length p = x -> n <= length p).
Proof.
  intros. generalize dependent n. revert u v g. induction l; intros.
  - simpl in H0. inversion H0.
  - simpl in H0. inversion H; subst. destruct (paths_of_length g u v a0) eqn : P.
    apply IHl in H0. destruct_all. solve_assume. solve_in. subst. 
    simpl in H5. destruct H5.
    + subst. pose proof (paths_of_length_def g u v (length p) p).
      rewrite P in H5. destruct H5. exfalso. apply H7. solve_assume.
    + eapply H2. apply H5. assumption. reflexivity.
    + assumption.
    + inversion H0; subst. solve_assume. solve_in. rewrite P. intro. inversion H1.
      subst. simpl in H1. destruct H1. subst. omega. rewrite Forall_forall in H4.
      apply H4. assumption.
Qed.

(*Definition of shortest path*)
Definition shortest_path g u v l :=
  path' g u v l /\ (forall l', length l' < length l -> ~path' g u v l'). 

(*One final lemma, that [seq] is [StronglySorted]*)
Lemma seq_sorted: forall n m,
  StronglySorted Nat.le (seq n m).
Proof.
  intros. revert n. induction m.
  - simpl. constructor.
  - simpl. constructor. apply IHm. rewrite Forall_forall. intros.
    rewrite in_seq in H. destruct H. assert (forall a b, S a <= b -> a <= b). intros. omega.
    apply H1. assumption.
Qed. 

Definition distance_some: forall g u v n,
  distance g u v = Some n -> exists l, shortest_path g u v l /\ length l = n.
Proof.
  intros. unfold distance in H. apply distance_list_some in H.
  - destruct_all. destruct (paths_of_length g u v n) eqn : P.
    + contradiction.
    + pose proof (paths_of_length_def g u v n l). destruct H2. clear H3. rewrite P in H2. simpl in H2.
      assert (path' g u v l /\ length l = n). apply H2. left. reflexivity. clear H2.
      destruct_all. exists l. split. unfold shortest_path. split. assumption. intros.
      intro. eapply H1 in H5. omega. assert (In (length l') (seq 0 (natNodes g + 1))).
      rewrite in_seq. rewrite in_seq in H. omega. apply H6. reflexivity. assumption.
  - apply seq_sorted.
Qed. 

(* Key property of shortest paths - if u -> v is a shortest path passing through w, 
  then the length is the shortest path from u to w + the shortest path from w to v (plus 1)*)
(*Not quite true because we count endpoints multiple times - TODO: see what is needed, come back after BFS*)

(*Lemma shortest_path_transitive: forall g u v l w l' l'',
  shortest_path g u v l ->
  In w l ->
  shortest_path g u w l' ->
  shortest_path g w v l'' ->
  length l = length l' + length l'' + 1.
Proof.
  intros. unfold shortest_path in *. destruct_all.
  assert (length l < length l' + length l'' + 1 \/
  length l > length l' + length l'' + 1 \/ length l = length l' + length l'' + 1) by omega.
  destruct H6.
  - apply in_split_app_fst in H0. destruct_all.
    rewrite H0 in H. apply path_app in H. destruct H.
    assert (length l = length x + length x0 + 1). rewrite H0. rewrite app_length.
    simpl. omega. rewrite H9 in H6. 
    assert (length x + length x0 < length l' + length l'') by omega. clear H6. clear H9.
    assert (length x < length l'' \/ length x0 < length l') by omega. destruct H6.
    + exfalso. eapply H3. apply H6. 
  rewrite H3 in H6. inversion H. assumption.
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


Definition distance (g: gr a b) (u v : Node) : option nat :=
  if (N.eq_dec u v) then if vIn g v then (Some 0) else None else
  fold_right (fun x acc => match paths_of_length g u v x with
                            | nil => acc
                            | _ => Some x
                           end) None (seq 0 (natNodes g + 1)).

(*Now we prove that this actually finds the shortest path*)

(*First, a helper lemma*)
Lemma shortest_none_helper: forall l u v,
  (fold_right
  (fun (x : nat) (acc : option (list Node)) =>
   match min_weight_size_n u v x with
   | Some l =>
       match acc with
       | Some l' => if lt_weight_b l l' then Some l else Some l'
       | None => Some l
       end
   | None => match acc with
             | Some l => Some l
             | None => None
             end
   end) None l) = None <-> (forall x, In x l -> min_weight_size_n u v x = None).

Lemma distance_none: forall g u v,
  distance g u v = None <-> (forall l, ~path' g u v l).
Proof.
  intros. unfold distance.


Definition shortest_wpath u v l :=
  path' g u v l /\ forall l', path' g u v l' -> le_weight l l'.

Lemma find_shortest_wpath_correct: forall u v l,
  find_shortest_wpath u v = Some l -> shortest_wpath u v l. 


(*
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
*)

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
  if (N.eq_dec u v) then if vIn g v then (Some 0) else None else
  fold_right (fun x acc => if path_of_length g u v x then Some (x + 1) else acc) None (seq 0 (natNodes g + 1)).

Lemma distance_none: forall g u v,
  distance g u v = None <-> ((forall l, path_list g u v l = false) /\ u <> v) \/ vIn g v = false.
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
  - unfold distance in H. destruct (N.eq_dec u v). destruct (vIn g v) eqn : ?. inversion H. right. reflexivity. 
    left. split; intros.
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
  - unfold distance. destruct (N.eq_dec u v). destruct (vIn g v) eqn : V. subst. destruct H.
    destruct H. contradiction. inversion H. reflexivity.
    apply A. intros. destruct (path_of_length g u v x) eqn : ?.
    + apply path_of_length_implies_path in Heqb0. destruct Heqb0. destruct H1. destruct H. destruct H. rewrite H in H1.
      inversion H1. apply path_implies_in_graph in H1. destruct_all. rewrite H3 in H. inversion H.
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
  distance g u v = Some n <-> vIn g v = true /\
  (((u = v /\ n = 0)) \/ (n > 0 /\ u <> v /\ (exists l, path g u v l /\ length l = (n - 1)) /\ (forall l, length l < (n - 1) -> path_list g u v l = false))).
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
  destruct (vIn g v) eqn : ?.
   destruct (N.eq_dec u v). 
   - unfold distance. subst. destruct (N.eq_dec v v ). rewrite Heqb0. 
    split; intros. inversion H0. subst. split. reflexivity. left. split; reflexivity. 
   destruct H0. destruct H1; destruct_all; subst. reflexivity. contradiction.  contradiction.
  - split; intros. split.  reflexivity.
    pose proof (distance_neq _ _ _ _ n0 H0). assert (exists m, m + 1 = n). {
    exists (n - 1). omega. } destruct H2 as [m]. subst.
    right. unfold distance in H0. destruct (N.eq_dec u v). subst. contradiction. 
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
    destruct (path_list g u v l) eqn : ?. eapply path_of_size_implies_function in Heqb1.

    rewrite (H2 (length l)) in Heqb1. inversion Heqb1.
    assumption. omega. reflexivity. simpl in H4. destruct H4. omega.
    apply H5 in H4. omega. destruct H0. destruct H1. destruct H1; contradiction. destruct_all.
    assert (exists m, m + 1 = n). exists (n-1). omega. destruct H6 as [m]. subst.
    assert (length x = m ) by omega. clear H5. unfold distance. destruct (N.eq_dec u v). subst. contradiction.
    clear n. rewrite H. 
    assert (m <= (natNodes g)). { assert (m <= natNodes g \/ m > natNodes g) by omega. destruct H5.
    assumption. rewrite path_list_equiv in H3. apply path_shorter_than_graph_size in H3.
    destruct H3. destruct H3. rewrite H4 in H3. inversion H3. unfold nodeList in H7.
    unfold ulabNodes in H7. rewrite map_length in H7. rewrite <- noNodes_def in H7.
    unfold natNodes in H5. omega. }
    pose proof (in_split_app_fst _ (seq 0 (natNodes g + 1)) m Nat.eq_dec).
    assert (In m (seq 0 (natNodes g + 1))). rewrite in_seq. omega.
    apply H7 in H8. clear H7. destruct_all. exists x0. exists x1. split. assumption.
    apply seq_split in H7. split; intros.
    destruct H7. destruct (path_of_length g u v y) eqn : ?.
    apply path_of_length_implies_path in Heqb1. destruct Heqb1.
    destruct H11. rewrite H4 in H11. inversion H11. apply H7 in H9. omega. reflexivity.
    eapply path_of_size_implies_function. assert (length x <= m) by omega. apply H9.
    rewrite <- path_list_equiv. assumption.
  - split; intros. assert (A:=H0). unfold distance in H0. destruct (N.eq_dec u v). rewrite Heqb0 in H0. inversion H0.
     assert (n > 0). eapply distance_neq.  apply n0. apply A. assert (exists m, n = m + 1).
      destruct n. omega. exists n. omega. destruct H2. subst. rewrite H in H0. destruct_all.
    apply path_of_length_implies_path in H3. destruct_all.
     apply path_implies_in_graph in H3. destruct_all. rewrite H5 in Heqb0. inversion Heqb0.
    destruct H0. inversion H0.
Qed.


Definition shortest_path g u v l :=
  path_list g u v l = true /\ (forall l', length l' < length l -> path_list g u v l' = false). 


*)
(* Weighted paths. We first define a new path definition that matches the one used in FGL code*)

Inductive path': (gr a b) -> Node -> Node -> (list Node) -> Prop :=
  | p_single: forall g v, vIn g v = true -> path' g v v (v :: nil)
  | p_multi: forall g u v v' l,
      path' g u v' l ->
      eIn g v' v = true ->
      path' g u v (v :: l).

Require Import GHC.Base.
Require Import OrdTactic.
Require Import Coq.micromega.OrderedRing.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Classes.SetoidTactics.
Require Import RealRing.
(*Paths and shortest paths in weighted graphs*)
Section Weighted.


(*We declare b as an ordered ring. GHC.Num should usually be a ring, and we need the fact that addition
  acts in a consistent way with the ordering (ie, x < y -> p + x < p + y and x >= 0 and y >= 0 -> x + y >= 0).
  I don't know if we need a full ordered ring, but Coq provides decent facilities for working with them*)

Context {Hnum: GHC.Num.Num b} {Heq: Base.Eq_ b} {HOrd: Base.Ord b} {Hreal: @GHC.Real.Real b Hnum Heq HOrd}
{Hlaw2 : (@WeightedGraphs.LawfulWGraph a b gr Hgraph) } {HEqLaw: Base.EqLaws b} {HOrdLaw: @OrdLaws b Heq HOrd HEqLaw}
{HorderedRing: @RealRing b Heq HOrd HEqLaw Hnum Hreal}.



Add Relation b (fun x y => x == y = true)
  reflexivity proved by (@Equivalence_Reflexive _ _ (SORsetoid real_ring))
  symmetry proved by (@Equivalence_Symmetric _ _ (SORsetoid real_ring))
  transitivity proved by (@Equivalence_Transitive _ _ (SORsetoid real_ring))
as sor_setoid.

Add Morphism op_zp__ with signature (fun x y => x == y = true) ==> (fun x y => x == y = true) ==> (fun x y => x == y = true) as rplus_morph.
destruct HorderedRing; assumption.
Qed.

Add Morphism op_zt__ with signature (fun x y => x == y = true) ==> (fun x y => x == y = true) ==> (fun x y => x == y = true) as rtimes_morph.
destruct HorderedRing; assumption.
Qed. 
Add Morphism negate with signature (fun x y => x == y = true) ==> (fun x y => x == y = true) as ropp_morph.
 destruct HorderedRing; assumption.
Qed. 
Add Morphism (fun x y => x <= y = true) with signature (fun x y => x == y = true) ==> (fun x y => x == y = true) ==> iff as rle_morph.
destruct HorderedRing; assumption. 
Qed.
Add Morphism (fun x y => x < y = true) with signature (fun x y => x == y = true) ==> (fun x y => x == y = true) ==> iff as rlt_morph.
destruct HorderedRing; assumption.
Qed.
Lemma req_dec: forall x y, x == y = true -> (fun x y => x == y = true) x y. intros. assumption.
Qed.

(*TODO: figure out why ring tactic is not working*)
Add Ring b : (SORrt real_ring) (decidable req_dec).


(*For now, I will assume that the graph is simple (no parallel edges). Eventually, I may be able to
  relax that restriction, and it should only matter for the path proofs*)
Variable g : gr a b.
Variable Hsimple: forall u v w w', WeIn g u v w -> WeIn g u v w' -> w = w'.
Variable HNonneg: forall u v w, WeIn g u v w -> #0 <= w = true.

Definition find_weight (g: gr a b) (u v : Node) : option b :=
  match (match_ u g) with
  | (Some (_, _, _, o), g') => fold_right (fun (x : b * Node) acc => let (w, y) := x in if N.eq_dec y v then Some w
    else acc) None o
  | (None, g') => None
  end. 

Fixpoint path_cost (g: gr a b) (l: list Node) : option b :=
  match l with
  | nil => None
  | (x :: l') => match l' with
                 | nil => if vIn g x then Some #0 else None
                 | y :: l'' =>  match (find_weight g y x) with
                      | None => None
                      | Some w => match (path_cost g l') with
                                  | None => None
                                  | Some w' => Some (w + w')
                                  end
                      end
                end
   end.

Definition eInP (g: gr a b) (u v : Node) : Prop :=
  In (u,v) (ulabEdges (labEdges g)).



Lemma eIn_equiv: forall g u v,
  eIn g u v = true <-> eInP g u v.
Proof.
  intros. unfold eIn. unfold eInP. unfold mem. split; intros.
  destruct_if.
  - unfold edgeList in i. apply i.
  - inversion H.
  - destruct_if. reflexivity. unfold edgeList in n. contradiction.
Qed.

Lemma edge_weight: forall (g: gr a b) u v,
  eIn g u v = true <-> exists w, WeIn g u v w.
Proof.
  intros. rewrite eIn_equiv.  unfold eInP. unfold WeIn. induction (labEdges g0); simpl.
  - split; intros; auto. destruct H. destruct_all. destruct H.
  - destruct a0. destruct p. split; intros.
    + destruct H. inversion H; subst. exists b0. left. reflexivity.
      apply IHl in H. destruct H. exists x. right. assumption.
    + destruct_all. destruct H. inversion H; subst. left. reflexivity.
      right. apply IHl. exists x. assumption.
Qed.

(*Not true in multigraph (only converse holds)*)
Lemma edge_weight_in: forall u v w,
  WeIn g u v w <-> find_weight g u v = Some w.
Proof.
  intros.
  assert (forall l w v,
        (forall w w', In (w,v) l -> In (w', v) l -> w = w') ->
        fold_right (fun (x : b * Node) (acc : option b) => let (w0, y) := x in if N.eq_dec y v then Some w0 else acc)
          None l = Some w <-> In (w, v) l). {
  intros. induction l; simpl.
  - split; intros. inversion H0. destruct H0.
  - destruct a0. destruct (N.eq_dec n v0). subst. split; intros. inversion H0; subst. left. reflexivity.
    destruct H0. inversion H0; subst. reflexivity. simpl in H. assert (b0 = w0). eapply H.
    left. reflexivity. right. assumption. subst. reflexivity.
    rewrite IHl. split; intros. right. assumption. destruct H0. inversion H0. subst. contradiction.
    assumption. intros. eapply H. simpl. right. assumption. right. assumption. }
 split; intros.
  - unfold find_weight. destruct (match_ u g) eqn : M. destruct m.
    + destruct c. destruct p. destruct p. epose proof (@Wmatch_context _ _ gr _ Hlaw2 _ _ _ _ _ _  _ M).
      rewrite H. destruct_all. apply H3. apply H0. intros. eapply Hsimple. destruct_all. apply i0. apply H2.
      destruct_all. apply H5. apply H3.
    + destruct (vIn g u) eqn : V. rewrite <- match_in in V. destruct_all. rewrite H1 in M. inversion M.
      assert (eIn g u v = true). rewrite edge_weight. exists w. assumption. apply edges_valid in H1.
      destruct_all. rewrite H1 in V. inversion V.
  - unfold find_weight in H0. destruct (match_ u g) eqn : M. destruct m.
    + destruct c. destruct p. destruct p. apply H in H0. 
       epose proof (@Wmatch_context _ _ gr _ Hlaw2 _ _ _ _ _ _  _ M). destruct_all.
      apply H3. assumption. intros. epose proof (@Wmatch_context _ _ gr _ Hlaw2 _ _ _ _ _ _  _ M).
      destruct_all. subst. eapply Hsimple. apply H6. apply H2. apply H6. apply H3.
    + inversion H0.
Qed.

Lemma find_weight_nonneg: forall u v w,
  find_weight g u v = Some w -> #0 <= w = true.
Proof.
  intros. rewrite <- edge_weight_in in H. eapply HNonneg. apply H.
Qed. 

(*Easier to work with, through equivalent, to [path_cost]*)
Inductive Wpath : (gr a b) -> Node -> Node -> (list Node) -> b -> Prop :=
  | wp_single: forall g v, vIn g v = true -> Wpath g v v (v :: nil) #0
  | wp_step: forall g u v v' w w' l, 
     Wpath g u v' l w ->
     WeIn g v' v w' ->
     Wpath g u v (v :: l) (_GHC.Num.+_ w' w) .

Lemma wpath_nonneg: forall u v l w,
  Wpath g u v l w ->
  #0 <= w = true.
Proof.
  intros. induction H.
  - order b.
  - apply HNonneg in H0.
    pose proof (Rplus_nonneg_nonneg real_ring). apply H1. assumption. apply IHWpath.
    apply Hsimple. apply HNonneg.
Qed. 

Lemma hd_path: forall g u v l w u',
  Wpath g u v (u' :: l) w ->
  v = u'.
Proof.
  intros. inversion H; subst; reflexivity.
Qed. 

Lemma path_cost_sum: forall l w,
  path_cost g l = Some w <-> (exists u v, Wpath g u v l w).
Proof.
  intros. split; intros.
  - generalize dependent w. induction l using (well_founded_induction
                     (wf_inverse_image _ nat _ (@length _)
                        PeanoNat.Nat.lt_wf_0)); intros.
    + destruct l. simpl in H0. inversion H0.
      simpl in H0. destruct l. 
      destruct (vIn g n) eqn : V. inversion H0; subst.
      exists n. exists n. constructor. assumption. inversion H0.
      destruct (find_weight g n0 n) eqn : W.
      * destruct (path_cost g (n0 :: l)) eqn : P.
        -- specialize (H (n0 :: l)). assert (exists u v : Node, Wpath g u v (n0 :: l) b1).
           apply H. simpl. omega. apply P. destruct_all. exists x. exists n. inversion H0; subst. eapply wp_step.
           apply H1. rewrite edge_weight_in. apply hd_path in H1. subst. apply W.
        -- inversion H0.
      * inversion H0.
  - destruct H as [u]. destruct H as [v]. remember g as g'. induction H; subst.
    + simpl. rewrite H. reflexivity.
    + simpl. destruct l. inversion H. assert (v' = n). eapply hd_path. apply H. subst.
      rewrite edge_weight_in in H0. rewrite H0. rewrite IHWpath. reflexivity. reflexivity. apply Hsimple. assumption.
Qed.

Lemma path_cost_nonneg: forall l w,
  path_cost g l = Some w ->
  #0 <= w = true.
Proof.
  intros. rewrite path_cost_sum in H. destruct_all. eapply wpath_nonneg. apply H.
Qed.


Lemma path'_WPath: forall u v l,
  path' g u v l <-> exists w, Wpath g u v l w.
Proof.
  intros. split; intros. induction H. exists #0. constructor.
  assumption. specialize (IHpath' Hsimple HNonneg).  destruct_all. 
  rewrite edge_weight in H0. destruct_all. exists (x0 + x). econstructor.
  apply H1. assumption. destruct H. induction H. constructor. assumption.
  econstructor. apply IHWpath. apply Hsimple. apply HNonneg. 
  rewrite edge_weight. exists w'. assumption.
Qed.

Lemma path_cost_path' : forall l,
  (exists w, path_cost g l = Some w) <-> (exists u v, path' g u v l).
Proof.
  intros; split; intros; destruct_all. eapply path_cost_sum in H. 
  destruct_all. exists x0. exists x1. rewrite path'_WPath. exists x. assumption.
  rewrite path'_WPath in H. destruct H. exists x1. rewrite path_cost_sum. exists x. exists x0. assumption.
Qed.

Lemma path_cost_cons: forall h' h t n m,
  path_cost g (h' :: t) = Some n ->
  find_weight g h' h = Some m ->
  path_cost g (h :: h' :: t) == Some (n + m) = true.
Proof.
  intros. remember (h' :: t) as l. simpl. rewrite Heql. rewrite <- Heql. rewrite H0. rewrite H. 
  rewrite Base.simpl_option_some_eq. (*ring*) destruct HorderedRing.
  destruct real_ring. destruct (SORrt). apply Radd_comm.
Qed. 

Lemma path_in_graph: forall u v l v',
  path' g u v l ->
  In v' l ->
  vIn g v' = true.
Proof.
  intros. induction H. simpl in H0. destruct H0. subst. assumption. destruct H0.
  simpl in H0. destruct H0. subst. apply edges_valid in H1. apply H1. apply IHpath'.
  apply Hsimple. assumption. assumption.
Qed.

Lemma some_none_eq: forall (n : b),
  None == Some n = false.
Proof.
  intros. unfold "==". unfold op_zeze____. unfold Eq___option.
  unfold Base.Eq___option_op_zeze__. reflexivity.
Qed.

Lemma path_cost_app: forall l l' a n,
  path_cost g (l ++ a :: l') == Some n = true ->
  exists m p, path_cost g (l ++ a :: nil) == Some m = true /\ path_cost g (a :: l') == Some p = true 
  /\  n == (m + p) = true.
Proof.
  intro l. induction l using (well_founded_induction
                     (wf_inverse_image _ nat _ (@length _)
                        PeanoNat.Nat.lt_wf_0)); intros.
  - assert (A: vIn g a0 = true). { 
    assert (exists u v, path' g u v (l ++ a0 :: l')). apply path_cost_path'.
    destruct (path_cost g (l ++ a0 :: l')). exists b0. reflexivity. rewrite some_none_eq in H0.
    inversion H0.
    destruct_all. eapply path_in_graph. apply H1. solve_in. } 
    destruct l.
    + simpl in H0. destruct l'. rewrite A in H0. inversion H0; subst.
      exists #0. exists #0. simpl. rewrite A. split. rewrite H0. 
      rewrite Base.simpl_option_some_eq. destruct HEqLaw. apply Eq_refl.
      split. rewrite H0. rewrite Base.simpl_option_some_eq. destruct HEqLaw; apply Eq_refl.
      rewrite H0. rewrite Base.simpl_option_some_eq in H2. 
      destruct HorderedRing. assert (#0 + n == #0 + #0 = true). eapply rplus_eq. destruct HEqLaw. apply Eq_refl.
      destruct HEqLaw; rewrite Eq_sym. assumption. destruct HEqLaw; eapply Eq_trans. 
      rewrite Eq_sym. apply H2. destruct real_ring. destruct SORrt. rewrite Eq_sym. apply Radd_0_l.
      destruct (find_weight g n0 a0) eqn : F.
      destruct (path_cost g (n0 :: l')) eqn : P. inversion H0; subst.
      rewrite app_nil_l. exists #0. exists (b0 + b1). split. simpl. rewrite A. rewrite H2.
      destruct HEqLaw; apply Eq_refl. 
      remember (n0 :: l') as l''. split. simpl. rewrite Heql''. rewrite <- Heql''.
      rewrite F. rewrite P. rewrite H2. destruct HEqLaw; apply Eq_refl.
      rewrite H0. rewrite Base.simpl_option_some_eq in H2. destruct HEqLaw. eapply Eq_trans.
      rewrite Eq_sym. apply H2. destruct HorderedRing. destruct real_ring. destruct SORrt. rewrite Eq_sym. apply Radd_0_l.
      rewrite some_none_eq in H0. inversion H0. rewrite some_none_eq in H0. inversion H0.
      (*ring.*)
    + assert (forall l', (n0 :: l) ++ a0 :: l' = n0 :: (l ++ a0 :: l')) by (intros; reflexivity). rewrite H1 in H0.
      destruct l.
      * replace (n0 :: nil ++ a0 :: l') with (n0 :: a0 :: l') in H0 by reflexivity.
        remember (a0 :: l') as l''. simpl in H0. rewrite Heql'' in H0. rewrite <- Heql'' in H0.
        destruct (find_weight g a0 n0) eqn : F. destruct (path_cost g l'') eqn : P'.
        exists b0. exists b1. split. simpl. rewrite F. rewrite A.
        rewrite Base.simpl_option_some_eq. destruct HEqLaw. rewrite Eq_sym.
        destruct HorderedRing. destruct real_ring. destruct SORrt. eapply Eq_trans.
        rewrite Eq_sym. apply Radd_0_l. apply Radd_comm. 
        split. destruct HEqLaw; apply Eq_refl. rewrite Base.simpl_option_some_eq in H0.
        destruct HEqLaw; rewrite Eq_sym. assumption.
        rewrite some_none_eq in H0. inversion H0. rewrite some_none_eq in H0. inversion H0. 
      * remember ((n1 :: l) ++ a0 :: l') as l''. simpl in H0.
        simpl in Heql''. rewrite Heql'' in H0. rewrite <- Heql'' in H0. 
        destruct (find_weight g n1 n0) eqn : F. destruct (path_cost g l'') eqn : P.
        rewrite Heql'' in P. specialize (H ((n1 :: l))).
        assert (n1 :: l ++ a0 :: l' = (n1 :: l) ++ a0 :: l'). simpl. reflexivity.
        rewrite H2 in P. clear H2. 
        assert (
        (exists m p : b,
        path_cost g ((n1 :: l) ++ a0 :: nil) == Some m = true /\ path_cost g (a0 :: l') == Some p = true
         /\ b1 == _+_ m p = true)).
        apply H. simpl. omega. rewrite P. rewrite Base.simpl_option_some_eq. destruct HEqLaw; apply Eq_refl.
         destruct H2 as [m]. destruct H2 as [p]. destruct_all.
        exists (b0 + m). exists p. split. replace (((n0 :: n1 :: l) ++ a0 :: nil)) with
        (n0 :: (n1 :: l ++ a0 :: nil)) by reflexivity. remember (n1 :: l ++ a0 :: nil) as l0.
        simpl. rewrite Heql0. rewrite <- Heql0.  rewrite F. 
        assert (((n1 :: l) ++ a0 :: nil) = l0). subst. reflexivity. rewrite H5 in H2.
        destruct (path_cost g l0) eqn : O. rewrite Base.simpl_option_some_eq in H2.
        rewrite Base.simpl_option_some_eq. destruct HorderedRing. apply rplus_eq.
        destruct HEqLaw; apply Eq_refl. assumption. rewrite some_none_eq in H2. inversion H2.
        split. apply H3. rewrite Base.simpl_option_some_eq in H0. 
        destruct HorderedRing. destruct HEqLaw. eapply Eq_trans. rewrite Eq_sym. apply H0.
        eapply Eq_trans. assert (b0 + b1 == b0 + (m + p) = true). apply rplus_eq.
        apply Eq_refl. assumption. apply H5. destruct real_ring. destruct SORrt. apply Radd_assoc.
        rewrite some_none_eq in H0. inversion H0. rewrite some_none_eq in H0. inversion H0.
Qed. 

(*Back to not as general version*)
(*had paths of lenght n here*)

Section Min.

Variable A : Type.
Variable lt: A -> A -> Prop.
Variable eqb : A -> A -> Prop.
Variable lt_dec: forall x y, {lt x y} + {~lt x y}.
Variable eq_dec: forall x y, {eqb x y} + {~ eqb x y}.
Variable eqb_equiv: RelationClasses.Equivalence eqb.
Variable lt_trans: forall x y z, lt x y -> lt y z -> lt x z.
Variable lt_neq: forall x y, lt x y -> ~eqb x y.
Variable lt_total: forall x y, lt x y \/ eqb x y \/ lt y x.
Variable lt_antisym: forall x y, lt x y -> ~lt y x.
Variable lt_compat_r: forall x y z, lt x y -> eqb y z -> lt x z.

(*General function for finding minimum according to a decidable lt relation TODO: move this*)
Definition min_list (l: list A) : option A :=
  fold_right (fun x acc => match acc with
                           | Some y => if lt_dec x y then Some x else Some y
                           | None => Some x
                           end) None l.

(*Proof that this actually finds the minimum*)
Lemma min_list_empty: forall (l: list A) ,
  min_list l = None <-> l = nil.
Proof.
  intros. split; intros. unfold min_list in H. destruct l. reflexivity. simpl in H.
  destruct (fold_right
        (fun (x : A) (acc : option A) =>
         match acc with
         | Some y => if lt_dec x y then Some x else Some y
         | None => Some x
         end) None l). destruct (lt_dec a0 a1); inversion H. inversion H. subst. simpl. reflexivity.
Qed.

Lemma min_list_in: forall (l: list A) x,
  min_list l = Some x -> In x l.
Proof.
  intros. generalize dependent x. induction l; intros. simpl in H. inversion H. simpl in H.
  destruct (min_list l) eqn : M. destruct (lt_dec a0 a1). inversion H; subst. solve_in.
  inversion H. subst. right. apply IHl. reflexivity. inversion H; subst. solve_in.
Qed.

Lemma min_list_min: forall (l: list A) x,
  min_list l = Some x ->  forall y, ~eqb x y -> In y l -> lt x y.
Proof.
  intros. generalize dependent x. induction l; intros.
  - simpl in H. inversion H.
  - simpl in H. destruct (min_list l) eqn : M.
    + destruct (lt_dec a0 a1).
      * inversion H; subst. 
        simpl in H1. destruct H1. subst. destruct eqb_equiv. unfold RelationClasses.Reflexive in Equivalence_Reflexive.
        specialize (Equivalence_Reflexive y). contradiction. 
        destruct (eq_dec y a1). eapply lt_compat_r. apply l0. destruct eqb_equiv as [E1 E2 E3]. eapply E2.
        assumption.
        eapply lt_trans. apply l0. apply IHl. assumption. reflexivity.
        intro. destruct eqb_equiv as [E1 E2 E3]. apply E2 in H2. contradiction.
      * inversion H; subst. simpl in H1. destruct H1.
        subst. specialize (lt_total x y). destruct lt_total. assumption. destruct H1. contradiction.
        contradiction. apply IHl. assumption. reflexivity. assumption.
   + inversion H; subst. rewrite min_list_empty in M. subst. destruct H1. subst.
     destruct eqb_equiv as [E1 E2 E3]. pose proof (E1 y). contradiction. destruct H1.
Qed.

End Min.

Definition lt_weight_b (l1 l2: list Node) :=
  match (path_cost g l1, path_cost g l2) with
  | (Some b1, Some b2) => b1 < b2
  | (None, Some _) => true
  | (_, _) => false
  end.

Definition eq_weight_b (l1 l2: list Node) :=
  match (path_cost g l1, path_cost g l2) with
  | (Some b1, Some b2) => b1 == b2
  | (None, None) => true
  | (_, _) => false
  end.

Definition lt_weight l1 l2 := lt_weight_b l1 l2 = true.
Definition eq_weight l1 l2 := eq_weight_b l1 l2 = true.

(*Prove this is a valid ordering on paths*)
Lemma lt_weight_dec: forall x y, {lt_weight x y} + {~lt_weight x y}.
Proof.
  intros. unfold lt_weight. destruct (lt_weight_b x y). left. reflexivity. right. intro. inversion H.
Qed.
Lemma eq_weight_dec: forall x y, {eq_weight x y} + {~ eq_weight x y}.
Proof.
  intros. unfold eq_weight. destruct (eq_weight_b x y). left. reflexivity. right. intro. inversion H.
Qed.
Lemma eq_weight_equiv: RelationClasses.Equivalence eq_weight.
Proof.
  split. unfold RelationClasses.Reflexive. intros. unfold eq_weight. unfold eq_weight_b.
  destruct (path_cost g x). order b. reflexivity.
  unfold RelationClasses.Symmetric. intros. unfold eq_weight in *. unfold eq_weight_b in *.
  destruct (path_cost g x). destruct (path_cost g y). order b. inversion H. apply H.
  unfold RelationClasses.Transitive. intros. unfold eq_weight in *. unfold eq_weight_b in *.
  destruct (path_cost g x). destruct (path_cost g z). destruct (path_cost g y); order b.
  destruct (path_cost g y); order b. destruct (path_cost g z); destruct (path_cost g y); order b.
Qed. 
Lemma lt_weight_trans: forall x y z, lt_weight x y -> lt_weight y z -> lt_weight x z.
Proof.
  intros. unfold lt_weight in *. unfold lt_weight_b in *. destruct (path_cost g x); destruct (path_cost g y);
  destruct (path_cost g z); order b.
Qed.
Lemma lt_weight_neq: forall x y, lt_weight x y -> ~eq_weight x y.
Proof.
  intros. intro. unfold eq_weight in *. unfold lt_weight in *. unfold lt_weight_b in *. unfold eq_weight_b in H0.
  destruct (path_cost g x); destruct (path_cost g y); try(order b). 
Qed. 
Lemma lt_weight_total: forall x y, lt_weight x y \/ eq_weight x y \/ lt_weight y x.
Proof.
  intros. unfold lt_weight. unfold eq_weight. unfold lt_weight_b. unfold eq_weight_b. destruct (path_cost g x).
  destruct (path_cost g y). pose proof Ord_total. specialize (H b0 b1). destruct (b0 == b1) eqn : ?. order b.
  order b. right. right. reflexivity. destruct (path_cost g y). left. reflexivity. right. left. reflexivity.
Qed. 
Lemma lt_weight_antisym: forall x y, lt_weight x y -> ~lt_weight y x.
Proof.
  intros. intro. unfold lt_weight in *. unfold lt_weight_b in *. destruct (path_cost g x); destruct(path_cost g y);
  order b.
Qed.
Lemma lt_weight_compat_r: forall x y z, lt_weight x y -> eq_weight y z -> lt_weight x z.
Proof.
  intros. unfold lt_weight in *. unfold eq_weight in *. unfold lt_weight_b in *. unfold eq_weight_b in *.
  destruct (path_cost g x); destruct (path_cost g z); destruct (path_cost g y); order b.
Qed.

Definition min_weight_size_n u v n := min_list _ lt_weight lt_weight_dec (paths_of_length u v n).

Definition le_weight l l' := lt_weight l l' \/ eq_weight l l'.

(*Now, we will show that this really does find the minimum weight path of a given length*)
Lemma min_weight_size_correct: forall u v n l,
  min_weight_size_n u v n = Some l ->
  path' g u v l /\ length l = n /\ forall l', path' g u v l' /\ length l' = n -> le_weight l l' .
Proof.
  intros. pose proof (min_list_min _ _ _ lt_weight_dec eq_weight_dec eq_weight_equiv lt_weight_trans
  lt_weight_total lt_weight_compat_r _ _ H). assert (A:= H).
  eapply (min_list_in _ _ lt_weight_dec) in H.  apply paths_of_length_def in H. split. apply H. split.
  apply H. intros. destruct (eq_weight_dec l l'). right. assumption.
  left. apply H0. assumption. apply paths_of_length_def. apply H1.
Qed.

Lemma path_app': forall u v w l1 l2,
  path' g u v (l1 ++ w :: l2) <->
  path' g w v (l1 ++ w :: nil) /\ path' g u w (w :: l2).
Proof.
  intros. split; intros. generalize dependent v. revert l2. induction l1; intros.
  - simpl in H. inversion H; subst. split; simpl; assumption.
    split. simpl. constructor. eapply edges_valid in H6. apply H6.
    eapply p_multi. apply H5. assumption.
  - simpl in H. simpl. inversion H; subst. destruct l1; inversion H5.
    split. eapply p_multi. apply (IHl1 l2 v'). assumption. assumption. apply (IHl1 l2 v').
    assumption.
  - generalize dependent v. revert u. revert l2. induction l1; intros; destruct_all. simpl in *.
    inversion H. subst. assumption. subst. inversion H6. simpl in *.
    inversion H; subst. destruct l1; inversion H6.
    eapply p_multi. apply (IHl1 l2 u v'). split; assumption. assumption.
Qed. 
Require Import Proofs.GHC.Base.
(*Now we can find the shortest path for a given length. We want to show that if all the edge weights
  are nonnegative, if there is a shortest path of size > n, then there is a shortest path of size at most n*)
Lemma path_app_strong: forall u v w l1 l2 ,
  path' g u v (l1 ++ w :: l2) ->
  path' g w v (l1 ++ w :: nil)  /\ path' g u w (w :: l2) /\ (forall n m,
    path_cost g (l1 ++ w :: nil) == Some n = true -> 
    path_cost g (w :: l2) == Some m = true -> path_cost g (l1 ++ w :: l2) == Some (n+m) = true).
Proof.
  intros. assert (A:= H). apply path_app' in A. split. apply A. split. apply A.
  intros.  pose proof path_cost_app. pose proof path_cost_path'.
  assert (exists w', path_cost g (l1 ++ w :: l2) = Some w'). apply H3. exists u. exists v. assumption.
  destruct H4 as [w']. assert (B:=H4). assert (C :path_cost g (l1 ++ w :: l2) == Some w' = true).
  rewrite H4. rewrite Base.simpl_option_some_eq. destruct HEqLaw; apply Eq_refl.
  apply H2 in C. destruct C as [m']. destruct H5 as [p'].
  destruct_all. 
  assert (n == m' = true). rewrite <- Base.simpl_option_some_eq. destruct (EqLaws_option).
  eapply Eq_trans. rewrite Eq_sym. apply H0. apply H5. rewrite H4.
  assert (Some p' == Some m = true). destruct (EqLaws_option). eapply Eq_trans.
  rewrite Eq_sym. apply H6. apply H1. rewrite Base.simpl_option_some_eq in H11.
  rewrite Base.simpl_option_some_eq. destruct HorderedRing. destruct real_ring. destruct SORrt.
  destruct HEqLaw. eapply Eq_trans. apply H7. eapply Eq_trans. eapply SORplus_wd.
  rewrite Eq_sym. apply H10. apply H11. apply Eq_refl.
Qed. 

Lemma le_weight_trans: forall l1 l2 l3,
  le_weight l1 l2 ->
  le_weight l2 l3 ->
  le_weight l1 l3.
Proof.
  intros. unfold le_weight in *. unfold lt_weight in *. unfold eq_weight in *.
  destruct H; destruct H0.
  - left. unfold lt_weight_b in *. destruct (path_cost g l1) eqn : P.
    destruct (path_cost g l3) eqn : P'.
    destruct (path_cost g l2) eqn : P''.
    order b. inversion H. destruct (path_cost g l2) eqn : P''. inversion H0. inversion H.
    destruct (path_cost g l3). destruct (path_cost g l2). reflexivity. inversion H. destruct (path_cost g l2).
    inversion H0. inversion H.
  - left. unfold eq_weight_b in *. unfold lt_weight_b in *. destruct (path_cost g l1);
    destruct (path_cost g l2); destruct (path_cost g l3); try(reflexivity); try( order b).
  - left. unfold eq_weight_b in *. unfold lt_weight_b in *. destruct (path_cost g l1);
    destruct (path_cost g l2); destruct (path_cost g l3); try(reflexivity); try( order b).
  - right. unfold eq_weight_b in *. destruct (path_cost g l1);
    destruct (path_cost g l2); destruct (path_cost g l3); try(reflexivity); try( order b).
Qed.

Lemma path'_remove_cycle: forall u v w l1 l2 l3,
  path' g u v (l1 ++ w :: l2 ++ w :: l3) ->
  path' g u v (l1 ++ w :: l3).
Proof.
  intros. apply path_app' in H. destruct_all. replace (w :: l2 ++ w :: l3) with ((w :: l2) ++ w :: l3) in H0 by
  reflexivity. apply path_app' in H0. destruct_all.
  apply path_app'. simplify'.
Qed.


(*If there is a path, then there is a path with no duplicates, and this list is smaller*)
(*A very hard theorem to prove (the le_weight part), but an important property: if there is a path,
  there is a smaller weight path with no duplicates*)
Lemma path_no_dups_strong: forall u v l,
  path' g u v l ->
  exists l1, path' g u v l1 /\ NoDup l1 /\
  (forall x, In x l1 -> In x l) /\ le_weight l1 l. 
  Proof.
    intros. induction l using (well_founded_induction
                       (wf_inverse_image _ nat _ (@length _)
                          PeanoNat.Nat.lt_wf_0)).
    destruct (NoDup_dec (N.eq_dec) l).
    - destruct (In_dec N.eq_dec u l).
      + eapply in_split_app_fst in i. destruct_all. clear H2. subst.
        apply path_app_strong in H. destruct H. destruct H1 as [H1 A]. destruct x0.
        * exists (x ++ u :: nil). split. assumption. split. assumption. split. intros.
          assumption. unfold le_weight. right. destruct (eq_weight_equiv) as [E1 E2 E3]. apply E1.
        * specialize (H0 (x ++ u :: nil)). destruct H0 as [l]. 
          repeat(rewrite app_length). simpl. omega. assumption. 
          exists l. destruct_all. repeat(split; try(assumption)). intros.
          apply H3 in H5. apply in_app_or in H5. destruct H5; simpl in H5. apply in_or_app.
          left. assumption. destruct H5; subst. apply in_or_app. right. solve_in. destruct H5.
          unfold le_weight. 
          assert (exists w', path_cost g (x ++ u :: nil) = Some w'). apply path_cost_path'.
          exists u. exists v. assumption.
          assert (exists w', path_cost g (u :: n0 :: x0) = Some w'). apply path_cost_path'.
          exists u. exists u. assumption. destruct H5 as [n']. destruct H6 as [m'].
          assert (D : path_cost g (x ++ u :: nil) == Some n' = true). rewrite H5.
          rewrite Base.simpl_option_some_eq. destruct (HEqLaw); apply Eq_refl.
          assert (E: path_cost g (u :: n0 :: x0) == Some m' = true). rewrite H6.
          rewrite Base.simpl_option_some_eq. destruct (HEqLaw); apply Eq_refl.
          specialize (A _ _ D E). 
          unfold le_weight in H4. destruct H4. left. unfold lt_weight. unfold lt_weight_b.
          unfold lt_weight in H4. unfold lt_weight_b in H4. destruct (path_cost g l) eqn : P'.
          rewrite H5 in H4.            
           match goal with
                      | [H: _ |- match ?b with | Some _ => _ | None => _ end = _] => destruct b eqn : P
                      end.
          assert (Some b1 == Some (n' + m') = true). rewrite <- P. rewrite <- A. reflexivity.
          rewrite Base.simpl_option_some_eq in H7. 
          apply path_cost_nonneg in H6. destruct HorderedRing.
          pose proof (Rplus_le_lt_mono real_ring _ _ _ _ H6 H4).
          assert (b0 == #0 + b0 = true). assert (R:= real_ring). destruct real_ring. destruct SORrt. destruct HEqLaw; rewrite Eq_sym.
          apply Radd_0_l. assert (n' + m' == m' + n' = true). destruct real_ring. destruct SORrt. apply Radd_comm.
          rewrite <- rlt_eq. 2 : { destruct HEqLaw; rewrite Eq_sym. apply H9. }
          2 : { destruct (HEqLaw); rewrite Eq_sym. apply H7. } 
          rewrite <- rlt_eq. 2 : { destruct HEqLaw; apply Eq_refl. }  2 : { destruct HEqLaw; rewrite Eq_sym. apply H10. }
          apply H8. assert (None == Some (n' + m') = true). rewrite <- A.
          rewrite <- P. reflexivity. rewrite some_none_eq in H7. inversion H7.
           match goal with
                      | [H: _ |- match ?b with | Some _ => _ | None => _ end = _] => destruct b eqn : P
                      end. reflexivity.
           assert (None == Some (n' + m') = true). rewrite <- A. rewrite <- P. reflexivity.
          rewrite some_none_eq in H7. inversion H7.
          assert (B:= H6). apply path_cost_nonneg in B. destruct HorderedRing. apply (Rle_lt_eq real_ring) in B.
          destruct B. left. unfold lt_weight. unfold lt_weight_b. unfold eq_weight in H4.
          unfold eq_weight_b in H4. destruct (path_cost g l) eqn : P'.
          rewrite H5 in H4. 
           match goal with
                      | [H: _ |- match ?b with | Some _ => _ | None => _ end = _] => destruct b eqn : P
                      end.
          assert (Some b1 == Some (n' + m') = true). rewrite <- P. rewrite <- A. reflexivity.
          rewrite Base.simpl_option_some_eq in H8.
          assert (b0 < n' + m' = true <-> n' < n' + m' = true). apply rlt_eq. apply H4. destruct HEqLaw; apply Eq_refl.
          eapply rlt_eq. apply H4. apply H8. 
          assert (n' + #0 < n' + m' = true). apply (Rplus_lt_mono_l real_ring). assumption.
          destruct real_ring. destruct SORrt. eapply rlt_eq. 3 : { apply H10. }
          destruct HEqLaw. destruct HEqLaw. eapply Eq_trans. rewrite Eq_sym; apply Radd_0_l.
          apply Radd_comm. apply Eq_refl. assert (None == Some (_+_ n' m') = true).
          rewrite <- P. rewrite <- A. reflexivity. rewrite some_none_eq in H8. inversion H8.
          match goal with
                      | [H: _ |- match ?b with | Some _ => _ | None => _ end = _] => destruct b eqn : P
                      end.
          reflexivity. assert (None == Some (_+_ n' m') = true). rewrite <- P. rewrite <- A. reflexivity.
          rewrite some_none_eq in H8. inversion H8.
          right. unfold eq_weight in *. unfold eq_weight_b in *.
          destruct (path_cost g l) eqn : P'.
          match goal with
                      | [H: _ |- match ?b with | Some _ => _ | None => _ end = _] => destruct b eqn : P
                      end.
          rewrite H5 in H4.
          assert (Some b1 == Some (n' + m') = true). rewrite <- P. rewrite <- A. reflexivity.
          rewrite Base.simpl_option_some_eq in H8. destruct (HEqLaw). eapply Eq_trans.
          apply H4. destruct real_ring. destruct SORrt. eapply Eq_trans. rewrite Eq_sym.
          apply Radd_0_l. rewrite Eq_sym. eapply Eq_trans. apply H8.
          eapply Eq_trans. apply Radd_comm.  eapply rplus_eq. rewrite Eq_sym. assumption.
          apply Eq_refl. assert (None == Some (_+_ n' m') = true). rewrite <- P. rewrite <- A. reflexivity.
          rewrite some_none_eq in H8. inversion H8. 
          rewrite H5 in H4. inversion H4.
      * apply N.eq_dec.
    + (*ugh, have to do it again*)
       destruct (In_dec N.eq_dec v l).
        * eapply in_split_app_fst in i. destruct_all; subst. clear H2. apply path_app_strong in H.
          destruct H. destruct H1 as [H1 A]. destruct x.
          --  exists (v :: x0). split. assumption. split. simpl in n. assumption.
              simpl. split; intros. assumption. unfold le_weight. right. 
              destruct (eq_weight_equiv) as [E1 E2 E3]. apply E1.
          -- specialize (H0 (v :: x0 )). destruct H0 as [l]. 
             repeat(rewrite app_length). simpl.
             assert (forall m n, Nat.lt (S(n))  (S(m + S(n)))). intros. unfold Nat.lt. omega.
             apply H0. assumption. 
            exists l. destruct_all. repeat(split; try(assumption)). intros.
            apply H3 in H5. simpl in H5. apply in_or_app. destruct H5. subst. right. left. reflexivity.
            right. right. assumption.
(*prove le_trans, and then prove that l1 ++ l2*)
            assert (exists w', path_cost g ((n1 :: x) ++ v :: nil) = Some w'). apply path_cost_path'.
            exists v. exists v. assumption.
            assert (exists w', path_cost g (v :: x0) = Some w'). apply path_cost_path'.
            exists u. exists v. assumption. destruct H5 as [n']. destruct H6 as [m'].
            assert (D : path_cost g ((n1 :: x) ++ v :: nil) == Some n' = true). rewrite H5.
            rewrite Base.simpl_option_some_eq. destruct (HEqLaw); apply Eq_refl.
            assert (E: path_cost g (v :: x0) == Some m' = true). rewrite H6.
            rewrite Base.simpl_option_some_eq. destruct (HEqLaw); apply Eq_refl.
            specialize (A _ _ D E). eapply le_weight_trans. apply H4.
            unfold le_weight.
            unfold lt_weight. unfold eq_weight. unfold lt_weight_b. unfold eq_weight_b.
            rewrite H6. 
            match goal with
                        | [H: _ |- (match ?b with | Some _ => _ | None => _ end = _ \/ _ )] => destruct b eqn : P
                        end.
            assert (Some b0 == Some (n' + m') = true). rewrite <- A. rewrite <- P. reflexivity.
            rewrite Base.simpl_option_some_eq in H7. 
            eapply path_cost_nonneg in H5.
            pose proof (Rle_lt_eq real_ring #0 n').  apply H8 in H5. clear H8. destruct H5.
            ++ left. destruct HorderedRing. pose proof (Rplus_lt_mono_l real_ring m' b0 n'). simpl in H8.
               apply H8. eapply rlt_eq. destruct HEqLaw; rewrite Eq_sym. apply H7. destruct HEqLaw; apply Eq_refl.
              eapply rlt_eq. destruct real_ring. destruct SORrt. destruct HEqLaw; rewrite Eq_sym; apply Radd_0_l.
              destruct HEqLaw; apply Eq_refl. rewrite <- (Rplus_lt_mono_r real_ring). assumption.
            ++ right. destruct HEqLaw. eapply Eq_trans. destruct HorderedRing. destruct real_ring.
              destruct SORrt. rewrite Eq_sym; apply Radd_0_l. eapply Eq_trans. 2 : { rewrite Eq_sym.
              apply H7. } destruct HorderedRing. eapply rplus_eq. assumption. apply Eq_refl.
            ++ assert (None == Some (n' + m') = true). rewrite <- P. rewrite <- A. reflexivity.
               rewrite some_none_eq in H7. inversion H7.
        -- apply N.eq_dec.
      * exists l. simplify'. unfold le_weight. right. destruct (eq_weight_equiv) as [E1 E2 E3]; apply E1.
  - rewrite no_no_dup in n. destruct_all. subst. assert (A:= H). 
      apply path'_remove_cycle in H. specialize (H0 (x0 ++ x :: x2)). destruct H0 as [l].
      repeat(rewrite app_length; simpl). omega. apply H. exists l. simplify'. apply H2 in H3.
      apply in_app_or in H3. destruct H3. apply in_or_app. left. assumption. simpl in H3.
      destruct H3. subst. solve_in. solve_in. eapply le_weight_trans. apply H4.
      unfold le_weight. unfold lt_weight. unfold lt_weight_b. unfold eq_weight. unfold eq_weight_b.
      assert (exists n, path_cost g (x0 ++ x :: x2) = Some n). apply path_cost_path'. exists u.
      exists v. assumption. destruct H3 as [n']. rewrite H3. 
      assert (exists n, path_cost g (x0 ++ x :: x1 ++ x :: x2) = Some n). apply path_cost_path'.
      exists u. exists v. assumption. destruct H5 as [m']. rewrite H5.
      pose proof (path_app_strong).
      specialize (H6 _ _ _ _ _ H). destruct_all.
      assert (exists a', path_cost g (x0 ++ x :: nil) = Some a'). apply path_cost_path'.
      exists x. exists v. assumption. destruct H9 as [a'].
      assert (exists b', path_cost g (x :: x2) = Some b'). apply path_cost_path'. 
      exists u. exists x. assumption. destruct H10 as [b'].
      assert (path_cost g (x0 ++ x :: nil) == Some a' = true). rewrite H9. destruct HEqLaw. apply Eq_refl.
      assert (path_cost g (x :: x2) == Some b' = true). rewrite H10. destruct HEqLaw. apply Eq_refl.
      specialize (H8 _ _ H11 H12).
      assert (Some n' == Some (a' + b') = true). rewrite <- H3. rewrite <- H8. reflexivity.
      rewrite Base.simpl_option_some_eq in H13.
      remember (x1 ++ x :: x2) as l'. 
      assert (C:= A). apply path_app' in C. destruct C. clear H14. 
      assert (exists c', path_cost g (x :: l') = Some c'). eapply path_cost_path'.
      exists u. exists x. assumption. destruct H14 as [c'].
      pose proof (@path_app_strong _ _ _ _ _ A). destruct_all. clear H16. clear H17.
      assert (path_cost g (x :: l') == Some c' = true). rewrite H14. destruct HEqLaw; apply Eq_refl.
      specialize (H18 _ _ H11 H16).
      assert (Some m' == Some (a' + c') = true). rewrite <- H18. rewrite <- H5. reflexivity.
      rewrite Base.simpl_option_some_eq in H17. subst. remember (x :: x1) as l'.
      pose proof (path_app_strong u x x (x :: x1) x2 H15). destruct_all. simpl in H19.
      assert (exists d', path_cost g (x :: x1 ++ x :: nil) = Some d'). apply path_cost_path'.
      exists x. exists x. assumption. destruct H22 as [d']. 
      assert ( path_cost g (x :: x1 ++ x :: nil) == Some d' = true). rewrite H22.
      destruct HEqLaw; apply Eq_refl. specialize (H21 _ _ H23 H12). 
      assert (Some c' == Some (d' + b') = true). rewrite <- H21.
      rewrite <- H14. reflexivity. rewrite Base.simpl_option_some_eq in H24.
      eapply path_cost_nonneg in H22.
      pose proof (Rle_lt_eq real_ring #0 d'). simpl in H25. apply H25 in H22. clear H25.
      destruct HorderedRing.
      destruct H22. left. eapply rlt_eq. apply H13. apply H17. 
      rewrite <- (Rplus_lt_mono_l real_ring). eapply rlt_eq. assert (b' == #0 + b' = true).
      destruct real_ring. destruct SORrt. destruct HEqLaw; rewrite Eq_sym; apply Radd_0_l.
      apply H25. apply H24. rewrite <- (Rplus_lt_mono_r real_ring). assumption. 
      right. destruct HEqLaw. eapply Eq_trans. apply H13. eapply Eq_trans. 2 : {  rewrite <- Eq_sym.
      apply H17. } apply rplus_eq. apply Eq_refl. eapply Eq_trans. 2 : { rewrite Eq_sym. apply H24. }
      eapply Eq_trans. assert (b' == #0 + b' = true). destruct real_ring. destruct SORrt.
      rewrite Eq_sym. apply Radd_0_l. apply H25. apply rplus_eq. assumption. apply Eq_refl.
      apply N.eq_dec.
Qed.

(*Finally!!!!!*)
 
(*If there is a path, then there is a path at most as large as the number of vertices in the graph (because
  there is a path with no duplicates and every vertex is in the graph*)

Lemma shortest_path_leq_n: forall u v l,
  path' g u v l ->
  exists l', path' g u v l' /\ Nat.le (length l') (length (nodeList g)) /\ le_weight l' l.
Proof.
  intros. apply path_no_dups_strong in H. destruct_all.
  assert (forall a, In a x -> In a (nodeList g)). intros. apply (path_in_graph _ _ _ a0) in H.
  unfold vIn in H. unfold mem in H.
  destruct_if. assumption. inversion H. assumption. exists x. split.
  assumption. split. eapply NoDup_incl_length. assumption. unfold incl. assumption.
  assumption.
Qed.

Definition find_shortest_wpath (u v : Node) : option (list Node) :=
  fold_right (fun x acc => match (min_weight_size_n u v x) with
                            | None => match acc with
                                        | None => None
                                        | Some l => Some l
                                        end
                            | Some l => match acc with
                                        | None => Some l
                                        | Some l' => if lt_weight_b l l' then Some l else Some l'
                                        end
                            end) None (List.seq 0 (natNodes g + 1)).

Ltac destruct_option H':= match goal with
  | [H: match ?x with | Some l' => _ | None => _  end = _ |- _] => destruct ?x eqn : H'
  end.

Lemma shortest_none_helper: forall l u v,
  (fold_right
  (fun (x : nat) (acc : option (list Node)) =>
   match min_weight_size_n u v x with
   | Some l =>
       match acc with
       | Some l' => if lt_weight_b l l' then Some l else Some l'
       | None => Some l
       end
   | None => match acc with
             | Some l => Some l
             | None => None
             end
   end) None l) = None <-> (forall x, In x l -> min_weight_size_n u v x = None).
Proof.
  intros. 
  induction l; simpl; split; intros.
  - destruct H0.
  - reflexivity.
  -  destruct (min_weight_size_n u v a0) eqn : M.
    destruct ( fold_right
        (fun (x : nat) (acc : option (list Node)) =>
         match min_weight_size_n u v x with
         | Some l =>
             match acc with
             | Some l' => if lt_weight_b l l' then Some l else Some l'
             | None => Some l
             end
         | None => match acc with
                   | Some l => Some l
                   | None => None
                   end
         end) None l). destruct (lt_weight_b l0 l1 ); inversion H. inversion H.
    destruct ( fold_right
        (fun (x : nat) (acc : option (list Node)) =>
         match min_weight_size_n u v x with
         | Some l =>
             match acc with
             | Some l' => if lt_weight_b l l' then Some l else Some l'
             | None => Some l
             end
         | None => match acc with
                   | Some l => Some l
                   | None => None
                   end
         end) None l ) eqn : H'. inversion H. destruct H0. subst. apply M. apply IHl. reflexivity. assumption.
  - destruct (min_weight_size_n u v a0) eqn : ?.
    rewrite H in Heqo. inversion Heqo. left. reflexivity.
    destruct (fold_right
    (fun (x : nat) (acc : option (list Node)) =>
     match min_weight_size_n u v x with
     | Some l0 =>
         match acc with
         | Some l' => if lt_weight_b l0 l' then Some l0 else Some l'
         | None => Some l0
         end
     | None => match acc with
               | Some l0 => Some l0
               | None => None
               end
     end) None l) eqn : ?. apply IHl. intros. apply H. right. assumption. reflexivity.
Qed.

Lemma find_shortest_wpath_none: forall u v,
  find_shortest_wpath u v = None <-> (forall l, ~path' g u v l).
Proof.
  intros. unfold find_shortest_wpath. assert (H:=  shortest_none_helper).
  rewrite H. clear H. split; intros.
  - intro. pose proof (shortest_path_leq_n _ _ _ H0). destruct H1. destruct H1.
    destruct H2.  assert (In (length x) (List.seq 0 (natNodes g + 1))). apply in_seq.
    split. omega. simpl. unfold Nat.le in H2.  unfold natNodes. rewrite noNodes_def.
    unfold nodeList in H2. unfold ulabNodes in H2. rewrite map_length in H2. 
    assert (forall n m, Nat.le n m -> Nat.lt n (m + 1)). intros. unfold Nat.lt.
    unfold Nat.le in H4. omega. apply H4. apply H2. apply H in H4.
    unfold min_weight_size_n in H4. rewrite min_list_empty in H4.
    pose proof (paths_of_length_appear u v (length x) x). 
    rewrite H4 in H5. simpl in H5. apply H5. split. assumption. reflexivity.
  - destruct (min_weight_size_n u v x) eqn : M.
    + apply min_weight_size_correct in M. destruct_all. exfalso. apply (H l). assumption.
    + reflexivity.
Qed.

(*The following lemma proves finally that this function actually computes the shortest path*)
Definition shortest_wpath u v l :=
  path' g u v l /\ forall l', path' g u v l' -> le_weight l l'.

Lemma find_shortest_wpath_correct: forall u v l,
  find_shortest_wpath u v = Some l -> shortest_wpath u v l. 
Proof.
  intros. unfold find_shortest_wpath in H. unfold shortest_wpath.
  assert (forall l' l'' u' v',
   (fold_right
      (fun (x : nat) (acc : option (list Node)) =>
       match min_weight_size_n u' v' x with
       | Some l => match acc with
                   | Some l' => if lt_weight_b l l' then Some l else Some l'
                   | None => Some l
                   end
       | None => match acc with
                 | Some l => Some l
                 | None => None
                 end
       end) None l') = Some l'' ->
      path' g u' v' l'' /\ (forall x p, In x l' -> path' g u' v' p -> length p = x -> le_weight l'' p)). { intros l'. induction l'; intros; simpl in H0.
  - inversion H0.
  - destruct (min_weight_size_n u' v' a0) eqn : M.
    + destruct (fold_right
             (fun (x : nat) (acc : option (list Node)) =>
              match min_weight_size_n u' v' x with
              | Some l0 =>
                  match acc with
                  | Some l' => if lt_weight_b l0 l' then Some l0 else Some l'
                  | None => Some l0
                  end
              | None => match acc with
                        | Some l0 => Some l0
                        | None => None
                        end
              end) None l') eqn : F.
    destruct (lt_weight_b l0 l1) eqn : L; inversion H0; subst.
    * assert (A:= M). apply min_weight_size_correct in M. destruct_all. split. assumption.
      intros. destruct H4. subst. apply H3. split; assumption. subst.
      eapply le_weight_trans. left. apply L. eapply IHl'. apply F. apply H4.
      assumption. reflexivity.
    * apply IHl' in F. destruct_all. split. assumption. intros. subst. simpl in H3.
      destruct H3. subst. apply min_weight_size_correct in M. destruct_all.
      assert (le_weight l'' l0). unfold le_weight. pose proof (lt_weight_total l'' l0).
      destruct H7. left. assumption. destruct H7. right. assumption. unfold lt_weight in H7.
      rewrite H7 in L. inversion L. eapply le_weight_trans. apply H7. apply H6.
      split. assumption. reflexivity. eapply H2. apply H3. assumption. reflexivity.
    * inversion H0; subst. rewrite shortest_none_helper in F. assert (A:= M).
      apply min_weight_size_correct in M. destruct_all. split. apply H1.
      intros. subst. simpl in H4. destruct H4.
      apply H3. split. assumption. symmetry. assumption. apply F in H2.
      unfold min_weight_size_n in H2. rewrite min_list_empty in H2.
      pose proof (paths_of_length_appear u' v' (length p) p). rewrite H2 in H4.
      simpl in H4. exfalso. apply H4. split. assumption. reflexivity.
    + destruct (fold_right
         (fun (x : nat) (acc : option (list Node)) =>
          match min_weight_size_n u' v' x with
          | Some l =>
              match acc with
              | Some l' => if lt_weight_b l l' then Some l else Some l'
              | None => Some l
              end
          | None => match acc with
                    | Some l => Some l
                    | None => None
                    end
          end) None l') eqn : F.
      * apply IHl' in F. inversion H0; subst. destruct_all. split. assumption.
        intros. simpl in H3. destruct H3. subst. unfold min_weight_size_n in M.
        rewrite min_list_empty in M. exfalso. 
        pose proof (paths_of_length_appear u' v' (length p) p). rewrite M in H3.
        simpl in H3. apply H3. split. assumption. reflexivity. eapply H2. apply H3.
        assumption. assumption.
      * inversion H0. }
  apply H0 in H. clear H0. destruct_all. split. assumption.
  intros. pose proof (shortest_path_leq_n _ _ _ H1). destruct_all. eapply le_weight_trans.
  2 : { apply H4. } eapply H0. 3 : { reflexivity. } rewrite in_seq. split. omega.
  simpl. assert (forall n m, Nat.le n m -> Nat.lt n (m+1)). intros. unfold Nat.lt.
  unfold Nat.le in H5. omega. apply H5. unfold natNodes. rewrite noNodes_def.
  unfold nodeList in H3. unfold ulabNodes in H3. rewrite map_length in H3. apply H3.
  assumption.
Qed.

(*2 other lemmas that are good to know - and actually let me use this information in proofs*)
Lemma path_implies_shortest: forall u v l,
  path' g u v l ->
  exists l', shortest_wpath u v l'.
Proof.
  intros. unfold shortest_wpath. destruct (find_shortest_wpath u v) eqn : D.
  - exists l0. apply find_shortest_wpath_correct. apply D.
  - rewrite find_shortest_wpath_none in D. specialize (D l). contradiction.
Qed.

Lemma path'_decidable: forall u v,
  {exists l, path' g u v l} + {~exists l, path' g u v l}.
Proof.
  intros. destruct (find_shortest_wpath u v) eqn : D.
  - left. exists l. apply find_shortest_wpath_correct in D. apply D.
  - right. intro. destruct H. rewrite find_shortest_wpath_none in D. specialize (D x). contradiction.
Qed.

Lemma shortest_wpath_same_weight: forall u v l l',
  shortest_wpath u v l ->
  path' g u v l' ->
  eq_weight l l' ->
  shortest_wpath u v l'.
Proof.
  intros. unfold shortest_wpath in *. split. assumption. intros. destruct_all.
  eapply le_weight_trans. unfold le_weight.  right. destruct (eq_weight_equiv). apply Equivalence_Symmetric.
  apply H1. apply H3. assumption.
Qed. 

Lemma shortest_path_refl: forall v,
  vIn g v = true ->
  shortest_wpath v v (v :: nil).
Proof.
  intros. unfold shortest_wpath. split. constructor. assumption. intros. unfold le_weight.
  unfold lt_weight. unfold lt_weight_b. unfold eq_weight. unfold eq_weight_b. simpl. rewrite H.
  pose proof (path_cost_path' l').
  assert (exists w : b, path_cost g l' = Some w). apply H1. exists v. exists v. assumption.
  destruct H2 as [w]. rewrite H2. apply path_cost_nonneg in H2.
  destruct HOrdLaw.
  assert (O := H2). destruct (w <= #0) eqn : R. right. apply Ord_antisym. assumption. assumption.
  left. rewrite Ord_lt_le. rewrite R. reflexivity.
Qed.

Definition sp_distance (g: gr a b) (o : option (list Node)) : option b :=
  match o with
  | None => None
  | Some l => path_cost g l
  end.

(*[sp_distance] unique*)
Lemma sp_distance_unique: forall u v l1 l2,
  shortest_wpath u v l1 ->
  shortest_wpath u v l2 ->
  sp_distance g (Some l1) == sp_distance g (Some l2) = true.
Proof.
  intros. unfold sp_distance. destruct (path_cost g l1 == path_cost g l2) eqn : E.
  reflexivity. assert (forall x y, x == y = false -> x < y = true \/ y < x = true). intros.
  destruct HOrdLaw. specialize (Ord_total x y). destruct Ord_total.
  destruct (y <= x) eqn : O. rewrite Ord_antisym in H1. inversion H1. assumption. assumption.
  left. rewrite Ord_lt_le. rewrite O. reflexivity. destruct (x <= y) eqn : O.
  rewrite Ord_antisym in H1. inversion H1. assumption. assumption.
  right. rewrite Ord_lt_le. rewrite O. reflexivity.
  pose proof path_cost_path'. assert (exists w : b, path_cost g l1 = Some w). apply H2.
  exists u. exists v. unfold shortest_wpath in H. apply H.
  assert (exists w : b, path_cost g l2 = Some w). apply H2. exists u. exists v.
  unfold shortest_wpath in H0. apply H0. clear H2. destruct H3 as [w1]. destruct H4 as [w2].
  rewrite H2 in E. rewrite H3 in E. rewrite Base.simpl_option_some_eq in E. apply H1 in E.
  clear H1. unfold shortest_wpath in *. destruct_all. destruct E.
  - specialize (H1 l1 H). unfold le_weight in H1. unfold lt_weight in H1.
    unfold eq_weight in H1. unfold lt_weight_b in H1. unfold eq_weight_b in H1. rewrite H2 in H1. rewrite H3 in H1.
    order b.
  - specialize (H4 l2 H0). unfold le_weight in H4. unfold lt_weight in H4.
    unfold eq_weight in H4. unfold lt_weight_b in H4. unfold eq_weight_b in H4. rewrite H2 in H4. rewrite H3 in H4.
    order b.
Qed.

Lemma path_start: forall u v l,
  path' g u v l -> exists l1, l = l1 ++ (u :: nil).
Proof.
  intros. induction H.
  - exists nil. reflexivity.
  - specialize (IHpath' Hsimple HNonneg). destruct_all. exists (v :: x). simpl. rewrite H1. reflexivity.
Qed.

(*Lemma 24.1 in CLRS*)
Lemma shortest_path_subpath: forall u v v' l1 l2,
  shortest_wpath u v (l1 ++ v' :: l2) ->
  shortest_wpath u v' (v' :: l2).
Proof.
  intros. unfold shortest_wpath in *. destruct_all. split. apply path_app' in H. apply H.
  intros. pose proof (lt_weight_total (v' :: l2) l'). unfold le_weight.
  destruct H2. simplify'. destruct H2. simplify'. destruct l'. inversion H1.
  assert (n = v'). rewrite path'_WPath in H1. destruct H1. eapply hd_path in H1. subst. reflexivity.
  subst. 
  assert (path' g u v (l1 ++ v' :: l')). apply path_app' in H. rewrite path_app'. split.
  apply H. assumption. apply H0 in H3.
  assert (exists w, path_cost g (l1 ++ v' :: l2) = Some w). apply path_cost_path'. exists u. exists v.
  assumption. assert (exists w, path_cost g (l1 ++ v' :: l') = Some w). apply path_cost_path'.
  exists u. exists v. apply path_app' in H. apply path_app'. split. apply H. assumption.
  destruct H4 as [w1]. destruct H5 as [w2].
  assert (path_cost g (l1 ++ v' :: l2) == Some w1 = true). rewrite H4. 
  rewrite simpl_option_some_eq. destruct HEqLaw as [E1 E2 E3]. apply E1.
  assert (path_cost g (l1 ++ v' :: l') == Some w2 = true). rewrite H5.
  rewrite simpl_option_some_eq. destruct HEqLaw as [E1 E2 E3]. apply E1.
  pose proof (path_cost_app _ _ _ _ H6). 
  pose proof (path_cost_app _ _ _ _ H7).
  destruct H8 as [m1]. destruct H8 as [p1].
  destruct H9 as [m2]. destruct H9 as [p2]. destruct_all.
  unfold le_weight in H3. unfold lt_weight in *. unfold eq_weight in *. exfalso.
  unfold lt_weight_b in *. unfold eq_weight_b in *. rewrite H4 in H3. rewrite H5 in H3.
  assert (w1 <= w2 = true) by (order b). clear H3.
  (*Lots of annoying stuff with ordering and addition because ring doesn't work*)
  destruct (path_cost g (v' :: l')). 
  destruct (path_cost g (v' :: l2)).
  rewrite simpl_option_some_eq in H10.
  rewrite simpl_option_some_eq in H12.
  destruct HorderedRing. destruct (HEqLaw) as [E1 E2 E3].
  assert (m1 + p1 <= m2 + p2 = true). eapply rle_eq. rewrite E2. apply H13.
  rewrite E2. apply H11. assumption.
  assert (Some m1 == Some m2 = true).   destruct (EqLaws_option). 
  eapply Eq_trans. rewrite Eq_sym. apply H8.
  apply H9. rewrite simpl_option_some_eq in H15.
  assert (p1 <= p2 = true).
  assert (m1 + p1 <= m1 + p2 = true). eapply rle_eq. apply E1.
  eapply rplus_eq. apply H15. apply E1. apply H3.
  apply (Rplus_le_mono_l real_ring) in H16. apply H16.
  assert (b1 <= b0 = true). eapply rle_eq. apply H12. apply H10.
  assumption. destruct real_ring.
  apply SORlt_le_neq in H2. destruct_all.
  eapply SORle_antisymm in H17. rewrite H17 in H18. contradiction. assumption.
  rewrite some_none_eq in H12. inversion H12. rewrite some_none_eq in H10. inversion H10.
Qed.


End Weighted.
End Path.

 
