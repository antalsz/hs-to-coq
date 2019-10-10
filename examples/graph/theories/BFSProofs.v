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

Require Import CoLoR.Util.Relation.Lexico.
Require Import CoLoR.Util.Relation.SN.

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
  match (Graph.match_ v g) with | (None, _) => false | _ => true end.

Definition in_graph (g : gr a b) (p: Graph.Path) : bool := 
  match p with
  | nil => false
  | v :: xs => vertex_in g v  end. 

Definition notIn_graph g := fun x => negb (in_graph g x). 

Inductive bfs_step : state -> state -> Prop :=
  | bfs_find: forall g l r (p: Graph.Path) (q' : list Graph.Path) c g' (v : Graph.Node) tl,
    pop_list l (notIn_graph g) = p :: q' ->
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

Definition natNodes (g : gr a b) := (BinInt.Z.abs_nat(Graph.noNodes g)).

Definition bfs_measure s := natNodes (get_graph s).

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
    let qnew := pop_list q (notIn_graph g) in
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
  null (pop_list (get_queue s) (notIn_graph (get_graph s))) || (Graph.isEmpty (get_graph s)).

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
     pose proof (pop_list_split l (notIn_graph g)). destruct H3 as [l']. destruct H3.
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
  destruct (pop_list q (notIn_graph g)) eqn : Q. inversion H0. 
  simpl in H0. 
  (*prove p = nil case impossible*)
  destruct p eqn : P. pose proof (pop_list_split q (notIn_graph g)). destruct H2 as [l'].
  destruct H2. rewrite Q in H2.  pose proof (queue_path_nonempty (g, q, r) v). 
  apply H4 in H. simpl in H. rewrite <- H2 in H. exfalso. apply H. apply in_or_app. right.
  simpl. left. reflexivity. destruct (match_ n g) eqn : M. assert (Q' := Q).
  apply pop_split_fst in Q. unfold notIn_graph in Q. simpl in Q. unfold vertex_in in Q. rewrite M in Q.
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

(*Well formed lexicographic measure - maybe put in own section*)


Definition natNodes_lt x y := natNodes x < natNodes y.
Definition natNodes_eq x y := natNodes x = natNodes y.
Definition list_length_lt {a} (x y : list a) := length x < length y.
Definition queue_length_lt  {a} (x y : Queue a) := list_length_lt (toList _ x) (toList _ y).

Definition bf_measure_list := 
  transp (lex (transp natNodes_lt) natNodes_eq (transp  (@list_length_lt Path))).

Definition bf_measure_queue :=
  transp (lex (transp natNodes_lt) natNodes_eq (transp (@queue_length_lt Path))).

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


Lemma wf_bf_measure_list : WF (transp bf_measure_list).
Proof.
  eapply WF_lex.
  - apply wf_transp_WF. unfold transp. 
    pose proof (f_nat_lt_wf (natNodes)). unfold f_nat_lt in H. unfold natNodes_lt. apply H.
  - apply wf_transp_WF. unfold transp.
    pose proof (f_nat_lt_wf (@length Path)). unfold f_nat_lt in H. unfold natNodes_lt. apply H.
  - unfold Transitive. intros. unfold natNodes_eq in *. omega.
  - unfold inclusion. unfold RelUtil.compose. intros.
    unfold transp in *. unfold natNodes_lt in *. unfold natNodes_eq in *. destruct H. omega.
Qed.

Lemma well_founded_bf_measure_list: well_founded (bf_measure_list).
Proof.
  apply WF_transp_wf. apply wf_bf_measure_list.
Qed.

Lemma wf_bf_measure_queue : WF (transp bf_measure_queue).
Proof.
  eapply WF_lex.
  - apply wf_transp_WF. unfold transp. 
    pose proof (f_nat_lt_wf (natNodes)). unfold f_nat_lt in H. unfold natNodes_lt. apply H.
  - apply wf_transp_WF. unfold transp.
    pose proof (f_nat_lt_wf (fun x => length (toList Path x))). unfold f_nat_lt in H. unfold queue_length_lt.
    unfold list_length_lt. apply H.
  - unfold Transitive. intros. unfold natNodes_eq in *. omega.
  - unfold inclusion. unfold RelUtil.compose. intros.
    unfold transp in *. unfold natNodes_lt in *. unfold natNodes_eq in *. destruct H. omega.
Qed.

Lemma well_founded_bf_measure_queue: well_founded (bf_measure_queue).
Proof.
  apply WF_transp_wf. apply wf_bf_measure_queue.
Qed.


Instance need_this_for_equations : WellFounded bf_measure_list.
Proof.
  unfold WellFounded. apply well_founded_bf_measure_list.
Defined.


Axiom match_None1: forall (g: gr a b) v g',
  match_ v g = (None, g') -> Graph.Desc g' (noNodes g) (fun x => vIn g x) (fun x y => eIn g x y).

Axiom match_None2: forall (g: gr a b) v,
  (exists g', match_ v g = (None, g')) <-> ~vIn g v.

(*should prove this from others ,also may have to change edge thing because of multiple edges*)
Axiom match_None3: forall (g: gr a b) v g',
  match_ v g = (None, g') -> noNodes g = noNodes g'.

Lemma match_none_size: forall g v g',
  match_ v g = (None, g') -> natNodes g = natNodes g'.
Proof.
  intros. unfold natNodes. erewrite match_None3. reflexivity. apply H.
Qed. 

Equations bf_list (x : (gr a b) * (list Path)) : RootPath.RTree by wf x bf_measure_list :=
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

(*Defn*)
Print bf_list_unfold.
Check bf_list_unfold_eq.
(*could be useful*)
Check bf_list_elim.




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
  induction (x) as [y IH] using (well_founded_induction well_founded_bf_measure_queue). 
  destruct y as [g q]. simpl. unfold deferredFix2 in *. unfold curry in *.
  rewrite (deferredFix_eq_on _ (fun x => True) ( bf_measure_queue )).
  - simpl. destruct (toList _ q) eqn : Q.  
    + simpl. assert (queueEmpty q = true). rewrite toList_queueEmpty. assumption. rewrite H.
      reflexivity.
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

(*Equivalence*)

(*Steps:
1. show we can unwrap BFS if first in queue not in graph
2. show we can unwrap to pop_list
3. equivalence of lists and queues
4. then can unwarp deferredFix and prove termination
5. need something about the paths, tail vs regular recursive*)

(*Next step: try to prove this is equivalent to Haskell BFS, then can just work with this version/ valid states*)
End Ind.