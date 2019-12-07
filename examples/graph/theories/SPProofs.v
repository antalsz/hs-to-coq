Require Import Data.Graph.Inductive.Query.SP.
Require Import Lex.
Require Import Path.
Require Import Data.Graph.Inductive.Internal.Heap.
Require Import Omega.
Require Import Equations.Equations.
Require Import Coq.Bool.Bool.
Require Import Data.Graph.Inductive.Graph.
Require Import Coq.Lists.List.
Require Import DeferredFix.
Require Import GHC.Num.
Import GHC.Num.Notations.
Require Import HeapProofs.
Require Import OrdTactic.
Require Import RealRing.
Require Import Helper.
Require Import Lex.

Require Import Coq.Wellfounded.Inverse_Image.

(* Inductive relation*)
Section Ind.

Context {a : Type} {b : Type} { gr : Type -> Type -> Type} {Hgraph : Graph.Graph gr} {Hlaw : Graph.LawfulGraph gr}
{Hnum: GHC.Num.Num b} {Heq: Base.Eq_ b} {HOrd: Base.Ord b} {Hreal: @GHC.Real.Real b Hnum Heq HOrd}
{Heq': Base.Eq_ a} {HOrd': Base.Ord a} {Herr: Err.Default (b)}{Hlaw2 : (@WeightedGraphs.LawfulWGraph a b gr Hgraph) } {HEqLaw: Base.EqLaws b} {HOrdLaw: @OrdLaws b Heq HOrd HEqLaw}
{HorderedRing: @RealRing b Heq HOrd HEqLaw Hnum Hreal}.

Program Instance path_default : Err.Default (Graph.LPath b).
Next Obligation.
constructor. apply nil.
Defined.

(*Well formed lexicographic measure*)
Definition natNodes := (@Path.natNodes a b gr Hgraph).

Definition natNodes_lt (x y : gr a b) := natNodes x < natNodes y.

Definition natNodes_eq (x y : gr a b) := natNodes x = natNodes y.
(*Definition list_length_lt {a b} (x y : list a) := size x < size y*)
Definition heap_length_lt {A} (x y : Heap b A) := (Heap.size x) < (Heap.size y).
 (*list_lsize (toList x) (toList y).*)

Definition bf_measure_heap {A} :=
  lex _ _ (natNodes_lt) natNodes_eq (@heap_length_lt A).

Lemma well_founded_bf_measure_heap : forall A,  well_founded (@bf_measure_heap A).
Proof.
  intros. eapply WF_lex.
  - apply f_nat_lt_wf.
  - apply f_nat_lt_wf.
  - unfold RelationClasses.Transitive. intros. unfold natNodes_eq in *; omega.
  - intros. unfold natNodes_eq in *. unfold natNodes_lt in *. destruct H. destruct H.
    omega.
  - unfold RelationClasses.Symmetric. intros. unfold natNodes_eq in *. omega.
Qed. 

(*A few properties of this relation*)
Lemma measure_trans: forall {a} x y z,
  @bf_measure_heap a x y ->
  bf_measure_heap y z ->
  bf_measure_heap x z.
Proof.
  intros. unfold bf_measure_heap in *.
  inversion H; subst.
  - inversion H0; subst.
    + apply lex1. unfold natNodes_lt in *. omega.
    + apply lex1. unfold natNodes_lt in *. unfold natNodes_eq in H4. omega.
  - inversion H0; subst.
    + apply lex1. unfold natNodes_lt in *. unfold natNodes_eq in H1. omega.
    + apply lex2. unfold natNodes_eq in *. omega. unfold heap_length_lt in *. omega.
Qed. 

Lemma measure_antisym: forall {a} x y,
  @bf_measure_heap a x y ->
  ~bf_measure_heap y x.
Proof.
  intros. intro. unfold bf_measure_heap in *. 
  inversion H; inversion H0; subst; unfold natNodes_lt in *; unfold natNodes_eq in *.
  - inversion H5; subst. inversion H6; subst. omega.
  - inversion H6; subst. inversion H7; subst. omega.
  - inversion H6; subst. inversion H7; subst. omega.
  - inversion H7; subst. inversion H8; subst.
    unfold heap_length_lt in *. omega.
Qed.

Lemma measure_antirefl: forall {a} x,
  ~@bf_measure_heap a x x.
Proof.
  intros. intro. inversion H; subst; unfold natNodes_lt in *; unfold heap_length_lt in *; try(omega).
Qed.

Instance need_this_for_equations : forall A, WellFounded (@bf_measure_heap A).
Proof.
  unfold WellFounded. apply well_founded_bf_measure_heap.
Defined.


(*TODO: Dont copy this*)
Lemma match_none_size: forall g v g',
  match_ v g = (None, g') -> natNodes g = natNodes g'.
Proof.
  intros. pose proof (match_remain_none g). erewrite H0. reflexivity. apply H.
Qed.  

Definition state : Type := (gr a b) * (Heap b Node) * (list (b * Node)).

Definition get_graph (s: state) :=
  match s with
  | (g, _, _) => g
  end.

Definition get_heap (s: state) :=
  match s with
  | (_, h, _) => h
end.

Definition get_dists (s: state) :=
  match s with
  | (_, _, p) => p
  end.

(*TODO: remove v*)
Definition expand_dist (d : b) (v : Node) (c: Context a b) :=
  match c with
  | (_, _, _, s) => map (fun x : b * Node => let (l,v') := x in unit (_GHC.Num.+_ l d) v') s
  end.

(*How to step from 1 state to another. The inductive definiction makes it easier to use as
  an assumption in proofs*)
Inductive sp_step : state -> state -> Prop :=
  | sp_find: forall (g: gr a b) (v : Node) (c: Context a b) (g': gr a b) 
      (d: b) (h' h : Heap b Node) (p : list (b * Node)),
      isEmpty g = false ->
      match_ v g = (Some c, g') ->
      splitMinT h = Some ((d,v), h') ->
      sp_step (g, h, p) (g', mergeAll (h' :: expand_dist d v c), p ++ (d,v) :: nil)
  | sp_skip : forall (g: gr a b) (v: Node) (g': gr a b) (h h' : Heap b Node)
     (p: list (b * Node)) d,
      isEmpty g = false ->
      match_ v g = (None, g') ->
      splitMinT h = Some ((d,v), h') ->
      sp_step (g, h, p) (g', h', p).


Definition start (g : gr a b) (v: Graph.Node) : state := (g, (Heap.unit #0 v), nil).

(*A valid state is any state that can be reached from the start state.*)
Inductive valid : state -> (gr a b) -> Node -> Prop :=
  | v_start : forall g v, vIn g v = true -> valid (start g v) g v
  | v_step : forall s s' v g, valid s' g v -> sp_step s' s -> valid s g v.

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

Definition sp_multi (s1 s2 : state):= multi (sp_step) s1 s2.

Lemma multi_valid: forall s1 s2 g v,
  valid s1 g v ->
  sp_multi s1 s2 ->
  valid s2 g v.
Proof.
  intros. induction H0. assumption. apply IHmulti. eapply v_step. apply H. assumption.
Qed.

Definition done (s: state) := Heap.isEmpty (get_heap s) || isEmpty (get_graph s).

(*Lots is basically the same as BFS, TODO see if I can improve that*)
Section Multi.

(*if we step from s to s', s' < s*)
Lemma measure_step: forall s s',
  sp_step s s' ->
  bf_measure_heap (get_heap s', get_graph s') (get_heap s, get_graph s) .
Proof.
  intros. unfold bf_measure_heap. inversion H; subst; simpl in *.
  - apply lex1. unfold natNodes_lt. eapply match_decr_size. symmetry. apply H1.
  - apply lex2. unfold natNodes_eq. symmetry. eapply match_none_size. apply H1.  unfold heap_length_lt.
    destruct h; inversion H2; subst. rewrite mergeAll_size. simpl. omega.
Qed.

(*The same for multistep*)
Lemma measure_multi: forall s s',
  sp_multi s s' ->
  s = s' \/ bf_measure_heap (get_heap s', get_graph s') (get_heap s, get_graph s) .
Proof.
  intros. induction H.
  - left. reflexivity.
  - destruct IHmulti. subst. right. apply measure_step. assumption.
    right. eapply measure_trans. apply H1. apply measure_step. assumption.
Qed.

(*If s multisteps to s', s and s' are equal exactly when s < s' and s' < s are both false*)
Lemma multistep_eq_measure: forall s s',
  sp_multi s s' ->
  (s = s') <-> (~bf_measure_heap (get_heap s', get_graph s') (get_heap s, get_graph s) /\
  ~bf_measure_heap  (get_heap s, get_graph s) (get_heap s', get_graph s')). 
Proof.
  intros. split. intros. subst. split; intro;
  pose proof (measure_antirefl (get_heap s', get_graph s')); contradiction. intros.
  destruct H0. apply measure_multi in H. destruct H. subst. reflexivity. contradiction.
Qed. 

Lemma sp_step_deterministic : forall s1 s2 s,
  sp_step s s1 -> sp_step s s2 -> s1 = s2.
Proof.
  intros. inversion H; inversion H0; subst; inversion H9; subst; rewrite H8 in H3; inversion H3; subst;
    rewrite H7 in H2; inversion H2; subst; reflexivity.
Qed.

Lemma multi_from_start: forall s s' s'',
  sp_multi s s'' ->
  sp_multi s s' ->
  (sp_multi s' s'' \/ sp_multi s'' s').
Proof.
  intros. generalize dependent s'. induction H; intros.
  - right. apply H0.
  - inversion H1; subst.
    + left. eapply multi_step. apply H. apply H0.
    + assert (y=y0). eapply sp_step_deterministic.
      apply H. apply H2. subst. apply IHmulti. apply H3.
Qed.

Lemma valid_begins_with_start: forall s g v,
  valid s g v ->
  sp_multi (start g v) s.
Proof.
  intros. induction H.
  - constructor.
  - eapply multi_trans. apply IHvalid.  eapply multi_step. apply H0. apply multi_refl.
Qed.

(*For any two valid states, one multisteps to the other*)
Lemma valid_multi: forall s s' g v,
  valid s g v ->
  valid s' g v ->
  sp_multi s s' \/ sp_multi s' s.
Proof.
  intros. eapply multi_from_start. apply valid_begins_with_start. apply H0.
  apply valid_begins_with_start. assumption.
Qed.

(*A valid state is not done iff it can step*)
Lemma not_done_step: forall s g v,
  valid s g v ->
  (done s = false <-> exists s', sp_step s s').
Proof.
  intros. split; intros.
  - destruct s as [p d]. destruct p as [g' h].
    unfold done in H0. simpl in H0.
    rewrite orb_false_iff in H0. destruct H0.
    destruct h. simpl in H0. inversion H0.
    destruct (match_ n g') eqn : M. destruct m.
    + exists (g0, mergeAll ((mergeAll l) :: expand_dist b0 n c), d ++ (b0,n) :: nil).
      constructor; try(assumption). simpl. reflexivity.
    + exists (g0, (mergeAll l), d). econstructor; try eassumption. simpl. reflexivity.
  - destruct H0. unfold done in *; inversion H0; subst; simpl in *; rewrite H1; simpl; destruct h;
    try(reflexivity); try(inversion H3).
Qed.

(*If a state is done, it cannot step*)
Lemma done_cannot_step: forall s g v,
  valid s g v ->
  done s = true ->
  ~(exists s', sp_step s s').
Proof.
  intros. intro. pose proof (not_done_step _ _ _ H).
  destruct H2. apply contrapositive in H3. contradiction. 
  rewrite H0. intro. inversion H4.
Qed.

(*A state is done if for every valid state s', s' < s is false*)
Lemma measure_done: forall s g v,
  valid s g v ->
  done s = true <-> 
  (forall s', valid s' g v -> ~bf_measure_heap (get_heap s', get_graph s') (get_heap s, get_graph s)).
Proof.
  intros. split; intros.
  - intro. pose proof (valid_multi _ _ _ _ H H1). destruct H3.
    + inversion H3. subst. pose proof (measure_antirefl (get_heap s', get_graph s')).
      contradiction. subst. pose proof (done_cannot_step _ _ _ H H0).
      apply H6. exists y. assumption.
    + apply measure_multi in H3. destruct H3. subst.
      pose proof (measure_antirefl (get_heap s, get_graph s)).
      contradiction. pose proof (measure_antisym _ _ H2). contradiction.
  - destruct (done s) eqn : D.
    + reflexivity.
    + pose proof (not_done_step _ _ _ H). apply H1 in D.
      destruct D. assert (valid x g v). eapply v_step. apply H. apply H2.
      apply H0 in H3. apply measure_step in H2. contradiction.
Qed.  

(*two valid states are equal if neither is less than the other*)
Lemma measure_unique: forall s g v s',
  valid s g v ->
  valid s' g v ->
  ~bf_measure_heap (get_heap s', get_graph s') (get_heap s, get_graph s) ->
  ~bf_measure_heap (get_heap s, get_graph s) (get_heap s', get_graph s') ->
  s = s'.
Proof.
  intros. pose proof (valid_multi _ _ _ _ H H0). destruct H3.
  - apply measure_multi in H3. destruct H3. assumption. contradiction.
  - apply measure_multi in H3. destruct H3. subst. reflexivity. contradiction.
Qed. 

(*An important lemma: any two done states that are valid are unique. This allows us to use a tail
  recursive function and still prove claims about generic done states*)
Lemma done_unique: forall s g v s',
  valid s g v ->
  valid s' g v ->
  done s = true ->
  done s' = true ->
  s = s'.
Proof.
  intros. assert (forall s', valid s' g v -> ~bf_measure_heap (get_heap s', get_graph s') (get_heap s, get_graph s)).
  eapply measure_done. assumption. assumption.
  assert (forall s'', valid s'' g v -> ~bf_measure_heap (get_heap s'', get_graph s'') (get_heap s', get_graph s')).
  eapply measure_done. assumption. assumption.
  eapply measure_unique. apply H. apply H0. apply H3. apply H0.
  apply H4. apply H.
Qed.
End Multi.

(*The executable, tail recursive version of this, which we will prove equivalent to the hs-to-coq version*)
Section Exec.

Program Instance default_state : Default state.
Next Obligation.
unfold state. apply ((empty, Heap.Empty, nil)).
Defined.


Equations sp_tail (s: state) : state by wf (get_heap s, get_graph s) (bf_measure_heap) :=
  sp_tail (g, h, l) =>  if bool_dec ((Heap.isEmpty h) || (@Graph.isEmpty gr Hgraph a b g)) true then (g, h, l) else
                        match (splitMinT h) as s return ((splitMinT h = s) -> _) with
                          |Some ((d,v), h') => fun H : (splitMinT h =  Some ((d,v), h')) =>
                                match (match_ v g) as y return ((match_ v g = y) -> _ ) with
                                | (Some c, g') => fun H : (match_ v g) = (Some c, g') => 
                                      sp_tail (g', mergeAll (h' :: expand_dist d v c), l ++ (d,v) :: nil)
                                | (None, g') => fun H: (match_ v g) = (None, g') => sp_tail(g', h', l)                                 end (eq_refl)
                          | None => fun H : (splitMinT h = None) => Err.patternFailure
                         end (eq_refl).
Next Obligation.
simpl. destruct c. destruct p. destruct p. unfold Base.map. apply lex1. unfold natNodes_lt. eapply match_decr_size.
symmetry. apply H.
Defined.
Next Obligation.
apply lex2. symmetry. unfold natNodes_eq. eapply match_none_size. apply H. unfold heap_length_lt.
unfold splitMin in H0. destruct h. simpl in n. contradiction. inversion H0; subst.
rewrite (mergeAll_size l0). simpl. assert (forall x, x < S x). intros.  omega. apply H1.
Defined.

Definition expand_sp_tail :=
fun s : gr a b * Heap b Node * list (b * Node) =>
let (p, l) := s in
(let (g, h) := p in
 fun l0 : list (b * Node) =>
 if bool_dec (Heap.isEmpty h || isEmpty g) true
 then (g, h, l0)
 else
  match splitMinT h as s0 return (splitMinT h = s0 -> gr a b * Heap b Node * list (b * Node)) with
  | Some p0 =>
      let (p1, h') as p1 return (splitMinT h = Some p1 -> gr a b * Heap b Node * list (b * Node)) := p0 in
      let (d, v) as p2 return (splitMinT h = Some (p2, h') -> gr a b * Heap b Node * list (b * Node)) := p1 in
      fun _ : splitMinT h = Some (d, v, h') =>
      (let (m, g') as y return (match_ v g = y -> gr a b * Heap b Node * list (b * Node)) := match_ v g in
       match m as m0 return (match_ v g = (m0, g') -> gr a b * Heap b Node * list (b * Node)) with
       | Some c =>
           fun _ : match_ v g = (Some c, g') =>
           sp_tail (g', mergeAll (h' :: expand_dist d v c), l0 ++ (d, v) :: nil)
       | None => fun _ : match_ v g = (None, g') => sp_tail (g', h', l0)
       end) eq_refl
  | None => fun _ : splitMinT h = None => patternFailure
  end eq_refl) l.

Lemma unfold_sp_tail: forall s,
  sp_tail s = expand_sp_tail s.
Proof.
  intros. unfold expand_sp_tail. apply sp_tail_elim; intros; reflexivity.
Qed.

Lemma sp_tail_multi: forall s,
  sp_multi s (sp_tail s).
Proof.
  intros.  destruct s as[r p].
  remember (snd r, fst r) as r'. generalize dependent r. revert p. 
  induction r' using (well_founded_induction (@well_founded_bf_measure_heap _)).
  intros. destruct r. destruct r'. simpl in Heqr'. inversion Heqr'; subst. clear Heqr'.
  rewrite unfold_sp_tail. unfold expand_sp_tail. destruct (Heap.isEmpty h) eqn : E.
  - simpl. apply multi_refl.
  - destruct (isEmpty g) eqn : G.
    + simpl. apply multi_refl.
    + destruct (bool_dec (false || false) true). simpl in e. inversion e. clear n.
      destruct (splitMinT h) eqn : Min.
      * destruct p0. destruct p0. destruct (match_ n g) eqn : M. destruct m.
        -- eapply multi_step. apply sp_find. assumption. apply M. apply Min. eapply H.
            2 : { reflexivity. } apply lex1. simpl. eapply match_decr_size. symmetry. apply M.
        -- eapply multi_step. eapply sp_skip. assumption. apply M. apply Min.
           eapply H. 2 : { reflexivity. } simpl. eapply lex2. symmetry. eapply match_none_size. apply M.
           unfold heap_length_lt. destruct h. simpl in Min. inversion Min. simpl in Min. inversion Min; subst.
           rewrite mergeAll_size. simpl. omega.
      * destruct h. simpl in E. inversion E. inversion Min.
Qed. 

Lemma sp_tail_done: forall s,
  done (sp_tail s) = true.
Proof.
  intros. unfold done. destruct s as[r p].
  remember (snd r, fst r) as r'. generalize dependent r. revert p. 
  induction r' using (well_founded_induction (@well_founded_bf_measure_heap _)).
  intros. destruct r. destruct r'. simpl in Heqr'. inversion Heqr'; subst.
  rewrite unfold_sp_tail. unfold expand_sp_tail. destruct (Heap.isEmpty h) eqn : E.
  - simpl. rewrite E. reflexivity.
  - destruct (isEmpty g) eqn : G.
    + simpl. rewrite G. rewrite E. reflexivity.
    + destruct (bool_dec (false || false) true). inversion e. clear n. destruct (splitMinT h) eqn : Min.
      * destruct p0. destruct p0. destruct (match_ n g) eqn : M. destruct m.
        -- eapply H. 2 : { reflexivity. } eapply lex1. simpl. eapply match_decr_size. symmetry.
           apply M.
        -- eapply H. 2 : {  reflexivity. } apply lex2; simpl. unfold natNodes_eq. symmetry.
           eapply match_none_size. apply M. unfold heap_length_lt. destruct h. inversion E. simpl.
            simpl in Min; inversion Min. rewrite mergeAll_size. omega.
      * destruct h. inversion E. inversion Min.
Qed. 

(*This enables us to talk about any prior valid state, with the assurance that we will multistep to the
  current, done state*)
Lemma multi_done: forall s s' g v,
  valid s g v ->
  valid s' g v ->
  done s = false ->
  done s' = true ->
  sp_multi s s'.
Proof.
  intros. assert (exists s'', sp_multi s s'' /\ done s'' = true).
  exists (sp_tail s). split. apply sp_tail_multi. apply sp_tail_done.
  destruct H3 as [s'']. destruct H3. assert (valid s'' g v). eapply multi_valid.
  apply H. apply H3. assert (s' = s''). eapply done_unique; try(assumption).
  apply H0. apply H5. subst. assumption.
Qed.



End Exec.

Require Import GHC.Base.

Section Correct.

Lemma graph_iff_not_output: forall s g v v',
  valid s g v ->
  vIn g v' = true ->
  In v' (map snd (get_dists s)) <->  (vIn (get_graph s) v' = false).
Proof.
  intros. induction H; split; intros; simpl in *.
  - contradiction. 
  - rewrite H0 in H1. inversion H1.
  - specialize (IHvalid H0). inversion H1; subst.
    + simpl. simpl in H2. unfold map in H2. rewrite map_app in H2. apply in_app_or in H2.
      destruct H2. simpl in IHvalid. eapply match_remain_some in H4. destruct_all.
      rewrite IHvalid in H2. destruct (vIn g' v') eqn : V.
      apply H4 in V. destruct_all. rewrite H2 in H7. inversion H7. reflexivity.
      simpl in H2. destruct H2. subst. eapply match_remain_some in H4. destruct_all.
      destruct (vIn g' v') eqn : V. apply H2 in V. destruct_all; contradiction. reflexivity.
      destruct H2.
    + simpl in *. eapply match_remain_none in H4. subst. apply IHvalid; assumption.
  - specialize (IHvalid H0). inversion H1; subst; simpl in *.
    + destruct (N.eq_dec v' v0). subst. unfold map. rewrite map_app. apply in_or_app.
      right. simpl. left. reflexivity.
      apply match_remain_some in H4. destruct_all.
      assert (vIn g0 v' = false). destruct (vIn g0 v') eqn : V. 
      assert (vIn g' v' = true). apply H4. split; assumption. rewrite H7 in H2. inversion H2. 
      reflexivity. unfold map. rewrite map_app. apply in_or_app. left. unfold map in IHvalid. apply IHvalid.
      assumption.
    + apply match_remain_none in H4. subst. apply IHvalid; assumption.
Qed.

Require Import WeightedGraphs.

Lemma graph_subset: forall s s' v g,
  valid s v g ->
  valid s' v g ->
  sp_multi s s' ->
  (forall v', vIn (get_graph s') v' = true -> vIn (get_graph s) v' = true) /\
  (forall u v w, WeIn (get_graph s') u v w -> WeIn (get_graph s) u v w).
Proof.
  intros. induction H1. split; intros. assumption. assumption.
  assert (valid y v g). eapply v_step. apply H. assumption. specialize (IHmulti H3 H0).
  inversion H1; subst. remember (g', mergeAll (h' :: expand_dist d v0 c), p ++ (d, v0) :: nil) as y.
  split; intros.
  - simpl. assert (M:= H5). apply (match_remain_some) in H5. destruct_all.
    apply H9 in H7. rewrite Heqy in H7; simpl in H7. rewrite H5 in H7. destruct_all; assumption.
  - simpl. apply (Wmatch_remain_some) in H5. destruct_all; subst.
    remember (g', mergeAll (h' :: expand_dist d v0 c), p ++ (d, v0) :: nil) as y. apply H10 in H7.
    rewrite Heqy in H7; simpl in H7. apply H8 in H7. destruct_all; assumption.
  - apply match_remain_none in H5. subst. split; intros; destruct_all; simpl in *.
    + apply H7. assumption.
    + apply H8. assumption.
Qed.

Lemma start_in: forall s v g,
  valid s g v ->
  vIn g v = true.
Proof.
  intros. induction H.
  - assumption.
  - assumption.
Qed.

Lemma graph_subset_start: forall s v (g: gr a b),
  valid s g v ->
  (forall v, vIn (get_graph s) v = true -> vIn g v = true) /\
  (forall u v w, WeIn (get_graph s) u v w -> WeIn g u v w).
Proof.
  intros. remember (start g v) as s'.
  assert (g = get_graph s'). subst; simpl. reflexivity. setoid_rewrite H0. eapply graph_subset.
  subst. apply v_start. eapply start_in. apply H. apply H. subst. apply valid_begins_with_start. apply H.
Qed.

Lemma eIn_WeIn: forall (g: gr a b) u v,
  eIn g u v = true <-> exists w, WeIn g u v w.
Proof.
  intros. unfold eIn. unfold WeIn. unfold edgeList. unfold ulabEdges. split; intros; unfold mem in *.
  - match goal with
    | [H: (if ?b then _ else _) = _ |- _] => destruct b
    end.
    rewrite in_map_iff in i. destruct_all. destruct x. destruct p. inversion H0; subst. exists b0. assumption.
    inversion H.
  - match goal with
    | [H: _ |- (if ?b then _ else _) = _ ] => destruct b
    end. reflexivity.
    destruct_all. setoid_rewrite in_map_iff in n. exfalso. apply n. exists (u,v,x). split. reflexivity. assumption.
Qed. 

(*Now we need analagous theorems as with reachability of BFS, in particular, we need to prove that
  if a vertex is in the output, then it is reachable and vice versa*)

(*First, the statement for the heap.*)
Lemma in_heap_reachable: forall s v g v',
  valid s g v ->
  (exists d, In_Heap (d, v') (get_heap s)) ->
  exists l, path' g v v' l.
Proof.
  intros. generalize dependent v'. induction H; intros.
  - simpl in H0. destruct_all. destruct H0. inversion H0; subst. exists (v' :: nil). constructor. assumption.
    destruct H0.
  - inversion H0; subst.
    + unfold get_heap in H1. destruct H1 as [d']. rewrite in_heap_mergeAll in H1.
      rewrite in_heap_unfold in H1. destruct H1. apply IHvalid. exists d'. simpl.
      destruct h; inversion H4. subst. simpl. right. rewrite <- in_heap_equiv.
      rewrite in_heap_mergeAll in H1. apply H1. destruct c. destruct p0. destruct p0. simpl in H1.
      rewrite in_heap_exists in H1. destruct H1 as [h'']. destruct_all.
      rewrite in_map_iff in H1. destruct H1. destruct x. destruct_all.
      subst. simpl in H5. destruct H5. inversion H1; subst.
      specialize (IHvalid v0). simpl in IHvalid. 
      assert (exists l : list Node, path' g v v0 l). apply IHvalid. exists d. destruct h;
      inversion H4. simpl. left. reflexivity. destruct H5 as [l]. exists (v' :: l).
      econstructor. apply H5. eapply (match_context) in H3. destruct_all; subst.
      assert (eIn g0 n v' = true). apply H8. rewrite in_map_iff. exists (b0, v'). split; simpl.
      reflexivity. assumption. pose proof (graph_subset_start _ _ _ H).
      simpl in H9. 
      assert (exists w, WeIn g0 n v' w). rewrite <- eIn_WeIn. assumption. destruct H10. apply H9 in H10.
      rewrite eIn_WeIn. exists x. assumption. destruct H1.
    + simpl in *. destruct H1 as [d']. apply IHvalid. exists d'.
      destruct h; inversion H4. subst. simpl. right. rewrite in_heap_mergeAll in H1. rewrite <- in_heap_equiv.
      assumption.
Qed.

Theorem output_is_reachable: forall s v g v',
  valid s g v ->
  In v' (map snd (get_dists s)) ->
  exists l, path' g v v' l.
Proof.
  intros. induction H.
  - simpl in H0. destruct H0.
  - inversion H1; subst.
    + simpl in *. unfold map in H0. rewrite map_app in H0.
      apply in_app_or in H0. destruct H0. apply IHvalid. assumption. simpl in H0. destruct H0. subst.
      eapply in_heap_reachable. apply H. simpl. destruct h; inversion H4. subst. simpl. exists d. left.
      reflexivity. destruct H0.
    + simpl in *. apply IHvalid; assumption.
Qed.

(*The harder direction: if a vertex is reachable, then it is in the output. We follow a similar strategy to BFS*)

(*Everything in the output at one state is there in all future states*)
Lemma output_preserved_strong: forall s v g v' s' d,
  valid s g v ->
  sp_multi s s' ->
  In (d, v') (get_dists s) ->
  In (d, v') (get_dists s').
Proof.
  intros. induction H0. assumption. assert (valid y g v). eapply v_step. apply H. assumption.
  specialize (IHmulti H3). clear H3. inversion H0; subst; simpl in *; apply IHmulti; solve_in.
Qed.

Lemma output_preserved: forall s v g v' s',
  valid s g v ->
  sp_multi s s' ->
  In v' (map snd (get_dists s)) ->
  In v' (map snd (get_dists s')).
Proof.
  intros. rewrite in_map_iff in *. destruct H1. exists x. destruct H1.
  split. assumption. destruct x; simpl. subst. eapply output_preserved_strong.
  apply H. apply H0. assumption.
Qed.

(*Everything in the heap is a valid vertex*)
Lemma heap_valid: forall s v g v' d,
  valid s g v ->
  In_Heap (d, v') (get_heap s) ->
  vIn g v' = true.
Proof.
  intros. induction H.
  - simpl in H0. destruct H0. inversion H0; subst. assumption. destruct H0.
  - inversion H1; subst.
    + unfold get_heap in H0. rewrite in_heap_mergeAll in H0. rewrite in_heap_unfold in H0.
      destruct H0. apply IHvalid. simpl. destruct h. inversion H4. inversion H4; subst.
      right. rewrite in_heap_mergeAll in H0. rewrite in_heap_equiv in H0. assumption.
      destruct c. destruct p0. destruct p0. simpl in H0. rewrite in_heap_exists in H0.
      destruct H0. rewrite in_map_iff in H0. destruct_all. destruct x0. subst. simpl in H5.
      destruct H5. inversion H0; subst. apply match_context in H3. destruct_all; subst.
      assert (eIn g0 n v' = true). apply H7. rewrite in_map_iff. exists (b0, v'). split; simpl; auto.
      apply edges_valid in H3. destruct_all. pose proof (graph_subset_start _ _ _ H).
      destruct_all. apply H9; simpl. assumption.
      destruct H0.
    + apply IHvalid. simpl in *. destruct h; inversion H4; subst. right. 
      rewrite in_heap_mergeAll in H0. rewrite in_heap_equiv in H0. assumption.
Qed.


(*Everything in the heap at one point that is not in the heap at a future point must be in the output*)
Lemma heap_added_to_output: forall s v g v' s',
  valid s g v ->
  sp_multi s s' ->
  (exists d, In_Heap (d, v') (get_heap s)) ->
  ~(exists d, In_Heap (d, v') (get_heap s')) ->
  In v' (map snd (get_dists s')).
Proof.
  intros. induction H0.
  - contradiction.
  - assert (valid y g v). eapply v_step. apply H; assumption. assumption.
    specialize (IHmulti H4). inversion H0; subst.
    + destruct H1 as [d']. simpl in H1. remember ((h' :: expand_dist d v0 c)) as h0.
      simpl in IHmulti. subst. destruct h; inversion H7. subst. simpl in H1.
      destruct H1. inversion H1; subst. eapply output_preserved. apply H4. 
      assumption. simpl. unfold map. rewrite map_app. apply in_or_app. simpl.
      right. left. reflexivity. 
      destruct_all. apply IHmulti. exists d'. rewrite in_heap_mergeAll.
      rewrite in_heap_unfold. left. rewrite in_heap_mergeAll. rewrite in_heap_equiv. apply H1.
      assumption.
    + destruct (N.eq_dec v' v0). subst. eapply output_preserved. apply H4.
      assumption. destruct H1. eapply graph_iff_not_output. apply H4. eapply heap_valid.
      apply H. simpl. apply H1. simpl. assert (M:= H6). apply match_remain_none in M. subst.
      destruct (vIn g' v0) eqn : V. apply match_in in V.
      destruct_all. rewrite H8 in H6. inversion H6. reflexivity. apply IHmulti.
      destruct h; inversion H7; subst. destruct H1. simpl in H1. destruct H1. inversion H1; subst. contradiction.
      exists x. simpl. rewrite in_heap_mergeAll. rewrite in_heap_equiv. assumption. assumption.
Qed.

(*An important lemma: If a vertex is on the heap at any point, when we multistep to the end, it is in
  the list of distances*)
Lemma heap_ends_in_output: forall s v g s' v',
  valid s g v ->
  sp_multi s s' ->
  done s' = true ->
  (exists d, In_Heap (d, v') (get_heap s)) ->
  In v' (map snd (get_dists s')).
Proof.
  intros. unfold done in H1. rewrite orb_true_iff in H1.
  destruct H1. destruct (get_heap s') eqn : E. 
  eapply heap_added_to_output. apply H. assumption. assumption. rewrite E. simpl. intro. destruct_all. destruct H3. 
  simpl in H1. inversion H1. rewrite graph_iff_not_output. 
  rewrite isEmpty_def in H1. apply H1. apply v'. 
  eapply multi_valid. apply H. assumption. destruct H2. eapply heap_valid. apply H. apply H2. 
Qed.
Require Import Coq.Lists.SetoidList.
(*Each vertex appears at most once in the output*)
Lemma no_dups_output: forall s g v,
  valid s g v ->
  NoDup (map snd (get_dists s)).
Proof.
  intros. induction H; simpl.
  - constructor.
  - inversion H0; subst; simpl in *. unfold map.
    rewrite map_app. simpl. assert (List.map snd p ++ v0 :: nil = rev (v0 :: rev ((map snd p)))).
    simpl. rewrite rev_involutive. reflexivity.
    rewrite H4. rewrite NoDup_NoDupA. apply NoDupA_rev. apply eq_equivalence.
    constructor. intro. rewrite <- In_InA_equiv in H5. rewrite <- in_rev in H5.
    assert (vIn g v0 = true). destruct h; inversion H3; subst. eapply heap_valid. apply H. simpl.
    left. reflexivity. 
    pose proof (graph_iff_not_output _ _ _ _ H H6) as D; simpl in *.
    apply D in H5. 
    assert (vIn g0 v0 = true). apply match_in. exists c. exists g'. assumption.
    rewrite H7 in H5. inversion H5. apply NoDupA_rev. apply eq_equivalence. rewrite <- NoDup_NoDupA.
    assumption. assumption.
Qed. 

(*If a vertex is in the distances at any point, there must be a step when it was added to the distances. The rest
  of the lemma gives a bunch of information about that state and the heap/distances*)
Lemma output_is_added: forall s v g v' d,
  valid s g v ->
  In (d, v') (get_dists s) ->
  (exists s'' s' c g', valid s'' g v /\ sp_step s'' s' /\ sp_multi s' s  /\ (exists h,
    get_heap s' = mergeAll (h :: expand_dist d v' c) /\ ~In v' (map snd (get_dists s'')) /\
    match_ v' (get_graph s'') = (Some c, g') /\
    splitMinT (get_heap s'') = Some (d, v',  h) /\ exists l2, get_dists s' = l2 ++ (d, v') :: nil)).
Proof.
  intros. induction H.
  - simpl in H0. destruct H0.
  - inversion H1; subst.
    + assert (~In v0 (map snd p)). { assert (valid (g', mergeAll (h' :: expand_dist d0 v0 c), p ++ (d0, v0) :: nil) g v).
      eapply v_step. apply H. assumption. apply no_dups_output in H5. simpl in H5. rewrite NoDup_NoDupA in H5. unfold map in H5.
      rewrite map_app in H5. simpl in H5. apply NoDupA_swap in H5. inversion H5; subst.
      intro. rewrite In_InA_equiv in H6. rewrite app_nil_r in H8. contradiction.
      apply eq_equivalence. } destruct (N.eq_dec v' v0).
      * subst. simpl in H0. apply in_app_or in H0. destruct H0.
        rewrite in_map_iff in H5. exfalso. apply H5. exists (d, v0). split; simpl. reflexivity. assumption.
        simpl in H0. destruct H0. inversion H0; subst. 
        exists (g0, h, p). exists ( (g', mergeAll (h' :: expand_dist d v0 c), p ++ (d, v0) :: nil)).
        exists c. exists g'.
        repeat(split; try(assumption); try(reflexivity)).
        apply multi_refl. exists h'. repeat(split; try(assumption); try(reflexivity)).
        exists p. simpl. reflexivity. destruct H0.
      * apply in_app_or in H0. destruct H0.
        apply IHvalid in H0. clear IHvalid. destruct H0 as [s'']. destruct H0 as [s']. destruct H0 as [c'].
        destruct H0 as [g'']. destruct_all. exists s''. exists s'. exists c'. exists g''.
        repeat(split; try(assumption)). eapply multi_trans. apply H7. apply multi_R. assumption.
        exists x. repeat(split; try(assumption)). exists x0. assumption. simpl in H0. destruct H0. inversion H0; subst.
        contradiction. destruct H0.
    + apply IHvalid in H0. clear IHvalid. destruct H0 as [s'']. destruct H0 as [s']. destruct H0 as [c'].
      destruct H0 as [g'']. destruct_all. exists s''. exists s'. exists c'. exists g''.
      repeat(split; try(assumption)). eapply multi_trans. apply H6. apply multi_R. assumption.
      exists x. split. assumption. repeat(split; try(assumption)). exists x0. assumption.
Qed.

(*Last lemma before reachability - an edge is in the graph in a given state exactly when both ot its
  vertices are in the graph*)
Lemma edge_in_state: forall s g v u' v' w,
  valid s g v ->  
  WeIn g u' v' w ->
  WeIn (get_graph s) u' v' w <-> (vIn (get_graph s) u' = true /\ vIn (get_graph s) v' = true).
Proof.
  intros. induction H.
  - unfold start; simpl. split; intros.
    + assert (eIn g u' v' = true). apply eIn_WeIn. exists w. assumption. apply edges_valid. assumption.
    + assumption.
  - specialize (IHvalid H0). inversion H1; subst; simpl in *.
    + split; intros.
      * assert (eIn g' u' v' = true). apply eIn_WeIn. exists w. assumption. apply edges_valid. assumption.
      * destruct H5. apply Wmatch_remain_some in H3. destruct H3. apply H3 in H5.
        apply H3 in H6. rewrite H7. split. rewrite IHvalid. destruct_all. split; assumption.
        destruct_all; split; assumption.
    + apply match_remain_none in H3. subst. apply IHvalid.
Qed.
Import GHC.Num.Notations.
(*Characterizing expand_dist, which is the function uesd by SP*)
Lemma expand_dists_def: forall d' v' v (c: Context a b) g g' d,
  match_ v g = (Some c, g') ->
  (exists h, In h (expand_dist d v c) /\ In_Heap (d', v') h) <-> 
  (exists (w : b), WeIn g v v' w /\ (d' = (_+_ w d))).
Proof.
  intros. split; intros. unfold expand_dist in H0. destruct c. destruct p. destruct p. destruct H0 as [h].
  rewrite in_map_iff in H0. destruct_all.  destruct x. subst. simpl in H1. destruct H1.
  inversion H0; subst. exists b0. apply (Wmatch_context) in H. destruct_all. subst.
  split. apply H3. assumption. reflexivity. destruct H0.
  destruct H0 as [w]. destruct_all. unfold expand_dist. destruct c. destruct p. destruct p.
  setoid_rewrite in_map_iff. exists (unit d' v'). split. exists (w, v'). simpl. split. subst.
  reflexivity. apply Wmatch_context in H. destruct_all; subst. apply H3. assumption. simpl.
  left. reflexivity.
Qed.

(*First, prove everything reachable is in heap at some point*)
Lemma reachable_in_heap: forall g v v',
  (exists l, path' g v v' l) ->
  (exists s, valid s g v /\ (exists d, In_Heap (d, v') (get_heap s))).
Proof.
  intros. destruct H as [l]. generalize dependent v'.
  induction l using (well_founded_induction
                     (wf_inverse_image _ nat _ (@length _)
                        PeanoNat.Nat.lt_wf_0)).
  intros. destruct l.
  - inversion H0; subst.
  - inversion H0; subst.  exists (start g n). simpl. split. constructor. assumption.
    exists #0. left. reflexivity.
    assert (exists s : state, valid s g v /\ (exists d', In_Heap (d', v'0) (get_heap s))).
    eapply H. 2 : { apply H6. } simpl. omega. 
    destruct H1 as [s]. destruct H1.  
    assert (exists sd, done sd = true /\ sp_multi s sd). exists (sp_tail s).
    split. apply sp_tail_done. apply sp_tail_multi. destruct H3 as [sd]. destruct H3.
    pose proof (heap_ends_in_output _ _ _ _ _ H1 H4 H3 H2).
    assert (valid sd g v). eapply multi_valid. apply H1. assumption.
    rewrite in_map_iff in H5. destruct H5. destruct x as [n' d]. simpl in H5. destruct H5; subst.
    pose proof (output_is_added _ _ _ _ _ H8 H9). destruct H5 as [sb]. destruct H5 as [sp]. destruct H5 as [c].
    destruct H5 as [g']. destruct H5. destruct H10. destruct H11. destruct H12 as [l1].
    (*need prior state*)
    destruct H12. destruct H13. destruct H14. destruct H15. assert (E: exists w, WeIn g v'0 n w).
    apply eIn_WeIn. assumption. destruct E as [w E].
    pose proof (edge_in_state _ _ _ _ _ _ H5 E). destruct (vIn (get_graph sb) n) eqn : M.
    + assert (vIn (get_graph sb) v'0 = true). erewrite <- match_in. exists c. exists g'. assumption.
      rewrite H18 in H17. assert (WeIn (get_graph sb) v'0 n w). rewrite H17. split; reflexivity.
      exists sp. split; try(assumption). eapply v_step. apply H5. assumption.
      rewrite H12. setoid_rewrite in_heap_mergeAll. setoid_rewrite in_heap_unfold.
      destruct c. destruct p. destruct p. exists (_+_ w n'). right.
      epose proof (expand_dists_def _ _ _ _ _ _ _ H14).
      rewrite in_heap_exists. apply H20. exists w. split.
      assumption. reflexivity.
    + rewrite <- graph_iff_not_output in M. rewrite in_map_iff in M. destruct M. destruct x. simpl in H18; destruct H18; subst.
      pose proof (output_is_added _ _ _ _ _ H5 H19). destruct_all. exists x. split. assumption.
      exists b0. destruct (get_heap x); inversion H25; subst. left. reflexivity. apply H5.
      apply edges_valid in H7. apply H7.
Qed. 

(*Now, everything reachable is in the ouptut*)
Lemma reachable_in_output: forall g v v' s,
  valid s g v ->
  done s = true ->
  (exists l, path' g v v' l) ->
  In v' (map snd (get_dists s)).
Proof.
  intros. eapply reachable_in_heap in H1. destruct H1 as [s']. destruct H1.
  eapply heap_ends_in_output. apply H1. destruct (done s') eqn : D.
  assert (s = s'). eapply done_unique. apply H. apply H1. assumption. assumption.
  subst. apply multi_refl. eapply multi_done. apply H1. apply H. assumption. assumption.
  assumption. assumption.
Qed.

(** Proof the SP finds vertices exactly when they are reachable **)
Theorem output_iff_reachable: forall s g v v',
  valid s g v ->
  done s = true ->
  In v' (map snd (get_dists s)) <->  (exists l, path' g v v' l).
Proof.
  intros. split; intros.
  - eapply output_is_reachable. apply H. apply H1.
  - eapply reachable_in_output. apply H. assumption. assumption.
Qed.

End Correct.


Equations sp_distance (x : (Heap b Node) * (gr a b)) : list (b * Node) by wf x (@bf_measure_heap Node) :=
  sp_distance (h, g) :=  if bool_dec ((Heap.isEmpty h) || (Graph.isEmpty g)) true then nil else
                        match (splitMinT h) as s return ((splitMinT h = s) -> _) with
                          |Some ((d,v), h') => fun H : (splitMinT h =  Some ((d,v), h')) =>
                                match (match_ v g) as y return ((match_ v g = y) -> _ ) with
                                | (Some c, g') => fun H : (match_ v g) = (Some c, g') => (d,v) :: 
                                      sp_distance (mergeAll (h' :: expand_dist d v c), g')
                                | (None, g') => fun H: (match_ v g) = (None, g') => sp_distance (h', g')
                                 end (eq_refl)
                          | None => fun H : (splitMinT h = None) => Err.patternFailure
                         end (eq_refl).
Next Obligation.
simpl. destruct c. destruct p. destruct p. unfold Base.map. apply lex1. unfold natNodes_lt. eapply match_decr_size.
symmetry. apply H.
Defined.
Next Obligation.
apply lex2. symmetry. unfold natNodes_eq. eapply match_none_size. apply H. unfold heap_length_lt.
unfold splitMin in H0. destruct h. simpl in n. contradiction. inversion H0; subst.
rewrite (mergeAll_size l). simpl. omega.
Defined.

Definition expand_sp_distance :=
  fun x : Heap b Node * gr a b =>
let (h, g) := x in
if bool_dec (Heap.isEmpty h || isEmpty g) true
then nil
else
 match splitMinT h as s return (splitMinT h = s -> list (b * Node)) with
 | Some p =>
     let (p0, h') as p0 return (splitMinT h = Some p0 -> list (b * Node)) := p in
     let (d, v) as p1 return (splitMinT h = Some (p1, h') -> list (b * Node)) := p0 in
     fun _ : splitMinT h = Some (d, v, h') =>
     (let (m, g') as y return (match_ v g = y -> list (b * Node)) := match_ v g in
      match m as m0 return (match_ v g = (m0, g') -> list (b * Node)) with
      | Some c =>
          fun _ : match_ v g = (Some c, g') => (d, v) :: sp_distance (mergeAll (h' :: expand_dist d v c), g')
      | None => fun _ : match_ v g = (None, g') => sp_distance (h', g')
      end) eq_refl
 | None => fun _ : splitMinT h = None => patternFailure
 end eq_refl.

Lemma unfold_sp_distance : forall x,
  sp_distance x = expand_sp_distance x.
Proof.
    intros. unfold expand_sp_distance. apply sp_distance_elim. reflexivity.
Qed.


(*Prove equivalence with equations version*)

Equations dijkstra' (x: (Heap b (Graph.LPath b)) * (gr a b)) : list (Graph.LPath b) by wf x (bf_measure_heap) :=
  dijkstra' (h, g) := if bool_dec ((Heap.isEmpty h) || (Graph.isEmpty g)) true then nil else
                        match (splitMinT h) as s return ((splitMinT h = s) -> _) with
                          |Some ((_, p), h') => fun H : (splitMinT h =  Some ((_, p), h')) =>
                          match p as p' return ((p = p') -> _) with
                            | LP nil => fun H : (p = LP nil) => Err.patternFailure
                            | LP ((v,d) :: t) => fun H : (p = LP ( (v,d) :: t)) =>
                                match (match_ v g) as y return ((match_ v g = y) -> _ ) with
                                | (Some c, g') => fun H : (match_ v g) = (Some c, g') => p :: dijkstra' (mergeAll (h' :: expand d p c), g')
                                | (None, g') => fun H: (match_ v g) = (None, g') => dijkstra' (h', g')
                                 end (eq_refl)
                            end (eq_refl)
                          | None => fun H : (splitMinT h = None) => Err.patternFailure
                         end (eq_refl).
Next Obligation.
simpl. destruct c. destruct p. destruct p. unfold Base.map. apply lex1. unfold natNodes_lt. eapply match_decr_size.
symmetry. apply H.
Defined.
Next Obligation.
apply lex2. symmetry. unfold natNodes_eq. eapply match_none_size. apply H. unfold heap_length_lt.
unfold splitMin in H0. destruct h. simpl in n. contradiction. inversion H0; subst.
rewrite (mergeAll_size l4). simpl. omega.
Defined.


Definition expand_dijkstra' := 
fun x : Heap b (LPath b) * gr a b =>
let (h, g) := x in
if bool_dec (Heap.isEmpty h || isEmpty g) true
then nil
else
 match splitMinT h as s return (splitMinT h = s -> list (LPath b)) with
 | Some p0 =>
     let (p1, h') as p1 return (splitMinT h = Some p1 -> list (LPath b)) := p0 in
     let (b0, p) as p2 return (splitMinT h = Some (p2, h') -> list (LPath b)) := p1 in
     fun _ : splitMinT h = Some (b0, p, h') =>
     match p as p' return (p = p' -> list (LPath b)) with
     | LP unLPath =>
         match unLPath as unLPath0 return (p = LP unLPath0 -> list (LPath b)) with
         | nil => fun _ : p = LP nil => patternFailure
         | l :: t =>
             let (v, d) as l0 return (p = LP (l0 :: t) -> list (LPath b)) := l in
             fun _ : p = LP ((v, d) :: t) =>
             (let (m, g') as y return (match_ v g = y -> list (LPath b)) := match_ v g in
              match m as m0 return (match_ v g = (m0, g') -> list (LPath b)) with
              | Some c => fun _ : match_ v g = (Some c, g') => p :: dijkstra' (mergeAll (h' :: expand d p c), g')
              | None => fun _ : match_ v g = (None, g') => dijkstra' (h', g')
              end) eq_refl
         end
     end eq_refl
 | None => fun _ : splitMinT h = None => patternFailure
 end eq_refl.

Lemma unfold_dijkstra' : forall x,
  expand_dijkstra' x = dijkstra' x.
Proof.
  intros. unfold expand_dijkstra'. apply dijkstra'_elim. reflexivity.
Qed.

(*Relation of distance to sp. If we take the list returned by disjkstra's and return the length of the path,
  as well as the head of the list, we should get the same as the distance*)

Definition labelHead (l: (LPath b)) : (option b * option Node)  :=
  match l with
  | LP nil => (None, None)
  | LP ((x,y) :: tl) => (Some y, Some x) 
  end.

Lemma distance_sp: forall (h : Heap b (LPath b)) (h' : Heap b Node) (g: gr a b) (Z: forall x, ~In_Heap (x, LP nil) h),
  map_heap (fun x l => (labelHead l)) h = map_heap (fun x y => (Some x, Some y)) h' ->
  map labelHead (dijkstra' (h,g)) =
  map (fun x => (Some (fst x), Some (snd x))) (sp_distance (h', g)).
Proof.
  intros. rewrite <- unfold_dijkstra'. rewrite unfold_sp_distance.
  remember (h,g) as x. generalize dependent g. generalize dependent h. revert h'.
  induction x using (well_founded_induction (@well_founded_bf_measure_heap _)).
  - intros. destruct x. inversion Heqx; subst. clear Heqx. unfold expand_dijkstra'.
    unfold expand_sp_distance.
    destruct h. simpl. destruct h'. simpl. reflexivity.
    simpl in H0. inversion H0.
    destruct h'. simpl in H0. inversion H0. destruct (isEmpty g) eqn : G'.
    + simpl. reflexivity.
    + remember (Heap.Node b0 l l0) as h. remember (Heap.Node b1 n l1) as h'.
      destruct (bool_dec (Heap.isEmpty h || false) true). subst. simpl in e. inversion e.
      destruct (bool_dec (Heap.isEmpty h' || false) true). subst. simpl in e. inversion e.
      clear n0. clear n1.
      destruct (splitMinT h) eqn : Mi. destruct p. destruct p.
      pose proof map_splitMin. 
      assert (splitMinT (map_heap (fun (_ : b) (l : LPath b) => labelHead l) h) = Some (b2, labelHead l2, 
      map_heap (fun (_ : b) (l : LPath b) => labelHead l) h0)).
      rewrite <- splitMin_equiv in Mi. rewrite <- splitMin_equiv. 
      assert (h <> Heap.Empty). intro. subst. inversion H2. inversion Mi.
      erewrite H1. reflexivity. constructor. apply (None, None). apply H2.
      apply H4. intro. subst. simpl in H2. inversion H2. intro. subst. inversion H2.
      assert (C := H2).
      rewrite H0 in H2. destruct (splitMinT h') eqn : Mi'. destruct p. destruct p.
      assert (splitMinT (map_heap (fun (x : b) (y : Node) => (Some x, Some y)) h') =
      Some (b3, (Some b3, Some n0), map_heap (fun (x : b) (y : Node) => (Some x, Some y)) h1)).
      rewrite <- splitMin_equiv. erewrite map_splitMin. reflexivity. constructor. apply (None, None).
      intro. subst. inversion H3. rewrite <- splitMin_equiv in Mi'. inversion Mi'. reflexivity.
      intro. subst. inversion H3. intro. subst. simpl in H3. inversion H3. rewrite H2 in H3.
      inversion H3.  destruct l2. destruct  unLPath.
      * subst. exfalso. apply (Z b3). rewrite in_heap_splitMin. left. reflexivity. intro. subst. inversion H4.
        rewrite <- splitMin_equiv in Mi. 
        assert ((splitMin (Heap.Node b0 l l0)) = (b3, LP nil, h0)). inversion Mi; subst. simpl. reflexivity. apply H4.
        intro. inversion H4.
      * destruct l2. simpl in H6. inversion H6. destruct (match_ n1 g) eqn : M. rewrite H9 in M. rewrite M. destruct m.
        -- remember ((mergeAll (h0 :: expand b3 (LP ((n0, b3) :: unLPath)) c), g0)) as P. rewrite <- HeqP.
            remember (mergeAll (h1 :: expand_dist b3 n0 c), g0) as P'. simpl.
           rewrite HeqP. rewrite HeqP'. rewrite <- unfold_dijkstra'. erewrite H. rewrite unfold_sp_distance. reflexivity.
          apply lex1. eapply match_decr_size. symmetry. apply M. 3 : { reflexivity. }
          intros. intro. rewrite in_heap_mergeAll in H4. rewrite in_heap_unfold in H4. destruct H4.
          apply (Z x). rewrite in_heap_splitMin. right. apply H4. intro. subst. inversion H10.
          rewrite <- splitMin_equiv in Mi. inversion Mi. apply H11. intro. subst. inversion H10.
          rewrite in_heap_exists in H4. destruct H4 as [h'']. destruct H4. simpl in H4.
          destruct c. destruct p. destruct p. rewrite in_map_iff in H4. destruct H4. destruct x0.
          unfold unit in H4.  simpl in H4. destruct H4; subst. simpl in H10. destruct H10. inversion H4. destruct H4.
          repeat(rewrite map_mergeAll). 
          assert (
           (List.map (map_heap (fun (_ : b) (l2 : LPath b) => labelHead l2))
     (h0 :: expand b3 (LP ((n0, b3) :: unLPath)) c)) =
        (List.map (map_heap (fun (x : b) (y : Node) => (Some x, Some y))) (h1 :: expand_dist b3 n0 c))).  simpl. unfold expand_dist.
        destruct c. destruct p. destruct p. rewrite H7. assert (forall l', 
         List.map (map_heap (fun (_ : b) (l2 : LPath b) => labelHead l2))
     (map (fun '(l2, v) => unit (_GHC.Num.+_ l2 b3) (LP ((v, _GHC.Num.+_ l2 b3) :: (n0, b3) :: unLPath))) l') =
      List.map (map_heap (fun (x : b) (y : Node) => (Some x, Some y)))
     (map (fun x : b * Node => let (l2, v') := x in unit (_GHC.Num.+_ l2 b3) v') l')). { intros. induction l'.
      simpl. reflexivity. simpl. rewrite IHl'. simpl. destruct a3. reflexivity. } rewrite H4. reflexivity.
      rewrite H4. reflexivity.
        -- rewrite <- unfold_dijkstra'. rewrite unfold_sp_distance. erewrite H. reflexivity.
           apply lex2. unfold natNodes_eq. symmetry. eapply match_none_size. apply M.
           unfold heap_length_lt. subst. simpl in Mi. inversion Mi; subst. rewrite (mergeAll_size l0).
           simpl. omega. 3 : { reflexivity. } intros. intro. apply (Z x). rewrite in_heap_splitMin.
            right. apply H4. intro. subst. inversion H10. rewrite <- splitMin_equiv in Mi. inversion Mi. apply H11.
          intro. subst. inversion H10. apply H7.
      * subst. inversion Mi'.
      * subst. inversion Mi.
Qed.

(*TODO: Now we prove that it has valid paths and weights*)
(*
Lemma paths_dijkstra: forall h g,
  map labelHead (dijkstra' (h,g)) = map (fun l => (path_cost (unlabel_path l), snd (labelHead l))) (dijkstra' (h,g
*)



Lemma dijkstra'_equiv: forall h g,
  dijkstra h g = dijkstra' (h, g).
Proof.
  intros. remember (h,g) as x. generalize dependent g. revert h.
  induction x using (well_founded_induction (well_founded_bf_measure_heap _)).
  intros. destruct x. inversion Heqx. subst. clear Heqx. unfold dijkstra.
  rewrite <- unfold_dijkstra'. simpl. unfold deferredFix2. unfold curry.
  rewrite (deferredFix_eq_on _ (fun x => True) ( (bf_measure_heap) )).
  - simpl. destruct (Heap.isEmpty h) eqn : E; simpl. reflexivity.
    destruct (isEmpty g) eqn : G; simpl. reflexivity. destruct h. simpl in E. inversion E.
    simpl. destruct l. destruct (unLPath). reflexivity. destruct l. 
    destruct (match_ n g) eqn : M. destruct m.
    +  unfold dijkstra in H. unfold deferredFix2 in H. unfold curry in H. erewrite H. reflexivity.
        apply lex1. unfold natNodes_lt. eapply match_decr_size. symmetry. apply M. reflexivity.
    + unfold dijkstra in H. unfold deferredFix2 in H. unfold curry in H. erewrite H. reflexivity.
      apply lex2. unfold natNodes_eq. symmetry. eapply match_none_size. apply M. unfold heap_length_lt.
      simpl. rewrite (mergeAll_size l0). omega. reflexivity.
  - apply well_founded_bf_measure_heap.
  - unfold recurses_on. intros. unfold uncurry. destruct x. destruct (Heap.isEmpty h1) eqn : H';
     simpl. reflexivity. destruct (isEmpty g1) eqn : G'; simpl. reflexivity. destruct h1. simpl in H'.
    inversion H'. simpl. destruct l; try(reflexivity). destruct unLPath; try(reflexivity). destruct l.
    destruct (match_ n g1) eqn : M'. destruct m.
    + erewrite H1. reflexivity. auto. apply lex1. unfold natNodes_lt. eapply match_decr_size.
      symmetry. apply M'.
    + apply H1. auto. apply lex2. unfold natNodes_eq. symmetry. eapply match_none_size. apply M'.
      unfold heap_length_lt. rewrite (mergeAll_size l0). simpl. omega.
  - auto.
Qed.

(*Equivalence with tail recursive version*)
Lemma sp_tail_equiv: forall g h l,
  get_dists (sp_tail (g, h, l)) = l ++ sp_distance (h, g).
Proof.
  intros. remember (h, g) as x. generalize dependent h. revert g. revert l.
  induction x using (well_founded_induction (well_founded_bf_measure_heap _)).
  intros. destruct x; inversion Heqx; subst; clear Heqx.
  rewrite unfold_sp_distance. rewrite unfold_sp_tail. unfold expand_sp_tail. unfold expand_sp_distance.
  destruct h eqn : H'. 
  - simpl. rewrite app_nil_r. reflexivity.
  - destruct (isEmpty g) eqn : G. 
    + simpl. rewrite app_nil_r. reflexivity.
    + destruct (bool_dec (Heap.isEmpty (Heap.Node b0 n l0) || false) true). simpl in e. inversion e. clear n0.
      destruct (splitMinT (Heap.Node b0 n l0)) eqn : Min. destruct p. destruct p.
      destruct (match_ n0 g) eqn : M. destruct m.
      * erewrite H. rewrite <- app_assoc. reflexivity. apply lex1. unfold natNodes_lt. eapply match_decr_size.
        symmetry. apply M. reflexivity.
      * erewrite H. reflexivity. apply lex2. unfold natNodes_eq. symmetry. eapply match_none_size. apply M.
        unfold heap_length_lt. inversion Min; subst. rewrite mergeAll_size. simpl. omega. reflexivity.
      * inversion Min.
Qed.

End Ind.
