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

(** Correctness of Dijkstra's **)
Definition find_dist_list l v :=
  fold_right (fun (x : b * Node)  acc => if N.eq_dec (snd x) v then Some (fst x) else acc) None l.

Definition find_dist s := find_dist_list (get_dists s).

(*TODO: reduce copy and paste form BFS*)
Lemma find_dist_in: forall s g v v' n,
  valid s g v ->
  find_dist s v' = Some n <-> In (n,v') (get_dists s).
Proof.
  intros. pose proof no_dups_output _ _ _ H. unfold find_dist.
  induction (get_dists s).
  - simpl. split; intros. inversion H1. destruct H1.
  - simpl. inversion H0; subst. split; intros.
    + destruct ( N.eq_dec (snd a0) v'). destruct a0. simpl in *. inversion H1; subst. left. reflexivity.
      right. apply IHl. assumption. assumption.
    + destruct H1. destruct a0; subst; simpl. inversion H1; subst. destruct (N.eq_dec v' v'). reflexivity.
      contradiction. destruct a0. simpl in *.
      destruct ( N.eq_dec n0 v'). subst.
      exfalso. apply H3. rewrite in_map_iff. exists (n, v'). simpl. split. reflexivity. assumption.
      apply IHl. assumption. assumption.
Qed.

Lemma find_dist_not: forall s v,
  find_dist s v = None <-> (forall y, ~In (y, v) (get_dists s)).
Proof.
  intros. unfold find_dist. induction (get_dists s).
  - simpl. split; intros. auto. reflexivity.
  - simpl. split; intros. intro. destruct H0. destruct a0; inversion H0; subst.
    simpl in *. destruct (N.eq_dec v v). inversion H. contradiction.
    destruct (N.eq_dec (snd a0) v). destruct a0. inversion H. rewrite IHl in H.
    apply (H y). assumption. destruct a0. simpl in *. destruct (N.eq_dec n v).
    subst. exfalso. apply (H b0). left. reflexivity. apply IHl. intros.
    intro. apply (H y). right. assumption.
Qed.

(*The first vertex is added with distance 0. We need a few small lemmas to deal with the fact that this
  is added specifically in the second state*)
Lemma second_state: forall s g v,
  vIn g v = true ->
  sp_step (start g v) s ->
  get_dists s = (#0, v) :: nil.
Proof.
  intros. unfold start in H0. inversion 0; subst; simpl.
  simpl in H7. inversion H7; subst. reflexivity.
  rewrite <- match_in in H. destruct H. destruct H. simpl in H7. inversion H7; subst.
  rewrite H in H6. inversion H6.
Qed.

Lemma dists_nil_iff_start: forall s g v,
  valid s g v ->
  get_dists s = nil <-> s = start g v.
Proof.
  intros. induction H.
  - split; intros; try(reflexivity).
  - split; intros.
    + inversion H0; subst.
      * simpl in H1. destruct p; inversion H1. 
      * unfold start in IHvalid. destruct IHvalid. simpl in H1. subst. 
        specialize (H5 eq_refl). inversion H5; subst. simpl in H4. inversion H4; subst.
        pose proof (start_in _ _ _ H). rewrite <- match_in in H1.
        destruct_all. rewrite H1 in H3. inversion H3.
    + subst. inversion H0; subst.
      * destruct p; inversion H3.
      * unfold start in IHvalid. destruct IHvalid. 
        specialize (H1 eq_refl). inversion H1; subst. simpl in H7. inversion H7.
Qed.

Lemma multi_from_second: forall s g v s',
  valid s g v  ->
  sp_step (start g v) s' ->
  s = start g v \/ sp_multi s' s.
Proof.
  intros. induction H.
  - left. reflexivity.
  - specialize (IHvalid H0). destruct IHvalid. subst.
    assert (s = s'). eapply sp_step_deterministic. apply H1. apply H0. subst.
    right. apply multi_refl. right. eapply multi_trans. apply H2. eapply multi_step.
    apply H1. apply multi_refl.
Qed. 

(*The start state is not done*)
Lemma done_not_start: forall g v,
  vIn g v = true ->
  done (start g v) = false.
Proof.
  intros. unfold start. unfold done. simpl. destruct (isEmpty g) eqn : E.
  rewrite isEmpty_def in E. rewrite E in H. inversion H. apply v. reflexivity.
Qed. 

Lemma start_0_dist: forall s g v,
  valid s g v ->
  (get_dists s) <> nil ->
  In (#0, v) (get_dists s).
Proof.
  intros. assert (exists s', sp_step (start g v) s').
  assert (vIn g v = true) by (eapply start_in; apply H).
  pose proof (done_not_start g v H1). rewrite not_done_step in H2.
  apply H2. apply v_start. apply H1. destruct H1 as [s'].
  pose proof (multi_from_second _ _ _ _ H H1). destruct H2. subst.
  rewrite dists_nil_iff_start in H0. contradiction. apply H. 
  eapply output_preserved_strong. eapply v_step. apply v_start.
  apply start_in in H. apply H. apply H1. assumption.
  erewrite second_state. simpl. left. reflexivity. 
  apply start_in in H. apply H. apply H1.
Qed.

Lemma find_dist_constant: forall s s' v g v' x y,
  valid s v g ->
  valid s' v g ->
  find_dist s v' = Some x ->
  find_dist s' v' = Some y ->
  x = y.
Proof.
  intros. pose proof (valid_multi _ _ _ _ H H0). rewrite find_dist_in in H1.
  rewrite find_dist_in in H2. pose proof (no_dups_output _ _ _ H).
  pose proof (no_dups_output _ _ _ H0). epose proof (NoDup_pairs' _ _ _ y H4 H1).
  pose proof (NoDup_pairs' _ _ _ x H5 H2).
  destruct H3.
  pose proof (output_preserved_strong _ _ _ _ _ _ H H3 H1).
  apply H7 in H8. subst. reflexivity. 
  pose proof (output_preserved_strong _ _ _ _ _ _ H0 H3 H2).
  apply H6 in H8. assumption. apply H0. apply H.
Qed.

(*Few more helper lemmas*)

(*Heap is WF*)
Lemma heap_WF: forall s v g,
  valid s g v ->
  get_heap s = Heap.Empty \/ WF (get_heap s).
Proof.
  intros. induction H.
  - simpl. right. constructor.
  - inversion H0; subst. destruct IHvalid. simpl in H4. subst. inversion H3.
    simpl in H4. right. unfold get_heap. constructor. intros.
    simpl in H5. destruct H5. subst. eapply splitMInT_WF. 2 : { apply H3. }
    assumption. 
    destruct c. destruct p0. destruct p0. simpl in H5. rewrite in_map_iff in H5.
    destruct H5. destruct x. destruct_all. subst. constructor.
    destruct IHvalid. simpl in H4. subst. inversion H3. simpl in *. right.
    eapply splitMInT_WF. apply H4. apply H3.
Qed.

(*If (a,b) is on heap and b is not chosen, (a,b) still on heap*)
Lemma heap_preserved: forall s v g s' v' d,
  valid s g v ->
  vIn (get_graph s) v' = true ->
  In_Heap (d, v') (get_heap s) ->
  sp_step s s' ->
  vIn (get_graph s') v' = true ->
  In_Heap (d, v') (get_heap s').
Proof.
  intros. inversion H2; subst.
  - unfold get_heap. simpl in H1. destruct (N.eq_dec v0 v'). subst.
    simpl in H3. apply match_remain_some in H5. destruct_all. apply H5 in H3.
    destruct_all. contradiction.
    rewrite in_heap_splitMin in H1. 3: { rewrite <- splitMin_equiv in H6. inversion H6. apply H8.
    intro; subst; inversion H6. } destruct H1. inversion H1; subst. contradiction.
    rewrite in_heap_mergeAll. rewrite in_heap_exists. exists h'. split. left. reflexivity. assumption.
    intro; subst; inversion H6.
  - simpl in *. rewrite in_heap_splitMin in H1. 3 : { rewrite <- splitMin_equiv in H6. inversion H6; subst.
    apply H8. intro; subst; inversion H6. } destruct H1. inversion H1; subst.
    rewrite <- match_in in H0. destruct_all. rewrite H0 in H5. inversion H5.
    assumption. intro; subst; inversion H6.
Qed.

(*multistep version*)
Lemma heap_preserved_multi: forall s v g s' v' d,
  valid s g v ->
  vIn (get_graph s) v' = true ->
  In_Heap (d, v') (get_heap s) ->
  sp_multi s s' ->
  vIn (get_graph s') v' = true ->
  In_Heap (d, v') (get_heap s').
Proof.
  intros. induction H2. assumption. 
  destruct (vIn (get_graph y) v') eqn : V.
  - apply IHmulti. eapply v_step. apply H. assumption. reflexivity.
    eapply heap_preserved; try(apply H); try assumption. assumption.
  - assert (valid y g v). eapply v_step. apply H. assumption.
    assert (valid z g v). eapply multi_valid. apply H5. assumption.
    pose proof (graph_subset _ _ _ _ H5 H6  H4). destruct_all. apply H7 in H3. rewrite H3 in V. inversion V.
Qed.

(*Everything in the heap is the distance of a valid path*)
Lemma heap_valid_path: forall s v g v' d,
  valid s g v ->
  In_Heap (d, v') (get_heap s) ->
  exists l, Wpath g v v' l d.
Proof.
  intros. generalize dependent v'. revert d. induction H; intros.
  - simpl in H0. destruct H0. inversion H0; subst. exists (v' :: nil). constructor. assumption. 
    destruct H0.
  - inversion H0; subst.
    + unfold get_heap in H1. rewrite in_heap_mergeAll in H1. rewrite in_heap_unfold in H1.
      destruct H1. apply IHvalid. simpl. rewrite in_heap_splitMin. right. apply H1. 
      intro; subst; inversion H4. rewrite <- splitMin_equiv in H4. inversion H4. apply H6.
      intro; subst; inversion H4. rewrite in_heap_exists in H1. destruct H1 as [h''].
      destruct H1. unfold expand_dist in H1. destruct c. destruct p0. destruct p0. 
      rewrite in_map_iff in H1. destruct H1. destruct x. destruct_all. subst. simpl in H5.
      destruct H5. inversion H1; subst. clear H1. 
      specialize (IHvalid d0 v0). assert (exists l : list Node, Wpath g v v0 l d0).
      apply IHvalid. simpl. rewrite in_heap_splitMin. left. reflexivity.
      intro; subst; inversion H4. rewrite <- splitMin_equiv in H4. inversion H4; eassumption.
      intro; subst; inversion H4. destruct H1 as [l]. exists (v' :: l). econstructor.
      apply H1. eapply Wmatch_context in H3. destruct_all; subst.
      apply H7 in H6. pose proof (graph_subset_start _ _ _ H). simpl in H3. apply H3. assumption.
      destruct H1.
    + apply IHvalid; simpl in *. rewrite in_heap_splitMin. right. apply H1. intro; subst; inversion H4.
      rewrite <- splitMin_equiv in H4. inversion H4; eassumption. intro; subst; inversion H4.
Qed.

Lemma next_graph: forall s  v' d h o g' s',
  splitMinT (get_heap s) = Some(d, v', h) ->
  match_ v' (get_graph s) = (o, g') ->
  sp_step s s' ->
  get_graph s' = g'.
Proof.
  intros. inversion H1; subst. simpl in *. rewrite H4 in H. inversion H; subst.
  rewrite H3 in H0. inversion H0; subst. reflexivity. simpl in *. rewrite H4 in H. inversion H; subst.
  rewrite H3 in H0. inversion H0. reflexivity.
Qed. 
(*
(*For convenience: if a vertex has a distance at the end but is not discovered at the current state, that is on
  the heap*)
Lemma dist_on_heap: forall s v g v' d' sd,
  valid s g v ->
  sp_multi s sd ->
  In (d', v') (get_dists sd) ->
  vIn (get_graph s) v' = true ->
  In_Heap (d',v) (get_heap s).
Proof.
  intros. assert (valid sd g v). eapply multi_valid. apply H. assumption.
  pose proof (output_is_added _ _ _ _ _ H2 H1). destruct_all.
  *)

(*For final lemma and theorem, we need more*)
(*Need 2 additional assumptions: the edge weights are nonnegative and there are no parallel edges. The latter
  restriction may be removed, but it would require more complicated functions in [Path.v]*)
Variable g : gr a b.
Variable Hsimple: forall u v w w', WeIn g u v w -> WeIn g u v w' -> w = w'.
Variable HNonneg: forall u v w, WeIn g u v w -> #0 <= w = true.

(*Therefore, heap values geq shortest path distance*)
Lemma heap_geq_sp_dist: forall s v  v' d l w,
  shortest_wpath g v v' l ->
  path_cost g l == Some w = true ->
  valid s g v ->
  In_Heap (d, v') (get_heap s) ->
  w <= d = true.
Proof.
  intros. eapply heap_valid_path in H2. 2 : { apply H1. }
  destruct H2 as [l']. assert (path_cost g l' = Some d). apply path_cost_sum.
  assumption. assumption. exists v. exists v'. assumption.
  unfold shortest_wpath in H. destruct_all.
  assert (path' g v v' l'). eapply path'_WPath.
  assumption. assumption. exists d. assumption. apply H4 in H5.
  unfold le_weight in H5. unfold lt_weight in H5.
  unfold lt_weight_b in H5. unfold eq_weight in H5. unfold eq_weight_b in H5.
  rewrite H3 in H5. destruct (path_cost g l). rewrite Base.simpl_option_some_eq in H0.
  order b. rewrite some_none_eq in H0. inversion H0.
Qed.

Require Import Coq.micromega.OrderedRing.


(*Theorem 24.6 of CLRS*)
Theorem sp_invariant: forall s s' v,
  valid s g v ->
  sp_step s s' ->
  (forall v', vIn g v' = true ->
  vIn (get_graph s) v' = false ->
  find_dist s v' == sp_distance g (find_shortest_wpath g v v') = true) ->
  forall v', vIn g v' = true ->
  vIn (get_graph s') v' = false ->
  find_dist s' v' == sp_distance g (find_shortest_wpath g v v') = true.
Proof.
  intros. assert (V: valid s' g v). eapply v_step. apply H. assumption.  inversion H0; subst.
  - simpl in H3. simpl in H1. destruct (N.eq_dec v0 v').
    + subst. remember (g', mergeAll (h' :: expand_dist d v' c), p ++ (d, v') :: nil) as s'.
      rewrite Heqs'. assert (find_dist (g', mergeAll (h' :: expand_dist d v' c), p ++ (d, v') :: nil) v' = Some d). {
      rewrite find_dist_in. simpl. apply in_or_app. right. left. reflexivity. rewrite Heqs' in H0. eapply v_step.
      apply H. assumption. }
      rewrite H7. destruct (sp_distance g (find_shortest_wpath g v v')) eqn : D.
      -- rewrite Base.simpl_option_some_eq. destruct (d == b0) eqn : E. reflexivity.
         (*What if v' is the start vertex?*)
         destruct (N.eq_dec v v').
         ++ subst. remember (g', mergeAll (h' :: expand_dist d v' c), p ++ (d, v') :: nil) as s'.
            assert (#0 == b0 = true). { unfold sp_distance in D. destruct (find_shortest_wpath g v' v') eqn : P.
            pose proof (sp_distance_unique g Hsimple HNonneg v' v' (v' :: nil) l).
            simpl in H8. rewrite H2 in H8. rewrite D in H8.
            rewrite Base.simpl_option_some_eq in H8. apply H8. apply shortest_path_refl. assumption. assumption.
            assumption. apply find_shortest_wpath_correct. assumption. assumption. assumption. inversion D. }
            assert (d = #0). { rewrite find_dist_in in H7. pose proof (start_0_dist s' g v' V).
            assert (In (#0, v') (get_dists s')). apply H9. subst. intro. simpl in H10. destruct p; inversion H10.
            apply no_dups_output in V.
            epose proof (NoDup_pairs' _ _ _ _ V H7 H10). assumption. apply V. } subst.
            rewrite H8 in E. inversion E.
            (*We now know that v' cannot be the start vertex*)
         ++ (*There must be a shortest path from v to v'*)
             unfold sp_distance in D. destruct (find_shortest_wpath g v v') eqn : P.
             apply find_shortest_wpath_correct in P.  assert (S:= P). unfold shortest_wpath in P.
             destruct P.
               (*Therefore, let us consider the first vertex in S on the path such that its sucessor is not in S*)
             pose proof (path_start g Hsimple HNonneg _ _  _ H8). destruct H10 as [l1].
             assert (exists x y, rev_split_function (fun z => negb(vIn g0 z)) l = Some (x,y)). {
             rewrite H10. rewrite rev_split_function_exists. exists v'. split.
             subst. inversion H8; subst. contradiction. destruct l1. inversion H10; subst. contradiction.  inversion H10; subst.
             left. reflexivity. epose proof (match_in g0 v').
             assert (vIn g0 v' = true). { apply H11. exists c. exists g'. assumption. } rewrite H12. reflexivity.
             assert (In (#0, v) (get_dists (g0, h, p))). { eapply start_0_dist. apply H.
             intro. rewrite dists_nil_iff_start in H11. 2 : { apply H. } unfold start in H11.
             inversion H11; subst. remember ((g', mergeAll (h' :: expand_dist d v' c), nil ++ (d, v') :: nil)) as s'.
             simpl in H6. inversion H6; subst. contradiction. } 
             assert (In v (map snd (get_dists (g0, h, p)))). { rewrite in_map_iff. exists (#0,v). simplify'. }
             rewrite graph_iff_not_output in H12. simpl in H12. rewrite H12. reflexivity. apply H.
             eapply start_in. apply H. }
             destruct H11 as [x]. destruct H11 as [y]. rewrite rev_split_function_def in H11.
             destruct H11 as [l1']. destruct H11 as [l2']. destruct_all.
             rewrite negb_true_iff in H12. rewrite negb_false_iff in H13.
             setoid_rewrite negb_true_iff in H14. 
             (*We can find a state at which x is discovered,
               and it must be before the current state (because x is in the output). So by induction, 
               this distance is its shortest path distance*)
             assert (In x (map snd (get_dists (g0, h, p)))). eapply graph_iff_not_output.
             apply H. eapply path_in_graph in H8. apply H8. assumption. assumption. rewrite H11.
             apply in_or_app. right. simpl. right. left. reflexivity. simpl. assumption.
             rewrite in_map_iff in H15. destruct H15. destruct x0. destruct H15. simpl in H15. 
             rewrite H15 in H16. clear H15. apply (output_is_added _ _ _ _ _ H) in H16.
             destruct H16 as [sp]. destruct H15 as [sx]. destruct H15 as [cx]. destruct H15 as [gx].
             destruct H15. destruct H16. destruct H17. destruct H18 as [hx].
             destruct_all.
             (*We can apply the IH to find that x's distance was set correctly*)
             assert (find_dist sx x = Some b1). { rewrite find_dist_in. rewrite H22. apply in_or_app. right.
             left. reflexivity. eapply v_step. apply H15. apply H16. } 
             assert ((find_dist sx x == sp_distance g (find_shortest_wpath g v x)) = true). {
             assert ((find_dist (g0, h, p) x == sp_distance g (find_shortest_wpath g v x)) = true). {
             eapply H1. eapply  path_in_graph. assumption. assumption. apply H8. rewrite H11.
             apply in_or_app. right. right. left. reflexivity. assumption. }
             assert (find_dist (g0, h, p) x = Some b1). { rewrite find_dist_in.
             eapply output_preserved_strong. eapply v_step. apply H15. apply H16.
             assumption. rewrite find_dist_in in H23. assumption. eapply v_step. apply H15. assumption.
             apply H. } rewrite H25 in H24. rewrite H23. assumption. }
             (*Now we need to prove that y is set to its correct distance*)
             (*Plan: show that shortest path dist is b0 + w, and that is in the heap.
               y has not been discovered yet, but we know that it will. Need to prove that
               all distances in the heap are >= shortest path distance and preserved iff still not discovered,
               so when y is discoverd, b0 + w will be smallest and it will be chosen. Therefore, at the end,
               y has its smallest distance. We know that v' will add a distance of d, so it has a distance of d
               at the end. By upper bound, d >= shortest path. b0 + w = dist(y) <= dist(u) (bc nonneg) <= d
               but we know that d <= b0 + w bc both are in the heap and heap finds min. So 
               dist(u) = d, as desired (then can push that back by lemma)
                - *)
              assert (exists sd, sp_multi s' sd /\ done sd = true). exists (sp_tail s').
              split. apply sp_tail_multi. apply sp_tail_done. destruct H25 as [sd].
              destruct H25. assert (find_dist sd y == sp_distance g (find_shortest_wpath g v y) = true). {
              (*Step 1: y's shortest path distance is b1 + w'*)
              assert (shortest_wpath g v y (y :: x :: l2')). { eapply shortest_path_subpath.
              assumption. assumption. rewrite <- H11. apply S. }
              assert (exists w, path_cost g (y :: x :: l2') = Some w). apply path_cost_path'.
              assumption. assumption. exists v. exists y. unfold shortest_wpath in H27. apply H27.
              destruct H28 as [dy].
              assert (path_cost g (y :: x :: l2') == Some dy = true). rewrite H28.
              rewrite Base.simpl_option_some_eq. destruct HEqLaw; apply Eq_refl.
              assert (P := H27). unfold shortest_wpath in P. destruct P. clear H31.
              rewrite path'_WPath in H30. destruct H30 as [dy'].
              assert (path_cost g (y :: x :: l2') = Some dy'). { rewrite path_cost_sum. exists v. exists y.
              assumption. assumption. assumption. } rewrite H28 in H31. inversion H31; subst.
              inversion H30; subst. apply hd_path in H32. clear H31. subst.
              assert (shortest_wpath g v x (x :: l2')). eapply shortest_path_subpath.
              assumption. assumption. assert ((y :: x :: l2') = ((y :: nil) ++ x :: l2')).
              simpl. reflexivity. rewrite <- H10. apply H27. 
              assert (Some b1 == path_cost g (x :: l2') = true ). {
              rewrite H23 in H24. unfold sp_distance in H24.  destruct (find_shortest_wpath g v x) eqn : F.
              assert (path_cost g l == path_cost g (x :: l2') = true). pose proof sp_distance_unique. simpl in H31. eapply H31.
              assumption. assumption. apply find_shortest_wpath_correct. assumption. assumption. apply F.
              assumption. 
              destruct Base.EqLaws_option.
              eapply Eq_trans. apply H24. apply H31. destruct Base.EqLaws_option. rewrite Eq_sym in H24.
              rewrite some_none_eq in H24. inversion H24. }
              assert (Some ( _+_ b1 w') == sp_distance g (find_shortest_wpath g v y) = true). {
              destruct (path_cost g (x :: l2')) eqn : T.  rewrite edge_weight_in in H36.
              epose proof (path_cost_cons _ _ _ _ _ _ T H36). 
              rewrite Base.simpl_option_some_eq in H31. 
              unfold sp_distance. destruct( find_shortest_wpath g v y ) eqn : F.
              assert (path_cost g (y :: x :: l2') == path_cost g l = true). 
              pose proof sp_distance_unique.  simpl in H33. eapply H33. assumption. assumption.
              apply H27. apply find_shortest_wpath_correct. assumption. assumption. apply F.
              destruct (Base.EqLaws_option). eapply Eq_trans. 2 : { apply H33. }
              eapply Eq_trans. 2 : { rewrite Eq_sym. apply H32. } 
              rewrite Base.simpl_option_some_eq. destruct HorderedRing. eapply rplus_eq.
               assumption. destruct HEqLaw. apply Eq_refl0. rewrite find_shortest_wpath_none in F.
              exfalso. apply (F (y :: x :: l2')). unfold shortest_wpath in H27. apply H27. assumption.
              assumption. assumption. destruct (Base.EqLaws_option). rewrite Eq_sym in H31. rewrite some_none_eq in H31.
              inversion H31. } 
              (*Step 2: b1 + w' is in the heap at state sx*)
              assert (In_Heap (_+_ w' b1, y) (get_heap sx)). { rewrite H18.
              rewrite in_heap_mergeAll. rewrite in_heap_unfold. right. unfold expand_dist.
              destruct cx. destruct p0. destruct p0. rewrite in_heap_exists. exists (unit (_+_ w' b1) y).
              split. rewrite in_map_iff. exists (w', y). split. reflexivity. assert (T:= H20).
              apply Wmatch_context in H20. destruct_all; subst. apply H34.
              eapply edge_in_state. apply H15. assumption. split. rewrite <- match_in.
              exists (a2, n1, a1, a0). exists gx. assumption. eapply graph_subset.
              apply H15. apply H. eapply multi_trans. apply multi_R. apply H16. apply H17. simpl. assumption.
              simpl. left. reflexivity. }
              (*Step 3: y has not been discovered, but it will at some future state sy*)
              assert (valid sd g v). eapply multi_valid. eapply v_step. apply H. eassumption. apply H25.
              assert (exists l, path' g v y l). unfold shortest_wpath in H27. exists (y :: x :: l2'). apply H27.
              pose proof (reachable_in_output _ _ _ _ H34 H26 H35). rewrite in_map_iff in H37.
              destruct H37. destruct x1. simpl in H37. destruct H37. subst.
              pose proof (output_is_added _ _ _ _ _ H34 H38). destruct H37 as [sy].
              destruct H37 as [syn]. destruct H37 as [c'']. destruct H37 as [g''].
              destruct_all.
              (*Step 4: at state sy, b0 + w will be chosen bc it is smallest *)
              assert (sp_multi (g0, h, p) sy). { pose proof (valid_multi _ _ _ _ H37 H).
              destruct H46. inversion H46. subst. apply multi_refl.
              subst. assert (y0 = syn). eapply sp_step_deterministic. apply H47. assumption. subst.
              clear H47. assert (vIn (get_graph syn) y = true). eapply graph_subset. eapply v_step. apply H37. assumption.
              apply H. assumption. simpl. assumption. pose proof (next_graph _ _ _ _ _ _ _ H44 H43 H39).
              rewrite H49 in H47. apply match_remain_some in H43. destruct_all. apply H43 in H47.
              destruct_all; contradiction. assumption. }
              assert (b2 == _+_ w' b1 = true). { 
              assert (In_Heap (_+_ w' b1, y) (get_heap sy)). eapply heap_preserved_multi.
              eapply v_step. apply H15. apply H16. eapply graph_subset. eapply v_step. apply H15. assumption.
              apply H. assumption. simpl. assumption. assumption. eapply multi_trans. apply H17. assumption.
              rewrite <- match_in. exists c''. exists g''. assumption. 
              pose proof (heap_WF sy v g H37). destruct H48. rewrite H48 in H44. inversion H44.
              epose proof (WF_min _ _ _ _ H48 H44 (_+_ w' b1) y H47).
              unfold sp_distance in H32.
              destruct ((find_shortest_wpath g v y)) eqn : L. destruct (path_cost g l) eqn : P.
              pose proof heap_geq_sp_dist. assert (_GHC.Num.+_ w' b1 <= b2 = true). eapply H50.
              apply find_shortest_wpath_correct. assumption. assumption. apply L. rewrite P.
              destruct (Base.EqLaws_option). eapply Eq_trans. rewrite Eq_sym. apply H32.
              rewrite Base.simpl_option_some_eq. destruct real_ring. destruct SORrt. apply Radd_comm.
              apply H37. rewrite in_heap_splitMin. left. reflexivity. intro; rewrite H51 in H44; inversion H44.
              rewrite <- splitMin_equiv in H44; inversion H44; subst. apply H52. intro; rewrite H51 in H44; inversion H44.
              order b. destruct (Base.EqLaws_option). rewrite Eq_sym in H32. rewrite some_none_eq in H32. inversion H32.
               destruct (Base.EqLaws_option). rewrite Eq_sym in H32. rewrite some_none_eq in H32. inversion H32. }
              (*Step 5: At the end, therefore, y is set to its correct distance*)
              assert (find_dist syn y == sp_distance g (find_shortest_wpath g v y) = true). {
              destruct (Base.EqLaws_option). eapply Eq_trans. 2 : { apply H32. }
              eapply Eq_trans. 2 : { assert (_GHC.Num.+_ w' b1 == (_GHC.Num.+_ b1 w') = true).
              destruct real_ring. destruct SORrt. apply Radd_comm. 
              assert  ((Some (_GHC.Num.+_ w' b1) == Some (_GHC.Num.+_ b1 w')) = true).
              rewrite Base.simpl_option_some_eq. assumption. apply H49. }
              eapply Eq_trans. 2 : { assert (Some b2 == Some (_GHC.Num.+_ w' b1) = true).
              rewrite Base.simpl_option_some_eq. assumption. apply H48. }
              assert (find_dist syn y = Some b2). rewrite find_dist_in. rewrite H45.
              apply in_or_app. right. left. reflexivity. eapply v_step. apply H37. assumption.
              rewrite H48. apply Eq_refl. }
              assert (find_dist syn y = find_dist sd y). { assert (find_dist syn y = Some b2).
              rewrite find_dist_in. 
              rewrite H45. apply in_or_app. right. left. reflexivity. eapply v_step. apply H37.
              assumption. rewrite H49. symmetry. rewrite find_dist_in. eapply output_preserved_strong.
              eapply v_step. apply H37. apply H39. assumption. rewrite <- find_dist_in. assumption. 
              eapply v_step. apply H37. apply H39. apply H34. } rewrite <- H49. assumption.
              assumption. assumption. }
              (*Yay, the hardest part is done! From here on out, we should basically be able to follow CLRS*)
              4 : { inversion D. } 2 : { assumption. } 2 : { assumption. }
              (*Need to prove that y's sp distance is <= v''s sp distance*)
              destruct (find_dist sd y) eqn : FY.
              assert (b2 <= b0 = true). {
              assert (shortest_wpath g v y (y :: x :: l2')). eapply shortest_path_subpath.
              assumption. assumption. rewrite <- H11. eassumption.
              destruct (path_cost g (y :: x :: l2')) eqn : P1.
              assert (b2 == b3 = true). destruct ((find_shortest_wpath g v y)) eqn : F. simpl in H27.
              apply find_shortest_wpath_correct in F.
              pose proof (sp_distance_unique _ Hsimple HNonneg _ _ _ _ H28 F). 
              unfold sp_distance at 1 in H29. rewrite P1 in H29. simpl in H29.
              assert (Some b2 == Some b3 = true). destruct (Base.EqLaws_option). eapply Eq_trans.
              apply H27. rewrite Eq_sym. assumption. rewrite Base.simpl_option_some_eq in H30.
              assumption. assumption. assumption. simpl in H27. destruct (Base.EqLaws_option).
              rewrite Eq_sym in H27. rewrite some_none_eq in H27. inversion H27.
              assert (b3 <= b0 = true). {  
              assert (path_cost g (l1' ++ y :: x :: l2') == Some b0 = true). rewrite <- H11. rewrite D. 
              destruct (Base.EqLaws_option). apply Eq_refl. 
              pose proof (path_cost_app _ Hsimple HNonneg _ _ _ _ H30). destruct_all.
              rewrite P1 in H32. rewrite Base.simpl_option_some_eq in H32. 
              destruct (path_cost g (l1' ++ y :: nil)) eqn : T.
              rewrite Base.simpl_option_some_eq in H31.
              assert (#0 <= b4 = true). pose proof (path_cost_nonneg). eapply H34. 3 : { apply T. }
              assumption. assumption. 
              destruct HorderedRing. eapply rle_eq. 2 : { apply H33. } destruct HEqLaw; apply Eq_refl.
              eapply rle_eq. destruct HEqLaw; apply Eq_refl. eapply rplus_eq. destruct HEqLaw; apply Eq_refl.
              destruct HEqLaw; rewrite Eq_sym. apply H32.
              assert (#0 <= x1 = true).  destruct HEqLaw. eapply rle_eq. apply Eq_refl.
              rewrite Eq_sym. apply H31. assumption. assert (b3 == _+_ #0 b3 = true).
              destruct real_ring. destruct SORrt. destruct HEqLaw; rewrite Eq_sym. apply Radd_0_l .
              eapply rle_eq. apply H36. destruct HEqLaw; apply Eq_refl.
              apply (Rplus_le_mono_r real_ring). assumption. rewrite some_none_eq in H31. inversion H31. }
              order b. pose proof path_cost_path'. assert ((exists w : b, path_cost g (y :: x :: l2') = Some w)). apply H29.
              assumption. assumption. exists v. exists y. unfold shortest_wpath in H28. apply H28. destruct_all. rewrite H30 in P1.
              inversion P1. } 
              (*Now, we know that v''s sp distance is smaller than its heap distance*)
              assert (b0 <= d = true). { eapply heap_geq_sp_dist. 2 : { rewrite D.
              destruct HEqLaw; apply Eq_refl. }  apply S. apply H. simpl. 
              rewrite in_heap_splitMin. left. reflexivity. intro; subst; inversion H6.
              rewrite <- splitMin_equiv in H6; inversion H6. apply H30. intro; subst; inversion H6. }
              assert (b2 <= d = true) by order b.
              (*Now we know that y's heap distance is smaller than v''s. But because the heap chooses the smallest,
                d <= b2*)
              (*Unfortunately, need to redo some of it because we lost information about y's heap*)
              assert ((exists o, In_Heap (o, y) (get_heap sx) /\ b2 == o = true) /\ vIn (get_graph sx) y = true). { rewrite H18.
              setoid_rewrite in_heap_mergeAll. setoid_rewrite in_heap_unfold. unfold expand_dist.
              destruct cx. destruct p0. destruct p0. setoid_rewrite in_heap_exists.
              assert (shortest_wpath g v y (y :: x :: l2')). eapply shortest_path_subpath. assumption.
              assumption. rewrite <- H11. apply S.
              assert (S' := H31).
              unfold shortest_wpath in H31. destruct H31. inversion H31; subst.
              assert (v'0 = x).  rewrite path'_WPath in H34. destruct H34 as [w'].
              eapply hd_path. apply H10. assumption. assumption. subst.
              rewrite edge_weight in H38. destruct H38 as [w'].  
              assert (exists w, path_cost g (x :: l2') = Some w). apply path_cost_path'. assumption.
              assumption. exists v. exists x. assumption. destruct H33 as [pw].
              apply edge_weight_in in H10.
              epose proof (path_cost_cons _ _ _ _ _ _ H33 H10).
              assert (b1 == pw = true). { assert (shortest_wpath g v x (x :: l2')). eapply shortest_path_subpath.
              assumption. assumption. assert (y :: x :: l2' = (y :: nil) ++ (x :: l2')). simpl. reflexivity.
              rewrite <- H36. apply S'.
              destruct ((find_shortest_wpath g v x)) eqn : T.  simpl in H24. destruct (path_cost g l) eqn : T'.
              rewrite H23 in H24. rewrite Base.simpl_option_some_eq in H24.
              assert (path_cost g (x :: l2') == path_cost g l = true). pose proof sp_distance_unique.
              simpl in H37. eapply H37. assumption. assumption. apply H36. apply find_shortest_wpath_correct.
              assumption. assumption. assumption.
              destruct HEqLaw. eapply Eq_trans. 
              apply H24. assert (Some b3 == Some pw = true). destruct (Base.EqLaws_option). eapply Eq_trans0.
              assert (Some b3 == path_cost g l = true). rewrite T'. apply Eq_refl. apply H38.
              eapply Eq_trans0. 2 : { rewrite <- H33. apply Eq_refl0. } rewrite Eq_sym0. assumption.
              rewrite  Base.simpl_option_some_eq in H38. assumption. destruct (Base.EqLaws_option); rewrite
              Eq_sym in H24. rewrite H23 in H24. rewrite some_none_eq in H24. inversion H24.
              simpl in H24. rewrite H23 in H24. destruct (Base.EqLaws_option); rewrite Eq_sym in H24.
              rewrite some_none_eq in H24; inversion H24. }
              assert (V': vIn (get_graph sx) y = true). eapply graph_subset. eapply v_step. apply H15. assumption.
              apply H. assumption. simpl. assumption. split.
              exists (_+_ w' b1). split. right.
              exists (unit (_+_ w' b1) y). rewrite in_map_iff. split. exists (w', y). split. reflexivity.
              rewrite <- edge_weight_in in H10. assert (M:= H20). apply Wmatch_context in H20. apply H20.
              rewrite edge_in_state. split. rewrite <- match_in. exists ( (a2, n1, a1, a0)). exists gx. assumption.
              eapply graph_subset. apply H15. apply H. eapply multi_trans. apply multi_R. eassumption. assumption.
              simpl. assumption. apply H15. assumption. assumption. simpl. left. reflexivity.
              assert (path_cost g (y :: x :: l2') == Some b2 = true). { destruct (Base.EqLaws_option). eapply Eq_trans.
              2 : { rewrite Eq_sym. apply H27. } destruct ((find_shortest_wpath g v y)) eqn : P1.
              unfold sp_distance. pose proof sp_distance_unique. simpl in H37. eapply H37.
              assumption. assumption. apply S'. apply find_shortest_wpath_correct. assumption. assumption.
              assumption. simpl in H27. destruct (Base.EqLaws_option); rewrite Eq_sym in H27. rewrite some_none_eq in H27;
              inversion H27. } 
              assert ( Some b2 == Some (_GHC.Num.+_ pw w') = true). destruct (Base.EqLaws_option); eapply Eq_trans.
              rewrite Eq_sym. apply H37. assumption. 
               rewrite Base.simpl_option_some_eq in H38. destruct HEqLaw. eapply Eq_trans.
              apply H38. destruct HorderedRing. eapply Eq_trans. destruct real_ring. destruct SORrt. apply Radd_comm.
              eapply rplus_eq. apply Eq_refl. rewrite Eq_sym. assumption. assumption. assumption. } destruct H31.
              destruct H31 as [o]. destruct H31.
              (*Now we know that b3 is in the heap, so we want to show that d <= b2 = b3 = o*)
              assert (d <= o = true). eapply WF_min in H6. apply H6. pose proof (heap_WF _ _ _ H).
              destruct H34. simpl in H34. subst. inversion H6. simpl in H34. apply H34. 
              assert (In_Heap (o, y) (get_heap (g0, h, p))). eapply heap_preserved_multi.
              eapply v_step. apply H15. eassumption. assumption. assumption. assumption. simpl.
              assumption. simpl in H34. apply H34. order b. (*CONTRADICTION!*)
              assert (shortest_wpath g v y (y :: x :: l2')). eapply shortest_path_subpath.
              assumption. assumption. rewrite <- H11. apply S.
              destruct ((find_shortest_wpath g v y)) eqn : P. simpl in H27.
              apply find_shortest_wpath_correct in P. assert (exists w, path_cost g l0 = Some w).
              apply path_cost_path'. assumption. assumption. exists v. exists y. unfold shortest_wpath in P.
              apply P. destruct_all. rewrite H29 in H27.
               rewrite some_none_eq in H27. inversion H27. assumption. assumption.
              rewrite find_shortest_wpath_none in P. unfold shortest_wpath in H28. destruct_all. exfalso.
              eapply P. apply H28. assumption. assumption.
       -- destruct ((find_shortest_wpath g v v')) eqn : P. 
          simpl in D. assert (exists w, path_cost g l = Some w). apply path_cost_path'.
          assumption. assumption. exists v. exists v'. apply find_shortest_wpath_correct in P.
          unfold shortest_wpath in P. apply P. assumption. assumption.
          destruct_all. rewrite D in H8. inversion H8. rewrite find_shortest_wpath_none in P.
          assert (exists sd, sp_multi s' sd /\ done sd = true). exists (sp_tail s'). split.
          apply sp_tail_multi. apply sp_tail_done. destruct_all.
          assert (In (d, v') (get_dists x)). eapply output_preserved_strong. eapply v_step.  apply H.
          eassumption. assumption. subst. rewrite find_dist_in in H7. assumption. eapply v_step. apply H.
          assumption. assert (In v' (map snd (get_dists x))). rewrite in_map_iff. exists (d, v'). split. 
          reflexivity. assumption. rewrite output_iff_reachable in H11. 2 : { eapply multi_valid.
          eapply v_step. apply H. eassumption. assumption. } exfalso. destruct H11. apply (P x0). assumption.
          assumption. assumption. assumption.
    + destruct (Base.EqLaws_option). eapply Eq_trans. 2 : { apply H1. assumption. 
      eapply match_remain_some in H5. destruct_all. destruct (vIn g0 v') eqn : V'.
      assert (vIn g' v' = true). apply H5. split; auto. rewrite H8 in H3. inversion H3.
      reflexivity. } 
      assert (find_dist (g', mergeAll (h' :: expand_dist d v0 c), p ++ (d, v0) :: nil) v' = find_dist (g0, h, p) v'). {
      destruct (find_dist (g0, h, p) v') eqn : F. rewrite find_dist_in in F.
      rewrite find_dist_in. simpl. simpl in F. apply in_or_app. left. assumption.
      eapply v_step. apply H. eassumption. apply H.
      rewrite find_dist_not in F. simpl in F.
      assert (In v' (map snd (get_dists (g', mergeAll (h' :: expand_dist d v0 c), p ++ (d, v0) :: nil)))).
      eapply graph_iff_not_output. eapply v_step. apply H. assumption. assumption. simpl. assumption.
      simpl in H7. unfold map in H7. rewrite map_app in H7. apply in_app_or in H7. destruct H7.
      rewrite in_map_iff in H7. destruct_all. destruct x. simpl in *; subst. exfalso. apply (F b0). assumption.
      simpl in H7. destruct H7. contradiction. destruct H7. }
      rewrite H7. apply Eq_refl.
  - simpl in *. eapply match_remain_none in H5. subst. destruct (Base.EqLaws_option). eapply Eq_trans. 2 : { apply H1. assumption.
    assumption. } assert  (find_dist (g', h', p) v' = find_dist (g', h, p) v').
    destruct (find_dist (g', h', p) v') eqn : F. rewrite find_dist_in in F. symmetry. rewrite find_dist_in.
     simpl in *. assumption. apply H.  eapply v_step. apply H. assumption.
    rewrite find_dist_not in F. simpl in F. symmetry. rewrite find_dist_not. simpl. apply F.
    rewrite H5. apply Eq_refl.
Qed.

(*Trivially, we get the final results*)
Theorem sp_invariant_multi: forall s s' v,
  valid s g v ->
  sp_multi s s' ->
  (forall v', vIn g v' = true ->
  vIn (get_graph s) v' = false ->
  find_dist s v' == sp_distance g (find_shortest_wpath g v v') = true) ->
  forall v', vIn g v' = true ->
  vIn (get_graph s') v' = false ->
  find_dist s' v' == sp_distance g (find_shortest_wpath g v v') = true.
Proof.
  intros. induction H0. apply H1. assumption. assumption.
  apply IHmulti. eapply v_step. apply H. assumption.
  eapply sp_invariant. apply H. assumption. assumption. assumption.
Qed.

Theorem sp_correct: forall s v,
  valid s g v ->
  done s = true ->
  forall v', vIn g v' = true ->
  find_dist s v' == sp_distance g (find_shortest_wpath g v v') = true.
Proof.
  intros. destruct (find_dist s v') eqn : F.
  - assert (vIn (get_graph s) v' = false). eapply graph_iff_not_output. apply H. assumption.
    rewrite find_dist_in in F. rewrite in_map_iff. exists (b0, v'). split; try reflexivity. assumption.
    apply H. rewrite <- F. clear F.
    eapply sp_invariant_multi. apply v_start. eapply start_in. apply H.
    eapply valid_begins_with_start. assumption. intros. simpl in H4. rewrite H4 in H3. inversion H3.
    assumption. assumption.
  - rewrite find_dist_not in F.
    pose proof (output_iff_reachable). 
    assert (forall l, ~path' g v v' l). intros. intro. 
    assert (exists l, path' g v v' l). exists l. assumption. rewrite <- H2 in H4.
    2 : { apply H. } rewrite in_map_iff in H4. destruct_all. destruct x; subst. simpl in F.
    apply (F b0). assumption. assumption. 
    destruct ((find_shortest_wpath g v v')) eqn : F1.
    simpl. apply find_shortest_wpath_correct in F1. unfold shortest_wpath in F1.
    destruct_all. exfalso. apply (H3 l). assumption.
    assumption. assumption. simpl. destruct (Base.EqLaws_option). apply Eq_refl.
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
