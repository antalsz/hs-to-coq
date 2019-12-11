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
Require Import Proofs.GHC.List.

Require Import Coq.Wellfounded.Inverse_Image.

(* Inductive relation*)
Section Ind.

Context {a : Type} {b : Type} { gr : Type -> Type -> Type} {Hgraph : Graph.Graph gr} {Hlaw : Graph.LawfulGraph gr}
{Hnum: GHC.Num.Num b} {Heq: Base.Eq_ b} {HOrd: Base.Ord b} {Hreal: @GHC.Real.Real b Hnum Heq HOrd}
{Heq': Base.Eq_ a} {HOrd': Base.Ord a} (*{Herr: Err.Default (b)}*){Hlaw2 : (@WeightedGraphs.LawfulWGraph a b gr Hgraph) } {HEqLaw: Base.EqLaws b} {HOrdLaw: @OrdLaws b Heq HOrd HEqLaw}
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

(*We can slightly strengthen the theorem by removing the assuming that v' is in the graph*)
Theorem sp_correct_all: forall s v v',
  valid s g v ->
  done s = true ->
  find_dist s v' == sp_distance g (find_shortest_wpath g v v') = true.
Proof.
  intros. destruct (vIn g v') eqn : ?.
  - apply sp_correct. assumption. assumption. assumption.
  - assert (find_dist s v' = None). { destruct (find_dist s v') eqn : F.
    rewrite find_dist_in in F. pose proof (output_iff_reachable).
    assert (In v' (map snd (get_dists s))). rewrite in_map_iff. exists (b0, v').
    split. reflexivity. assumption. rewrite H1 in H2. 2 : { apply H. }
    destruct_all. apply in_path' in H2. destruct H2. rewrite Heqb0 in H3. inversion H3. assumption.
    assumption. assumption. apply H. reflexivity. } rewrite H1.
    destruct ((find_shortest_wpath g v v')) eqn : F. simpl.
    apply find_shortest_wpath_correct in F. unfold shortest_wpath in F. destruct_all.
    apply in_path' in H2. destruct_all. rewrite H4 in Heqb0. inversion Heqb0.
    assumption. assumption. assumption. assumption. simpl.
    destruct (Base.EqLaws_option); apply Eq_refl.
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

(*Equivalence with Haskell version*)
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

(*Similar to [bf] in BFSProofs, we want to first prove the correctness of [spTree] in relation to [sp_distance].
  Eventually, we will provide a proofs of correctness that do not rely on [sp_distance] 
  (in particular [spTree_shortest_paths] and [spTree_reachable]), but before that, we prove the following results:
  1. [spTree] returns valid WPaths from the start to the second element in [sp_distance]
  2. The weight of the path equals the first element in [sp_distance], and the ending vertex is the second element
  3. Therefore, every path in [spTree] is in fact a shortest path*)

(*First, we need to prove that [dijsktra] returns valid WPaths. Simple induction will not work
  because the graph is changing at each step, so we will use a tail recursive approach, as in BFSProofs *)
Section ValidPath.
Definition d_state : Type := (gr a b) * (Heap b (LPath b)) * (list (LPath b)).

Definition d_graph (s: d_state) :=
  match s with
  | (g, _, _) => g
  end.

Definition d_heap (s: d_state) :=
  match s with
  | (_, h, _) => h
end.

Definition d_paths (s: d_state) :=
  match s with
  | (_, _, p) => p
  end.

Inductive d_step : d_state -> d_state -> Prop :=
  | d_find: forall (g: gr a b) (v : Node) (c: Context a b) (g': gr a b) (a' : b) 
      (d: b) (t: list (Node * b)) (h' h : Heap b (LPath b)) (p : list (LPath b)) (p' : (LPath b)),
      isEmpty g = false ->
      match_ v g = (Some c, g') ->
      splitMinT h = Some ((a', p'), h') ->
      p' = LP ((v,d) :: t) ->
      d_step (g, h, p) (g', mergeAll (h' :: expand d p' c), p ++ p' :: nil)
  | d_skip : forall (g: gr a b) (v: Node) (g': gr a b) (h h' : Heap b (LPath b))
     (p: list (LPath b)) (p': (LPath b)) (a' : b),
      isEmpty g = false ->
      match_ v g = (None, g') ->
      splitMinT h = Some ((a', p'), h') ->
      d_step (g, h, p) (g', h', p).

Definition d_start (g : gr a b) (v: Graph.Node) : d_state := (g, Heap.unit #0 (LP ((v, #0) :: nil)), nil).

(*A valid state is any state that can be reached from the start state.*)
Inductive d_valid : d_state -> (gr a b) -> Node -> Prop :=
  | v_d_start : forall g v, vIn g v = true -> d_valid (d_start g v) g v
  | v_d_step : forall s s' v g, d_valid s' g v -> d_step s' s -> d_valid s g v.

Lemma d_multi_valid: forall s s' v g,
  d_valid s g v ->
  multi d_step s s' ->
  d_valid s' g v.
Proof.
  intros. induction H0. assumption. apply IHmulti. eapply v_d_step. apply H. assumption.
Qed.

(*There are no paths that are nil on the heap at any time*)
Lemma heap_not_none: forall s v g k,
  d_valid s v g ->
  ~ In_Heap (k, (LP nil)) (d_heap s).
Proof.
  intros. induction H; intro.
  - simpl in H0. destruct H0. inversion H0. destruct H0.
  - inversion H0; subst.
    + unfold d_heap in H1. rewrite in_heap_mergeAll in H1. apply in_heap_unfold in H1.
      destruct H1. simpl in IHd_valid. apply IHd_valid.
      pose proof (in_heap_splitMin (k, (LP nil)) h h' a' (LP ((v0, d) :: t))).
      rewrite H5. right. assumption. intro. subst. simpl in H4. inversion H4. 
      rewrite <- splitMin_equiv in H4. inversion H4. reflexivity. intro. subst. simpl in H4. inversion H4.
      rewrite in_heap_exists in H1.
      destruct H1. destruct H1. simpl in IHd_valid.
      simpl in H1. destruct c. destruct p0. destruct p0. unfold Base.map in H1.
      rewrite in_map_iff in H1. destruct H1. destruct x0. destruct H1.
      rewrite <- H1 in H5. unfold unit in H5. simpl in H5. destruct H5. inversion H5. destruct H5.
    + simpl in IHd_valid. simpl in H1. destruct h. simpl in H4. inversion H4. simpl in H4. 
      inversion H4. subst. simpl in IHd_valid. rewrite in_heap_mergeAll in H1. apply IHd_valid.
      right. rewrite <- in_heap_equiv. apply H1. 
Qed.

Definition unlabel_path (l : LPath b) : Path := 
  match l with
  | LP l' => map fst l'
  end.

(*Characterizing the [expand] function*)
Lemma expand_preserves_valid: forall (w : Node) (l: LPath b) (l': list Node)
   (c : Context a b) (u v : Node) (y : b) (g g': gr a b) g'',
  unlabel_path l = w :: l' ->
  Wpath g v u (unlabel_path l) y ->
  match_ w g'' = (Some c, g') ->
  (forall u v w, WeIn g'' u v w -> WeIn g u v w) -> 
  (forall h, In h (expand y l c) ->
  forall x l'', In_Heap (x, l'') h -> 
  exists b' u', WeIn g w u' b' /\ x == op_zp__ b' y = true /\  Wpath g v u' (unlabel_path l'') x).
Proof.
  intros. unfold expand in H2. destruct c. destruct p. destruct p. destruct l.
  simpl in H3. rewrite in_map_iff in H3. destruct H3. destruct x0. destruct H3. unfold unit in H3.
  subst. simpl in H4. destruct H4. inversion H3; subst. simpl. simpl in H. rewrite H.  exists b0.
  exists n0. simpl in H0. rewrite H in H0. assert (WeIn g w n0 b0).  
  - apply Wmatch_context in H1. destruct_all. subst. apply H2. apply H6. assumption.
  - split. assumption. split. destruct HEqLaw; apply Eq_refl. 
    assert (u = w). inversion H0; subst; reflexivity. subst. econstructor. apply H0. apply H4.
  - destruct H3.
Qed. 

Lemma heap_path_value: forall s g v x u d t,
  d_valid s g v ->
  In_Heap (x, (LP ((u, d) :: t))) (d_heap s) ->
  x = d.
Proof.
  intros. induction H.
  - simpl in H0. destruct H0. inversion H0. subst. reflexivity. destruct H0.
  - inversion H1; subst.
    + unfold d_heap in H0. rewrite in_heap_mergeAll in H0. rewrite in_heap_unfold in H0.
      destruct H0.
      * simpl in IHd_valid. apply IHd_valid. rewrite in_heap_splitMin. right. apply H0.
        intro. subst. inversion H4. rewrite <- splitMin_equiv in H4. inversion H4. apply H6. intro.
        subst. inversion H4.
      * rewrite in_heap_exists in H0. destruct H0 as [h'']. destruct H0. simpl in H0.
        destruct c. destruct p0. destruct p0. rewrite in_map_iff in H0. destruct_all. destruct x0.
        unfold unit in H0. subst. simpl in H5. destruct H5. inversion H0; subst. reflexivity.
        destruct H0.
    + simpl in *. apply IHd_valid. rewrite in_heap_splitMin. right.
      apply H0. intro. subst. inversion H4. rewrite <- splitMin_equiv in H4. inversion H4. apply H6.
      intro. subst. inversion H4.
Qed. 

Lemma graph_subset_start': forall s v (g: gr a b),
  d_valid s g v ->
  (forall u v w, WeIn (d_graph s) u v w -> WeIn g u v w).
Proof.
  intros. induction H; subst.
  - simpl in H0. assumption.
  - inversion H1; subst.
    + simpl in H0. simpl in IHd_valid. apply IHd_valid.
      apply Wmatch_remain_some in H3. destruct_all. apply H5 in H0. destruct_all. assumption.
    + apply match_remain_none in H3. subst. apply IHd_valid. assumption.
Qed.

(*The result that we want: everything on the heap is a valid Wpath*)
Lemma in_heap_wpath: forall s g v x u d t,
  d_valid s g v ->
  In_Heap (x, (LP ((u, d) :: t))) (d_heap s) ->
  Wpath g v u (unlabel_path (LP ((u, d) :: t))) d.
Proof.
  intros. generalize dependent u. revert d. revert t. revert x. induction H; intros.
  - simpl in H0. destruct H0. inversion H0; subst. simpl.  constructor. assumption.
    destruct H0.
  - inversion H0; subst.
    + unfold d_heap in H1. rewrite in_heap_mergeAll in H1.
      rewrite in_heap_unfold in H1. destruct H1.
    * simpl in IHd_valid. eapply IHd_valid. rewrite in_heap_splitMin. right. apply H1. intro. subst.
      inversion H4. rewrite <- splitMin_equiv in H4.
    inversion H4; subst. apply H6. intro. subst. simpl in H4. inversion H4.
    * rewrite in_heap_exists in H1. destruct H1 as [h'']. destruct H1.
      simpl in H1. destruct c. destruct p0. destruct p0. rewrite in_map_iff in H1. destruct H1. destruct x0.
      destruct_all. subst. simpl in H5. destruct H5. inversion H1; subst. simpl. 
      specialize (IHd_valid a' t0 d0 v0). assert (Wpath g v v0 (unlabel_path (LP ((v0, d0) :: t0))) d0).
      apply IHd_valid. rewrite in_heap_splitMin. left. reflexivity. intro. simpl in H5; subst. inversion H4.
      rewrite <- splitMin_equiv in H4. inversion H4; simpl; subst. apply H7. intro. subst. inversion H4.
      simpl in H5. econstructor. apply H5. eapply Wmatch_context in H3. destruct_all. apply H8 in H6.
      eapply graph_subset_start'. apply H. simpl. assumption. destruct H1.
    + simpl in *. eapply IHd_valid. rewrite in_heap_splitMin. right. apply H1. intro. subst. inversion H4.
      rewrite <- splitMin_equiv in H4. inversion H4. apply H6. intro. subst. inversion H4.
Qed.

Lemma in_output_wpath: forall s v g u t d,
  d_valid s g v ->
  In (LP ((u, d) :: t)) (d_paths s) ->
  Wpath g v u (unlabel_path (LP ((u, d) :: t))) d.
Proof.
  intros.
  induction H; subst.
  - simpl in H0. destruct H0.
  - inversion H1; subst.
    + unfold d_paths in H0. apply in_app_or in H0. destruct H0. apply IHd_valid. apply H0.
      simpl in H0. destruct H0. inversion H0; subst. eapply in_heap_wpath. apply H. simpl. rewrite in_heap_splitMin.
      left. reflexivity. intro. subst. inversion H4. rewrite <- splitMin_equiv in H4. inversion H4. apply H6.
      intro. subst. inversion H4. destruct H0.
    + apply IHd_valid. simpl in *. assumption.
Qed.

(*To apply this result, we need a tail recursive version which we can prove equivalent*)

Program Instance default_d_state : Default d_state.
Next Obligation.
unfold d_state. apply ((empty, Heap.Empty, nil)).
Defined.

Equations d_tail (s: d_state) : d_state by wf (d_heap s, d_graph s) (bf_measure_heap) :=
  d_tail (g, h, l) =>  if bool_dec ((Heap.isEmpty h) || (@Graph.isEmpty gr Hgraph a b g)) true then (g, h, l) else
                        match (splitMinT h) as s return ((splitMinT h = s) -> _) with
                          |Some ((_, p), h') => fun H : (splitMinT h = Some ((_, p), h')) =>
                          match p as p'' return ((p = p'') -> _) with
                            | LP nil => fun H : (p = LP nil) => Err.patternFailure
                            | LP ((v,d) :: t) => fun H : (p = LP ( (v,d) :: t)) =>
                                match (match_ v g) as y return ((match_ v g = y) -> _ ) with
                                | (Some c, g') => fun H : (match_ v g) = (Some c, g') => d_tail (g', mergeAll (h' :: expand d p c), l ++ (p :: nil))
                                | (None, g') => fun H: (match_ v g) = (None, g') => d_tail (g', h', l)
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
rewrite (mergeAll_size l5). simpl. omega.
Defined.


Definition expand_d_tail :=
fun s : gr a b * Heap b (LPath b) * list (LPath b) =>
let (p, l) := s in
(let (g, h) := p in
 fun l0 : list (LPath b) =>
 if bool_dec (Heap.isEmpty h || isEmpty g) true
 then (g, h, l0)
 else
  match splitMinT h as s0 return (splitMinT h = s0 -> gr a b * Heap b (LPath b) * list (LPath b)) with
  | Some p0 =>
      let (p1, h') as p1 return (splitMinT h = Some p1 -> gr a b * Heap b (LPath b) * list (LPath b)) := p0 in
      let (b0, p2) as p2 return (splitMinT h = Some (p2, h') -> gr a b * Heap b (LPath b) * list (LPath b)) :=
        p1 in
      fun _ : splitMinT h = Some (b0, p2, h') =>
      match p2 as p'' return (p2 = p'' -> gr a b * Heap b (LPath b) * list (LPath b)) with
      | LP unLPath =>
          match unLPath as unLPath0 return (p2 = LP unLPath0 -> gr a b * Heap b (LPath b) * list (LPath b)) with
          | nil => fun _ : p2 = LP nil => patternFailure
          | l1 :: t =>
              let (v, d) as l2 return (p2 = LP (l2 :: t) -> gr a b * Heap b (LPath b) * list (LPath b)) := l1 in
              fun _ : p2 = LP ((v, d) :: t) =>
              (let (m, g') as y return (match_ v g = y -> gr a b * Heap b (LPath b) * list (LPath b)) :=
                 match_ v g in
               match m as m0 return (match_ v g = (m0, g') -> gr a b * Heap b (LPath b) * list (LPath b)) with
               | Some c =>
                   fun _ : match_ v g = (Some c, g') =>
                   d_tail (g', mergeAll (h' :: expand d p2 c), l0 ++ p2 :: nil)
               | None => fun _ : match_ v g = (None, g') => d_tail (g', h', l0)
               end) eq_refl
          end
      end eq_refl
  | None => fun _ : splitMinT h = None => patternFailure
  end eq_refl) l.

Lemma unfold_d_tail: forall s,
  d_tail s = expand_d_tail s.
Proof.
  intros. unfold expand_d_tail. apply d_tail_elim; intros; reflexivity.
Qed.

(*Now we again prove equivalence by showing that this tail recursive version is valid and done*)

Lemma d_tail_multi: forall s v g,
  d_valid s v g ->
  multi (d_step) s (d_tail s).
Proof.
  intros. destruct s as[r p].
  remember (snd r, fst r) as r'. generalize dependent r. revert p. 
  induction r' using (well_founded_induction (well_founded_bf_measure_heap _)).
  intros. destruct r' as [q h]. inversion Heqr'; subst. clear Heqr'. destruct r as [g' h].
  rewrite unfold_d_tail. unfold expand_d_tail. destruct (Heap.isEmpty h) eqn : E. apply multi_refl.
  destruct (isEmpty g') eqn : GE. simpl. apply multi_refl. destruct (bool_dec (false || false) true) eqn : U.
  simpl in e. inversion e. destruct (splitMinT h) eqn : S. destruct p0. destruct p0. 
  destruct l. destruct h. inversion S. simpl in S. inversion S. subst. destruct unLPath.
  exfalso. eapply heap_not_none. apply H0. simpl.  left. reflexivity. destruct l. 
  destruct (match_ n0 g') eqn : M. destruct m.
  - eapply multi_step. eapply d_find. assumption. apply M. simpl. reflexivity.
    reflexivity. eapply H. apply lex1. 3 :{ reflexivity. } unfold natNodes_lt. simpl.
    eapply match_decr_size. symmetry. apply M. eapply v_d_step. apply H0. eapply d_find.
    apply GE. apply M. simpl. reflexivity. reflexivity.
  - eapply multi_step. eapply d_skip. apply GE. apply M. simpl. reflexivity.
    eapply H. 3 : { reflexivity. }  apply lex2. simpl. symmetry. eapply match_none_size.
    apply M. simpl. unfold heap_length_lt. rewrite mergeAll_size. simpl.
    omega. eapply v_d_step. apply H0. eapply d_skip. assumption. apply M. simpl. reflexivity.
  - destruct h. simpl in E. inversion E. simpl in S. inversion S.
Qed.

(*Equivalence with tail recursive version*)
Lemma dijkstra_tail_equiv: forall g h l,
  (forall k, ~In_Heap (k, LP nil) h) ->
  d_paths (d_tail (g, h, l)) = l ++ dijkstra' (h, g).
Proof.
  intros. remember (h, g) as x. generalize dependent h. revert g. revert l.
  induction x using (well_founded_induction (well_founded_bf_measure_heap _)).
  intros. destruct x; inversion Heqx; subst; clear Heqx.
  rewrite <- unfold_dijkstra'. rewrite unfold_d_tail. simpl.
  destruct h eqn : H'. 
  - simpl. rewrite app_nil_r. reflexivity.
  - simpl. destruct (isEmpty g) eqn : G. 
    + simpl. rewrite app_nil_r. reflexivity.
    + simpl. destruct l0. destruct unLPath. exfalso. eapply H0. simpl. left. reflexivity.
      destruct l0. destruct (match_ n g) eqn : M. destruct m.
      * erewrite H. rewrite <- app_assoc. reflexivity. apply lex1. unfold natNodes_lt. eapply match_decr_size.
        symmetry. apply M. intros. intro. destruct (expand b1 (LP ((n, b1) :: unLPath)) c) eqn : E; rewrite E in H1.
        -- rewrite in_heap_mergeAll in H1. eapply H0. simpl. right. rewrite <- in_heap_equiv. apply H1.
        -- simpl in E. destruct c. destruct p. destruct p.
           rewrite in_heap_merge in H1. destruct H1.
           ++ rewrite in_heap_merge in H1. destruct H1.
              ** rewrite in_heap_mergeAll in H1. eapply H0. simpl. right. rewrite <- in_heap_equiv. apply H1.
              ** destruct a0. simpl in E. inversion E. simpl in E. inversion E. destruct p. 
                 rewrite <- H3 in H1. simpl in H1. destruct H1. inversion H1. destruct H1.
          ++ destruct a0. simpl in E. inversion E. simpl in E. inversion E. rewrite in_heap_mergeAll in H1.
             rewrite in_heap_exists in H1. destruct H1. rewrite <- H4 in H1. destruct H1. 
             unfold Base.map in H1. rewrite in_map_iff in H1. destruct H1. destruct x0.
             destruct H1. rewrite <- H1 in H2. unfold unit in H2. simpl in H2. destruct H2. inversion H2.
             destruct H2.
        -- reflexivity.
      * erewrite H. reflexivity. apply lex2. unfold natNodes_eq. symmetry. eapply match_none_size. apply M.
        unfold heap_length_lt. rewrite mergeAll_size. simpl. omega. intros. intro.
        apply (H0 k). right. rewrite in_heap_mergeAll in H1. rewrite in_heap_equiv in H1. apply H1. reflexivity.
Qed.

Lemma spTree_tail_equiv: forall v g,
  d_paths (d_tail (d_start g v)) = spTree v g.
Proof.
  intros. pose proof dijkstra_tail_equiv. setoid_rewrite <- dijkstra'_equiv in H.
  rewrite H. unfold spTree. simpl. reflexivity. intros. intro. unfold unit in H0.
  simpl in H0. destruct H0. inversion H0. destruct H0.
Qed.

End ValidPath.

Lemma spTree_notin: forall v (g: gr a b),
  vIn g v = false ->
  spTree v g = nil.
Proof.
  intros. unfold spTree. rewrite dijkstra'_equiv. unfold unit. 
  rewrite <- unfold_dijkstra'. simpl. destruct (isEmpty g); simpl. reflexivity.
  destruct (match_ v g) eqn : M. destruct m.
  assert (vIn g v = true). eapply match_in. exists c. exists g0. assumption.
  rewrite H0 in H. inversion H. rewrite <- unfold_dijkstra'. simpl. reflexivity.
Qed. 

Theorem spTree_validPaths: forall v (g: gr a b) u d t,
  In (LP ((u, d) :: t))  (spTree v g) ->
   Wpath g v u (unlabel_path (LP ((u, d) :: t))) d.
Proof.
  intros. destruct (vIn g v) eqn : V.
  rewrite <- spTree_tail_equiv in H. eapply in_output_wpath. 
  eapply d_multi_valid. apply v_d_start. assumption. eapply d_tail_multi. eapply v_d_start. assumption.
  assumption. apply spTree_notin in V. rewrite V in H. inversion H.
Qed.

(*2. The weight of the path is the corresponding first element in [sp_distance]. We will also prove that the
     first vertex in the path is the corresponding second element in [sp_distance] *)

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
      assert (E : h <> Heap.Empty). intro. subst. inversion H1.
      pose proof @map_splitMinT. 
      assert (splitMinT (map_heap (fun (_ : b) (l : LPath b) => labelHead l) h) = Some (b2, labelHead l2, 
      map_heap (fun (_ : b) (l : LPath b) => labelHead l) h0)). assert (Mi2 := Mi).
      rewrite <- splitMin_equiv in Mi. rewrite <- splitMin_equiv. 
      assert (h <> Heap.Empty). intro. subst. inversion H2. inversion Mi.
      rewrite splitMin_equiv. 
      erewrite H1. reflexivity. assumption. assumption. 
      (intro; destruct h; try(inversion Mi2); try(inversion H3)).
      (intro; destruct h; try(inversion Mi2); try(inversion H3)).
      subst. inversion H2. assumption.
      destruct l2. destruct  unLPath.
      * subst. exfalso. apply (Z b2). rewrite in_heap_splitMin. left. reflexivity. intro. subst. inversion H3.
        rewrite <- splitMin_equiv in Mi. 
        assert ((splitMin (Heap.Node b0 l l0)) = (b2, LP nil, h0)). inversion Mi; subst. simpl. reflexivity. apply H3.
        intro. inversion H3.
      * destruct l2. simpl in H2. destruct (match_ n0 g) eqn : M. destruct m.
        assert (splitMinT h' = Some(b1, n, mergeAll l1)). rewrite Heqh'. simpl. reflexivity.
        rewrite H3. rewrite Heqh in H2. simpl in H2. inversion H2. subst. simpl in H0. inversion H0; subst. destruct l.
        simpl in H8. destruct unLPath0. inversion H8. destruct l. inversion H8; subst.
        simpl in H2. inversion H2; subst. rewrite M.
        -- remember ((mergeAll (h0 :: expand b3 (LP ((n0, b3) :: unLPath)) c), g0)) as P. rewrite <- HeqP.
            remember (mergeAll (mergeAll l1 :: expand_dist b3 n0 c), g0) as P'. simpl.
           rewrite HeqP. rewrite HeqP'. rewrite <- unfold_dijkstra'. erewrite H. rewrite unfold_sp_distance. reflexivity.
          apply lex1. eapply match_decr_size. symmetry. apply M. 3 : { reflexivity. }
          intros. intro. rewrite in_heap_mergeAll in H4. rewrite in_heap_unfold in H4. destruct H4.
          apply (Z x). rewrite in_heap_splitMin. right. apply H4. intro. subst. inversion H5.
          rewrite <- splitMin_equiv in Mi.
          assert ((splitMin (Heap.Node b3 (LP ((n0, b3) :: unLPath0)) l0)) = (b3, LP ((n0, b3) :: unLPath), h0)).
          inversion Mi; subst. simpl. reflexivity. apply H5.
          intro. subst. inversion H5.
          rewrite in_heap_exists in H4. destruct H4 as [h'']. destruct H4. simpl in H4.
          destruct c. destruct p. destruct p. rewrite in_map_iff in H4. destruct H4. destruct x0.
          unfold unit in H4.  simpl in H4. destruct H4; subst. simpl in H5. destruct H5. inversion H4. destruct H4.
          repeat(rewrite map_mergeAll). 
          assert (
           (List.map (map_heap (fun (_ : b) (l : LPath b) => labelHead l))
     (h0 :: expand b3 (LP ((n0, b3) :: unLPath)) c)) =
        (List.map (map_heap (fun (x : b) (y : Node) => (Some x, Some y))) (mergeAll l1 :: expand_dist b3 n0 c))).  simpl. unfold expand_dist.
        destruct c. destruct p. destruct p. rewrite map_mergeAll. rewrite <- H9. rewrite H7. assert (forall l', 
         List.map (map_heap (fun (_ : b) (l2 : LPath b) => labelHead l2))
     (map (fun '(l2, v) => unit (_GHC.Num.+_ l2 b3) (LP ((v, _GHC.Num.+_ l2 b3) :: (n0, b3) :: unLPath))) l') =
      List.map (map_heap (fun (x : b) (y : Node) => (Some x, Some y)))
     (map (fun x : b * Node => let (l2, v') := x in unit (_GHC.Num.+_ l2 b3) v') l')). { intros. induction l'.
      simpl. reflexivity. simpl. rewrite IHl'. simpl. destruct a3. reflexivity. } rewrite H4. reflexivity. unfold map.
      rewrite H4. reflexivity.
        -- rewrite Heqh in H2. simpl in H2. rewrite Heqh'. unfold splitMinT. rewrite Heqh' in H0.
           rewrite Heqh in H0. inversion H0; subst. destruct l; simpl in H5. destruct unLPath0; simpl in H5.
           inversion H5. destruct l. inversion H5; subst. simpl in H2. inversion H2; subst.
           rewrite M. 
           rewrite <- unfold_dijkstra'.  rewrite unfold_sp_distance. erewrite H. reflexivity.
           apply lex2. unfold natNodes_eq. symmetry. eapply match_none_size. apply M.
           unfold heap_length_lt. subst. simpl in Mi. inversion Mi; subst. rewrite (mergeAll_size l0).
           simpl. omega. 3 : { reflexivity. } intros. intro. apply (Z x). rewrite in_heap_splitMin.
            right. apply H3. intro. subst. inversion H4. rewrite <- splitMin_equiv in Mi. inversion Mi. subst. reflexivity.
          intro. subst. inversion H4. rewrite map_mergeAll. rewrite <- H9. rewrite H6. reflexivity.
      * subst. inversion Mi.
Qed.

(*We need to prove equivalence between [sp_distance] and [sp_tail]*)
Lemma sp_distance_sp_tail: forall g h l,
  get_dists (sp_tail (g, h, l)) = l ++ sp_distance (h,g).
Proof.
  intros.
  intros. remember (h, g) as x. generalize dependent h. revert g. revert l.
  induction x using (well_founded_induction (well_founded_bf_measure_heap _)).
  intros. destruct x. inversion Heqx; subst; clear Heqx. rewrite unfold_sp_tail. rewrite unfold_sp_distance.
  unfold expand_sp_tail. unfold expand_sp_distance. destruct ( bool_dec (Heap.isEmpty h || isEmpty g) true).
  simpl. rewrite app_nil_r. reflexivity.
  destruct (splitMinT h) eqn : S. destruct p. destruct p. destruct (match_ n0 g) eqn : M. destruct m.
  remember (h0 :: expand_dist b0 n0 c) as h1. erewrite H. rewrite <- app_assoc. simpl. reflexivity.
  subst. apply lex1. unfold natNodes_lt. eapply match_decr_size. symmetry. apply M.
  reflexivity. erewrite H. reflexivity. apply lex2. unfold natNodes_eq. symmetry. eapply match_none_size.
  apply M. unfold heap_length_lt. destruct h. inversion S. inversion S; subst.
  simpl. rewrite mergeAll_size. omega. reflexivity. destruct h. simpl in n. contradiction. inversion S.
Qed. 

(*The analogue of [spTree]*)
Definition spDistTree (v: Node) (g: gr a b) := sp_distance ((unit #0 v), g).

Lemma spDistTree_tail: forall v g,
  spDistTree v g = get_dists (sp_tail (start g v)).
Proof.
  intros. unfold spDistTree. unfold start. rewrite sp_distance_sp_tail. simpl. reflexivity.
Qed.

Theorem vertex_and_weight_same: forall v g,
  map labelHead (spTree v g) = map (fun x => (Some (fst x), Some (snd x))) (spDistTree v g).
Proof.
  intros. unfold spTree. unfold spDistTree. rewrite dijkstra'_equiv. eapply distance_sp.
  intros. intro. simpl in H. destruct H. inversion H. destruct H.
  simpl. reflexivity.
Qed.

(*Need a more careful specification of List.zip*)
Lemma zip_spec: forall {A B} (l: list A) (l': list B) x y,
  length l = length l' ->
  In (x,y) (List.zip l l') ->
  exists l1 l2 l3 l4, l = l1 ++ x :: l2 /\ l' = l3 ++ y :: l4 /\
  length l1 = length l3 /\ length l2 = length l4.
Proof.
  intros. generalize dependent l'. induction l; intros.
  - simpl in H0. destruct H0.
  - destruct l'. simpl in H. omega. simpl in H. inversion H.
    simpl in H0. destruct H0. inversion H0; subst.
    exists nil. exists l. exists nil. exists l'. split. reflexivity.
    split. reflexivity. split. reflexivity. assumption.
    specialize (IHl _ H2 H0). destruct_all. exists (a0 :: x0).
    rewrite H1. exists x1. exists (b0 :: x2). rewrite H3. exists x3. split. reflexivity.
    split. reflexivity. split. simpl. rewrite H4. reflexivity. assumption.
Qed.

Lemma in_zip_map_weak: forall {A B C} (l: list A) (l': list B) x y (f: A -> C) f',
  length l = length l' ->
  In (x,y) (List.zip l l') ->
  map f l = map f' l' ->
  f x = f' y.
Proof.
  intros. generalize dependent l'. induction l; intros.
  - simpl in H0. inversion H0.
  - destruct l'. simpl in H. omega.
    simpl in H. inversion H. simpl in H1. simpl in H0. inversion H1.
    destruct H0. inversion H0; subst. assumption.
    eapply IHl. apply H3. assumption. assumption.
Qed.



Lemma map_length: forall {A B C} (l: list A) (l' : list B) (f: A -> C) f',
  map f l = map f' l' ->
  length l = length l'.
Proof.
  intros. generalize dependent l'. induction l; intros.
  - simpl in H. destruct l'. reflexivity. inversion H.
  - destruct l'. inversion H. simpl in H. simpl. inversion H; subst.
    erewrite IHl. reflexivity. assumption.
Qed.

Lemma in_zip_map: forall {A B C} (l: list A) (l': list B) x y (f: A -> C) f',
  In (x,y) (List.zip l l') ->
  map f l = map f' l' ->
  f x = f' y.
Proof.
  intros. eapply in_zip_map_weak. eapply map_length. apply H0. assumption. assumption.
Qed.

Lemma in_zip_reverse: forall {A} {B} (l: list A) (l' : list B) x,
  length l = length l' ->
  In x l ->
  exists y, In (x,y) (List.zip l l').
Proof.
  intros. generalize dependent l'. induction l; intros.
  - inversion H0.
  - simpl in H. destruct l'. simpl in H. omega.
    simpl in H. inversion H. simpl in H0. destruct H0. subst. exists b0. simpl.
    left. reflexivity. specialize (IHl H0 _ H2). destruct_all. exists x0. simpl. right. assumption.
Qed.

Lemma in_zip_reverse_snd: forall {A} {B} (l: list A) (l' : list B) x,
  length l = length l' ->
  In x l' ->
  exists y, In (y, x) (List.zip l l').
Proof.
  intros. generalize dependent l. induction l'; intros.
  - inversion H0.
  - simpl in H. destruct l. simpl in H. omega.
    simpl in H. inversion H. simpl in H0. destruct H0. subst. exists a1. simpl.
    left. reflexivity. specialize (IHl' H0 _ H2). destruct_all. exists x0. simpl. right. assumption.
Qed.

(*Copied from BFS: TODO move to helper*)
Lemma zip_in: forall {a} {b} (l1 : list a) (l2: list b),
  (forall x y, In (x,y) (List.zip l1 l2) -> In x l1 /\ In y l2).
Proof.
  intros. generalize dependent l2. induction l1; intros.
  - simpl in H. destruct H.
  - simpl in H. destruct l2. destruct H.
    simpl in H.  destruct H. inversion H; subst.
    split; simpl; left; reflexivity. simpl. apply IHl1 in H. destruct H.
    split; right; assumption. 
Qed. 

(*For the final proof of correctness, we need the same assumptions as before*)
Section SpTreeCorrect.
Variable g : gr a b.
Variable Hsimple: forall u v w w', WeIn g u v w -> WeIn g u v w' -> w = w'.
Variable HNonneg: forall u v w, WeIn g u v w -> #0 <= w = true.

(*Finally, each path is actually a shortest path. It's a bit annoying to state this in terms of mapping since we need
  access to both, so we use List.zip*)
Theorem spTree_finds_shortest_paths: forall (v: Node) p d u,
  In (p, (d, u)) (List.zip (spTree v g) (spDistTree v g)) ->
  shortest_wpath g v u (unlabel_path p) /\ path_cost g (unlabel_path p) = Some d.
Proof.
  intros. assert (Z:= H). pose proof (vertex_and_weight_same v g).
  pose proof (in_zip_map _ _ _ _ _ _ H H0).
  assert (labelHead p = (Some d, Some u)). rewrite H1. simpl. reflexivity. clear H1.
  unfold labelHead in H2. destruct p. destruct unLPath. inversion H2. destruct l.
  simpl in H2; inversion H2; subst. clear H2.
  apply zip_in in H. destruct H.
  assert (Wpath g v u (unlabel_path (LP ((u, d) :: unLPath))) d). {
  pose proof  spTree_validPaths. apply H2 in H. clear H2.  assumption. }
  assert (path_cost g (unlabel_path (LP ((u, d) :: unLPath))) = Some d). {
  rewrite path_cost_sum. exists v. exists u. assumption. assumption. assumption. }
   split. 2 : { assumption. }
  rewrite spDistTree_tail in H1. remember (sp_tail (start g v)) as s.
  assert (path' g v u  (unlabel_path (LP ((u, d) :: unLPath)))). apply path'_WPath. assumption.
  assumption. exists d. assumption.
  assert (vIn g v = true). apply in_path' in H4. apply H4. assumption. assumption.
  assert (valid s g v). subst. eapply multi_valid. apply v_start. assumption.
  eapply sp_tail_multi. 
  assert (done s = true). subst. eapply sp_tail_done.
  pose proof (sp_correct_all _ Hsimple HNonneg _ _ u H6 H7).
  assert ((find_dist s u) = Some d). rewrite find_dist_in. assumption. apply H6.
  rewrite H9 in H8. destruct (find_shortest_wpath g v u) eqn : P. simpl in H8.
  eapply shortest_wpath_same_weight.
  apply find_shortest_wpath_correct. assumption. assumption. apply P. 
  assumption. unfold eq_weight. unfold eq_weight_b. destruct (path_cost g l) eqn : P'.
  rewrite H3. rewrite Base.simpl_option_some_eq in H8.
  destruct HEqLaw; rewrite Eq_sym. apply H8. 
  destruct (Base.EqLaws_option); rewrite Eq_sym in H8. rewrite some_none_eq in H8. inversion H8.
  simpl in H8. 
   destruct (Base.EqLaws_option); rewrite Eq_sym in H8. rewrite some_none_eq in H8. inversion H8.
Qed.

(*The following two theorems provide an overall specification of the [spTree] function. We prove that:
1. If there is a path beginning with (u,d) in (spTree v g), then this is in fact a shortest
   path from v to u with cost d
2. There is a (shortest) path from v to u that appears in the output of [spTree] iff u is reachable from v.
Together, this shows that [spTree] correctly returns a list of shortest paths
to every reachable vertex. *)

(*A version that makes no reference to [spTreeDists]*)
Theorem spTree_shortest_paths: forall v u d t,
  In (LP ((u,d) :: t)) (spTree v g) ->
  shortest_wpath g v u (unlabel_path (LP ((u,d) :: t))) /\ path_cost g (unlabel_path (LP ((u,d) :: t))) = Some d.
Proof.
  intros. pose proof spTree_finds_shortest_paths.
  assert (length (spTree v g) = length (spDistTree v g)). eapply map_length. apply vertex_and_weight_same.
  epose proof (in_zip_reverse _ _ _ H1 H). destruct H2. destruct x.
  apply spTree_finds_shortest_paths in H2. destruct_all. simpl in H2.
  assert (n = u). unfold shortest_wpath in H2. destruct H2.
  apply path'_WPath in H2. destruct_all. eapply hd_path. apply H2. assumption. assumption. split.
  subst. apply H2. subst. apply path_cost_sum. assumption. assumption.
  exists v. exists u. eapply spTree_validPaths. assumption.
Qed. 

(*Finally, the result that shows that this function computes shortest paths for all reachable vertices*)
Theorem spTree_reachable: forall v u,
  (exists l, path' g v u l ) <-> (exists p, In p (spTree v g) /\ shortest_wpath g v u (unlabel_path p)).
Proof.
  intros. remember (sp_tail (start g v)) as s. destruct (vIn g v) eqn : V. 2 : {
  split; intros. destruct H. apply in_path' in H. destruct_all. rewrite H in V. inversion V.
  assumption. assumption. destruct_all. unfold shortest_wpath in H0. destruct_all.
  apply in_path' in H0. destruct_all. rewrite H0 in V. inversion V. assumption. assumption. }
  assert (valid s g v). subst. eapply multi_valid. apply v_start. assumption. apply sp_tail_multi.
  assert (done s = true). subst. apply sp_tail_done.
  assert (length (spTree v g) = length (spDistTree v g)). eapply map_length. apply vertex_and_weight_same.
 split; intros.
  - pose proof output_iff_reachable s g v u H H0. rewrite <- H3 in H2.
    clear H3. subst. rewrite <- spDistTree_tail in H2.
    rewrite in_map_iff in H2. destruct H2. destruct x; destruct_all; simpl in *; subst.
    epose proof (in_zip_reverse_snd _ _ _ H1 H3). destruct H2. exists x.
    assert (W:=H2). apply  zip_in in H2. destruct H2. split. assumption.
    apply spTree_finds_shortest_paths in W. destruct_all. assumption.
  - destruct_all. unfold shortest_wpath in H3. destruct_all. exists (unlabel_path x). assumption.
Qed.

(** Verification of [spLength] **)

Definition lhead (l: list (Node * b)) : option Node:=
  match l with
  |  nil => None
  | ((x, y) :: t) => Some x
  end. 

Lemma node_eq: forall (u v : Node),
  u == v = true <-> u = v.
Proof.
  intros; split; intros.
  - unfold "==" in H. unfold op_zeze____ in H. unfold Eq_Char___ in H.
    apply Neqb_ok  in H. assumption.
  - subst. unfold "==". unfold Eq_Char___. unfold op_zeze____.
    apply N.eqb_refl.
Qed.

(*First, need a result about [findP]*)
Lemma findP_In: forall n t p,
  p <> nil ->
  RootPath.findP n t =  p -> (In (LP p) t /\ lhead p = Some n).
Proof.
  intros. induction t; simpl.
  - simpl in H0. subst. contradiction.
  - simpl in H0. destruct a0. destruct unLPath. apply IHt in H0. destruct_all. split. right. assumption.
    assumption.
    destruct l. destruct (n == n0) eqn : E. rewrite H0.
    split. left. reflexivity. subst. simpl.
    rewrite node_eq in E. subst. reflexivity.
    apply IHt in H0. destruct_all. split. right. assumption. assumption.
Qed.


Lemma findP_nil: forall n t,
  RootPath.findP n t = nil <-> (forall p, In (LP p) t -> lhead p <> Some n).
Proof.
  intros. induction t; simpl; split; intros.
  - destruct H0.
  - reflexivity.
  - destruct H0. subst. intro. destruct p. simpl in H0. inversion H0.
    simpl in H0. destruct l. inversion H0; subst.
    assert (n == n = true). rewrite node_eq. reflexivity. rewrite H1 in H.
    inversion H. destruct a0. destruct unLPath. apply IHt. assumption. assumption.
    destruct l. destruct (n == n0) eqn : E. inversion H.
    apply IHt. assumption. assumption.
  - destruct a0. destruct unLPath. apply IHt. intros. apply H. right. assumption.
   destruct l. destruct (n == n0) eqn : N. assert (lhead ((n0, b0) :: unLPath) <> Some n).
   apply H. left. reflexivity. rewrite node_eq in N. subst. simpl in H0. contradiction.
   apply IHt. intros. apply H. right. assumption.
Qed.

(*[spLength] actually returns the shortest distance between two vertices*)
Theorem spLength_dist: forall (v u : Node) n,
  spLength v u g == Some n = true <-> exists p, shortest_wpath g v u p /\ path_cost g p == Some n = true.
Proof.
  intros. split; intros.
  - unfold spLength in H. unfold "∘" in H. unfold RootPath.getDistance in H.
    destruct (RootPath.findP u (spTree v g)) eqn : R.
    rewrite some_none_eq in H.
    inversion H. destruct l. apply findP_In in R.
    destruct_all. simpl in H1. inversion H1; subst.
    apply spTree_shortest_paths in H0.
    exists (unlabel_path (LP ((u, n) :: l0))). destruct_all. split. assumption.
    rewrite H2. assumption.  intro. inversion H0.
  - destruct (spLength v u g) eqn : V.
    unfold spLength in V. unfold "∘" in V. unfold RootPath.getDistance in V.
    destruct (RootPath.findP u (spTree v g)) eqn : R. inversion V.
    destruct l. inversion V; subst. apply findP_In in R.
    destruct_all. simpl in H1. inversion H1; subst.
    apply spTree_shortest_paths in H0. destruct_all.
    pose proof sp_distance_unique. simpl in H4.
    destruct (Base.EqLaws_option). eapply Eq_trans. rewrite <- H3. apply Eq_refl.
    eapply Eq_trans. eapply H4. assumption. assumption. apply H0. apply H.
    assumption. intro. inversion H0. 
    unfold spLength in V. unfold "∘" in V. unfold RootPath.getDistance in V. 
    destruct (RootPath.findP u (spTree v g)) eqn : R.
    rewrite findP_nil in R. 
    pose proof spTree_reachable v u.
    assert ((exists p : LPath b, In p (spTree v g) /\ shortest_wpath g v u (unlabel_path p))). apply H0.
    destruct_all. exists x. unfold shortest_wpath in H. apply H.
    clear H0. destruct H1. destruct_all. destruct x.
    apply R in H0. destruct unLPath. simpl in H1. unfold shortest_wpath in H1.
    destruct_all. inversion H1. simpl in H1.
    destruct l. simpl in H0. simpl in H1. unfold shortest_wpath in H1. destruct_all.
    rewrite path'_WPath in H1. destruct_all.
    apply hd_path in H1. subst. contradiction. assumption. assumption.
    destruct l. inversion V.
Qed.

(** Verification of [sp] **)

Lemma getLPathNodes_unlabel: forall l v,
  RootPath.getLPathNodes v l = unlabel_path (RootPath.getLPath v l).
Proof.
  intros. unfold RootPath.getLPathNodes. unfold Tuple.fst. unfold unlabel_path.
  reflexivity.
Qed.

Theorem sp_finds_shortest_path: forall v u p,
  sp v u g = Some p -> shortest_wpath g v u (rev p).
Proof.
  intros.  
  - unfold sp in H. rewrite getLPathNodes_unlabel in H.
    destruct (unlabel_path (RootPath.getLPath u (spTree v g))) eqn : U.
    inversion H. inversion H; subst.
    unfold RootPath.getLPath in U. unfold "∘" in U. rewrite <- U.
    simpl. rewrite <- map_rev. rewrite hs_coq_reverse. rewrite rev_involutive.
    destruct (RootPath.findP u (spTree v g)) eqn : R. simpl in U. inversion U.
    apply findP_In in R. destruct_all.  destruct l.
    apply spTree_shortest_paths in H0.
    destruct_all. simpl in H0. simpl. simpl in H1. inversion H1; subst. assumption.
    intro. inversion H0.
Qed.

(*Since shortest paths are not unique, we cannot say that sp gives Some p iff p is a shortest path,
  but we do know that sp return p iff there is some shortest path*)
Theorem sp_iff_shortest_path: forall v u,
  (exists p, sp v u g = Some p) <-> (exists p', shortest_wpath g v u p').
Proof.
  intros. split; intros. destruct H as [p]. exists (rev p). apply sp_finds_shortest_path. assumption.
  destruct H. unfold sp. destruct (RootPath.getLPathNodes u (spTree v g)) eqn : R.
  - rewrite getLPathNodes_unlabel in R. simpl in R.
    pose proof spTree_reachable v u. 
     assert (exists p : LPath b, In p (spTree v g) /\ shortest_wpath g v u (unlabel_path p)).
    apply H0. exists x. unfold shortest_wpath in H. apply H. clear H0.
    destruct_all.
    destruct (spTree v g) eqn : S.  inversion H0.
    rewrite <- S in H0.  unfold "∘" in R.
    rewrite hs_coq_reverse in R.
    destruct ((RootPath.findP u (l :: l0))) eqn : R'. rewrite findP_nil in R'.
    destruct x0. rewrite <- S in R'. apply R' in H0. destruct unLPath. 
    simpl in H1. unfold shortest_wpath in H1. destruct_all. inversion H1.
    simpl in H0. destruct l1.
    unfold shortest_wpath in H1. destruct_all. rewrite path'_WPath in H1. destruct_all. apply hd_path in H1.
    simpl in H1. subst. contradiction. assumption. assumption.
    simpl in R. destruct (rev l2); inversion R.
  - exists (n :: p). reflexivity.
Qed.

End SpTreeCorrect.


End Ind.
