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

Definition state : Type := (gr a b) * (Heap b (LPath b)) * (list (LPath b)).

Definition get_graph (s: state) :=
  match s with
  | (g, _, _) => g
  end.

Definition get_heap (s: state) :=
  match s with
  | (_, h, _) => h
end.

Definition get_paths (s: state) :=
  match s with
  | (_, _, p) => p
  end.


(*How to step from 1 state to another. The inductive definiction makes it easier to use as
  an assumption in proofs*)
Inductive sp_step : state -> state -> Prop :=
  | sp_find: forall (g: gr a b) (v : Node) (c: Context a b) (g': gr a b) (a' : b) 
      (d: b) (t: list (Node * b)) (h' h : Heap b (LPath b)) (p : list (LPath b)) (p' : (LPath b)),
      isEmpty g = false ->
      match_ v g = (Some c, g') ->
      splitMinT h = Some ((a', p'), h') ->
      p' = LP ((v,d) :: t) ->
      sp_step (g, h, p) (g', mergeAll (h' :: expand d p' c), p ++ p' :: nil)
  | sp_skip : forall (g: gr a b) (v: Node) (g': gr a b) (h h' : Heap b (LPath b))
     (p: list (LPath b)) (p': (LPath b)) (a' : b),
      isEmpty g = false ->
      match_ v g = (None, g') ->
      splitMinT h = Some ((a', p'), h') ->
      sp_step (g, h, p) (g', h', p).

Definition start (g : gr a b) (v: Graph.Node) : state := (g, Heap.unit #0 (LP ((v, #0) :: nil)), nil).

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

(*The executable, tail recursive version of this, which we will prove equivalent to the hs-to-coq version*)
Section Exec.

Program Instance default_state : Default state.
Next Obligation.
unfold state. apply ((empty, Heap.Empty, nil)).
Defined.


Equations sp_tail (s: state) : state by wf (get_heap s, get_graph s) (bf_measure_heap) :=
  sp_tail (g, h, l) =>  if bool_dec ((Heap.isEmpty h) || (@Graph.isEmpty gr Hgraph a b g)) true then (g, h, l) else
                        match (splitMinT h) as s return ((splitMinT h = s) -> _) with
                          |Some ((_, p), h') => fun H : (splitMinT h = Some ((_, p), h')) =>
                          match p as p'' return ((p = p'') -> _) with
                            | LP nil => fun H : (p = LP nil) => Err.patternFailure
                            | LP ((v,d) :: t) => fun H : (p = LP ( (v,d) :: t)) =>
                                match (match_ v g) as y return ((match_ v g = y) -> _ ) with
                                | (Some c, g') => fun H : (match_ v g) = (Some c, g') => sp_tail (g', mergeAll (h' :: expand d p c), l ++ (p :: nil))
                                | (None, g') => fun H: (match_ v g) = (None, g') => sp_tail (g', h', l)
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

Definition expand_sp_tail :=
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
                   sp_tail (g', mergeAll (h' :: expand d p2 c), l0 ++ p2 :: nil)
               | None => fun _ : match_ v g = (None, g') => sp_tail (g', h', l0)
               end) eq_refl
          end
      end eq_refl
  | None => fun _ : splitMinT h = None => patternFailure
  end eq_refl) l.

Lemma unfold_sp_tail: forall s,
  sp_tail s = expand_sp_tail s.
Proof.
  intros. unfold expand_sp_tail. apply sp_tail_elim; intros; reflexivity.
Qed.

(*This is equivalent to repeatedly stepping with the sp_step inductive relation. We prove this by proving that
  bfs_tail represents a multistep to a done state. So when we start with the start state, we get a valid
  done state. We will later prove that all valid done states are equivalent, so we can prove claims about bfs_tail
  by considering valid done states in general*)

Lemma heap_not_none: forall s v g k,
  valid s v g ->
  ~ In_Heap (k, (LP nil)) (get_heap s).
Proof.
  intros. induction H; intro.
  - simpl in H0. destruct H0. inversion H0. destruct H0.
  - inversion H0; subst.
    + unfold get_heap in H1. rewrite in_heap_mergeAll in H1. unfold fold_right in H1.
      destruct H1. simpl in IHvalid. apply IHvalid. pose proof (in_heap_splitMin (k, (LP nil)) h h' a' (LP ((v0, d) :: t))).
      rewrite H5. right. assumption. intro. subst. simpl in H4. inversion H4. 
      rewrite <- splitMin_equiv in H4. inversion H4. reflexivity. intro. subst. simpl in H4. inversion H4.
      assert (fold_right (fun x acc => In_Heap (k, LP nil) x \/ acc) False (expand d (LP ((v0, d) :: t)) c)).
      unfold fold_right. apply H1. clear H1. rewrite in_heap_exists in H5.
      destruct H5. destruct H1. simpl in IHvalid.
      simpl in H1. destruct c. destruct p0. destruct p0. unfold Base.map in H1.
      rewrite in_map_iff in H1. destruct H1. destruct x0. destruct H1.
      rewrite <- H1 in H5. unfold unit in H5. simpl in H5. destruct H5. inversion H5. destruct H5.
    + simpl in IHvalid. simpl in H1. destruct h. simpl in H4. inversion H4. simpl in H4. 
      inversion H4. subst. simpl in IHvalid. rewrite in_heap_mergeAll in H1. apply IHvalid.
      right. rewrite <- in_heap_equiv. apply H1. 
Qed.

Lemma sp_tail_multi: forall s v g,
  valid s v g ->
  sp_multi s (sp_tail s).
Proof.
  intros. destruct s as[r p].
  remember (snd r, fst r) as r'. generalize dependent r. revert p. 
  induction r' using (well_founded_induction (@well_founded_bf_measure_heap _)).
  intros. destruct r' as [q h]. inversion Heqr'; subst. clear Heqr'. destruct r as [g' h].
  rewrite unfold_sp_tail. unfold expand_sp_tail. destruct (Heap.isEmpty h) eqn : E. apply multi_refl.
  destruct (isEmpty g') eqn : GE. simpl. apply multi_refl. destruct (bool_dec (false || false) true) eqn : U.
  simpl in e. inversion e. destruct (splitMinT h) eqn : S. destruct p0. destruct p0. 
  destruct l. destruct h. inversion S. simpl in S. inversion S. subst. destruct unLPath.
  exfalso. eapply heap_not_none. apply H0. simpl.  left. reflexivity. destruct l. 
  destruct (match_ n0 g') eqn : M. destruct m.
  - eapply multi_step. eapply sp_find. assumption. apply M. simpl. reflexivity.
    reflexivity. eapply H. apply lex1. 3 :{ reflexivity. } unfold natNodes_lt. simpl.
    eapply match_decr_size. symmetry. apply M. eapply v_step. apply H0. eapply sp_find.
    apply GE. apply M. simpl. reflexivity. reflexivity.
  - eapply multi_step. eapply sp_skip. apply GE. apply M. simpl. reflexivity.
    eapply H. 3 : { reflexivity. }  apply lex2. simpl. symmetry. eapply match_none_size.
    apply M. simpl. unfold heap_length_lt. rewrite mergeAll_size. simpl.
    omega. eapply v_step. apply H0. eapply sp_skip. assumption. apply M. simpl. reflexivity.
  - destruct h. simpl in E. inversion E. simpl in S. inversion S.
Qed.

Lemma sp_tail_done: forall s v g,
  valid s v g ->
  done (sp_tail s) = true.
Proof.
  intros. unfold done. destruct s as[r p].
  remember (snd r, fst r) as r'. generalize dependent r. revert p. 
  induction r' using (well_founded_induction (@well_founded_bf_measure_heap _)).
  intros. destruct r. simpl in Heqr'. destruct r'. inversion Heqr'. subst. clear Heqr'.
  rewrite unfold_sp_tail. unfold expand_sp_tail. destruct h. simpl. reflexivity.
  destruct (isEmpty g0) eqn : E. simpl. assumption.
  destruct (bool_dec (Heap.isEmpty (Heap.Node b0 l l0) || false) true) eqn : ?. simpl in Heqs. inversion Heqs.
  clear Heqs. destruct (splitMinT (Heap.Node b0 l l0)) eqn : Min. simpl in Min. destruct p0. destruct p0.
  inversion Min; subst. clear Min. destruct l1. destruct unLPath.
  exfalso. eapply heap_not_none. apply H0. simpl. left. reflexivity. destruct l. 
  destruct (match_ n0 g0) eqn : M. destruct m.
  -  remember (sp_tail (g1, mergeAll (mergeAll l0 :: expand b0 (LP ((n0, b0) :: unLPath)) c),
        p ++ LP ((n0, b0) :: unLPath) :: nil)) as s'. eapply H.  3 : { reflexivity. } apply lex1.
    simpl. eapply match_decr_size. symmetry. apply M. eapply v_step. apply H0. eapply sp_find.
    symmetry. symmetry; assumption. apply M. simpl. reflexivity. reflexivity.
  - eapply H. 3 : { reflexivity. } apply lex2. simpl. symmetry. eapply match_none_size. apply M.
    simpl. unfold heap_length_lt. rewrite mergeAll_size.  simpl. omega. eapply v_step. apply H0.
    eapply sp_skip. assumption. apply M. simpl. reflexivity.
  - simpl in Min. inversion Min.
Qed.

End Exec.

Require Import GHC.Base.

Section Correct.
Require Import Data.Graph.Inductive.Internal.RootPath.
Require Import Helper.

Definition orl {A} (l l': list A) :=
  match l with
  | nil => l'
  | _ => l
  end.

Lemma findP_app: forall {A} v (l l' : LRTree A),
  findP v (l ++ l') = orl (findP v l) (findP v l').
Proof.
  intros. generalize dependent l'. induction l; intros.
  - simpl. reflexivity.
  - simpl. destruct a0. destruct unLPath. apply IHl. destruct l0.
    destruct (Base.op_zeze__ v n) eqn : E. simpl. reflexivity.
    apply IHl.
Qed.

Lemma node_eq: forall (v v' : Node),
  v == v' = true <-> v = v'.
Proof.
  intros. unfold "==". unfold Eq_Char___. unfold op_zeze____. apply N.eqb_eq.
Qed. 

Ltac unfold_eq H :=
  unfold "==" in H; unfold Eq_Char___ in H; unfold op_zeze____ in H;
  try (apply N.eqb_eq in H); try (apply N.eqb_neq in H).

Lemma graph_iff_not_output: forall s g v v',
  valid s g v ->
  vIn g v' = true ->
  findP v' (get_paths s) <> nil <->  (vIn (get_graph s) v' = false).
Proof.
  intros. induction H; split; intros; simpl in *.
  - contradiction. 
  - rewrite H0 in H1. inversion H1.
  - inversion H1; subst.
    + simpl. unfold get_paths in H2. rewrite findP_app in H2. 
      destruct (findP v' p) eqn : F. simpl in H2. destruct (Base.op_zeze__ v' v0) eqn : E.
      apply node_eq in E. subst. epose proof (match_remain_some g0 v0 c g' H4). destruct_all.
      destruct (vIn g' v0) eqn : V. apply H6 in V. destruct_all; contradiction. reflexivity.
      contradiction. simpl in IHvalid. 
      rewrite F in IHvalid. pose proof (match_remain_some g0 v0 c g' H4). destruct_all.
      destruct (vIn g' v') eqn : V. apply H6 in V. destruct_all. 
      assert (vIn g0 v' = false). apply IHvalid. assumption. auto. rewrite H10 in H8. inversion H8.
      reflexivity.
    + simpl. simpl in IHvalid. simpl in H2. assert (g' = g0). erewrite match_remain_none. reflexivity. apply H4.
      subst. apply IHvalid. assumption. assumption.
  - inversion H1; subst. simpl in IHvalid. simpl in H2. simpl. rewrite findP_app. destruct (findP v' p) eqn : F.
    simpl. destruct (v' == v0) eqn : E. intro. inversion H6. apply IHvalid. assumption.
    pose proof (match_remain_some g0 v0 c g' H4). destruct_all. destruct (vIn g0 v') eqn : V.
    assert (vIn g' v' = true). apply H6. split. assumption. intro. subst. unfold_eq E. contradiction.
    rewrite H8 in H2. inversion H2. reflexivity. simpl. intro. inversion H6.
    simpl in *. apply IHvalid. assumption. assert (g0 = g'). eapply match_remain_none. apply H4. subst.
    assumption.
Qed.

Require Import WeightedGraphs.

Lemma graph_subset: forall s s' v g,
  valid s v g ->
  valid s' v g ->
  sp_multi s s' ->
  (forall u v w, WeIn (get_graph s') u v w -> WeIn (get_graph s) u v w).
Proof.
  intros. induction H1. assumption. inversion H1; subst.
  - remember ((g', mergeAll (h' :: expand d (LP ((v1, d) :: t)) c), p ++ LP ((v1, d) :: t) :: nil)) as s''.
    rewrite Heqs'' in IHmulti at 2. simpl in IHmulti. simpl. eapply Wmatch_remain_some in H5.
    destruct_all. apply IHmulti in H2. apply H7 in H2. destruct_all; assumption. eapply v_step. apply H.
    assumption. eapply multi_valid. eapply v_step. apply H. apply H1. assumption.
  - eapply match_remain_none in H5. subst. simpl in *. apply IHmulti. eapply v_step. apply H. assumption.
    eapply multi_valid. eapply v_step. apply H. apply H1. assumption. assumption.
Qed.

Lemma valid_begins_with_start: forall s g v,
  valid s g v ->
  sp_multi (start g v) s.
Proof.
  intros. induction H.
  - constructor.
  - eapply multi_trans. apply IHvalid.  eapply multi_step. apply H0. apply multi_refl.
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
  (forall u v w, WeIn (get_graph s) u v w -> WeIn g u v w).
Proof.
  intros. remember (start g v) as s'.
  assert (g = get_graph s'). subst; simpl. reflexivity. rewrite H1. eapply graph_subset.
  subst. apply v_start. eapply start_in. apply H. apply H. subst. apply valid_begins_with_start. apply H.
  assumption.
Qed. 

Definition unlabel_path (l : LPath b) : Path := 
  match l with
  | LP l' => map fst l'
  end.
(*All paths in the heap are valid Wpaths. Then, we can use the equivalent definitions of Wpaths (in terms of 
  paths anf path_cost, to reason about the paths*)

(*Require Import GHC.Base.
Import GHC.Num.Notations.
*)

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
  valid s g v ->
  In_Heap (x, (LP ((u, d) :: t))) (get_heap s) ->
  x = d.
Proof.
  intros. induction H.
  - simpl in H0. destruct H0. inversion H0. subst. reflexivity. destruct H0.
  - inversion H1; subst.
    + unfold get_heap in H0. rewrite in_heap_mergeAll in H0. rewrite in_heap_unfold in H0.
      destruct H0.
      * simpl in IHvalid. apply IHvalid. rewrite in_heap_splitMin. right. apply H0.
        intro. subst. inversion H4. rewrite <- splitMin_equiv in H4. inversion H4. apply H6. intro.
        subst. inversion H4.
      * rewrite in_heap_exists in H0. destruct H0 as [h'']. destruct H0. simpl in H0.
        destruct c. destruct p0. destruct p0. rewrite in_map_iff in H0. destruct_all. destruct x0.
        unfold unit in H0. subst. simpl in H5. destruct H5. inversion H0; subst. reflexivity.
        destruct H0.
    + simpl in *. apply IHvalid. rewrite in_heap_splitMin. right.
      apply H0. intro. subst. inversion H4. rewrite <- splitMin_equiv in H4. inversion H4. apply H6.
      intro. subst. inversion H4.
Qed. 

Lemma in_heap_wpath: forall s g v x l,
  valid s g v ->
  In_Heap (x, l) (get_heap s) ->
  exists u, Wpath g v u (unlabel_path l) x.
Proof.
  intros. generalize dependent l. revert x. induction H; intros.
  - simpl in H0. destruct H0. inversion H0; subst. simpl. exists v. constructor. assumption.
    destruct H0.
  - inversion H0; subst.
    + unfold get_heap in H1. rewrite in_heap_mergeAll in H1.
      rewrite in_heap_unfold in H1. destruct H1.
    * simpl in IHvalid. apply IHvalid. rewrite in_heap_splitMin. right. apply H1. intro. subst.
      inversion H4. rewrite <- splitMin_equiv in H4.
    inversion H4; subst. apply H6. intro. subst. simpl in H4. inversion H4.
    * rewrite in_heap_exists in H1. destruct H1 as [h'']. destruct H1.
      pose proof (expand_preserves_valid v0 (LP ((v0, d) :: t)) (map fst t) c v0 v d g g' g0 eq_refl). 
      assert (a' = d). eapply heap_path_value. apply H. simpl.
      rewrite in_heap_splitMin. left. reflexivity. intro. subst. inversion H4.
      rewrite <- splitMin_equiv in H4. inversion H4. apply H8. intro. subst. inversion H4.
      subst.
      assert (Wpath g v v0 (unlabel_path (LP ((v0, d) :: t))) d). simpl. simpl in IHvalid.
      specialize (IHvalid d (LP ((v0, d) :: t))). simpl in IHvalid. destruct IHvalid. 
      rewrite in_heap_splitMin. left. reflexivity. intro. subst. inversion H4.
      rewrite <- splitMin_equiv in H4. inversion H4; subst. apply H8.
      intro. subst. inversion H4. assert (A:=H7). apply hd_path in H7. subst. apply A.
      specialize (H6 H7 H3).
      assert ((forall (u v : Node) (w : b), WeIn g0 u v w -> WeIn g u v w)). intros.
      eapply graph_subset_start. apply H. simpl. assumption. specialize (H6 H8 h'' H1 x l H5).
      destruct H6 as [b']. destruct H6 as [u']. destruct_all.
      exists u'. assumption.
    + simpl in *. apply IHvalid. rewrite in_heap_splitMin. right. apply H1. intro. subst. inversion H4.
      rewrite <- splitMin_equiv in H4. inversion H4. apply H6. intro. subst. inversion H4.
Qed.

Lemma in_output_wpath: forall s v g l,
  valid s g v ->
  In l (get_paths s) ->
  exists x u, Wpath g v u (unlabel_path l) x.
Proof.
  intros.
  induction H; subst.
  - simpl in H0. destruct H0.
  - inversion H1; subst.
    + unfold get_paths in H0. apply in_app_or in H0. destruct H0. apply IHvalid. apply H0.
      simpl in H0. destruct H0. subst. exists a'.   eapply in_heap_wpath. apply H. simpl. rewrite in_heap_splitMin.
      left. reflexivity. intro. subst. inversion H4. rewrite <- splitMin_equiv in H4. inversion H4. apply H5.
      intro. subst. inversion H4. destruct H0.
    + apply IHvalid. simpl in *. assumption.
Qed.

(*

(*Everything on the heap is in the graph*)


(*A safe head function that uses a default value so that we don't have to wrap and unwarp options. We know
  by above that each list in the output is a valid path, so it is not nil*)
Definition hdDefault {A} (x : A) (l : list A) : A :=
  match l with
  | nil => x
  | h :: t => h
  end.

Definition get_verts v l := map (hdDefault v) (map unlabel_path l).

Require Import Coq.Lists.SetoidList.

Lemma nodups_output: forall s g v,
  valid s g v ->
  NoDup (get_verts v (get_paths s)).
Proof.
  intros. induction H.
  - simpl. unfold get_verts; simpl. constructor.
  - inversion H0; subst.
    + simpl. unfold get_verts. unfold map. rewrite map_map. rewrite map_app.
      simpl.
      assert (List.map (fun x : LPath b => hdDefault v (unlabel_path x)) p ++ v0 :: nil = 
      rev (v0 :: rev (List.map (fun x : LPath b => hdDefault v (unlabel_path x)) p))). simpl.
      rewrite rev_involutive. reflexivity.
      rewrite H4. rewrite NoDup_NoDupA. apply NoDupA_rev. apply eq_equivalence.
      constructor. intro. rewrite <- In_InA_equiv in H5. rewrite <- in_rev in H5.
      assert (vIn g v0 = true). 

  apply SetoiList.NoDupA_rev. simpl.

(*Each vertex appears at most once in the output*)
Lemma no_dups_output: forall s g v,
  valid s g v ->
  NoDup (map fst (get_dists s)).
Proof.
  intros. induction H; simpl.
  - constructor.
  - inversion H0; subst; simpl in *.
    rewrite map_app. simpl. assert (map fst d ++ v0 :: nil = rev (v0 :: rev ((map fst d)))).
    simpl. rewrite rev_involutive. reflexivity.
    rewrite H3. rewrite NoDup_NoDupA. apply NoDupA_rev. apply eq_equivalence.
    constructor. intro. rewrite <- In_InA_equiv in H4. rewrite <- in_rev in H4.
    assert (vIn g v0 = true). eapply queue_in_graph. apply H. simpl. left. reflexivity. 
    pose proof (graph_iff_not_output _ _ _ _ H H5) as D; simpl in *.
    apply D in H4. 
    assert (vIn g0 v0 = true). apply match_in. exists c. exists g'. assumption.
    rewrite H6 in H4. inversion H4. apply NoDupA_rev. apply eq_equivalence. rewrite <- NoDup_NoDupA.
    assumption. assumption.
Qed. 
  


(*Theorem 24.6 in CLRS*)
Theorem sp_invariant: forall s g v u,
  valid s g v ->
  vIn g u = true ->
  vIn (get_graph s) u = false ->
  shortest_wpath g u v (getDistance u (get_paths s)).
Proof.
  intros. generalize dependent u. generalize dependent H. induction (get_heap s, get_graph s) using (well_founded_induction well_founded_bf_measure_heap).
  intros. inversion H0; subst.
  - simpl. unfold getDistance. simpl. simpl in H2. rewrite H2 in H1. inversion H1.
  - inversion H4; subst.
    + simpl. unfold getDistance. rewrite findP_app. destruct (N.eq_dec v0 u). subst.
      destruct (findP u p0) eqn : F. simpl. assert (u == u = true). apply node_eq. reflexivity.
      rewrite H8. clear H8. 
  (*Plan
    - show that shortest path always exists - DONE
    - prove that the heap contains valid paths to the start vertex - DONE
    - so there is a shortest path from u to v
    - then, if a condition holds at the start of a path and doesn't hold at the end, there is a boundary
      where it doesn/doesnt not hold (may have proved for SCC)
    - then I have x and y in the CLRS proof
    - also, may need to prove that u <> v (which should not be hard) - or really just prove for this*)
  (*Need to know that shortest_wpath is not None*)
        unfold findP. simpl.
    + destruct c. destruct p1. destruct p1. simpl in *.

(*Need to reason about distance*)
Print expand.
(*Either have additional distance information*)
Definition path_cost (l :LPath b) : b :=
  match l with
  | LP l' => fold_right (fun (x: LNode b) acc => let (_, y) := x in y + acc) #0 l' end.

Print findP.


(*Some stuff
- prove by well founded induction (strong induction)
 - need to prove that there is a state where previous one found and multisteps (anything on path)
- ie, if a path is the min chosen in the heap, all previous ones are already there (?)
*)


*)
End Correct.

Definition expand_dist (d : b) (v : Node) (c: Context a b) :=
  match c with
  | (_, _, _, s) => map (fun x : b * Node => let (l,v') := x in unit (_GHC.Num.+_ l d) v') s
  end.

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
  as well as the head of the list, ew should get the same as the distance*)

Definition labelHead (l: (LPath b)) : (option b * option Node)  :=
  match l with
  | LP nil => (None, None)
  | LP ((x,y) :: tl) => (Some y, Some x) 
  end.
Require Import Coq.Wellfounded.Inverse_Image.
(*
(*First, we need to know that nil is not in the heap*)
Lemma nil_notin_heap: forall h g,
  (forall x, ~In_Heap (x, LP nil) h) ->
  *)

(*If we calculate the path cost *)
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

(*Now we prove that it has valid paths and weights*)
Lemma paths_dijkstra: forall h g,
  map labelHead (dijkstra' (h,g)) = map (fun l => (path_cost (unlabel_path l), snd (labelHead l))) (dijkstra' (h,g


apply lex2. symmetry. unfold natNodes_eq. eapply match_none_size. apply H. unfold heap_length_lt.
unfold splitMin in H0. destruct h. simpl in n. contradiction. inversion H0; subst.
rewrite (mergeAll_size l4). simpl. omega.

 }
     (map (fun x : b * Node => let (l2, v') := x in unit (_GHC.Num.+_ l2 b3) v') l')). intros; induction l'.
      simpl. rewrite H7. reflexivity. simpl. destruct a3. 


 induction a0. simpl. rewrite H7. reflexivity.  simpl.



 simpl. 
          destruct c. destruct p. destruct p. simpl. 
          assert (forall l, 
          map_heap (fun (_ : b) (l2 : LPath b) => labelHead l2)
  match
    map (fun '(l2, v) => unit (_GHC.Num.+_ l2 b3) (LP ((v, _GHC.Num.+_ l2 b3) :: (n0, b3) :: unLPath))) l
  with
  | nil => h0
  | h'0 :: hs => merge (merge h0 h'0) (mergeAll hs)
  end =
map_heap (fun (x : b) (y : Node) => (Some x, Some y))
  match map (fun x : b * Node => let (l2, v') := x in unit (_GHC.Num.+_ l2 b3) v') l with
  | nil => h1
  | h'0 :: hs => merge (merge h1 h'0) (mergeAll hs)
  end). { intros. induction l2. simpl. apply H7.
    
      unfold map. unfold

 intros;  induction l2 using (well_founded_induction
                     (wf_inverse_image _ nat _ (@length _)
                        PeanoNat.Nat.lt_wf_0)). destruct l2. simpl. assumption. simpl. 
    rewrite map_merge. rewrite map_merge. rewrite map_merge. rewrite map_merge. 
     rewrite map_mergeAll. rewrite map_mergeAll. destruct l2. simpl.
      rewrite H7. destruct p. simpl. reflexivity. simpl.
     



 reflexivity. subst.  rewrite H7. simpl.
    simpl.



 reflexivity. unfold map. unfold List.map. rewrite H. simpl. rewrite 


 rewrite H8 in 


 unfold Default. apply None. specialize (H1 _ _ _ (fun l : LPath b => snd (labelHead l)) _ _ _ _ H2 H4).
      assert (h <> Heap.Empty) by (intro; subst). rewrite H1. simpl. rewrite H1.



    destruct (Heap.isEmpty h) eqn : He. simpl.
    destruct h. simpl in H0. destruct h'. simpl. reflexivity. simpl in H0; inversion H0. simpl in He; inversion He. simpl.
    destruct (Heap.isEmpty h') eqn : Hf. destruct h'.


Lemma dijkstra'_equiv: forall h g,
  dijkstra h g = dijkstra' (h, g).
Proof.
  intros. remember (h,g) as x. generalize dependent g. revert h.
  induction x using (well_founded_induction (well_founded_bf_measure_heap)).
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
  (forall k, ~In_Heap (k, LP nil) h) ->
  get_paths (sp_tail (g, h, l)) = l ++ dijkstra' (h, g).
Proof.
  intros. remember (h, g) as x. generalize dependent h. revert g. revert l.
  induction x using (well_founded_induction (well_founded_bf_measure_heap)).
  intros. destruct x; inversion Heqx; subst; clear Heqx.
  rewrite <- unfold_dijkstra'. rewrite unfold_sp_tail. simpl.
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

End Ind.
