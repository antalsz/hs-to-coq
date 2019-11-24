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


(* Inductive relation*)
Section Ind.

Context {a : Type} {b : Type} { gr : Type -> Type -> Type} {Hgraph : Graph.Graph gr} {Hlaw : Graph.LawfulGraph gr}
{Hnum: GHC.Num.Num b} {Heq: Base.Eq_ b} {HOrd: Base.Ord b} {Hreal: @GHC.Real.Real b Hnum Heq HOrd}
{Heq': Base.Eq_ a} {HOrd': Base.Ord a} {Herr: Err.Default (b)}.

Program Instance path_default : Err.Default (Graph.LPath b).
Next Obligation.
constructor. apply nil.
Defined.

(*Well formed lexicographic measure*)
Definition natNodes := (@Path.natNodes a b gr Hgraph).

Definition natNodes_lt (x y : gr a b) := natNodes x < natNodes y.

Definition natNodes_eq (x y : gr a b) := natNodes x = natNodes y.
(*Definition list_length_lt {a b} (x y : list a) := size x < size y*)
Definition heap_length_lt (x y : Heap b (Graph.LPath b)) := (Heap.size x) < (Heap.size y).
 (*list_lsize (toList x) (toList y).*)

Definition bf_measure_heap:=
  lex _ _ (natNodes_lt) natNodes_eq (heap_length_lt).

Lemma well_founded_bf_measure_heap : well_founded (bf_measure_heap).
Proof.
  intros. eapply WF_lex.
  - apply f_nat_lt_wf.
  - apply f_nat_lt_wf.
  - unfold RelationClasses.Transitive. intros. unfold natNodes_eq in *; omega.
  - intros. unfold natNodes_eq in *. unfold natNodes_lt in *. destruct H. destruct H.
    omega.
  - unfold RelationClasses.Symmetric. intros. unfold natNodes_eq in *. omega.
Qed. 

Instance need_this_for_equations : WellFounded (bf_measure_heap).
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
  induction r' using (well_founded_induction (well_founded_bf_measure_heap)).
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
  induction r' using (well_founded_induction (well_founded_bf_measure_heap)).
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
Lemma leveln_tail_equiv: forall g h l,
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
