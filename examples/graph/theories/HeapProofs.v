Require Import Data.Graph.Inductive.Internal.Heap.
Require Import Coq.Lists.List.
Require Import Coq.Wellfounded.Inverse_Image.
Require Import Omega.
Require Import HeapEquiv.
Require Import Helper.

Require Import Equations.Equations.
Require Import OrdTactic.

Section Heap.

Context {A B : Type} `{Hord: Base.Ord A} {Hdefault : Err.Default A} {Hdefault' : Err.Default B} `{HOrdLaws: OrdLaws A}.


(*An equivalent version that uses Equations*)

Equations toList' {a} {b} `{GHC.Base.Ord a} `{Err.Default (a * b)} (h: Heap a b) : list (a * b) by wf (size h) lt :=
toList' h => match h with 
              | Heap.Empty => nil 
              | h' => let 'pair x r := pair (findMin h') (deleteMin h') in cons x (toList r)
              end. 

(*Better induction for heaps (from CPDT)*)

Section All.
  Variable T : Type.
  Variable P : T -> Prop.

  Fixpoint All (ls : list T) : Prop :=
    match ls with
      | nil => True
      | cons h t => P h /\ All t
    end.
End All.

Section Heap_ind'.
  Variable P : (Heap A B) -> Prop.

  Hypothesis Node_case : forall a b (ls : list (Heap A B)),
    All (Heap A B) P ls -> P (Node a b ls).

  Hypothesis Empty_case :  P Heap.Empty.

  Fixpoint Heap_ind' (tr : (Heap A B)) : P tr :=
    match tr with
      | Node a b ls => Node_case a b ls
        ((fix list_nat_tree_ind (ls : list (Heap A B)) : All (Heap A B) P ls :=
          match ls  with
            | nil => I
            | cons tr' rest => conj (Heap_ind' tr') (list_nat_tree_ind rest)
          end) ls)
      | Empty => Empty_case
    end.

End Heap_ind'.

(*Now we can work with Equations version instead, which might be easier*)
Lemma toList_equiv: forall h,
  toList h = toList' h.
Proof.
  intros. rewrite <- unfold_toList. eapply toList'_elim. intros. destruct h0. simpl.
  reflexivity. simpl. reflexivity.
Qed.

(*In the heap*)
Fixpoint In_Heap  (p : A * B) (h: Heap A B) :=
  match h with
  | Heap.Empty => False
  | Node x y l => (x,y) = p \/ List.fold_right (fun y acc => y \/ acc) False (List.map (fun y => In_Heap p y) l)
  end.

(*Specifications for different functions*)
Lemma in_heap_merge: forall p h1 h2,
  In_Heap p (merge h1 h2) <-> In_Heap p h1 \/ In_Heap p h2.
Proof.
  intros. unfold merge. generalize dependent h2. 
  induction h1 using Heap_ind'.
  - intros. destruct h2. simpl. split; intros. left. assumption. destruct H1; try assumption. destruct H1.
    destruct (Base.op_zl__ a a0) eqn : ?.
    + simpl. split; intros. destruct H1. left. left. assumption. destruct H1. destruct H1.
      right. left. assumption. right. right. assumption. left. right. assumption.
      destruct H1. destruct H1. left. assumption. right. right. assumption.
      destruct H1. right. left. left. assumption. right. left. right. assumption.
    + simpl. split; intros. destruct H1. right. left. assumption. destruct H1. destruct H1.
      left. left. assumption. left. right. assumption. right. right. assumption.
      destruct H1. destruct H1. right. left. left. assumption. right. left. right. assumption.
      destruct H1. left. assumption. right. right. assumption.
  - intros. simpl. destruct h2. split; intros; simpl in *. auto. destruct H0; auto. split; intros.
    right. assumption. destruct H0. destruct H0. assumption.
Qed.

Lemma in_heap_mergeAll: forall p hs,
  In_Heap p (mergeAll hs) <-> fold_right (fun x acc => In_Heap p x \/ acc) False hs.
Proof.
  intros. induction hs using (well_founded_induction
                     (wf_inverse_image _ nat _ (@length _)
                        PeanoNat.Nat.lt_wf_0)).
  destruct hs. simpl. reflexivity. simpl. destruct hs.
  simpl. split; intros. left. assumption. destruct H1. assumption. destruct H1.
  split; intros. apply in_heap_merge in H1. destruct H1. apply in_heap_merge in H1.
  destruct H1. left. assumption. simpl. right. left. assumption. 
  right. apply H0 in H1. simpl. right. apply H1. simpl. omega.
  rewrite in_heap_merge. rewrite in_heap_merge. simpl in H1. destruct H1.
  left. left. assumption. destruct H1. left. right. assumption. 
  right. apply H0. simpl. omega. assumption.
Qed.

Program Instance triple : Err.Default (A * B * Heap A B).
Next Obligation.
inversion Hdefault. inversion Hdefault'. apply (default, default0, Heap.Empty).
Defined.

Lemma in_heap_splitMin: forall (p: A * B) (h h': Heap A B) k v,
  h <> Heap.Empty ->
  splitMin h = (k, v, h') ->
  In_Heap p h <-> p = (k,v) \/ In_Heap p h'.
Proof.
  intros. unfold splitMin in H1. destruct h. contradiction. inversion H1; subst.
  rewrite in_heap_mergeAll. simpl.
  assert (forall l' p,
  fold_right (fun y acc : Prop => y \/ acc) False (map (fun y : Heap A B => In_Heap p y) l') <->
  fold_right (fun (x : Heap A B) (acc : Prop) => In_Heap p x \/ acc) False l'). { intros; induction l'.
  simpl. reflexivity. simpl. split; intros. destruct H2. left. assumption. right. apply IHl'. apply H2.
  destruct H2. left. assumption. right. apply IHl'. apply H2. } rewrite H2. split; intros.
  destruct H3. left. subst. reflexivity. right. assumption. destruct H3. left. subst. reflexivity. right.
  assumption.
Qed.

(*Empty does not appear in the heap*)
Inductive nEmpty : Heap A B -> Prop  :=
  | h_unit : forall x y, nEmpty (unit x y)
  | h_merge: forall h h', nEmpty h -> nEmpty h' -> nEmpty (merge h h')
  | h_mergeAll: forall hs, (forall h, In h hs -> nEmpty h) -> nEmpty (mergeAll hs).
(*
Inductive WF_Heap : Heap A B -> Prop :=
  | h_empty : WF_Heap Heap.Empty
  | h_merge : forall h h', WF_Heap h -> WF_Heap h' -> nEmpty h -> nEmpty h' -> WF_Heap 
*)

(*Total versions of the partial functions in [Heap.v]*)

Definition splitMinT (h: Heap A B) :=
match h with
| Heap.Empty => None
| Node key val hs => Some (key, val, mergeAll hs)
end.

(*Equivalence of [splitMin] and [splitMinT]*)
Lemma splitMin_equiv: forall (h : Heap A B),
  h <> Heap.Empty ->
  Some (splitMin h) = splitMinT h.
Proof.
  intros. destruct h. contradiction. simpl. reflexivity.
Qed.

Definition findMinT (h: Heap A B) :=
  match h with
  | Heap.Empty => None
  | Node key val _ => Some (key, val)
  end.


(*Equivalence of [findMin] and [findMinT]*)
Lemma findMin_equiv: forall (h: Heap A B),
  h <> Heap.Empty ->
  Some (findMin h) = findMinT h.
Proof.
  intros. destruct h; [contradiction | reflexivity].
Qed. 

(*Two equivalent functions used in In_Heap*)
Lemma in_heap_equiv: forall l k v,
fold_right (fun (x : Heap A B) (acc : Prop) => In_Heap (k, v) x \/ acc) False l <->
fold_right (fun y acc : Prop => y \/ acc) False (map (fun y : Heap A B => In_Heap (k, v) y) l).
Proof.
  intros. induction l; simpl. reflexivity. rewrite IHl. reflexivity.
Qed.

(*Another property used for In_Heap*)
Lemma in_heap_exists: forall l k v,
  fold_right (fun (x : Heap A B) (acc : Prop) => In_Heap (k, v) x \/ acc) False l <->
  exists h, In h l /\ In_Heap (k, v) h.
Proof.
  intros. induction l; intros; simpl.
  - split; intros. destruct H0. destruct_all. destruct H0.
  - rewrite IHl. split; intros.
    + destruct H0. exists a. simplify'. destruct_all. exists x. split. right. all: assumption.
    + destruct_all. destruct H0. subst. left. assumption. right. exists x. simplify'.
Qed.

(*A rewrite rule to avoid using [simpl] and unfolding lots of things*)
Lemma in_heap_unfold: forall h t k v,
  fold_right (fun (x : Heap A B) (acc : Prop) => In_Heap (k, v) x \/ acc) False (h :: t) <->
  In_Heap (k, v) h \/ fold_right (fun (x : Heap A B) (acc : Prop) => In_Heap (k, v) x \/ acc) False t.
Proof.
  intros. simpl. reflexivity.
Qed.

(*HMap function with key*)
Fixpoint map_heap {C} (f: A -> B -> C) (h: Heap A B) : Heap A C :=
  match h with
  | Heap.Empty => Heap.Empty
  | Node x y l => Node x (f x y) (map (map_heap f) l)
  end.

Lemma map_merge: forall {C} (f: A -> B -> C) (h1 h2: Heap A B),
  map_heap f (merge h1 h2) = merge (map_heap f h1) (map_heap f h2).
Proof.
  intros. destruct h1; destruct h2; try(reflexivity).
  simpl. destruct (Base.op_zl__ a a0); reflexivity.
Qed. 

Lemma map_mergeAll: forall {C} (f : A -> B -> C) (l: list (Heap A B)),
  map_heap f (mergeAll l) = mergeAll (map (map_heap f) l).
Proof.
  intros. induction l using (well_founded_induction
                     (wf_inverse_image _ nat _ (@length _)
                        PeanoNat.Nat.lt_wf_0)).
  - destruct l. simpl. reflexivity. simpl. destruct l. simpl. reflexivity.
    rewrite map_merge. rewrite H0. simpl. rewrite map_merge. reflexivity. simpl. omega.
Qed.

Lemma map_splitMin: forall C `{Err.Default C} `{Err.Default (A * C * Heap A C)} (f : A -> B -> C) x y
   (h : Heap A B) (h' : Heap A B),
  h <> Heap.Empty ->
  splitMin h = ((x,y), h') ->
  splitMin (@map_heap C f h) = ((x, f x y), (@map_heap C f h')).
Proof.
  intros. destruct h. contradiction.
  simpl. simpl in H3. inversion H3; subst. rewrite map_mergeAll. reflexivity.
Qed.



Lemma all_in: forall {A : Type} (P : A -> Prop) l,
  All A P l <-> (forall x, In x l -> P x).
Proof.
  intros. induction l; simpl; split; intros.
  - destruct H1.
  - apply I.
  - destruct_all. destruct H1. subst. assumption. apply IHl. assumption. assumption.
  - split. apply H0. left. reflexivity. apply IHl. intros. apply H0. right. assumption.
Qed.

Lemma map_in_heap: forall f h x y,
  In_Heap (x,y) (map_heap f h) <-> exists z, f x z = y /\ In_Heap (x,z) h.
Proof.
  intros. induction h using Heap_ind'.
  - simpl. split; intros.
    + destruct H1.
      * inversion H1; subst. exists b. split. reflexivity. left. reflexivity.
      * rewrite <- in_heap_equiv in H1. rewrite all_in in H0.
        rewrite in_heap_exists in H1.
        destruct H1 as [h]. assert (C:= H1). destruct H1. rewrite in_map_iff in H1. destruct H1.
        assert (D:= H1). destruct_all.
        subst. apply H0 in H4. apply H4 in H2. destruct_all. exists x1. split. assumption.
        right.  rewrite <- in_heap_equiv. rewrite in_heap_exists. exists x0. split; assumption.
    + destruct H1 as [z]. destruct_all. subst. destruct H2. inversion H1; subst. left. reflexivity.
      right. rewrite <- in_heap_equiv in H1. rewrite <- in_heap_equiv. rewrite in_heap_exists in H1.
      rewrite in_heap_exists. rewrite all_in in H0.
       destruct_all. assert (C := H1). apply H0 in H1.
      destruct H1. assert ( In_Heap (x, f x z) (map_heap f x0)). apply H3. 
      exists z. split. reflexivity. assumption. exists (map_heap f x0). rewrite in_map_iff.
      split. exists x0. split. reflexivity. assumption. assumption.
  - simpl. split; intros. destruct H0. destruct_all. destruct H1.
Qed.

(*Proving that findMin actually works: we need a well-founded heap, ie, a heap that can actually be
  created by the exported functions*)

Inductive WF : Heap A B -> Prop :=
  | WF_unit: forall x y, WF (unit x y)
  | WF_merge: forall h1 h2, WF h1 -> WF h2 -> WF (merge h1 h2)
  | WF_mergeAll: forall l, (forall h, In h l -> WF h) -> WF (mergeAll l).

Require Import GHC.Base.

(*The [mergeAll] case needs additional results, since the IH is not strong enough on its own to prove
  the claim. We need to know that for any heap in the list that is merged, the root is larger than
  the minimum of the merged heap. To do this, we need a few helper lemmas *)

Lemma merge_min': forall h1 h2 x y h',
  splitMinT (merge h1 h2) = Some (x,y,h') ->
  (exists h'', h1 = Node x y h'' /\ (forall x' y' z', h2 = Node x' y' z' -> x <= x' = true))
 \/ (exists h'', h2 = Node x y h'' /\ (forall x' y' z', h1 = Node x' y' z' -> x <= x' = true )).
Proof.
  intros. destruct h1; destruct h2. inversion H0. simpl in H0. inversion H0; subst. right.
  exists l. split. reflexivity. intros. inversion H1. inversion H0; subst. left. exists l. split. reflexivity.
  intros. inversion H1.
  simpl in H0. destruct (a < a0) eqn : L. remember (Node a0 b0 l0 :: l) as h. inversion H0; subst.
  left. exists l. split. reflexivity. intros. inversion H1; subst. order A.
  remember ((Node a b l :: l0)) as h. inversion H0; subst.
  right. exists l0. split. reflexivity. intros. inversion H1; subst. order A.
Qed.


Lemma merge_empty: forall (h1 h2 : Heap A B),
  merge h1 h2 = Heap.Empty <-> h1 = Heap.Empty /\ h2 = Heap.Empty.
Proof.
  intros. split; intros. destruct h1; destruct h2; simpl in H0; try(split; reflexivity); try(inversion H0).
  destruct (a < a0); inversion H0. destruct_all; subst. simpl. reflexivity.
Qed.

Lemma mergeAll_empty: forall (l: list (Heap A B)),
  mergeAll l = Heap.Empty <-> l = nil \/ (forall h, In h l -> h = Heap.Empty).
Proof.
  intros. induction l using (well_founded_induction
                     (wf_inverse_image _ nat _ (@length _)
                        PeanoNat.Nat.lt_wf_0)). split; intros.
  - destruct l. left. reflexivity. destruct l. simpl in H1.
    subst. right. intros. simpl in H1. destruct H1. subst. reflexivity. destruct H1.
    simpl in H1. rewrite merge_empty in H1. destruct H1. rewrite merge_empty in H1.
    destruct_all. subst. right. intros. simpl in H1. destruct H1. subst. reflexivity.
    destruct H1. subst. reflexivity. apply H0 in H2. destruct H2. subst. inversion H1.
    apply H2. assumption. simpl. omega.
  - destruct l. reflexivity. destruct l. simpl. destruct H1. inversion H1.
    apply H1. left. reflexivity. simpl. destruct H1. inversion H1.
    rewrite merge_empty. split. rewrite merge_empty. split; apply H1; try(solve_in).
    right. left. reflexivity. apply H0. simpl. omega. right. intros. apply H1. right. right. assumption.
Qed. 

(*The key lemma for proving mergeAll finds the minimum. The proof boils down to checking a lot of cases
  and using [merge_min']*)
Lemma mergeAll_min'': forall l x y h',
  splitMinT (mergeAll l) = Some (x,y,h') ->
  forall x' y' z', In (Node x' y' z') l -> x <= x' = true.
Proof.
  intros. generalize dependent h'. revert x y. induction l using (well_founded_induction
                     (wf_inverse_image _ nat _ (@length _)
                        PeanoNat.Nat.lt_wf_0)); intros.
  destruct l. simpl in H1. inversion H1. destruct l. simpl in H2. simpl in H1. destruct H1. subst.
  inversion H2; subst. order A. destruct H1. simpl in H2.
  apply merge_min' in H2.
 destruct H2; simpl in H1; destruct_all.
  assert (splitMinT (merge h h0) = Some(x,y,(mergeAll x0))) by (rewrite H2; reflexivity).
  apply merge_min' in H4. destruct H4; destruct_all. destruct H1.
  subst. inversion H4; subst. order A. destruct H1. subst. eapply H5. reflexivity.
  destruct (mergeAll l) eqn : M.
  - rewrite mergeAll_empty in M. destruct M. subst. inversion H1. apply H6 in H1. inversion H1.
  - assert (x <= a = true). eapply H3. reflexivity. 
    assert (a <= x' = true). eapply H0. 2 : { apply H1. } simpl. omega. rewrite M. simpl. reflexivity.
    order A.
  - subst. destruct H1; subst. eapply H5. reflexivity. destruct H1. inversion H1; subst. order A.
    destruct (mergeAll l) eqn : M.
    + rewrite mergeAll_empty in M. destruct M; subst. inversion H1. apply H4 in H1. inversion H1.
    + assert (x <= a = true). eapply H3. reflexivity. assert (a <= x' = true). eapply H0.
      2 : { apply H1. } simpl. omega. rewrite M. reflexivity. order A.
  - destruct (merge h h0) eqn : M.
    + rewrite merge_empty in M. destruct_all. subst. destruct H1. inversion H1. destruct H1. inversion H1.
      eapply H0. 2 : { apply H1. } simpl. omega. rewrite H2. simpl. reflexivity.
    + assert (splitMinT (merge h h0) = Some (a, b, mergeAll l0)) by (rewrite M; reflexivity).
      apply merge_min' in H4. destruct H4; destruct_all; subst.
      * destruct H1; subst. inversion H1; subst. eapply H3. reflexivity.
        destruct H1; subst. simpl in M. destruct (a < x') eqn : L.
        assert (x <= a = true). eapply H3. reflexivity. order A. inversion M; subst.
        eapply H3. reflexivity. eapply H0. 2 : { apply H1. } simpl. omega. rewrite H2. reflexivity.
      * destruct H1; subst. simpl in M. destruct (x' < a) eqn : L.
        inversion M; subst. order A. assert (x <= a = true). eapply H3. reflexivity. order A.
        destruct H1. inversion H1; subst. eapply H3. reflexivity.
        eapply H0. 2 : { apply H1. } simpl. omega. rewrite H2. reflexivity.
Qed. 

(*If the heap is well_formed, then findMin actually finds the min.*)
Lemma WF_min: forall h x y h',
  WF h ->
  splitMinT h = Some (x,y, h') ->
  forall a b, In_Heap (a,b) h -> x <= a = true.
Proof.
  intros. generalize dependent x. revert y. generalize dependent a. revert h'. revert b. induction H0; intros.
  - simpl in H1. inversion H1; subst. simpl in H2. destruct H2. inversion H0; subst. order A. destruct H0.
  - destruct h1; simpl in H1.
    + destruct h2; inversion H1. subst. unfold merge in H2. eapply IHWF2. apply H2. reflexivity.
    + destruct h2.
      * simpl in H1. unfold merge in H2. inversion H1; subst. eapply IHWF1. apply H2. reflexivity.
      * destruct (a0 < a1) eqn : L.
        -- rewrite in_heap_merge in H2. remember (Node a1 b1 l0 :: l) as h. simpl in H1. inversion H1.
           subst. destruct H2.
           ++ eapply IHWF1. apply H0. reflexivity.
           ++ assert (a1 <= a = true). eapply IHWF2. apply H0. reflexivity.
              order A.
       -- assert (a1 <= a0 = true) by (order A). clear L. rewrite in_heap_merge in H2.
          remember (Node a0 b0 l :: l0) as h. simpl in H1. inversion H1. subst. destruct H2.
          ++ assert (a0 <= a = true). eapply IHWF1. apply H2. reflexivity. order A.
          ++ eapply IHWF2. apply H2. reflexivity.
  - rewrite in_heap_mergeAll in H2. rewrite in_heap_exists in H2. destruct H2 as [h'']. destruct_all. 
    destruct h''. simpl in H4. destruct H4.
    assert (splitMinT  (Node a0 b0 l0) = Some (a0, b0, mergeAll l0)). reflexivity.
    assert (a0 <= a = true). eapply H1. apply H2. apply H4. apply H5. 
    assert (x <= a0 = true).
    eapply mergeAll_min'' in H3. apply H3. apply H2. order A.
Qed.
End Heap.
