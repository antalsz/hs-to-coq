Require Import Data.Graph.Inductive.Internal.Heap.
Require Import Coq.Lists.List.
Require Import Coq.Wellfounded.Inverse_Image.
Require Import Omega.
Require Import HeapEquiv.
Require Import Helper.

Require Import Equations.Equations.

Section Heap.

Context {A B : Type} `{Hord: Base.Ord A} {Hdefault : Err.Default A} {Hdefault' : Err.Default B}.


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

End Heap.
