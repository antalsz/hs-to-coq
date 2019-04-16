Require Import GHC.Base.
Import GHC.Base.Notations.
Require Import Proofs.GHC.Base.
Require Import Data.Map.Internal.
Import GHC.Num.Notations.
Require Import OrdTactic.
Require Import Psatz.
Require Import Tactics.
Set Bullet Behavior "Strict Subproofs".
Require Import MapProofs.Bounds.
Require Import MapProofs.Tactics.
Require Export MapProofs.PairTypeclass.

Section WF.
Context {e : Type} {a : Type} {HEq : Eq_ e} {HOrd : Ord e} {HEqLaws : EqLaws e}  {HOrdLaws : OrdLaws e}.

(** ** Verification of [foldrWithKey] *)

Lemma fold_right_toList_go:
  forall f (n : a) map (xs : list (e * a)),
  fold_right f n (foldrWithKey (fun x y t  => (x,y) :: t) xs map) = 
  foldrWithKey (fun x y t => f (x,y) t) (fold_right f n xs) map.
Proof.
  intros. generalize dependent xs. induction map.
  - intros. simpl. rewrite IHmap1. simpl. rewrite IHmap2. reflexivity.
  - simpl. intros. reflexivity.
Qed.

Lemma foldrWithKey_spec:
  forall f (n : a) map,
  foldrWithKey f n map = fold_right (fun (x : e * a) t => let (a0, b0) := x in f a0 b0 t) n (toList map).
Proof.
  intros. unfold toList. unfold toAscList. rewrite fold_right_toList_go. simpl. reflexivity.
Qed.

(** ** Verification of [foldr] *)
Lemma foldr_spec:
  forall f (n: a) (map : Map e a),
  foldr f n map = foldrWithKey (fun x y t => f y t) n map.
Proof.
  intros. generalize dependent n. induction map.
  - intros. simpl. rewrite IHmap1. rewrite IHmap2. reflexivity.
  - intros. simpl. reflexivity.
Qed.

(** ** Verification of [foldr'] *)
Lemma foldr'_spec:
  forall {k : Type} (f : a -> k -> k) (n : k) (m : Map e a),
  foldr' f n m = foldr f n m.
Proof. reflexivity. Qed.

(** ** Verification of [toList] *)

Lemma foldrWithKey_const_append:
  forall xs (map : Map e a),
  foldrWithKey (fun x y t => (x,y) :: t) xs map = toList map ++ xs.
Proof.
  intros. generalize dependent xs. induction map; intros.
  - unfold toList, toAscList in *. simpl. rewrite IHmap1. rewrite IHmap2. 
    rewrite (IHmap1 ((k, a0) :: foldrWithKey (fun (k0 : e) (x : a) (xs0 : list (e * a)) => (k0, x) :: xs0) nil map2)).
    rewrite <- app_assoc. reflexivity.
  - simpl. reflexivity.
Qed.

(*Allows us to decompose toList*)
Lemma toList_Bin:
  forall sz key value (m1 m2 : Map e a),
  toList (Bin sz key value m1 m2) = toList m1 ++ (key, value) :: nil ++ toList m2.
Proof.
  intros.
  unfold toList. unfold toAscList. simpl.
  rewrite foldrWithKey_const_append. rewrite foldrWithKey_const_append.
  rewrite foldrWithKey_const_append. rewrite app_nil_r. rewrite app_nil_r.
  reflexivity.
Qed.

(*We have two different versions of toList_sem for use in proving [Eq], preceded by several helper lemmas*)

(*This function imposes a stronger condition than List.elem - the values must be equal according to Coq.
This is used in proving strong equality*)
Fixpoint Key_In {e} {a} `{EqLaws e} (key : e) (value : a) (l : list (e * a)) : Prop :=
  match l with
  | nil => False
  | a :: tl => (let (x,y):= a in x == key = true /\ y = value) \/ Key_In key value tl
  end.

(*Helper methods for logic*)

Lemma or_assoc: forall b1 b2 b3,
  (b1 \/ b2) \/ b3 <-> b1 \/ ( b2 \/ b3).
Proof.
  intros. split; intros.
  - destruct H. destruct H. left. assumption. right. left. assumption. right.
    right. assumption.
  - destruct H. left. left. assumption. destruct H. left. right. assumption. right.
    assumption.
Qed.

Lemma false_or: forall (P : Prop),
  False \/ P <-> P.
Proof.
  intros. split; intros.
  - destruct H. destruct H. apply H.
  - right. apply H.
Qed. 

(*Key property of Key_In for lists - if we append to 2 lists, an item is in the whole list
iff it is in one of them*)
Lemma elem_or : forall {e} {a} `{EqLaws e} (key : e) (value : a) l1 l2,
  Key_In key value (l1 ++ l2) <-> Key_In key value l1 \/ Key_In key value l2.
Proof.
  intros. generalize dependent l2. induction l1.
  - intros. simpl. split; intros.
    + right. assumption.
    + destruct H1. destruct H1. assumption.
  - intros. simpl. rewrite IHl1. rewrite or_assoc. apply iff_refl.
Qed.

(*The first toList_sem:
This says that sem m key returns a Value iff that key, value pair appears in the 
resulting toList of the map (according to Coq equality for values)*)
Lemma toList_sem :
  forall  `{EqLaws a}  (m: Map e a) lb ub, Bounded m lb ub ->
  forall key value, sem m key = Some value <-> Key_In key value (toList m).
Proof.
  intros. generalize dependent value. induction H1.
  - simpl. intros. split; intros. discriminate H1. destruct H1.
  - intros. simpl. rewrite toList_Bin. rewrite elem_or. 
    assert (((x, v) :: nil ++ toList s2) = (((x, v) :: nil) ++ toList s2)).
    simpl. reflexivity. rewrite H5. rewrite elem_or. split; intros.
      + destruct (sem s1 key) eqn : ?; simpl in H6.
      * apply IHBounded1 in H6. left. apply H6. 
      * destruct (key == x) eqn : ?; simpl in H6.
        { right. left. simpl. left. apply Eq_Symmetric in Heqb.
          split. apply Heqb. inversion H6. reflexivity. }
        { apply IHBounded2 in H6. right. right. assumption. }
     + destruct H6.
      * apply IHBounded1 in H6. rewrite H6. simpl. reflexivity.
      * destruct H6. simpl in H6. destruct H6. destruct H6.
        assert (sem s1 key = None). { eapply sem_outside_above.
        apply H1_. order_Bounds e. }
        rewrite H8. simpl. apply Eq_Symmetric in H6. rewrite H6. simpl.
        rewrite H7. reflexivity. destruct H6. apply IHBounded2 in H6.
        assert (H1_1:=H1_0). eapply sem_inside in H1_0. destruct H1_0.
        assert (sem s1 key = None). { eapply sem_outside_above. apply H1_.
        assert (isLB (Some x) key = true). { apply H7. }
        order_Bounds e. }
        assert (key == x = false) by (order_Bounds e).
        rewrite H9. rewrite H10. simpl. assumption. apply H6.
Qed.

(*Helper lemmas for [toList_sem']*)
(*Analogue of [elem_or] for List.elem*)
Lemma list_elem_or : forall `{Eq_ a} `{EqLaws a} l1 l2 (x : e * a),
  List.elem x (l1 ++ l2) = List.elem x l1 || List.elem x l2.
Proof.
  intros. generalize dependent l2. induction l1; intros.
  - destruct l2. simpl. reflexivity. simpl. reflexivity.
  - destruct l2. simpl. rewrite app_nil_r. rewrite orb_false_r .
    reflexivity. simpl. rewrite IHl1. rewrite orb_assoc. simpl. reflexivity.
Qed.

(*Weaker version of [toList_sem], using Haskell equality instead of Coq's. sem m key == Some value 
iff the (key, value) pair appears in toList*)
Lemma toList_sem' :
  forall `{Eq_ a} `{EqLaws a}  m lb ub, Bounded m lb ub ->
  forall key value, sem m key == Some value = true <->
     List.elem (key, value) (toList m) = true.
Proof.
  intros. generalize dependent value. induction H2.
  - simpl. intros. split; intros.
    + discriminate H2.
    + discriminate H2.
  - intros; split; intros; simpl.
    + rewrite toList_Bin. simpl. rewrite list_elem_or. simpl.
      simpl in H6. destruct (List.elem (key, value) (toList s1)) eqn : ?.
      * simpl. reflexivity.
      * simpl. specialize (IHBounded1 value). destruct IHBounded1.
        apply contrapositive in H7. destruct (sem s1 key) eqn : ?.
        { simpl in H6. contradiction. }
        { simpl in H6. destruct (_GHC.Base.==_ (key, value) (x, v)) eqn : ?.
          { simpl. reflexivity. }
          { simpl. rewrite eq_tuple_eq in Heqb0. 
            rewrite andb_false_iff in Heqb0. destruct Heqb0.
            { rewrite H9 in H6. simpl in H6. apply IHBounded2. apply H6. }
            { destruct (_GHC.Base.==_ key x) eqn : ?.
              { simpl in H6. rewrite simpl_option_some_eq in H6. 
                apply Eq_Symmetric in H6. unfold is_true in H6. 
                rewrite H9 in H6. discriminate H6. }
              { simpl in H6. apply IHBounded2. assumption. }
            }
          }
        }
        { destruct (List.elem (key, value) (toList s1)). discriminate Heqb.
          intro. discriminate H9. }
    + rewrite toList_Bin in H6. simpl in H6. rewrite list_elem_or in H6.
      rewrite orb_true_iff in H6. destruct H6.
      * apply IHBounded1 in H6. destruct (sem s1 key) eqn : ?.
        { simpl. assumption. }
        { discriminate H6. }
      * simpl in H6. rewrite orb_true_iff in H6. destruct H6.
        { assert (forall i, sem s1 key <> Some i). { rewrite eq_tuple_prop in H6.
          destruct H6. intros. intro. solve_Bounds e. } 
          assert (sem s1 key = None). { destruct (sem s1 key). specialize (H7 a0).
          contradiction. reflexivity. }
          rewrite H8. simpl. rewrite eq_tuple_prop in H6. destruct H6.
          rewrite H6. simpl. rewrite simpl_option_some_eq. apply Eq_Symmetric.
          apply H9. }
        { apply IHBounded2 in H6. destruct (sem s2 key) eqn : ?.
          assert (sem s1 key = None). { apply (sem_inside H2_0) in Heqo.
          destruct Heqo. eapply sem_outside_above. apply H2_. order_Bounds e. }
          rewrite H7. simpl. assert (key == x = false) by solve_Bounds e. rewrite H8.
          simpl. assumption. discriminate H6. }
Qed. 

(*Equality based (rather than prop based) version of the above*)
Lemma toList_sem'_eq :
  forall `{Eq_ a} `{EqLaws a}  m lb ub, Bounded m lb ub ->
  forall key value, sem m key == Some value = List.elem (key, value) (toList m).
Proof.
  intros. rewrite prop_bool.  eapply toList_sem'. apply H2.
Qed.

(*The next two lemmas say that every key in toList m is between the bounds of the map*)
Lemma toList_lb : forall m lb ub,
  Bounded m lb ub ->
  Forall (fun (i : e * a) => let (x, _) := i in isLB lb x = true) (toList m).
Proof.
  intros. induction H.
  - apply Forall_nil.
  - rewrite toList_Bin. rewrite Forall_forall in *.
    intros. simpl in H5. rewrite in_app_iff in *.
    destruct H5.
    + apply IHBounded1. assumption.
    +  simpl in H5.  destruct H5. 
      *  subst.  assumption. 
      * apply IHBounded2 in H5. simpl in H5. rename x0 into x2. 
        destruct x2. order_Bounds e.
Qed.

Lemma toList_ub : forall m lb ub,
  Bounded m lb ub ->
  Forall (fun (i : e * a) => let (x, _) := i in isUB ub x = true) (toList m).
Proof.
  intros. induction H.
  - apply Forall_nil.
  - rewrite toList_Bin. rewrite Forall_forall in *. intros.
    simpl in H5. rewrite in_app_iff in *. destruct H5.
    + apply IHBounded1 in H5. destruct x0. order_Bounds e.
    + simpl in H5. destruct H5. subst. assumption. apply IHBounded2. assumption.
Qed. 

(*The list of the empty tree is empty*)
Lemma toList_Tip: toList (@Tip e a) = nil.
Proof. reflexivity. Qed.

(*The list contains the left subtree, then the current value, then the right subtree
(crucial in showing that the list is sorted)*)
Lemma toList_bin:
  forall key value n (m1 m2 : Map e a),
  toList (Bin n key value m1 m2) = toList m1 ++ ((key, value) :: nil) ++ toList m2.
Proof. intros. apply toList_Bin. Qed.

(*The next two lemmas prove that the list from toList is in the same order even if we balance the tree. The
proofs are very similar to setProofs, only 1 more case at the end*)
Lemma toList_balanceR :
  forall x y (m1: Map e a) m2 lb ub,
  Bounded m1 lb (Some x) ->
  Bounded m2 (Some x) ub ->
  balance_prop (size m1) (size m2) \/
  balance_prop_inserted (size m2 - 1) (size m1) /\ (1 <= size m2)%Z  \/
  balance_prop (size m1 + 1) (size m2) ->
  toList (balanceR x y m1 m2) = toList m1 ++ ((x,y) :: nil) ++ toList m2.
Proof.
  intros.
  unfold balanceR.
  unfold op_zg__, op_zl__, Ord_Integer___, op_zg____, op_zl____.

  repeat lazymatch goal with [ H : Bounded ?s _ _ |- context [match ?s with _ => _ end] ] => inversion H; subst; clear H end;
  repeat lazymatch goal with [ |- context [if (?x <? ?y)%Z then _ else _] ] => destruct (Z.ltb_spec x y) end;
  rewrite ?size_Bin in *; simpl (size Tip) in *; simpl sem;
  simpl isLB in *;
  simpl isUB in *.
  all: try solve [exfalso; lia_sizes]. (* Some are simply impossible *)
  all: repeat find_Tip.
  all: rewrite ?toList_Bin, <- ?app_assoc; try reflexivity.
  simpl. rewrite <- app_assoc. simpl. reflexivity. simpl. rewrite <-app_assoc. simpl.
  reflexivity. 
Qed.

Lemma toList_balanceL:
  forall x y (m1: Map e a) m2 lb ub,
  Bounded m1 lb (Some x) ->
  Bounded m2 (Some x) ub  ->
  balance_prop (size m1) (size m2) \/
  balance_prop_inserted (size m1 - 1) (size m2) /\ (1 <= size m1)%Z \/
  balance_prop (size m1) (size m2 + 1) ->
  toList (balanceL x y m1 m2) = toList m1 ++ ((x, y) :: nil) ++ toList m2.
Proof.
  intros.
  unfold balanceL.
  unfold op_zg__, op_zl__, Ord_Integer___, op_zg____, op_zl____.

  repeat lazymatch goal with [ H : Bounded ?s _ _ |- context [match ?s with _ => _ end] ] => inversion H; subst; clear H end;
  repeat lazymatch goal with [ |- context [if (?x <? ?y)%Z then _ else _] ] => destruct (Z.ltb_spec x y) end;
  rewrite ?size_Bin in *; simpl (size Tip) in *; simpl sem;
  simpl isLB in *;
  simpl isUB in *.
  all: try solve [exfalso; lia_sizes]. (* Some are simply impossible *)
  all: repeat find_Tip.
  all: rewrite ?toList_Bin, <- ?app_assoc; try reflexivity.
  all: simpl; rewrite <- app_assoc; reflexivity.
Qed.

(*If we insertMax into a tree, that value is at the end of the list*)
Lemma toList_insertMax:
   forall x y (m: Map e a) lb,
   Bounded m lb (Some x) ->
   toList (insertMax x y m) = toList m ++ (x,y) :: nil.
Proof.
  intros. remember (Some x) as ub'. generalize dependent x.
  induction H; intros.
  - simpl. reflexivity.
  - simpl. subst. specialize(IHBounded2 x0 eq_refl). revert IHBounded2.
    assert (isUB None x0 = true) by reflexivity. applyDesc e (@insertMax_Desc e a).
    intro. erewrite toList_balanceR. rewrite IHBounded2. rewrite toList_bin.
    rewrite <- app_assoc. simpl. reflexivity. apply H. apply HB.
    solve_size.
Qed.

(*If we insertMin into a tree, that value is at the beginning of the list*)
Lemma toList_insertMin:
   forall x y (m: Map e a) ub,
   Bounded m (Some x) ub ->
   toList (insertMin x y m) = (x,y) :: nil ++ toList m.
Proof.
  intros. remember (Some x) as ub'. generalize dependent x.
  induction H; intros.
  - simpl. reflexivity.
  - simpl. subst. specialize(IHBounded1 x0 eq_refl). revert IHBounded1.
    assert (isLB None x0 = true) by reflexivity. applyDesc e (@insertMin_Desc e a).
    intro. erewrite toList_balanceL. rewrite IHBounded1. rewrite toList_bin.
    simpl. reflexivity. apply HB. apply H0. solve_size.
Qed.

(*States that if we link 2 maps together, then the list is in the same order. These
past few lemmas together mean that when balancing the tree, the list does not change*)
Program Fixpoint toList_link (x : e) (y : a) (m1: Map e a)  (m2: Map e a)
  {measure (map_size m1 + map_size m2)} :
    forall lb ub,
    Bounded m1 lb (Some x) ->
    Bounded m2 (Some x) ub  ->
    isLB lb x = true ->
    isUB ub x = true->
    toList (link x y m1 m2) = toList m1 ++ (x,y) :: nil ++ toList m2 := _.
Next Obligation.
  intros.
  rewrite link_eq. 
  inversion H; subst; clear H;
  inversion H0; subst; clear H0.
  * reflexivity.
  * erewrite toList_insertMin by solve_Bounded e.
    rewrite toList_Bin.
    reflexivity.
  * erewrite toList_insertMax by solve_Bounded e.
    rewrite toList_Bin.
    reflexivity.
  * destruct (Sumbool.sumbool_of_bool _);
    only 2: destruct (Sumbool.sumbool_of_bool _);
    rewrite ?Z.ltb_lt, ?Z.ltb_ge in *.
    - erewrite toList_balanceL; only 3: solve_Precondition e.
      erewrite toList_link by solve_Precondition e.
      rewrite ?toList_Bin, <- ?app_assoc. reflexivity.
      applyDesc e (@link_Desc e a); eassumption.
      applyDesc e (@link_Desc e a); solve_size.
    - erewrite toList_balanceR; only 2: solve_Precondition e.
      erewrite toList_link by solve_Precondition e.
      rewrite ?toList_Bin, <- ?app_assoc. reflexivity.
      applyDesc e (@link_Desc e a); eassumption.
      applyDesc e (@link_Desc e a); solve_size.
    - rewrite ?toList_bin, ?toList_Bin, <- ?app_assoc.
      unfold bin. rewrite toList_bin. rewrite toList_bin.
      rewrite toList_bin. simpl. rewrite <- app_assoc. simpl.
      reflexivity. 
Qed.


(** *** Sortedness of [toList] *)

Require Import Coq.Sorting.Sorted.
Close Scope Z.

(*Maps are sorted only by keys*)
Local Definition lt : e * a -> e * a -> Prop
  := fun x1 x2 => let (e1, a1) := x1 in let (e2, a2) := x2 in (e1 < e2) = true.

(* States that if two lists are sorted and all values in the first are smaller
than all values in the second, then appending the two lists gives a sorted list. *)
Lemma sorted_append:
  forall (l1 : list (e * a)) (l2 : list (e * a)) (x : e),
  StronglySorted lt l1 ->
  StronglySorted lt l2 ->
  (forall (y : e) (z : a), List.In (y, z) l1 -> (y < x) = true) ->
  (forall y z, List.In (y, z) l2 -> (x <= y) = true) ->
  StronglySorted lt (l1 ++ l2).
Proof.
  intros ??? Hsorted1 Hsorted2 Hlt Hge.
  induction Hsorted1.
  * apply Hsorted2.
  * simpl. apply SSorted_cons.
    + apply IHHsorted1.
      intros y z Hy.
      eapply Hlt.
      right. apply Hy.
    + rewrite Forall_forall.
      intros z Hz.
      rewrite in_app_iff in Hz.
      destruct Hz.
      - rewrite Forall_forall in H.
        apply H; auto.
      - destruct a0.  assert (e0 < x = true). eapply Hlt. left. reflexivity. 
        unfold lt. destruct z. apply Hge in H0. order e.
Qed.

(*Similar to List.elem, but does not require that a be in the Eq typeclass (because it doesn't actually
matter; the a's are not ever compared)*)
Fixpoint list_elem_tuple (x : e * a) (l : list (e * a)) :=
  match l with
  | nil => false
  | h :: t => let (a, b) := h in let (x1, x2) := x in (a == x1) || list_elem_tuple x t
  end.

(*This states that if x is a lower bound for a list and the tuple i is in the list, then x is less than i.
Note: this required a change from toList (using lt rather than < in the conclusion), though this 
is needed because there is no definition of ordering on all tuples*)
Lemma All_lt_elem:
  forall x i xs,
  Forall (lt x) xs ->
  list_elem_tuple i xs = true ->
  lt x i.
Proof.
  intros.
  induction H.
  * simpl in H0. inversion H0.
  * simpl in *. destruct x0. destruct i.
    rewrite orb_true_iff in H0.
    destruct H0.
    - unfold lt in *. destruct x. order e.
    - intuition.
Qed.

(*toList is sorted by key*)
Lemma to_List_sorted:
  forall m lb ub,
  Bounded m lb ub ->
  StronglySorted lt (toList m).
Proof.
  intros. induction H.
  - apply SSorted_nil.
  - rewrite toList_bin. eapply sorted_append. assumption.
    apply SSorted_cons. assumption. apply toList_lb in H0.
    apply H0. apply toList_ub in H.  intros. 
    rewrite Forall_forall in H.
    remember (y,z) as t. 
    apply H in H5. destruct t. inversion Heqt. rewrite <- H7. unfold isUB in H5. apply H5.
    intros. simpl in H5. destruct H5.
    + inversion H5. order e.
    + apply toList_lb in H0. 
      rewrite Forall_forall in H0. apply H0 in H5. order_Bounds e.
Qed. 

(** ** Verification of [toAscList] *)

Lemma toAscList_spec: @toAscList = @toList. Proof. reflexivity. Qed.

(** ** Verification of [elems] *)

Lemma fold_right_with_assoc:
  forall l1 l2,
    fold_right (fun (x : e * a) acc => let (a,b) := x in b :: acc) l1 l2  = 
  fold_right (fun (x : e * a) acc => let (a,b) := x in b :: acc) nil l2 ++ l1.
Proof.
  intros. generalize dependent l1. induction l2.
  - intros. simpl. reflexivity.
  - intros. simpl. destruct a0. rewrite IHl2. simpl. reflexivity.
Qed. 

Lemma foldr_const_append:
  forall xs (map : Map e a),
  foldr cons xs map = elems map ++ xs.
Proof.
  intros. generalize dependent xs. induction map; intros.
  - simpl. unfold elems. simpl. rewrite IHmap1. rewrite IHmap2. rewrite IHmap1.
    rewrite IHmap2. rewrite <- app_assoc. simpl. rewrite <- app_assoc. reflexivity.
  - simpl. reflexivity.
Qed.

Lemma elems_Bin:
  forall sz key value (m1 m2 : Map e a),
  elems (Bin sz key value m1 m2) = elems m1 ++ (value :: nil) ++ elems m2.
Proof.
  intros. 
  unfold elems at 1. simpl. rewrite foldr_const_append. rewrite foldr_const_append. 
  rewrite app_nil_r. reflexivity.
Qed.

(*For a map, elems means we take the 2nd element of each tuple in toList*)
Lemma elems_spec: forall map,
  elems map = fold_right (fun (x : e * a) acc => let (a,b) := x in  b :: acc) nil (toList map).
Proof.
  intros. induction map.
  - rewrite elems_Bin.  rewrite IHmap1. simpl. rewrite IHmap2. rewrite toList_bin. 
    rewrite fold_right_app. simpl. rewrite <- fold_right_with_assoc. reflexivity.
  - simpl. unfold elems. simpl. reflexivity.
Qed.

(** ** Verification of [keys] *)

Lemma fold_right_with_assoc':
  forall l1 l2,
    fold_right (fun (x : e * a) acc => let (a,b) := x in a :: acc) l1 l2  = 
  fold_right (fun (x : e * a) acc => let (a,b) := x in a :: acc) nil l2 ++ l1.
Proof.
  intros. generalize dependent l1. induction l2.
  - intros. simpl. reflexivity.
  - intros. simpl. destruct a0. rewrite IHl2. simpl. reflexivity.
Qed. 

Lemma foldrWithKey_const_append':
  forall xs (map : Map e a),
  foldrWithKey (fun x y t => x :: t) xs map = keys map ++ xs.
Proof.
  intros. generalize dependent xs. induction map; intros.
  - unfold keys in *.  simpl. rewrite IHmap1. rewrite IHmap2. 
    rewrite (IHmap1 (k :: foldrWithKey (fun (arg_0__ : e) (_ : a) (arg_2__ : list e) => arg_0__ :: arg_2__) nil map2) ).
    rewrite <- app_assoc. reflexivity.
  - simpl. reflexivity.
Qed.

Lemma keys_Bin:
  forall sz key value (m1 m2 : Map e a),
  keys (Bin sz key value m1 m2) = keys m1 ++ (key :: nil) ++ keys m2.
Proof.
  intros. 
  unfold keys at 1. simpl. rewrite foldrWithKey_const_append'. rewrite foldrWithKey_const_append'. 
  rewrite app_nil_r. reflexivity.
Qed.

Lemma keys_spec: forall map,
  keys map = fold_right (fun (x : e * a) acc => let (a,b) := x in  a :: acc) nil (toList map).
Proof.
  intros. induction map.
  - rewrite keys_Bin.  rewrite IHmap1. simpl. rewrite IHmap2. rewrite toList_bin. 
    rewrite fold_right_app. simpl. rewrite <- fold_right_with_assoc'. reflexivity.
  - simpl. unfold keys. simpl. reflexivity.
Qed.

(** ** Verification of [assocs] *)
Lemma assocs_spec: forall (map: Map e a),
  assocs map = toList map.
Proof.
  intros. unfold assocs. unfold toList. reflexivity.
Qed.

(** ** Verification of [toDescList] *)

(*The reverse of a list is empty iff the original list was empty*)
Lemma rev_nil : forall {A : Type} (x : list A),
  rev x = nil <-> x = nil.
Proof.
  intros. split; intros.
  - destruct x. 
    + reflexivity.
    + simpl in H. assert (nil <> rev x ++ a0 :: nil ) by apply app_cons_not_nil.  
      rewrite H in H0. contradiction.
  - rewrite H. reflexivity.
Qed.

(*Reversing a list is injective*)
Lemma rev_inj {A} (x y : list A) :
  rev x = rev y -> x = y.
Proof.
  intros. generalize dependent y. induction x using rev_ind; intros.
  - simpl in H.  symmetry. apply rev_nil. symmetry. assumption.
  - rewrite rev_app_distr in H. simpl in H. destruct y using rev_ind.
    + simpl in H. discriminate H.
    + rewrite rev_app_distr in H. simpl in H. inversion H. subst.
    apply IHx in H2. subst. reflexivity.
Qed.

(*from SetProofs, not actually useful*)
Lemma foldl_acc_app: forall l (m : Map e a),
  foldl (flip cons) l m = foldl (flip cons) nil m ++ l.
Proof.
  intros. generalize dependent l. induction m; intros.
  - simpl. rewrite IHm2. rewrite  IHm1. symmetry. rewrite IHm2. rewrite <- app_assoc.
    simpl. unfold flip. reflexivity.
  - simpl. reflexivity.
Qed.

(*The version we want for toDescList_spec*)
Lemma foldlWithKey_acc_app: forall l (m : Map e a),
  foldlWithKey (fun acc x y => (x, y) :: acc) l m = foldlWithKey (fun acc x y => (x,y) :: acc) nil m ++ l.
Proof.
  intros. generalize dependent l. induction m; intros.
  - simpl. rewrite IHm2. rewrite IHm1. symmetry. rewrite IHm2. rewrite <- app_assoc.
    reflexivity.
  - simpl. reflexivity.
Qed. 

(*reversing a list takes the last element and puts it at the front*)
Lemma rev_cons: forall {A: Type} (l : list A) (x : A),
  rev (l ++ x :: nil) = x :: rev l.
Proof.
  intros. induction l.
  - simpl. reflexivity.
  - simpl. rewrite IHl. simpl. reflexivity.
Qed. 

(*toDescList returns the reverse of toAscList on a map*)
Lemma toDescList_spec (map : Map e a) :
  toDescList map = rev (toAscList map).
Proof.
  unfold toDescList. unfold toAscList.
  induction map.
  - simpl. rewrite IHmap1. rewrite foldlWithKey_acc_app. rewrite IHmap2.
    assert ((k, a0) :: rev (foldrWithKey (fun (k0 : e) (x : a) (xs : list (e * a)) => (k0, x) :: xs) nil map1)=
      rev (foldrWithKey (fun (k0 : e) (x : a) (xs : list (e * a)) => (k0, x) :: xs) nil map1 ++ (k, a0) :: nil))
      by (symmetry; apply rev_cons).
    rewrite H. rewrite <- rev_app_distr.
    rewrite foldrWithKey_const_append. rewrite app_nil_r. rewrite foldrWithKey_const_append. rewrite app_nil_r.
    rewrite foldrWithKey_const_append. rewrite <- app_assoc. simpl. reflexivity.
  - simpl. reflexivity.
Qed. 

(** ** Verification of [foldl] and [foldlWithKey *)

(** This relates [foldl] and [elems]. *)
Lemma foldl_spec:
  forall k (n : a) (m: Map e a),
  foldl k n m = fold_left k (elems m) n.
Proof.
  intros. generalize dependent n. induction m; intros.
  - simpl. rewrite (elems_Bin s k0 a0 m1 m2) . rewrite IHm1. rewrite IHm2.
    rewrite fold_left_app. simpl. reflexivity.
  - simpl. reflexivity.
Qed. 

(*TODO: REPLACE WITH UPDATED SPEC FROM MAPFUNCTIONPROOFS*)
(** This relates [foldlWithKey] and [toList]. *)
Lemma foldlWithKey_spec:
  forall f (n : e * a) (m: Map e a),
  foldlWithKey f n m = fold_left (fun xs (x : e * a) => let (a,b) := x in f xs a b)  (toList m) n.
Proof.
  intros. generalize dependent n. induction m; intros.
  - simpl. rewrite toList_Bin. rewrite IHm1. rewrite IHm2.
    rewrite fold_left_app. simpl. reflexivity.
  - reflexivity.
Qed.

(** ** Verification of [foldl'] *)

Lemma foldl'_spec:
  forall k (n : a) (m : Map e a),
  foldl' k n m = foldl k n m.
Proof. reflexivity. Qed.

(** ** Verification of [foldlWithKey'] *)
Lemma foldlWithKey'_spec:
  forall k (n : a) (m : Map e a),
  foldlWithKey' k n m = foldlWithKey k n m.
Proof. reflexivity. Qed.

(** ** Verification of [size] *)

Lemma size_spec:
  forall (s: Map e a) lb ub,
  Bounded s lb ub ->
  size s = Z.of_nat (length (toList s)).
Proof.
  intros. induction H.
  - simpl. reflexivity.
  - simpl. rewrite toList_Bin. simpl. rewrite app_length. simpl. 
    rewrite Nat2Z.inj_add. rewrite <- IHBounded1.
    rewrite Nat2Z.inj_succ. rewrite <- IHBounded2.
    omega.
Qed.

(** ** Verification of [Eq] *)

(*Note: This is substantially different from SetProofs because the values' equality may differ between
Coq and Haskell. Instead of a single spec, we will prove 3 different specifications of [Eq]
1. [weak_equals_spec]: This states that m1 == m2 iff for every key, sem m1 key == sem m2 key 
 (all according to Haskell notions of equality)
2. [strong_eq1]: If sem m1 key = sem m2 key for all keys, then m1 == m2 (the other direction is not true
in general)
3. [strong_eq2]: If Haskell equality is equivalent to Coq equality for the values (for example, if the
values are integers), then m1 == m2 iff for every key, sem m1 key = sem m2 key

The benefit of this is that the stronger notions of equality are much easier to work with in Coq proofs,
and means that if Coq and Haskell equality agree, we have a very strong specification of the equality of the
corresponding maps.
*)

(*[eqlist] is symmetric*)
Lemma eqlist_sym:
  forall {a} `{EqLaws a} (xs ys : list a),
  eqlist xs ys = eqlist ys xs.
Proof.
  intros. generalize dependent ys. induction xs; intros.
  - destruct ys. reflexivity. simpl. reflexivity. 
  - destruct ys. simpl. reflexivity. simpl.
    destruct (a1 == a2) eqn : ?.
    + simpl. rewrite Eq_Symmetric. simpl. apply IHxs. apply Heqb.
    + simpl. assert (a2 == a1 = false). apply Lemmas.Eq_neq_sym. assumption.
      rewrite H1. simpl. reflexivity.
Qed. 

(*Equal lists have the same length*)
Lemma eqlist_length:
  forall {a} `{Eq_ a} (xs ys : list a),
  eqlist xs ys = true ->
  length xs = length ys.
Proof.
  intros. generalize dependent ys. induction xs; intros.
  - destruct ys. reflexivity. simpl in H0. discriminate H0.
  - destruct ys. simpl in H0. discriminate H0. simpl in H0.
    simpl. rewrite (IHxs ys). reflexivity. apply andb_true_iff in H0.
    destruct H0. assumption.
Qed.

(*Equal lists have the same elements in them*)
Lemma eqlist_elem:
  forall `{Eq_ a}  `{EqLaws a} (xs ys : list (e * a)) x y,
  eqlist xs ys = true ->
  List.elem (x, y) xs = true <-> List.elem (x, y) ys = true.
Proof.
  intros. generalize dependent ys. induction xs; intros.
  - simpl. destruct ys. simpl. reflexivity. simpl in H2. discriminate H2.
  - destruct ys. simpl in H2. discriminate H2. simpl. simpl in H2. split; intros.
    + destruct p. rewrite andb_true_iff in H2. destruct H2. rewrite orb_true_iff.
      rewrite orb_true_iff in H3. destruct H3. left. destruct a0.  eapply Eq_Tuple_Trans. 
      apply H3. apply H2. right. apply IHxs. assumption. assumption.
    + rewrite orb_true_iff. rewrite orb_true_iff in H3. rewrite andb_true_iff in H2.
      destruct H2. destruct H3. left. destruct a0. destruct p. eapply Eq_Tuple_Trans.
      apply H3. eapply Eq_Tuple_Sym. assumption. right. rewrite (IHxs ys). assumption. assumption.
Qed.

(*States that a map is empty iff sem key map returns None for every key*)
Lemma sem_false_nil:
  forall (m: Map e a),
  (forall i, sem m i = None) <-> m = Tip.
Proof.
  intros. remember m as m1. split; intros.
  - destruct m.
    + assert (sem m1 e0 <> None). { subst. 
      simpl. destruct (sem m2 e0). 
      * simpl. intro. discriminate H0.
      * simpl. rewrite Eq_Reflexive. simpl. intro. discriminate H0. }
        specialize (H e0). rewrite H in H0. contradiction.
    + assumption.
  - rewrite H. simpl. reflexivity.
Qed. 

(*We don't want to use Forall_forall because all we know is that List.elem is true,
which is much weaker than List.In*)
Lemma Forall_lt: forall `{Eq_ a} `{EqLaws a} (l : list (e * a)) t,
  Forall (lt t) l <-> (forall x y, List.elem (x, y) l = true -> lt t (x,y)).
Proof.
  intros. split; induction l; intros.
  - simpl in H3. discriminate H3.
  - inversion H2. subst. simpl in H3. rewrite orb_true_iff in H3. destruct H3.
    destruct t. destruct a0. unfold lt in H6. unfold lt. rewrite eq_tuple_prop in H3.
    order e. apply IHl. apply H7. apply H3.
  - apply Forall_nil.
  - apply Forall_cons. destruct a0. specialize (H2 e0 a0). apply H2. simpl.
    apply orb_true_iff. left. apply Eq_Tuple_Refl. apply IHl. intros. apply H2.
    simpl. apply orb_true_iff. right. apply H3.
Qed. 

(*If two tuples are equal according to Haskell, List.elem returns the same result for either on a list*)
Lemma list_elem_eq : forall `{Eq_ a} `{EqLaws a} (x1 x2 : e) (y1 y2 : a) l,
  (x1, y1) == (x2, y2) = true ->
  List.elem (x1, y1) l = true <-> List.elem (x2, y2) l = true.
Proof.
  intros. induction l.
  - simpl. split; intros; discriminate H3.
  - split; intros; simpl in *; rewrite orb_true_iff in *.
    + destruct H3.
      * left. destruct a0. eapply Eq_Tuple_Trans. eapply Eq_Tuple_Sym. apply H2. apply H3.
      * right. apply IHl. apply H3.
    + destruct H3.
      * left. destruct a0. eapply Eq_Tuple_Trans. apply H2. apply H3.
      * right. apply IHl. apply H3.
Qed.

(*Strongly sorted lists with the same elements are the same.*)
(*TODO: Clean up the proof*)
Lemma strongly_sorted_unique:
  forall `{Eq_ a} `{EqLaws a} (xs ys : list (e * a)),
  StronglySorted lt xs ->
  StronglySorted lt ys ->
  (forall x y, List.elem (x, y) xs = true <-> List.elem (x,y) ys = true) ->
  eqlist xs ys = true.
Proof.
  intros. generalize dependent ys. induction xs; intros.
  - simpl in H4. destruct ys. reflexivity. 
    assert (forall x y, List.elem (x,y) (p :: ys) = false). { intros. specialize (H4 x y).
   destruct H4. apply contrapositive in H5. destruct (List.elem (x, y) (p :: ys)). contradiction.
    reflexivity. intro. discriminate H6. }
    assert (List.elem p (p :: ys) = true). { simpl. rewrite orb_true_iff. left. destruct p.
    apply Eq_Tuple_Refl. } destruct p. specialize (H5 e0 a0). rewrite H6 in H5. discriminate H5.
  - destruct ys. 
    + assert (forall x y, List.elem (x,y) (a0 :: xs) = false). { intros x y.
      specialize (H4 x y). destruct H4. apply contrapositive in H4. destruct (List.elem (x, y) (a0 :: xs)).
      contradiction. reflexivity. intro. simpl in H6. discriminate H6. }
      destruct a0. assert (List.elem (e0, a0) ((e0, a0) :: xs) = true). { simpl. rewrite orb_true_iff.
      left. apply Eq_Tuple_Refl. }
      specialize (H5 e0 a0). rewrite H6 in H5. discriminate H5.
    + simpl. rewrite andb_true_iff. inversion H2; subst. inversion H3; subst. split. 
      assert (A:=H4). destruct a0. destruct p. specialize (H4 e0 a0). specialize (A e1 a1).
      destruct H4. destruct A. 
      assert (List.elem (e0, a0) ((e1, a1) :: ys) = true). { apply H4. simpl. rewrite orb_true_iff.
      left. apply Eq_Tuple_Refl. }
      assert (List.elem (e1, a1) ((e0, a0) :: xs) = true). { apply H11. simpl. rewrite orb_true_iff.
      left. apply Eq_Tuple_Refl. }
      rewrite Forall_lt in H8. rewrite Forall_lt in H10. simpl in H12. simpl in H13. 
      rewrite orb_true_iff in *. destruct H12. destruct H13. apply H12. apply H12. 
      destruct H13. apply Eq_Tuple_Sym. apply H13. apply H8 in H13. apply H10 in H12. 
      unfold lt in H12. unfold lt in H13. order e. 
      apply IHxs. assumption. assumption. intros. split; intros.
      * assert (A1:=H4). specialize (H4 x y). destruct H4. rewrite Forall_lt in H8. rewrite Forall_lt in H10.
        assert (A:=H5).  assert (List.elem (x,y) (a0 :: xs) = true). {
        simpl. rewrite orb_true_iff. right. assumption. }
        apply H4 in H11. simpl in H11.  rewrite orb_true_iff in H11. destruct H11.
        { apply H8 in H5. destruct p. assert (List.elem (e0, a1) (a0 :: xs) = true). {
          apply A1. simpl. rewrite orb_true_iff. left. apply Eq_Tuple_Refl. }
          simpl in H12. rewrite orb_true_iff in H12. destruct H12.
          { destruct a0. unfold lt in H5. rewrite eq_tuple_prop in H11. rewrite eq_tuple_prop in H12.
            order e. }
          { destruct a0. assert (List.elem (e1, a0) ((e0, a1) :: ys) = true). { apply A1.
            simpl. rewrite orb_true_iff. left. apply Eq_Tuple_Refl. }
           simpl in H13. rewrite orb_true_iff in H13. destruct H13.
            { rewrite eq_tuple_prop in H11. rewrite eq_tuple_prop in H13.
              apply H8 in A. apply H8 in H12. unfold lt in *. order e. }
            { assert (A2:=H13). assert (A3:=H12). apply H10 in H13. apply H8 in H12.
              unfold lt in *. order e. }
            }
          }
          { apply H11. }
          (*Basically the same proof - try to clean up*)
        * assert (A1:=H4). specialize (H4 x y). destruct H4. rewrite Forall_lt in H8. rewrite Forall_lt in H10.
        assert (A:=H5).  assert (List.elem (x,y) (p :: ys) = true). {
        simpl. rewrite orb_true_iff. right. assumption. }
        apply H6 in H11. simpl in H11.  rewrite orb_true_iff in H11. destruct H11.
        { apply H10 in H5. destruct p. assert (List.elem (e0, a1) (a0 :: xs) = true). {
          apply A1. simpl. rewrite orb_true_iff. left. apply Eq_Tuple_Refl. }
          simpl in H12. rewrite orb_true_iff in H12. destruct H12.
          { destruct a0. unfold lt in H5. rewrite eq_tuple_prop in H11. rewrite eq_tuple_prop in H12.
            order e. }
          { destruct a0. assert (List.elem (e1, a0) ((e0, a1) :: ys) = true). { apply A1.
            simpl. rewrite orb_true_iff. left. apply Eq_Tuple_Refl. }
           simpl in H13. rewrite orb_true_iff in H13. destruct H13.
            { rewrite eq_tuple_prop in H11. rewrite eq_tuple_prop in H13.
              apply H10 in A. apply H8 in H12. unfold lt in *. order e. }
            { assert (A2:=H13). assert (A3:=H12). apply H10 in H13. apply H8 in H12.
              unfold lt in *. order e. }
            }
          }
          { apply H11. }
Qed.

(*A few final lemmas before the [Eq] specs. The first states that if a key is not in [toList],
  then sem returns false, and vice versa. *)

Lemma elem_not_in_list : forall `{Eq_ a} `{EqLaws a} key map lb ub,
  Bounded map lb ub ->
  (forall value, List.elem (key, value) (toList map) = false) <-> sem map key = None.
Proof.
  intros; split; intros.
  - destruct (sem map key) eqn : ?.
    + assert (sem map key == Some a0 = true). { rewrite Heqo. apply Eq_Reflexive. } eapply toList_sem' in H4.
      specialize (H3 a0). rewrite H4 in H3. discriminate H3. apply H2.
    + reflexivity.
  - destruct (List.elem (key, value) (toList map)) eqn : ?.
    + rewrite <- toList_sem' in Heqb. rewrite H3 in Heqb. discriminate Heqb. apply H2.
    + reflexivity.
Qed.
      
(*If two maps have equal lists, their size is equal*)
Lemma eq_size : forall `{Eq_ a} `{EqLaws a} m1 m2 lb ub,
  Bounded m1 lb ub ->
  Bounded m2 lb ub ->
  toList m1 == toList m2 = true ->
  Internal.size m1 = Internal.size m2.
Proof.
  intros. rewrite size_size. erewrite size_spec. erewrite size_spec. 
  unfold op_zeze__ in H4. unfold Eq_list in H4. unfold op_zeze____ in H4. apply eqlist_length in H4.
  rewrite H4. reflexivity. apply H3. apply H2.
Qed.

(*Map equality is defined by checking both [length] and [toList], but [length] does not matter.
This makes the next proofs a bit easier.*)
Lemma eq_toList : forall `{Eq_ a} `{EqLaws a} m1 m2 lb ub,
  Bounded m1 lb ub ->
  Bounded m2 lb ub ->
  m1 == m2 = true <-> (toList m1 == toList m2) = true.
Proof.
  intros. split; intros.
  - unfold op_zeze__ in H4. unfold Eq___Map in H4. unfold op_zeze____ in H4. 
    unfold Internal.Eq___Map_op_zeze__ in H4. rewrite andb_true_iff in H4. destruct H4.
    unfold toList. assumption.
  - unfold_zeze. unfold  Eq___Map. unfold Internal.Eq___Map_op_zeze__. rewrite andb_true_iff.
    split. assert (Internal.size m1 = Internal.size m2). eapply eq_size. apply H2. apply H3.
    assumption. rewrite H5. apply Eq_Reflexive. unfold toList in *. assumption.
Qed.

Lemma weak_equals_spec:
  forall `{Eq_ a} `{EqLaws a} m1 m2 lb ub,
  Bounded m1 lb ub ->
  Bounded m2 lb ub ->
  m1 == m2 = true <-> (forall i, sem m1 i == sem m2 i = true).
Proof.
  intros. split; intros. unfold op_zeze__ in H4. unfold Eq___Map in H4.
      unfold op_zeze____ in H4. unfold Internal.Eq___Map_op_zeze__ in H4.  rewrite andb_true_iff in H4.
      destruct H4. unfold op_zeze__ in H5. unfold Eq_list in H5. unfold op_zeze____ in H5.
  - destruct (sem m1 i) eqn : ?. 
    + eapply eqlist_elem in H5. assert (sem m1 i == Some a0 = true). { rewrite Heqo. apply Eq_Reflexive. }
      rewrite toList_sem' in H6. unfold toList in H6. apply H5 in H6. rewrite <- toList_sem' in H6.
      apply Eq_Symmetric. apply H6. apply H3. apply H2.
    + rewrite <- elem_not_in_list in Heqo. pose proof (toList_sem') as H7. specialize (H7 m2 lb ub H3 i).
      assert (forall value, List.elem (i, value) (toList m2) = false). { intros.
      specialize (H7 value). destruct H7. apply contrapositive in H7.
      destruct (List.elem (i, value) (toList m2)). contradiction. reflexivity. 
      assert (forall value, List.elem (i, value) (toAscList m2) = false). { intros.
      apply (eqlist_elem _ _ i value0) in H5. destruct H5. apply contrapositive in H8.
      destruct (List.elem (i, value0) (toAscList m2)). contradiction. reflexivity.
      destruct (List.elem (i, value0) (toAscList m1)) eqn : ?. specialize (Heqo value0).
      unfold toList in Heqo. rewrite Heqo in Heqb. discriminate Heqb. intro. discriminate H9. }
      eapply elem_not_in_list in H8. rewrite H8. intro. discriminate H9. apply H3. }
      eapply elem_not_in_list in H6. rewrite H6. order e. apply H3. apply H2.
  - eapply eq_toList. apply H2. apply H3. apply strongly_sorted_unique. eapply to_List_sorted.
    apply H2. eapply to_List_sorted. apply H3. intros. split; intros.
    + rewrite <- toList_sem' in H5. specialize (H4 x). assert (sem m2 x == Some y = true).
      { eapply Eq_Transitive. apply Eq_Symmetric. apply H4. apply H5. }
      rewrite toList_sem' in H6. assumption. apply H3. apply H2.
    + rewrite <-toList_sem' in H5. specialize (H4 x). assert (sem m1 x == Some y = true).
      { eapply Eq_Transitive. apply H4. apply H5. } rewrite toList_sem' in H6. assumption.
      apply H2. apply H3.
Qed.

Lemma strong_eq1 : forall `{Eq_ a} `{EqLaws a} m1 m2 lb ub,
  Bounded m1 lb ub ->
  Bounded m2 lb ub ->
  (forall i, sem m1 i = sem m2 i) -> m1 == m2 = true.
Proof. intros.
  assert (forall i, (sem m1 i == sem m2 i = true)). { intros. specialize (H4 i).
  rewrite H4. apply Eq_Reflexive. } eapply weak_equals_spec in H5. assumption.
  apply H2. apply H3.
Qed.

Lemma strong_eq2 : forall `{Eq_ a} `{EqLaws a} m1 m2 lb ub,
  Bounded m1 lb ub ->
  Bounded m2 lb ub ->
  (forall (y1 : a) (y2 : a), y1 == y2 = true <-> y1 = y2) ->
  (forall i, sem m1 i =  sem m2 i) <-> m1 == m2 = true.
Proof.
  intros. split; intros.
  - eapply strong_eq1. apply H2. apply H3. apply H5.
  - rewrite weak_equals_spec in H5. specialize (H5 i).
    destruct (sem m1 i). destruct (sem m2 i). 
    rewrite simpl_option_some_eq in H5. rewrite H4 in H5. subst. reflexivity.
    discriminate H5. destruct (sem m2 i). discriminate H5. reflexivity. apply H2. apply H3.
Qed.

End WF.