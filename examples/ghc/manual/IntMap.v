Set Warnings "-notation-overridden".
Set Warnings "-masking-absolute-name".

Require Import GHC.Base.
Require Data.IntSet.Internal. 
Require Import Data.Map.Internal.
Require Import GHC.Num.
Require Import Coq.Classes.Morphisms.
Import GHC.Num.Notations.

From Coq Require Import ssreflect ssrbool.

Require Proofs.GHC.Base.

Require Import MapProofs.

Definition IntMap := WFMap Word.

Global Instance Eq_IntMap {A} `{ Base.Eq_ A} : Base.Eq_ (IntMap A) :=
  Eq_Map_WF.

Ltac prove_WF :=
  match goal with
  | [ |- WF (proj1_sig ?x) ] =>
    match goal with
    | [ x : IntMap _ |- _] =>
      destruct x; assumption
    end
  end.


Section IntMap.

  Context {A B C: Type}.
  
  Program Definition empty : IntMap A := empty.
  Next Obligation. apply empty_WF. Defined.

  Program Definition singleton : Word -> A -> IntMap A := singleton.
  Next Obligation. apply singleton_WF. Defined.

  Program Definition null : IntMap A -> bool := null.

  Program Definition keys : IntMap A -> list Word := keys.

  Definition keysSet (m : IntMap A) : Data.IntSet.Internal.IntSet :=
    Data.IntSet.Internal.fromList (keys m).

  Program Definition elems : IntMap A -> list A := elems.

  Program Definition member : Word -> IntMap A -> bool := member.

  Program Definition size : IntMap A -> nat := map_size.

  Program Definition insert : Word -> A -> IntMap A -> IntMap A := insert.
  Next Obligation. apply insert_WF; prove_WF. Defined.

  Program Definition insertWith : (A -> A -> A) -> Word -> A -> IntMap A -> IntMap A :=
    insertWith.
  Next Obligation. apply insertWith_WF; prove_WF. Defined.

  Program Definition delete : Word -> IntMap A -> IntMap A := delete.
  Next Obligation. apply delete_WF; prove_WF. Defined.

  Program Definition alter : (option A -> option A) -> Word -> IntMap A -> IntMap A :=
    alter.
  Next Obligation. apply alter_WF. prove_WF. Defined.

  Program Definition adjust : (A -> A) -> Word -> IntMap A -> IntMap A := adjust.
  Next Obligation. apply adjust_WF. prove_WF. Defined.

  Program Definition map : (A -> B) -> IntMap A -> IntMap B := map.
  Next Obligation. apply map_WF. prove_WF. Defined.

  Program Definition mapWithKey : (Word -> A -> B) -> IntMap A -> IntMap B :=
    mapWithKey.
  Next Obligation.
    apply mapWithKey_WF.
    - intros i j H. f_equal.
      apply /Base.Eq_eq =>//.
    - prove_WF.
  Defined.

  Program Definition filter : (A -> bool) -> IntMap A -> IntMap A := filter.
  Next Obligation. apply filter_WF. destruct x0. assumption. Defined.

  Program Definition filterWithKey : (Word -> A -> bool) -> IntMap A -> IntMap A :=
    filterWithKey.
  Next Obligation.
    apply filterWithKey_WF.
    - intros i j H. f_equal. apply /Base.Eq_eq =>//.
    - destruct x0; assumption.
  Defined.

  Program Definition union : IntMap A -> IntMap A -> IntMap A := union.
  Next Obligation.
    eapply Desc'_WF.
    destruct x; destruct x0.
    eapply union_Desc; try eassumption.
  Defined.

  Program Definition unionWith : (A -> A -> A) -> IntMap A -> IntMap A -> IntMap A :=
    unionWith.
  Next Obligation.
    eapply Desc'_WF.
    destruct x0; destruct x1.
    eapply unionWith_Desc; try eassumption.
  Defined.

  Program Definition intersection : IntMap A -> IntMap B -> IntMap A :=
    intersection.
  Next Obligation.
    eapply Desc'_WF.
    destruct x; destruct x0.
    apply intersection_Desc; try eassumption.
  Defined.
  
  Program Definition intersectionWith : (A -> B -> C) ->
                                        IntMap A -> IntMap B -> IntMap C :=
    intersectionWith.
  Next Obligation.
    eapply Desc'_WF.
    destruct x0; destruct x1.
    apply intersectionWith_Desc; try eassumption.
  Defined.    

  Program Definition difference : IntMap A -> IntMap B -> IntMap A := difference.
  Next Obligation.
    destruct x; destruct x0. simpl.
    eapply Desc'_WF.
    eapply difference_Desc; try eassumption.
    intros. apply showDesc'; split.
    - assumption.
    - apply H2.
  Defined.

  Program Definition partition : (A -> bool) -> IntMap A -> IntMap A * IntMap A :=
    partition.
  Next Obligation.
    destruct x0; simpl.
    eapply Desc'_WF.
    eapply partition_spec; try eassumption.
    intros. destruct H. eassumption.
  Defined.
  Next Obligation.
    destruct x0; simpl.
    eapply Desc'_WF.
    eapply partition_spec; try eassumption.
    intros. destruct H. eassumption.
  Defined.

  Program Definition toList : IntMap A -> list (Word * A) := toList.

  Program Definition foldr : (A -> B -> B) -> B -> IntMap A -> B := foldr.

  Program Definition foldrWithKey : (Word -> A -> B -> B) -> B -> IntMap A -> B :=
    foldrWithKey.

  Program Definition findWithDefault : A -> Word -> IntMap A -> A := findWithDefault.

  Program Definition lookup : Word -> IntMap A -> option A := lookup.

End IntMap.

(** These should be in [containers]. *)

Lemma list_KeyIn : forall {A B} `{Base.EqLaws A} `{Base.EqLaws B}
                     (l1 l2 : list (A * B)) k v,
    l1 == l2 ->
    Key_In k v l1 ->
    (exists v', v == v' /\ Key_In k v' l2).
Proof.
  intros. generalize dependent l2. induction l1.
  - inversion H4. 
  - destruct a; simpl in H4. destruct H4.
    + destruct H3; subst. intros. destruct l2.
      * inversion H4.
      * destruct p. exists b. split.
        -- move: H4. cbn. move /andP =>[Hh ?].
           move /andP in Hh. tauto.
        -- constructor. move: H4. cbn. move /andP =>[Hh ?].
           move /andP in Hh. intuition.
           apply Base.Eq_trans with (y:=a); [symmetry |]; assumption.
    + intros. destruct l2.
      * inversion H4.
      * destruct p. cbn in H4. move /andP in H4.
        destruct H4. specialize (IHl1 H3 l2 H5).
        destruct IHl1 as [v' IHl]. exists v'. intuition.
        simpl. right. assumption.
Qed.
 
Lemma Eq_membership : forall {A} `{ Base.EqLaws A} (s1 s2: IntMap A),
    s1 == s2 -> (forall k, member k s1 == member k s2).
Proof.    
  intros A ?? s1 s2. destruct s1; destruct s2; simpl.
  unfold member, "==". simpl. cbn. unfold Internal.Eq___Map_op_zeze__.
  move /andP. intros Heq. destruct Heq as [Hs Hl].
  rewrite !toAscList_spec in Hl. intro k.
  destruct (Internal.member k x) eqn:Hkx.
  - rewrite Hkx.
    eapply member_spec in Hkx; [| eassumption].
    destruct Hkx as [v Hkx].
    apply eqb_true_iff. symmetry.
    eapply toList_sem in Hkx; [| eassumption].
    apply (list_KeyIn _ _ _ _ Hl) in Hkx. destruct Hkx as [v' Hkv'].
    eapply member_spec; [eassumption|]. exists v'.
    eapply toList_sem; [eassumption|]. tauto.
  - rewrite Hkx. apply not_true_iff_false in Hkx.
    erewrite member_spec in Hkx; [|eassumption].
    apply eqb_true_iff. symmetry. apply not_true_iff_false.
    intro. apply Hkx. eapply member_spec in H1; [|eassumption].
    destruct H1 as [v Hkv]. eapply toList_sem in Hkv; [|eassumption].
    eapply list_KeyIn in Hkv; [| symmetry; eassumption].
    destruct Hkv as [v' [??]]. exists v'. eapply toList_sem; eassumption.
Qed.    
