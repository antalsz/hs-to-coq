(* Disable notation conflict warnings *)
Set Warnings "-notation-overridden".

From mathcomp.ssreflect
Require Import ssreflect ssrnat prime ssrbool eqtype.

Require Import Core.
Require Import FV.
Require Import Proofs.Axioms.
Require Import ContainerProofs.
Require Import Proofs.VarSet.
Require Import Proofs.VarSetFSet.
Require Import Proofs.Var.

Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.

Require Import GHC.Base.
Require Import Proofs.Prelude.
Import GHC.Base.ManualNotations.

Require Import Coq.Classes.Morphisms.

Set Bullet Behavior "Strict Subproofs".


(** * Well-formedness of [FV]s. *)

(* A FV is well formed when it is denoted by some VarSet vs. *)


Lemma RespectsVar_const_true : RespectsVar (const true).
Proof. move => x1 x2 Eq. reflexivity. Qed.
Hint Resolve RespectsVar_const_true.
Lemma RespectsVar_andb f0 f: 
  RespectsVar f0 -> RespectsVar f ->
  RespectsVar (fun v : Var => f0 v && f v).
Proof.
  move => r1 r2 x1 x2 Eq.
  erewrite r1; eauto. 
  erewrite r2; eauto.
Qed.

Reserved Notation "A ⊢ B" (at level 70, no associativity).

Inductive Denotes : VarSet -> FV -> Prop :=
| DenotesVarSet : forall vs fv,
    (forall f in_scope vs' l,
        RespectsVar f ->
        extendVarSetList emptyVarSet l [=] vs' ->
        extendVarSetList emptyVarSet (fst (fv f in_scope (l, vs'))) [=]
        Tuple.snd (fv f in_scope (l, vs')) /\
        Tuple.snd (fv f in_scope (l, vs')) [=]
        unionVarSet (minusVarSet (filterVarSet f vs) in_scope) vs') ->
    vs ⊢ fv
where "A ⊢ B" := (Denotes A B).


Theorem Denotes_fvVarSet : forall m fv f in_scope l vs,
    m ⊢ fv ->
    RespectsVar f ->
    extendVarSetList emptyVarSet l [=] vs ->
    Tuple.snd (fv f in_scope (l, vs)) [=]
    unionVarSet (minusVarSet (filterVarSet f m) in_scope) vs.
Proof.
  move => m fv f in_scope l vs [vs' fv' H0] H1 H2.
  specialize (H0 f in_scope vs l H1 H2); subst.
  destruct fv'.
  move: H0 => [h0 h1].
  auto.
Qed.


Lemma Denotes_Equal vs1 vs2 f : vs1 [=] vs2 -> Denotes vs1 f -> Denotes vs2 f.
Proof.
  move => Eqx.
  move=> h. inversion h. subst.
  constructor.
  move => f0 in_scope vs' l RV EX.
  specialize (H f0 in_scope vs' l RV EX).
  move: H => [h0 h1].
  split. done.
  rewrite h1.
  f_equiv.
  f_equiv.
  apply filterVarSet_equal; eauto.
Qed.

Require Import Coq.Classes.Morphisms.
Instance Denotes_m : Proper (Equal ==> Logic.eq ==> iff) Denotes.
Proof.
  move=> vs1 vs2 EqV f0 f EqF. rewrite EqF.
  split; apply Denotes_Equal; try done.
  symmetry. auto.
Qed.


Definition WF_fv (fv : FV) : Prop := exists vs, vs ⊢ fv.
      
Ltac unfold_WF :=
  repeat match goal with
  | [ H : WF_fv ?fv |- _] =>
    let vs := fresh "vs" in
    let Hd := fresh "Hdenotes" in
    inversion H as [vs Hd]; inversion Hd; subst; clear H
  | [ |- WF_fv ?fv ] =>
    unfold WF_fv
  end.


(* We show that the various operations on FVs produce well-formed FVs. *)

Lemma emptyVarSet_emptyFV : Denotes emptyVarSet emptyFV.
Proof.
  constructor; intros; subst.
  unfold emptyFV.
  unfold Tuple.fst, Tuple.snd.
  hs_simpl.
  split; auto.
  reflexivity.
Qed.

Lemma empty_FV_WF :
  WF_fv emptyFV.
Proof.
  unfold WF_fv. exists emptyVarSet. eapply emptyVarSet_emptyFV. 
Qed.


Lemma unitVarSet_unitFV x : Denotes (unitVarSet x) (unitFV x).
Proof.
  constructor; intros; subst. 
  unfold fst, snd.
  unfold unitFV.
  destruct elemVarSet eqn:E1;
  destruct (f x) eqn:FX;
  hs_simpl; split; auto.
  - rewrite -> filterSingletonTrue; try done.
    rewrite elemVarSet_minusVarSetTrue; try done.
    hs_simpl.
    reflexivity.
  - rewrite filterSingletonFalse; try done.
    hs_simpl.
    reflexivity.
  - elim In: (elemVarSet x vs') => //.    
    hs_simpl.
    rewrite <- H0.
    rewrite extendVarSetList_extendVarSet_iff.
    reflexivity.
  - rewrite filterSingletonTrue; try done.
    rewrite elemVarSet_minusVarSetFalse; try done.
    elim E2: (elemVarSet x vs').
    hs_simpl.
    set_b_iff.
    rewrite add_equal; try done.
    hs_simpl.
    reflexivity.
  - elim E2: (elemVarSet x vs'); done.
  - rewrite filterSingletonFalse; try done.
    hs_simpl.
    elim E2: (elemVarSet x vs'); done.
Qed.


Lemma unit_FV_WF :
  forall x, WF_fv (unitFV x).
Proof.
  move=>x. unfold WF_fv.
  exists (unitVarSet x).
  eapply unitVarSet_unitFV.
Qed.

Lemma filterVarSet_filterFV f vs x :
  Proper ((fun x0 y : Var => x0 == y) ==> Logic.eq) f ->
  Denotes vs x -> Denotes (filterVarSet f vs) (filterFV f x).
Proof.
  move => p D.
  constructor. move=> f0 in_scope vs' l h0 h1.
  inversion D.
  unfold filterFV.
  specialize (H (fun v : Var => f0 v && f v) in_scope vs' l ltac:(eauto using RespectsVar_andb)).
  destruct H. auto. 
  rewrite H.
  rewrite H2.
  rewrite <- filterVarSet_comp. 
  split; reflexivity. 
Qed.


Lemma filter_FV_WF : forall f x,
    RespectsVar f ->
    WF_fv x -> WF_fv (filterFV f x).
Proof.
  intros. unfold_WF.
  exists (filterVarSet f vs). 
  eapply filterVarSet_filterFV; auto.
Qed.

Lemma delVarSet_delFV vs v fv :
  Denotes vs fv -> Denotes (delVarSet vs v) (delFV v fv).
Proof.
  move=> H. inversion H.
  constructor; intros. unfold delFV.
  specialize (H0 f (extendVarSet in_scope v) vs' l H3 H4).
  destruct H0. intuition. rewrite H5.
  destruct (fv f (extendVarSet in_scope v)) as [l0 h0] eqn:h.
  simpl in *.
  apply union_equal_1.
  move => x. 
  unfold VarSetFSet.In.
  rewrite !elemVarSet_minusVarSet.
  split.
  - move=> /andP [h1 h2].
    apply /andP.
    hs_simpl in h2.
    rewrite negb_or in h2.
    move: h2 => /andP.
    move => [h3 h4].
    intuition.
    rewrite elemVarSet_filterVarSet in h1 => //.
    rewrite elemVarSet_filterVarSet => // .
    apply /andP.
    move: h1 => /andP [h1 h2].
    rewrite elemVarSet_delVarSet.
    split; auto.
    apply /andP. split; auto.
  - move=> /andP [h1 h2].
    apply /andP.

    rewrite elemVarSet_filterVarSet in h1 => //.
    move: h1 => /andP. move => [h3 h4].
    elim hf: (f x); rewrite hf in h3; try done; clear h3.
    rewrite elemVarSet_delVarSet in h4.
    elim ev: (v GHC.Base.== x).
    + rewrite ev in h4. done. 
    + rewrite ev in h4. 
      move: h4 => /andP. move => [h5 h6].
      rewrite elemVarSet_filterVarSet => //.
      rewrite elemVarSet_extendVarSet.
      rewrite hf.
      rewrite ev.
      rewrite h6.
      done.
Qed.


Lemma del_FV_WF : forall fv v,
    WF_fv fv -> WF_fv (delFV v fv).
Proof.
  intros. unfold_WF.
  exists (delVarSet vs v). 
  eapply delVarSet_delFV. auto.
Qed.

Lemma unionVarSet_unionFV vs vs' fv fv' :
  Denotes vs fv -> Denotes vs' fv' -> Denotes (unionVarSet vs vs') (unionFV fv' fv).
Proof.
  move=> H H1. inversion H. inversion H1. subst.
  constructor.
  move=> f in_scope vs1 l h h0.
  unfold unionFV.
  specialize (H0 f in_scope vs1 l h h0).  move: H0 => [h1 h2].
  remember (fv f in_scope (l, vs1)) as vs_mid.
  specialize (H4 f in_scope (Tuple.snd vs_mid) (Tuple.fst vs_mid) h h1); move: H4 => [h3 h4].
  replace vs_mid with (Tuple.fst vs_mid, Tuple.snd vs_mid); [| destruct vs_mid; reflexivity].
  intuition.
  remember (fv' f in_scope (Tuple.fst vs_mid, Tuple.snd vs_mid)) as vs_fin.
  rewrite h4.
  rewrite h2.
  rewrite <- union_assoc.
  apply union_equal_1.
  rewrite -> unionVarSet_minusVarSet.
  rewrite unionVarSet_filterVarSet => //.
  f_equiv.
  apply filterVarSet_equal; try done.
  set_b_iff. rewrite union_sym.
  reflexivity. 
Qed.

Lemma union_FV_WF : forall fv fv',
    WF_fv fv -> WF_fv fv' -> WF_fv (unionFV fv fv').
Proof.
  intros. unfold_WF.
  exists (unionVarSet vs vs0). 
  eapply unionVarSet_unionFV; eauto.
Qed.  

Lemma mapUnionFV_nil A f : 
  mapUnionFV f (nil : list A) = emptyFV.
Proof.
  simpl.
  unfold emptyFV.
  reflexivity.
Qed. 
Hint Rewrite mapUnionFV_nil : hs_simpl. 

Lemma mapUnionFV_cons A f (x : A) xs : 
  mapUnionFV f (x :: xs) = unionFV (mapUnionFV f xs) (f x).
Proof.
  simpl.
  unfold unionFV.
  reflexivity.
Qed.
Hint Rewrite mapUnionFV_cons : hs_simpl. 


Lemma map_union_FV_WF : forall A f (ls : list A),
    (forall e, In e ls -> WF_fv (f e)) ->
    WF_fv (mapUnionFV f ls).
Proof.
  induction ls.
  - intros.
    exists emptyVarSet.
    hs_simpl.
    eapply emptyVarSet_emptyFV.
  -  move=> h. simpl in h.
    assert (h0 : forall e : A, In e ls -> WF_fv (f e)). { intros. apply h. tauto. }
    apply IHls in h0.
    assert (WF_fv (f a)). { apply h; tauto. }
    hs_simpl.
    move: h0 => [vs D].
    move: H => [vs' D'].
    eexists.
    eapply unionVarSet_unionFV; eauto.
Qed.

Lemma unions_FV_WF : forall fvs,
    (forall fv, In fv fvs -> WF_fv fv) ->
    WF_fv (unionsFV fvs).
Proof.
  apply map_union_FV_WF.
Qed.

Lemma mkFVs_FV_WF : forall vs,
    WF_fv (mkFVs vs).
Proof.
  intros. apply map_union_FV_WF; intros. apply unit_FV_WF.
Qed.

Hint Resolve unit_FV_WF.
Hint Resolve empty_FV_WF.
Hint Resolve union_FV_WF.
Hint Resolve unions_FV_WF.
Hint Resolve del_FV_WF.
Hint Resolve mkFVs_FV_WF.

(** * Some other theroems about [FV]s. *)

Lemma union_empty_l : forall fv, FV.unionFV FV.emptyFV fv = fv.
Proof. reflexivity. Qed.

Lemma union_empty_r : forall fv, FV.unionFV fv FV.emptyFV = fv.
Proof. reflexivity. Qed.

Lemma DenotesfvVarSet vs fv :
  Denotes vs fv -> fvVarSet fv [=] vs.
Proof.
  move => [vs0 fv0 h1].
  unfold fvVarSet, op_z2218U__, fvVarListVarSet, Tuple.snd.
  specialize (h1 (const true) emptyVarSet emptyVarSet nil ltac:(eauto)). 
  destruct h1.
  rewrite extendVarSetList_nil.
  reflexivity.
  remember (fv0 (const true) emptyVarSet (nil, emptyVarSet)) as tup.
  replace tup with (Tuple.fst tup, Tuple.snd tup); [| destruct tup; reflexivity].
  rewrite H0.
  hs_simpl.
  reflexivity.
Qed.



Lemma Denotes_inj1 vs1 vs2 fv : Denotes vs1 fv -> Denotes vs2 fv -> vs1 [=] vs2.
Proof.      
  move => h1. inversion h1.
  move => h2. inversion h2.
  subst.
  set in_scope := emptyVarSet.
  assert (h : extendVarSetList emptyVarSet nil [=] emptyVarSet).
  { rewrite <- mkVarSet_extendVarSetList. reflexivity. }
  specialize (H (const true) in_scope emptyVarSet nil ltac:(auto) h).
  specialize (H2 (const true) in_scope emptyVarSet nil ltac:(auto) h).
  move: H => [h3 h4].
  move: H2 => [h5 h6].
  remember (fv (const true) emptyVarSet (nil,emptyVarSet)) as tup1.
  replace tup1 with (Tuple.fst tup1, Tuple.snd tup1); [| destruct tup1; reflexivity].
  remember (fv (const true) emptyVarSet (nil,emptyVarSet)) as tup2.
  replace tup2 with (Tuple.fst tup2, Tuple.snd tup2); [| destruct tup2; reflexivity].
  hs_simpl in h4.
  hs_simpl in h6.
  rewrite <- h4.
  rewrite <- h6.
  reflexivity.
Qed.

Lemma unionVarSet_same vs : unionVarSet vs vs [=] vs.
Proof. set_b_iff. fsetdec. Qed.
Hint Rewrite unionVarSet_same : hs_simpl.

Lemma delVarSet_fvVarSet: forall fv x,
    WF_fv fv ->
    delVarSet (fvVarSet fv) x [=] fvVarSet (delFV x fv).
Proof.
  move => fv x [vs D].
  move: (delVarSet_delFV _ x _ D) => h1.
  move: (DenotesfvVarSet _ _ h1) => h2.
  move: (DenotesfvVarSet _ _ D) => h3.
  rewrite h3.
  rewrite h2.
  reflexivity.
Qed.

(* --------------------------------------- *)



Lemma mapUnionVarSet_mapUnionFV A (ps : list A) 
      (f1 :  A -> VarSet) (f2 : A -> FV.FV) :
  Forall2 Denotes (map f1 ps) (map f2 ps) ->
  Denotes  (mapUnionVarSet f1 ps) (FV.mapUnionFV f2 ps).
Proof.
  elim: ps => [|p ps IH]; unfold mapUnionVarSet; simpl.
  hs_simpl.
  - move=>h. constructor; intros; subst.
    unfold Tuple.fst, Tuple.snd.
    hs_simpl.
    split; auto.
    reflexivity.
  - hs_simpl.
    move=>h. inversion h. subst.
    unfold mapUnionVarSet in IH.
    specialize (IH H4). clear H4.
    move: (unionVarSet_unionFV _ _ _ _ H2 IH) => h0.
    unfold FV.unionFV in h0.
    auto.
Qed.


Lemma unionsFV_cons fv fvs : 
  FV.unionsFV (fv :: fvs) = 
  FV.unionFV (FV.unionsFV fvs) fv.
Proof.
  repeat unfold FV.unionsFV, FV.unionFV.
  rewrite mapUnionFV_cons.
  unfold FV.unionFV.
  simpl.
  reflexivity.
Qed.


Lemma unionsVarSet_unionsFV vss fvs: 
   Forall2 Denotes vss fvs ->
   Denotes (Foldable.foldr unionVarSet emptyVarSet vss) (FV.unionsFV fvs).
Proof.
  elim.
  - hs_simpl. 
    unfold FV.unionsFV, FV.mapUnionFV.
    constructor; intros; subst.
    unfold Tuple.fst, Tuple.snd.
    hs_simpl.
    split; auto.
    reflexivity.
  - move => vs fv vss1 fvs1 D1 D2 IH. 
    hs_simpl. 
    move: (unionVarSet_unionFV _ _ _ _ D1 IH) => h0.
    rewrite unionsFV_cons.
    auto.
Qed.

