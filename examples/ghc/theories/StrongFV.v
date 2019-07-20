(* Disable notation conflict warnings *)
Set Warnings "-notation-overridden".

From mathcomp.ssreflect
Require Import ssreflect ssrnat prime ssrbool eqtype.

Require Import Core.
Require Import FV.
Require Import Proofs.Axioms.
Require Import Proofs.ContainerAxioms.
Require Import Proofs.VarSet.
Require Import Proofs.StrongVarSet.
Require Import Proofs.Var.

Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.

Require Import GHC.Base.
Require Import Proofs.Prelude.
Import GHC.Base.ManualNotations.

Require Import Coq.Classes.Morphisms.

Set Bullet Behavior "Strict Subproofs".

Lemma fold_is_true : forall b, b = true <-> b.
Proof. intros. unfold is_true. reflexivity. Qed.

Lemma RespectsAEVar_const_true : RespectsAEVar (const true).
Proof. move => x1 x2 Eq. reflexivity. Qed.
Hint Resolve RespectsAEVar_const_true.
Lemma RespectsAEVar_andb f0 f: 
  RespectsAEVar f0 -> RespectsAEVar f ->
  RespectsAEVar (fun v : Var => f0 v && f v).
Proof.
  move => r1 r2 x1 x2 Eq.
  erewrite r1; eauto. 
  erewrite r2; eauto.
Qed.

Lemma emptyVarSet_StrongSubset :
  forall vs, emptyVarSet {<=} vs.
Admitted.
Hint Resolve emptyVarSet_StrongSubset.


Instance StrongSubset_m : Proper (StrongEquivalence ==> StrongEquivalence ==> iff) StrongSubset.
Admitted.

(* ---- Extensional Equality for VarSets --- *)

(*
Definition extEqual vs1 vs2 := forall v, lookupVarSet vs1 v = lookupVarSet vs2 v.
Definition extSubset vs1 vs2 := forall v v1, lookupVarSet vs1 v = Some v1 -> lookupVarSet vs2 v = Some v1.

Notation "vs1 |=| vs2" := (extEqual vs1 vs2) (at level 70, no associativity).
Notation "vs1 |<=| vs2" := (extSubset vs1 vs2) (at level 70, no associativity).

Instance extEqual_Reflexive : Reflexive extEqual.
Proof. move => vs v. auto. Qed.
Instance extEqual_Symmetric : Symmetric extEqual.
Proof. move => vs1 vs2 E v. rewrite (E v). done. Qed.
Instance extEqual_Transitive : Transitive extEqual.
Proof. move => vs1 vs2 vs3 E1 E2 v. rewrite (E1 v). rewrite (E2 v). done. Qed.
*)

(* This is actually a fairly strong statement of our VarSet implementation. It says that the VarSets are 'parametric' 
   WRT to the non-unique information stored in the Var. In other words, 
   we know that there is no way to produce the following situation (where 123 is the unique, 
   A/B is the aux info.)

      123_A  ...  `unionVarSet` 123_B  =>  123_A ...

      123_A  ... `unionVarSet`  123_B   =>  123_B ...
*)
Instance unionVarSet_m : Proper (StrongEquivalence ==> StrongEquivalence ==> StrongEquivalence) unionVarSet.
Proof.
Admitted.
(*
  move=> [[x1]] [[y1]] E1 [[x2]] [[y2]] E2.
  move=> v.
  move: (E1 v) (E2 v) => e1 e2.
  unfold lookupVarSet,UniqSet.lookupUniqSet,UniqFM.lookupUFM  in *.
  set (k := (Unique.getWordKey (Unique.getUnique v))) in *.
  unfold unionVarSet, UniqSet.unionUniqSets, UniqFM.plusUFM.
  destruct (IntMap.lookup k x2) eqn:L2; 
  destruct (IntMap.lookup k x1) eqn:L1.
  + move: (lookup_union _ k v0 x2 x1) => [hx _].
    move: (lookup_union _ k v0 y2 y1) => [hy _].
    rewrite hx. rewrite hy.   
    done.
    left. done.
    left. done.
  + move: (lookup_union _ k v0 x2 x1) => [hx _].
    move: (lookup_union _ k v0 y2 y1) => [hy _].
    rewrite hx. rewrite hy.   
    done.
    left. done.
    left. done.
  + move: (lookup_union _ k v0 x2 x1) => [hx _].
    move: (lookup_union _ k v0 y2 y1) => [hy _].
    rewrite hx. rewrite hy.   
    done.
    right. done.
    right. done.
  + symmetry in e1. rewrite <- non_member_lookup in e1.
    symmetry in e2. rewrite <- non_member_lookup in e2.
    (* seems provable but fussy. *)
Admitted.  *)

Instance minusVarSet_ext_m : Proper (StrongEquivalence ==> StrongEquivalence ==> StrongEquivalence) minusVarSet.
Proof.
  move=> [[x1]] [[y1]] E1 [[x2]] [[y2]] E2.
(*  move=> v.
  move: (E1 v) (E2 v) => e1 e2.
  unfold lookupVarSet,UniqSet.lookupUniqSet,UniqFM.lookupUFM  in *.
  set (k := (Unique.getWordKey (Unique.getUnique v))) in *.
  unfold minusVarSet, UniqSet.minusUniqSet, UniqFM.minusUFM.
  destruct (IntMap.lookup k x2) eqn:L2. symmetry in e2.
  erewrite lookup_difference_in_snd; eauto.
  erewrite lookup_difference_in_snd; eauto.
  rewrite lookup_difference_not_in_snd; eauto.
  rewrite lookup_difference_not_in_snd; eauto.
Qed. *)
Admitted.

Instance filterVarSet_ext_m : 
  forall f, RespectsAEVar f ->
  Proper (StrongEquivalence ==> StrongEquivalence) (filterVarSet f).
Proof.
(*   move=> v.
   move: (E2 v) => e2.
   unfold lookupVarSet,UniqSet.lookupUniqSet,UniqFM.lookupUFM  in *.
   set (k := (Unique.getWordKey (Unique.getUnique v))) in *.
   unfold filterVarSet,UniqSet.filterUniqSet,UniqFM.filterUFM. *)
Admitted.

Definition almostEqual_option (o1 : option Var) (o2: option Var) : Prop :=
  match o1 , o2 with 
  | Some v1 , Some v2 => almostEqual v1 v2
  | None , None => True 
  | _ , _ => False
end.


Instance lookupVarSet_ext_m : 
  Proper (StrongEquivalence ==> almostEqual ==> almostEqual_option) lookupVarSet.
Proof.
    move=> [[x1]] [[y1]] E1 v1 v2 E2.
(*    move: (E1 v1) => e.
    done.
Qed. *) 
Admitted.

Instance elemVarSet_ext_m : Proper (almostEqual ==> StrongEquivalence ==> Logic.eq) elemVarSet.
Proof.
    move=> v1 v2 E2 [[x1]] [[y1]] E1 .
(*    move: (E1 v1) => e. *)
Admitted.

Instance extendVarSet_ext_m : Proper (StrongEquivalence ==> almostEqual ==> StrongEquivalence) extendVarSet.
Proof.
Admitted.

Instance extendVarSetList_ext_m : Proper (StrongEquivalence ==> Forall2 almostEqual ==>  StrongEquivalence) extendVarSetList.
Proof.
  move=> vs1 vs2 E1 l1 l2 E2.
(*  subst l1.
  move: l2 vs1 vs2 E1.
  induction l2; move=> vs1 vs2 E1.
  hs_simpl. done.
  hs_simpl. erewrite IHl2; eauto.
  rewrite -> E1. done.
Qed. *) 
Admitted.
  
Instance delVarSet_ext_m  : Proper (StrongEquivalence ==> almostEqual ==> StrongEquivalence) delVarSet.
Admitted.

(* -------------------------- *)


Lemma unionVarSet_emptyVarSet_l : forall vs, unionVarSet emptyVarSet vs {=} vs.
Proof.
  move=> [[i]].
  unfold lookupVarSet,UniqSet.lookupUniqSet,UniqFM.lookupUFM  in *.
  simpl.
Admitted.

Axiom unionVarSet_emptyVarSet_r : forall vs, unionVarSet vs emptyVarSet {=} vs.



Axiom filterSingleton_true : forall f x,
  RespectsAEVar f -> f x = true -> filterVarSet f (unitVarSet x) {=} unitVarSet x.
Axiom filterSingleton_false : forall f x,
  RespectsAEVar f -> f x = false -> filterVarSet f (unitVarSet x) {=} emptyVarSet.
  
Lemma filterVarSet_StrongEquivalence : forall (f : Var -> bool) (vs1 vs2 : VarSet),
   RespectsAEVar f ->
   vs1 {=} vs2 -> (filterVarSet f vs1) {=} (filterVarSet f vs2).
Proof.
  move => f [[i1]] [[i2]] E.
  unfold lookupVarSet,UniqSet.lookupUniqSet,UniqFM.lookupUFM  in *.
  unfold filterVarSet,UniqSet.filterUniqSet,UniqFM.filterUFM.
Admitted.

Hint Resolve filterVarSet_StrongEquivalence.

Axiom filterVarSet_constTrue:
  forall vs : VarSet, (filterVarSet (const true) vs) {=} vs.

Axiom filterVarSet_StrongSubset : forall (f : Var -> bool) (vs : VarSet),
   RespectsAEVar f ->
   (filterVarSet f vs) {=} vs.

Lemma filterVarSet_comp : forall f f' vs,
    RespectsAEVar f ->
    RespectsAEVar f' ->
    filterVarSet f (filterVarSet f' vs) {=} filterVarSet (fun v => f v && f' v) vs.
Proof.
   intros. destruct vs, getUniqSet'. simpl.
Admitted.

Hint Rewrite unionVarSet_emptyVarSet_l  unionVarSet_emptyVarSet_r : hs_simpl.


Lemma minusVarSet_unitVarSet_true : forall x s,
  elemVarSet x s = true -> 
  minusVarSet (unitVarSet x) s = emptyVarSet.
Proof.
  move=> x [[i]] E.
Admitted.

(* Maybe this can also be true with '=' *)
Axiom minusVarSet_unitVarSet_false : forall x s,
  elemVarSet x s = false -> 
  minusVarSet (unitVarSet x) s {=} unitVarSet x.

(* This is only true on the left *)
Lemma unionVarSet_unitVarSet_l x : forall vs0 ,
  elemVarSet x vs0 = true ->
  unionVarSet (unitVarSet x) vs0 {=} vs0.
Proof.
  move=> [[i]] E.
Admitted.
(*
  move=> v.
  unfold unionVarSet, UniqSet.unionUniqSets, UniqFM.plusUFM.
  unfold elemVarSet,UniqSet.elementOfUniqSet,UniqFM.elemUFM  in *.
  unfold lookupVarSet,UniqSet.lookupUniqSet,UniqFM.lookupUFM  in *.
  simpl.
  destruct (IntMap.lookup (realUnique v) i) eqn:L.
  + rewrite <- lookup_union.
    left. auto.
  + destruct (v == x) eqn:Ex.
    ++ rewrite var_eq_realUnique in Ex.
       admit.
    ++ admit.
Admitted. *)

(* Scoped commutation for VarSet union. *)
Lemma unionVarSet_commute : forall vs0 vs1 sc,
  vs0 {<=} sc ->
  vs1 {<=} sc ->
  unionVarSet vs0 vs1 {=} unionVarSet vs1 vs0.
Proof.
Admitted.


Lemma filterVarSet_delVarSet_1 f vs v:
  RespectsAEVar f ->
  filterVarSet f (delVarSet vs v) {<=} delVarSet (filterVarSet f vs) v.
Admitted.
Lemma filterVarSet_delVarSet_2 f vs v:
  RespectsAEVar f ->
  delVarSet (filterVarSet f vs) v {<=} filterVarSet f (delVarSet vs v).
Admitted.
Lemma filterVarSet_delVarSet f vs v:
  RespectsAEVar f ->
  filterVarSet f (delVarSet vs v) {=} delVarSet (filterVarSet f vs) v.
Proof.
  intro Hf. split. eapply filterVarSet_delVarSet_1; eauto.
  eapply filterVarSet_delVarSet_2; eauto.
Qed.

Lemma minusVarSet_extendVarSet_1 vs1 vs2 v :
  minusVarSet vs1 (extendVarSet vs2 v) {<=}
  minusVarSet (delVarSet vs1 v) vs2. 
Admitted.
Lemma minusVarSet_extendVarSet_2 vs1 vs2 v :
  minusVarSet (delVarSet vs1 v) vs2 {<=}
  minusVarSet vs1 (extendVarSet vs2 v).
Admitted.
Lemma minusVarSet_extendVarSet vs1 vs2 v :
  minusVarSet vs1 (extendVarSet vs2 v) {=}
  minusVarSet (delVarSet vs1 v) vs2. 
Admitted.


Axiom unionVarSet_assoc_StrongEquivalence : forall vs1 vs2 vs3,
  unionVarSet vs1 (unionVarSet vs2 vs3) {=}
  unionVarSet (unionVarSet vs1 vs2) vs3.
Axiom unionVarSet_minusVarSet : forall vs1 vs2 vs : VarSet,
  (unionVarSet (minusVarSet vs1 vs) (minusVarSet vs2 vs)) 
    {=} (minusVarSet (unionVarSet vs1 vs2) vs).
Axiom unionVarSet_filterVarSet : forall (f : Var -> bool) (vs1 vs2 : VarSet),
   RespectsAEVar f ->
   (unionVarSet (filterVarSet f vs1) (filterVarSet f vs2))
    {=} (filterVarSet f (unionVarSet vs1 vs2)).


(* ------- Denote --------- *)

(* Add the elements in the list in the reverse order *)
Definition extendVarSetList' vs (l : list Var) :=
  Foldable.foldr (fun vs0 x => extendVarSet x vs0) vs l.

Lemma extendVarSetList_rev vs l : 
  extendVarSetList' vs (rev l) = extendVarSetList vs l.
Proof.
  unfold extendVarSetList'. rewrite extendVarSetList_foldl'. unfold VarSetFSet.VarSetFSet.add.
  rewrite hs_coq_foldr_list.
  rewrite hs_coq_foldl'_list.
  rewrite fold_left_rev_right.
  done.
Qed.

Instance extendVarSetList'_ext_m : Proper (StrongEquivalence ==> Forall2 almostEqual ==>  StrongEquivalence) extendVarSetList'.
Proof.
  move=> vs1 vs2 E1 l1 l2 E2.
(*  subst l1.
  unfold extendVarSetList'.
  induction l2. 
  hs_simpl. done.
  hs_simpl. 
  admit. *)
Admitted.


(*
Lemma ext_weak vs1 vs2 : vs1 {=} vs2 -> vs1 [=] vs2.
Proof.
  move=> h v .
  move: (h v) => hv.
  unfold VarSetFSet.In.
  split; move=> h1.
  all: apply elemVarSet_lookupVarSet in h1.
  all: move: h1 => [var h2].
  rewrite -> hv in h2. eapply lookupVarSet_elemVarSet; eauto.
  rewrite <- hv in h2. eapply lookupVarSet_elemVarSet; eauto.
Qed.
*)



(* NOTE: 

      The lists are the "real" representation of the set and are stored in reverse order.
      The sets (vs0 and vs1) are only used for expedient equality testing.

      NO: this is not true. fvVarSet 

      FV = InterestingVarFun -> VarSet -> list Var * VarSet -> list Var * VarSet
*)

Inductive Denotes : VarSet -> FV -> VarSet -> Prop :=
| DenotesVarSet : forall vs fv out_scope,
    (forall f in_scope l0 vs0,
        RespectsAEVar f ->
        vs0 {<=} out_scope ->
        let vl0        := extendVarSetList' emptyVarSet l0 in
        vl0 {=} vs0 ->
        let '(l1, vs1) := fv f in_scope (l0, vs0) in
        let vl1        := extendVarSetList' emptyVarSet l1 in
        vl1 {=} vs1 /\
        vs1 {=} unionVarSet vs0 (minusVarSet (filterVarSet f vs) in_scope) /\
        vs1 {<=} out_scope) ->
    Denotes vs fv out_scope.
Notation "A ⊢ B <={ C } " := (Denotes A B C) (at level 70).


Theorem Denotes_fvVarSet : forall m fv sc f in_scope l0 vs0,
    (m ⊢ fv <={ sc }) ->
    RespectsAEVar f ->
    extendVarSetList' emptyVarSet l0 {=} vs0 ->
    vs0 {<=} sc ->
    snd (fv f in_scope (l0, vs0))
      {=} unionVarSet vs0 (minusVarSet (filterVarSet f m) in_scope) /\
    snd (fv f in_scope (l0, vs0)) 
      {<=} sc.
Proof.
  move => m fv sc f in_scope l0 vs0 [vs' fv' out H0] H1 H2 H3.
  specialize (H0 f in_scope l0 vs0 H1 H3); subst.
  set (vl0 := extendVarSetList' emptyVarSet l0) in *.
  destruct fv'.
  specialize (H0 H2).
  set (vl1 := extendVarSetList' emptyVarSet l) in *.
  simpl in H0.
  move: H0 => [h0 [h1 h2]].
  simpl.
  done.
Qed.



Instance Denotes_m : 
  Proper (StrongEquivalence ==> Logic.eq ==> StrongEquivalence ==> iff) Denotes.
Admitted.

Lemma Denotes_weaken vs fv sc1 sc2:
  sc1 {<=} sc2 -> Denotes vs fv sc1 -> Denotes vs fv sc2.
Proof.  
Admitted.

Definition WF_fv (fv : FV) sc : Prop := exists vs, Denotes vs fv sc.

(* -------------------------------------------- *)

Lemma emptyVarSet_emptyFV sc : Denotes emptyVarSet emptyFV sc.
Proof.
  constructor; intros; subst.
  unfold emptyFV.
  split; auto.
  hs_simpl.
  split; eauto.
  reflexivity.
Qed.


Lemma empty_FV_WF sc :
  WF_fv emptyFV sc.
Proof.
  unfold WF_fv. exists emptyVarSet. eapply emptyVarSet_emptyFV. 
Qed.


Lemma unitVarSet_unitFV x sc : 
   unitVarSet x {<=} sc ->
   Denotes (unitVarSet x) (unitFV x) sc.
Proof.
  constructor; intros; subst.
  unfold unitFV.
  destruct elemVarSet eqn:E1;
  destruct (f x) eqn:FX;
  hs_simpl. 
  all: try (split; auto).
  - rewrite -> filterSingleton_true; try done.
    rewrite -> minusVarSet_unitVarSet_true; try done.
    hs_simpl. 
    split. reflexivity. done.
  - rewrite -> filterSingleton_false; try done.
    hs_simpl. 
    split. reflexivity. done.
  - elim In: (elemVarSet x vs0) => //.  split; auto.
    + rewrite -> filterSingleton_true => //.
      rewrite -> minusVarSet_unitVarSet_false; try done.  
      rewrite unionVarSet_commute; eauto.
      rewrite -> unionVarSet_unitVarSet_l; eauto. 
      split. reflexivity. done.
    + unfold extendVarSetList' .
      hs_simpl.
      split.
      f_equiv. auto.
      split.
      rewrite -> filterSingleton_true => //.      
      rewrite -> minusVarSet_unitVarSet_false => //.
      ++ admit.
      ++ admit.
Admitted.

Lemma unit_FV_WF x sc :
  unitVarSet x {<=} sc ->
  WF_fv (unitFV x) sc.
Proof.
   unfold WF_fv.
  exists (unitVarSet x).
  eapply unitVarSet_unitFV; eauto.
Qed.


Lemma filterVarSet_filterFV f vs x sc:
  RespectsAEVar f ->
  Denotes vs x sc -> Denotes (filterVarSet f vs) (filterFV f x) sc.
Proof.
  move => p D.
  constructor. move=> f0 in_scope vs' l h0 h1 l1 h2.
  inversion D.
  unfold filterFV. subst.

  specialize (H (fun v : Var => f0 v && f v) in_scope vs' l 
                ltac:(eauto using RespectsAEVar_andb)
                ltac:(auto)
                ltac:(eauto)
               ).
  destruct x.
  set (vl1:= extendVarSetList' emptyVarSet l0) in *.
  destruct H as [k0 [k1 k2]].
  split; auto. split; auto.
  rewrite <- filterVarSet_comp in k1; eauto.
Qed.

Ltac unfold_WF :=
  repeat match goal with
  | [ H : WF_fv ?fv ?sc |- _] =>
    let vs := fresh "vs" in
    let Hd := fresh "Hdenotes" in
    inversion H as [vs Hd]; inversion Hd; subst; clear H
  | [ |- WF_fv ?fv ?sc] =>
    unfold WF_fv
  end.

Lemma filter_FV_WF : forall f x sc,
    RespectsAEVar f ->
    WF_fv x sc -> WF_fv (filterFV f x) sc.
Proof.
  intros. unfold_WF.
  exists (filterVarSet f vs). 
  eapply filterVarSet_filterFV; auto.
Qed.

Axiom delVarSet_StrongSubset : forall xs v sc,
  xs {<=} sc ->
  delVarSet xs v {<=} sc.


Lemma delVarSet_delFV vs v fv sc :
  Denotes vs fv sc -> Denotes (delVarSet vs v) (delFV v fv) (delVarSet sc v).
Proof.
  move=> H. inversion H. subst.
  constructor; intros. unfold delFV.
  specialize (H0 f (extendVarSet in_scope v) l0 vs0 H1).
  have h0: vs0 {<=} sc. { eapply StrongSubset_trans; eauto.
                         eapply delVarSet_StrongSubset; eauto. reflexivity.
                       }
  specialize (H0 h0 H3).
  destruct fv.
  set (vl1 := extendVarSetList' emptyVarSet l) in *. 
  destruct H0 as [h1 [h2 h3]].
  split; auto.
  split.
  rewrite -> h2. 
  f_equiv.
  rewrite filterVarSet_delVarSet; eauto.
  rewrite minusVarSet_extendVarSet; eauto.
  reflexivity.
  (* Ugh. need to argue that v is not in v0 *)
  (* we know this because v is not in vs0 
     and it is subtracted out from filterVarSet f vs *)
  admit.
Admitted.


Lemma del_FV_WF : forall fv v sc,
    WF_fv fv sc -> WF_fv (delFV v fv) (delVarSet sc v).
Proof.
  intros. unfold_WF.
  exists (delVarSet vs v). 
  eapply delVarSet_delFV. auto.
Qed.

Lemma unionVarSet_unionFV vs vs' fv fv' sc:
  Denotes vs fv sc -> Denotes vs' fv' sc -> Denotes (unionVarSet vs vs') (unionFV fv' fv) sc.
Proof.
  move=> H H1. inversion H. inversion H1. subst.
  constructor.
  move=> f in_scope l0 vs0 h h0.
  move=> vl0 h1.
  unfold unionFV.
  specialize (H0 f in_scope l0 vs0 h h0 h1).  
  set (vs_mid := (fv f in_scope (l0, vs0))) in *. destruct vs_mid as [l1 vs1].
  move: H0 => [h2 [h3 h4]].
  specialize (H5 f in_scope l1 vs1 ltac:(auto) ltac:(auto) ltac:(eauto)).  
  destruct fv' as [l2 vs2].
  move: H5 => [h5 [h6 h7]].
  split. auto.
  split; auto. 
  rewrite -> h6.
  rewrite -> h3.

  rewrite <- unionVarSet_assoc_StrongEquivalence.
  f_equiv.
  rewrite -> unionVarSet_minusVarSet.  
  f_equiv.
  rewrite unionVarSet_filterVarSet => //.
  reflexivity. 
Qed.

Lemma union_FV_WF : forall fv fv' vs,
    WF_fv fv vs -> WF_fv fv' vs -> WF_fv (unionFV fv fv') vs.
Proof.
  intros. unfold_WF.
  exists (unionVarSet vs0 vs1). 
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


Lemma map_union_FV_WF : forall A f vs (ls : list A),
    (forall e, In e ls -> WF_fv (f e) vs) ->
    WF_fv (mapUnionFV f ls) vs.
Proof.
  induction ls.
  - intros.
    exists emptyVarSet.
    hs_simpl.
    eapply emptyVarSet_emptyFV.
  -  move=> h. simpl in h.
    assert (h0 : forall e : A, In e ls -> WF_fv (f e) vs). { intros. apply h. tauto. }
    apply IHls in h0.
    assert (WF_fv (f a) vs). { apply h; tauto. }
    hs_simpl.
    move: h0 => [vs1 D1].
    move: H => [vs' D'].
    eexists.
    eapply unionVarSet_unionFV; eauto.
Qed.

Lemma unions_FV_WF : forall fvs vs,
    (forall fv, In fv fvs -> WF_fv fv vs) ->
    WF_fv (unionsFV fvs) vs.
Proof.
  intros.
  eapply map_union_FV_WF. auto.
Qed.


Lemma mkFVs_FV_WF : forall vs sc,
    (forall v, In v vs -> unitVarSet v {<=} sc) ->
    WF_fv (mkFVs vs) sc.
Proof.
  intros. apply map_union_FV_WF; intros. apply unit_FV_WF.
  eauto.
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


Lemma Denotes_fvVarSet_vs vs fv sc :
  Denotes vs fv sc -> fvVarSet fv {=} vs.
Proof.
  move => [vs0 fv0 sc0 h1].
  unfold fvVarSet, op_z2218U__, fvVarListVarSet.
  specialize (h1 (const true) emptyVarSet nil emptyVarSet ltac:(eauto) 
    ltac:(eauto)).
  unfold extendVarSetList' in h1. hs_simpl in h1.
  destruct fv0 as [l1 vs1].
  destruct h1 as [h2 [h3 h4]]. reflexivity.
  simpl.
  rewrite -> h3.
  rewrite unionVarSet_emptyVarSet_l.
  rewrite filterVarSet_constTrue.
  reflexivity.
Qed.

Lemma Denotes_sc vs fv sc :
  Denotes vs fv sc -> vs {<=} sc.
Proof.
  move=> [vs0 fv0 sc0 h1].
  unfold fvVarSet, op_z2218U__, fvVarListVarSet.
  specialize (h1 (const true) emptyVarSet nil emptyVarSet ltac:(eauto) 
    ltac:(eauto)).
  unfold extendVarSetList' in h1. hs_simpl in h1.
  destruct fv0 as [l1 vs1].
  destruct h1 as [h2 [h3 h4]]. reflexivity.
  hs_simpl in h3.
  rewrite -> filterVarSet_constTrue in h3.
  rewrite <- h3.
  auto.
Qed.


Lemma Denotes_inj1 vs1 vs2 fv sc : Denotes vs1 fv sc -> Denotes vs2 fv sc -> vs1 {=} vs2.
Proof.      
  move => h1. inversion h1.
  move => h2. inversion h2.
  subst.
  set in_scope := emptyVarSet.
  assert (h : extendVarSetList emptyVarSet nil {=} emptyVarSet).
  { rewrite <- mkVarSet_extendVarSetList. reflexivity. }
  specialize (H (const true) in_scope nil emptyVarSet ltac:(auto) ltac:(auto) h).
  specialize (H3 (const true) in_scope nil emptyVarSet ltac:(auto) ltac:(auto) h).
  destruct fv as [l3 vs3].
  move: H => [h3 [h4 hg]].
  move: H3 => [h5 [h6 hh]].
  hs_simpl in h4.
  hs_simpl in h6.
  rewrite -> filterVarSet_constTrue in h4.
  rewrite -> filterVarSet_constTrue in h6.
  rewrite <- h4.
  rewrite <- h6.
  reflexivity.
Qed.


Lemma delVarSet_fvVarSet: forall fv x sc,
    WF_fv fv sc ->
    delVarSet (fvVarSet fv) x {=} fvVarSet (delFV x fv).
Proof.
  move => fv x sc [vs D].
  move: (delVarSet_delFV _ x _ sc D) => h1.
  move: (Denotes_fvVarSet_vs _ _ _ h1) => h2.
  move: (Denotes_fvVarSet_vs _ _ _ D) => h3.
  rewrite h2.
  rewrite h3.
  reflexivity.
Qed.

Lemma mapUnionVarSet_mapUnionFV A (ps : list A) 
      (f1 :  A -> VarSet) (f2 : A -> FV.FV) sc :
  Forall2 (fun vs fv => Denotes vs fv sc) (map f1 ps) (map f2 ps) ->
  Denotes  (mapUnionVarSet f1 ps) (FV.mapUnionFV f2 ps) sc.
Proof.
  elim: ps => [|p ps IH]; unfold mapUnionVarSet; simpl.
  hs_simpl.
  - move=>h. constructor; intros; subst.
    hs_simpl.
    split; auto.
    split.
    reflexivity.
    auto.
  - hs_simpl.
    move=>h. inversion h. subst.
    unfold mapUnionVarSet in IH.
    specialize (IH H4). clear H4.
    move: (unionVarSet_unionFV _ _ _ _ _ H2 IH) => h0.
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


Lemma unionsVarSet_unionsFV vss fvs sc: 
   Forall2 (fun vs fv => Denotes vs fv sc) vss fvs ->
   Denotes (Foldable.foldr unionVarSet emptyVarSet vss) (FV.unionsFV fvs) sc.
Proof.
  elim.
  - hs_simpl. 
    unfold FV.unionsFV, FV.mapUnionFV.
    constructor; intros; subst.
    hs_simpl.
    split; auto.
    split; auto. reflexivity.
  - move => vs fv vss1 fvs1 D1 D2 IH. 
    hs_simpl. 
    move: (unionVarSet_unionFV _ _ _ _ _ D1 IH) => h0.
    rewrite unionsFV_cons.
    auto.
Qed.

