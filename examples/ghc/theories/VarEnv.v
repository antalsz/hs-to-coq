(* Disable notation conflict warnings *)
Set Warnings "-notation-overridden".


From mathcomp.ssreflect
Require Import ssreflect ssrnat prime ssrbool eqtype.

Require Import Coq.Lists.List.

Require Import GHC.Base.
Require Import Proofs.Data.Foldable.

Require Import Id.
Require Import Core.

Require Import Proofs.Axioms.
Require Import Proofs.ContainerProofs.

Require Import Proofs.Core.
Require Import Proofs.Var.
Require Import Proofs.Unique.
Require Import Proofs.VarSet.
Require Import Proofs.VarSetFSet.
Require Import Proofs.VarSetStrong.

Require Import Proofs.GHC.Base.

Set Bullet Behavior "Strict Subproofs".


Lemma elemVarSet_uniqAway:
  forall v iss vs,
  subVarSet vs (getInScopeVars iss) = true ->
  elemVarSet (uniqAway iss v) vs = false.
Proof.
  intros.
  apply subVarSet_elemVarSet_false with (vs' := getInScopeVars iss). auto.
  rewrite <- lookupVarSet_None_elemVarSet.
  eapply uniqAway_lookupVarSet_fresh.  
Qed.



(** ** [VarEnv] axiomatization *)

(* Eventually replace these with container axioms. *)

Lemma lookupVarEnv_elemVarEnv_true :
  forall A v (vs : VarEnv A),
   elemVarEnv v vs = true <-> (exists a, lookupVarEnv vs v = Some a).
Proof.
  move=> A v vs.
  elim: vs => [i].
  unfold elemVarEnv, lookupVarEnv.
  unfold  UniqFM.elemUFM,  UniqFM.lookupUFM.
  rewrite <- member_lookup. done.
Qed.

Lemma lookupVarEnv_elemVarEnv_false :
  forall A v (vs : VarEnv A),
   elemVarEnv v vs = false <-> (lookupVarEnv vs v = None).
Proof.
  move=> A v vs.
  elim: vs => [i].
  unfold elemVarEnv, lookupVarEnv.
  unfold  UniqFM.elemUFM,  UniqFM.lookupUFM.
  rewrite non_member_lookup.
  done.
Qed.

Lemma lookupVarEnv_eq :
  forall A v1 v2 (vs : VarEnv A),
    (v1 == v2) = true ->
    lookupVarEnv vs v1 = lookupVarEnv vs v2.
Proof.
  move=> A v1 v2 vs.
  elim: vs => [i].
  unfold elemVarEnv, lookupVarEnv.
  unfold  UniqFM.elemUFM,  UniqFM.lookupUFM.
  move=> h.
  erewrite lookup_eq ; eauto.
Qed.

Lemma elemVarEnv_eq :
  forall A v1 v2 (vs : VarEnv A),
    (v1 == v2) = true ->
    elemVarEnv v1 vs = elemVarEnv v2 vs.
  move=> A v1 v2 vs.
  elim: vs => [i].
  unfold elemVarEnv, lookupVarEnv.
  unfold  UniqFM.elemUFM,  UniqFM.lookupUFM.
  move=> h.
  erewrite member_eq ; eauto.
Qed.


Lemma lookupVarEnv_extendVarEnv_eq :
  forall A v1 v2 (vs : VarEnv A) val, 
    v1 == v2 = true ->
    lookupVarEnv (extendVarEnv vs v1 val) v2 = Some val.
Proof.
  move=> A v1 v2 vs val.
  elim: vs => [i].
  unfold elemVarEnv, lookupVarEnv, extendVarEnv.
  unfold  UniqFM.elemUFM,  UniqFM.lookupUFM, UniqFM.addToUFM.
  move=> h.
  erewrite lookup_eq.
  erewrite lookup_insert ; eauto.
  rewrite -> fold_is_true  in h.
  apply eq_unique in h.
  rewrite h.
  reflexivity.
Qed.



Lemma lookupVarEnv_extendVarEnv_neq :
  forall A v1 v2 (vs : VarEnv A) val, 
    v1 == v2 <> true ->
    lookupVarEnv (extendVarEnv vs v1 val) v2 = lookupVarEnv vs v2.
Proof.
  move=> A v1 v2 vs val.
  elim: vs => [i].
  unfold elemVarEnv, lookupVarEnv, extendVarEnv.
  unfold  UniqFM.elemUFM,  UniqFM.lookupUFM, UniqFM.addToUFM.
  move=> h.
  rewrite lookup_insert_neq //.
  move => nh.
  rewrite <- eq_unique in nh.
  rewrite Eq_sym in nh.
  done.
Qed.

Lemma elemVarEnv_extendVarEnv_eq :
  forall A v1 v2 (vs : VarEnv A) val, 
    v1 == v2 = true ->
    elemVarEnv v2 (extendVarEnv vs v1 val) = true.
Proof.
  move=> A v1 v2 vs val.
  elim: vs => [i].
  unfold elemVarEnv, lookupVarEnv, extendVarEnv.
  unfold  UniqFM.elemUFM,  UniqFM.lookupUFM, UniqFM.addToUFM.
  move=> h.
  rewrite member_insert.
  apply /orP.
  left.
  erewrite fold_is_true in h.
  rewrite -> eq_unique in h.
  rewrite h.
  reflexivity.
Qed.

Lemma elemVarEnv_extendVarEnv_neq :
  forall A v1 v2 (vs : VarEnv A) val, 
    v1 == v2 <> true ->
    elemVarEnv v2 (extendVarEnv vs v1 val) = elemVarEnv v2 vs.
Proof.
  move=> A v1 v2 vs val.
  elim: vs => [i].
  unfold elemVarEnv, lookupVarEnv, extendVarEnv.
  unfold  UniqFM.elemUFM,  UniqFM.lookupUFM, UniqFM.addToUFM.
  move=> h.
  rewrite member_insert.
  elim M: (IntMap.member (Unique.getWordKey (Unique.getUnique v2)) i).
  rewrite orbT. done.
  rewrite orbF.
  apply /Eq_eq.
  move => h0.
  rewrite <- eq_unique in h0.
  rewrite Eq_sym in h0.
  done.
Qed.  



Lemma elemVarEnv_delVarEnv_eq :
  forall A v1 v2 (vs : VarEnv A), 
    v1 == v2 = true ->
    elemVarEnv v2 (delVarEnv vs v1) = false.
Proof.
  move=> A v1 v2 vs.
  elim: vs => [i].
  unfold elemVarEnv, lookupVarEnv, extendVarEnv, delVarEnv.
  unfold  UniqFM.elemUFM,  UniqFM.lookupUFM, UniqFM.addToUFM, UniqFM.delFromUFM.
  move => h.
  rewrite -> fold_is_true in h.
  rewrite -> eq_unique in h.
  rewrite h.
  rewrite non_member_lookup.
  apply delete_eq.
Qed.


Lemma elemVarEnv_delVarEnv_neq :
  forall A v1 v2 (env: VarEnv A), (v1 == v2) = false -> 
               elemVarEnv v2 (delVarEnv env v1) = elemVarEnv v2 env.
Proof.
  move=> A v1 v2 vs.
  elim: vs => [i].
  unfold elemVarEnv, lookupVarEnv, extendVarEnv, delVarEnv.
  unfold  UniqFM.elemUFM,  UniqFM.lookupUFM, UniqFM.addToUFM, UniqFM.delFromUFM.
  move => h.
  set k1 := (Unique.getWordKey (Unique.getUnique v1)).
  set k2 := (Unique.getWordKey (Unique.getUnique v2)).
  assert (k1 <> k2).
   { move => h1. subst k1. subst k2.
     rewrite <- eq_unique in h1.
     rewrite h1 in h.
     done. }
   apply member_delete_neq.
   auto.
Qed.

Lemma lookupVarEnv_delVarEnv_eq :
  forall A v1 v2 (vs : VarEnv A), 
    v1 == v2 = true ->
    lookupVarEnv (delVarEnv vs v1) v2 = None.
Proof. 
  move=> A v1 v2 vs.
  elim: vs => [i].
  unfold elemVarEnv, lookupVarEnv, extendVarEnv, delVarEnv.
  unfold  UniqFM.elemUFM,  UniqFM.lookupUFM, UniqFM.addToUFM, UniqFM.delFromUFM.
  move => h.
  erewrite fold_is_true in h.
  erewrite eq_unique in h.
  rewrite h.
  apply delete_eq.
Qed.

Lemma lookupVarEnv_delVarEnv_neq :
  forall A v1 v2 (vs : VarEnv A), 
    v1 == v2 <> true ->
    lookupVarEnv (delVarEnv vs v1) v2 = lookupVarEnv vs v2.
Proof.
  move=> A v1 v2 vs.
  elim: vs => [i].
  unfold elemVarEnv, lookupVarEnv, extendVarEnv, delVarEnv.
  unfold  UniqFM.elemUFM,  UniqFM.lookupUFM, UniqFM.addToUFM, UniqFM.delFromUFM.
  move => h.
  apply delete_neq.
  move => h0.
  erewrite <- eq_unique in h0.
  rewrite Eq_sym in h0.
  rewrite h0 in h.
  done.
Qed.

(** [minusDom] **)

(* To be able to specify the property of a wellformed substitution, 
   we need to define the operation of taking a variable set and 
   removing all of the vars that are part of the domain of the 
   substitution. *)


Definition minusDom {a} (vs : VarSet) (e : VarEnv a) : VarSet :=
  filterVarSet (fun v => negb (elemVarEnv v e)) vs.


Ltac specialize_all var := 
  repeat 
    match goal with 
    | [ H : forall var:Var, _ |- _ ] => specialize (H var)
    end.

(* After a case split on whether a var is present in a minusDom'ed env, 
   rewrite a use of minusDom appropriately. *)
Ltac rewrite_minusDom_true := 
  match goal with 
  | [ H : elemVarEnv ?var ?init_env = true |- 
      context [ lookupVarSet 
                  (minusDom ?s ?init_env) ?var ] ] =>  
    unfold minusDom;
    repeat rewrite -> lookupVarSet_filterVarSet_false with 
        (f := (fun v0 : Var => negb (elemVarEnv v0 init_env ))); try rewrite H; auto 
  | [ H : elemVarEnv ?var ?init_env = true, 
          H2: context [ lookupVarSet 
                          (minusDom ?s ?init_env) ?var ] |- _ ] =>  
    unfold minusDom in H2;
    rewrite -> lookupVarSet_filterVarSet_false with
        (f := (fun v0 : Var => negb (elemVarEnv v0 init_env ))) in H2; 
    try rewrite H; auto 
                                                                    
  end.

Ltac rewrite_minusDom_false := 
  match goal with 
  | [ H : elemVarEnv ?var ?init_env  = false |- 
      context [ lookupVarSet 
                  (minusDom ?s ?init_env) ?var ] ] =>  
    unfold minusDom;
    repeat rewrite -> lookupVarSet_filterVarSet_true
    with (f := (fun v0 : Var => negb (elemVarEnv v0 init_env ))); 
    try rewrite H; auto 
  | [ H : elemVarEnv ?var ?init_env = false, 
          H2: context [ lookupVarSet 
                          (minusDom ?s ?init_env) ?var ] |- _ ] =>  
    unfold minusDom in H2;
    rewrite -> lookupVarSet_filterVarSet_true with 
        (f := (fun v0 : Var => negb (elemVarEnv v0 init_env ))) in H2 ; 
    try rewrite H; auto  
  end.

Lemma RespectsVar_negbElemVarEnv A (e :VarEnv A) : 
  RespectsVar (fun v0 : Var => ~~ elemVarEnv v0 e).
Proof. 
  move=> x1 x2 Eq.
  f_equal.
  erewrite elemVarEnv_eq; try done.
Qed.
Hint Resolve RespectsVar_negbElemVarEnv.

Lemma StrongSubset_minusDom {a} : forall vs1 vs2 (e: VarEnv a), 
    vs1 {<=} vs2 ->
    minusDom vs1 e {<=} minusDom vs2 e.
Proof.
  intros. 
  unfold StrongSubset in *.
  intros var.
  destruct (elemVarEnv var e) eqn:IN_ENV.
  + rewrite_minusDom_true; try done.
  + rewrite_minusDom_false; try done.
    eapply H.
Qed.


Lemma lookupVarSet_minusDom_1 :
  forall a (env : VarEnv a) vs v,
    lookupVarEnv env v = None -> 
    lookupVarSet (minusDom vs env) v = lookupVarSet vs v.
Proof.
  intros.
  rewrite <- lookupVarEnv_elemVarEnv_false in H.
  unfold minusDom.
  rewrite -> lookupVarSet_filterVarSet_true
    with (f := (fun v0 : Var => negb (elemVarEnv v0 env))); try done.
  rewrite H. simpl. auto.
Qed.



Lemma lookup_minusDom_inDom : forall a vs (env:VarEnv a) v',
    elemVarEnv v' env = true ->
    lookupVarSet (minusDom vs env) v' = None.
Proof.
  intros.
  rewrite_minusDom_true.
Qed. 


Lemma minusDom_extend : 
  forall a vs (env : VarEnv a) v,
    minusDom (extendVarSet vs v) (delVarEnv env v) {<=} 
    extendVarSet (minusDom vs env) v.
Proof.
  intros.
  unfold StrongSubset.
  intros var.
  destruct (elemVarEnv var (delVarEnv env v)) eqn:IN.
  rewrite_minusDom_true.
  rewrite_minusDom_false.
  destruct (v == var) eqn:EQ.
  rewrite lookupVarSet_extendVarSet_eq;auto.
  rewrite lookupVarSet_extendVarSet_eq; auto.
  eapply almostEqual_refl; auto.
  rewrite lookupVarSet_extendVarSet_neq; auto.
  destruct (lookupVarSet vs var) eqn:IN2; auto.
  rewrite lookupVarSet_extendVarSet_neq; auto.
  rewrite lookupVarSet_filterVarSet_true; try rewrite IN; auto.
  rewrite IN2.
  apply almostEqual_refl; auto.
  rewrite elemVarEnv_delVarEnv_neq in IN; auto.
  rewrite IN. auto.
  intro h. rewrite EQ in h. auto. 
  intro h. rewrite EQ in h. auto.
Qed.


Lemma lookup_minusDom_extend : forall a vs (env:VarEnv a) v v' e,
    v ==  v' <> true ->
    lookupVarSet (minusDom (extendVarSet vs v) (extendVarEnv env v e)) v' =
    lookupVarSet (minusDom vs env) v'.
Proof.
  intros.
  destruct (elemVarEnv v' env) eqn:Eenv; auto.
  + (* v' is in dom of env. so cannot be looked up. *)
    unfold minusDom.
    rewrite -> lookupVarSet_filterVarSet_false; auto.  
    rewrite -> lookupVarSet_filterVarSet_false; auto.  
    rewrite Eenv. simpl. auto.
    rewrite elemVarEnv_extendVarEnv_neq.
    rewrite Eenv. simpl. auto.
    auto.
  + unfold minusDom.
    rewrite -> lookupVarSet_filterVarSet_true; auto.  
    rewrite -> lookupVarSet_filterVarSet_true; auto.  
    rewrite lookupVarSet_extendVarSet_neq; auto.
    auto.
    rewrite Eenv. simpl. auto.
    rewrite elemVarEnv_extendVarEnv_neq.
    rewrite Eenv. simpl. auto.
    auto.
Qed.

Lemma StrongSubset_minusDom_left {a} : forall vs (e: VarEnv a), 
    minusDom vs e {<=} vs.
Proof.
  intros.
  unfold StrongSubset. intro var.
  destruct (elemVarEnv var e) eqn:EL.
  rewrite_minusDom_true.
  rewrite_minusDom_false.
  destruct lookupVarSet.
  eapply almostEqual_refl.
  auto.
Qed.


Lemma StrongSubset_minusDom_extend_extend : forall vs v e (env: IdEnv CoreExpr),
           minusDom (extendVarSet vs v) (extendVarEnv env v e) {<=} minusDom vs env.
Proof.
  intros.
  intro var.
  destruct (var == v) eqn:EQ.
  rewrite -> lookupVarSet_eq with (v2 := v); auto.
  unfold minusDom.
  rewrite lookupVarSet_filterVarSet_false; try done. 
  rewrite elemVarEnv_extendVarEnv_eq.
  simpl. auto.
  rewrite Base.Eq_refl. auto.
  rewrite lookup_minusDom_extend.
  destruct (lookupVarSet (minusDom vs env) var).
  eapply almostEqual_refl. auto.
  intro h.
  rewrite Base.Eq_sym in h.
  rewrite h in EQ.
  discriminate.
Qed.


(** ** [InScopeSet] *)

Lemma getInScopeVars_extendInScopeSet:
  forall iss v,
  getInScopeVars (extendInScopeSet iss v) = extendVarSet (getInScopeVars iss) v.
Proof.
  intros.
  unfold getInScopeVars.
  unfold extendInScopeSet.
  destruct iss.
  reflexivity.
Qed.

Lemma getInScopeVars_extendInScopeSetList:
  forall iss vs,
  getInScopeVars (extendInScopeSetList iss vs) = extendVarSetList (getInScopeVars iss) vs.
Proof.
  intros.
  rewrite -> extendVarSetList_foldl'.
  unfold getInScopeVars.
  unfold extendInScopeSetList.
  set_b_iff.
  destruct iss.
  unfold_Foldable_foldl'.
  unfold_Foldable_foldl.
  f_equal.
Qed.


Lemma extendInScopeSetList_cons : forall v vs in_scope_set,
           (extendInScopeSetList in_scope_set (v :: vs) = 
            (extendInScopeSetList (extendInScopeSet in_scope_set v) vs)).
Proof.
  unfold extendInScopeSetList.
  destruct in_scope_set.
  unfold_Foldable_foldl.
  simpl.
  f_equal.
  unfold Pos.to_nat.
  unfold Pos.iter_op.
  omega.
Qed.

Lemma extendInScopeSetList_nil : forall in_scope_set,
           extendInScopeSetList in_scope_set nil = in_scope_set.
Proof.
  unfold extendInScopeSetList.
  destruct in_scope_set.
  unfold_Foldable_foldl.
  simpl.
  f_equal.
  omega.
Qed.




