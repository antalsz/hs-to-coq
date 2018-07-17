Require Import GHC.Base.
Require Import CoreFVs.
Require Import Id.
Require Import Core.
Require UniqFM.

Import GHC.Base.ManualNotations.

Require Import Proofs.GHC.Base.
Require Import Proofs.GHC.List.

Require Import Psatz.
Require Import Coq.Lists.List.
Require Import Coq.NArith.BinNat.

Import ListNotations.

Require Import Proofs.GhcTactics.
Require Import Proofs.Unique.
Require Import Proofs.Var.
Require Import Proofs.Base.
(* Require Import Proofs.ContainerAxioms.
   Require Import IntSetProofs.  *)

Require Import Proofs.VarSetFSet.

Open Scope Z_scope.

Set Bullet Behavior "Strict Subproofs".

Ltac unfold_VarSet_to_IntMap :=
  repeat match goal with
         | [vs : VarSet |- _ ] =>
           let u := fresh "u" in
           destruct vs as [u]; destruct u; simpl
         | [ |- UniqSet.Mk_UniqSet _ = UniqSet.Mk_UniqSet _ ] =>
           f_equal
         | [ |- UniqFM.UFM _ = UniqFM.UFM _ ] =>
           f_equal
         end.

(** ** Valid VarSets *)

(* This property is an invariant of the VarSet/UniqFM type. We may want to either 
   axiomatize it or add it to a sigma type in one of the definitions. *)

Definition ValidVarSet (vs : VarSet) : Prop :=
  forall v1 v2, lookupVarSet vs v1 = Some v2 -> (v1 GHC.Base.== v2) = true.


(** ** [VarSet] as FiniteSets  *)

(* These lemmas relate the GHC VarSet operations to more general 
   operations on finite sets. *)

Lemma emptyVarSet_empty : emptyVarSet = empty.
  reflexivity. Qed.

Lemma delVarSet_remove : forall x s, delVarSet s x = remove x s.
  reflexivity. Qed.

Lemma extendVarSet_add : forall x s, extendVarSet s x = add x s.
  reflexivity. Qed.

Lemma unitVarSet_singleton : forall x, unitVarSet x = singleton x.
  reflexivity. Qed.

Lemma unionVarSet_union : forall x y, unionVarSet x y = union x y.
  reflexivity. Qed.

Lemma minusVarSet_diff : forall x y, minusVarSet x y = diff x y.
  (* Why simply [reflexivity] does not work? *)
  intros. destruct x; destruct u. destruct y; destruct u. reflexivity. Qed.

Lemma filterVarSet_filter : forall f x, filterVarSet f x = filter f x.
  reflexivity. Qed.

Lemma extendVarSetList_foldl' : forall x xs, 
    extendVarSetList x xs = 
    Foldable.foldl' (fun x y => add y x) x xs.
Proof.
  intros.
  unfold extendVarSetList,
         UniqSet.addListToUniqSet;
  replace UniqSet.addOneToUniqSet with 
      (fun x y => add y x).
  auto.
  auto.
Qed.

Lemma delVarSetList_foldl : forall vl vs,
    delVarSetList vs vl = Foldable.foldl delVarSet vs vl.
Proof. 
  induction vl.
  - intro vs. 
    unfold delVarSetList.
    unfold UniqSet.delListFromUniqSet.
    destruct vs.
    unfold UniqFM.delListFromUFM.
    unfold_Foldable_foldl.
    simpl.
    auto.
  - intro vs. 
    unfold delVarSetList in *.
    unfold UniqSet.delListFromUniqSet in *.
    destruct vs.
    unfold UniqFM.delListFromUFM in *.
    revert IHvl.
    unfold_Foldable_foldl.
    simpl.
    intro IHvl.
    rewrite IHvl with (vs:= (UniqSet.Mk_UniqSet (UniqFM.delFromUFM u a))).
    auto.
Qed.


Lemma mkVarSet_extendVarSetList : forall xs,
    mkVarSet xs = extendVarSetList emptyVarSet xs.
Proof.
  reflexivity.
Qed.

Ltac rewrite_extendVarSetList := 
  unfold extendVarSetList, UniqSet.addListToUniqSet;
  replace UniqSet.addOneToUniqSet with (fun x y => add y x) by auto.

(* This tactic rewrites the boolean functions into the 
   set properties to make them more suitable for fsetdec. *)

Ltac set_b_iff :=
  repeat
   progress
    rewrite <- not_mem_iff in *
  || rewrite <- mem_iff in *
  || rewrite <- subset_iff in *
  || rewrite <- is_empty_iff in *
  || rewrite emptyVarSet_empty in *
  || rewrite delVarSet_remove in *
  || rewrite extendVarSet_add in *
  || rewrite unionVarSet_union in *
  || rewrite minusVarSet_diff in *
  || rewrite filterVarSet_filter in *
  || rewrite empty_b in *
  || rewrite unitVarSet_singleton in *
  || rewrite_extendVarSetList
  || rewrite delVarSetList_foldl in *.

(**************************************)

(* Q: is there a way to do the automatic destructs safely? Sometimes 
   loses too much information. *)

Ltac unfold_VarSet :=
  unfold subVarSet,elemVarSet, isEmptyVarSet, 
         minusVarSet, extendVarSet, extendVarSetList in *;
  unfold UniqSet.elementOfUniqSet, 
         UniqSet.isEmptyUniqSet, 
         UniqSet.addOneToUniqSet,
         UniqSet.minusUniqSet,
         UniqSet.addListToUniqSet in *;
  try repeat match goal with
  | vs: VarSet, H : context[match ?vs with _ => _ end]  |- _ => destruct vs
  end;
  try repeat match goal with
  | vs: VarSet |- context[match ?vs with _ => _ end ] => destruct vs
  end;

  unfold UniqFM.addToUFM, 
         UniqFM.minusUFM, UniqFM.isNullUFM, 
         UniqFM.elemUFM in *;
  try repeat match goal with
  | u: UniqFM.UniqFM ?a, H : context[match ?u with _ => _ end]  |- _ => destruct u
  end;
  try repeat match goal with
  | u: UniqFM.UniqFM ?a |- context[match ?u with _ => _ end] => destruct u
  end. 

Ltac safe_unfold_VarSet :=
  unfold subVarSet,elemVarSet, isEmptyVarSet, 
         minusVarSet, extendVarSet, extendVarSetList in *;
  unfold UniqSet.elementOfUniqSet, 
         UniqSet.isEmptyUniqSet, 
         UniqSet.addOneToUniqSet,
         UniqSet.minusUniqSet,
         UniqSet.addListToUniqSet in *;
  unfold UniqFM.addToUFM, 
         UniqFM.minusUFM, UniqFM.isNullUFM, 
         UniqFM.elemUFM in *.

(**************************************)

(** ** [extendVarSetList]  *)

Lemma extendVarSetList_nil:
  forall s,
  extendVarSetList s [] = s.
Proof.
  intro s.
  set_b_iff.
  reflexivity.
Qed.

Lemma extendVarSetList_cons:
  forall s v vs,
  extendVarSetList s (v :: vs) = extendVarSetList (extendVarSet s v) vs.
Proof.
  intros.
  set_b_iff.
  unfold_Foldable_foldl'.
  reflexivity.
Qed.


Lemma extendVarSetList_append:
  forall s vs1 vs2,
  extendVarSetList s (vs1 ++ vs2) = extendVarSetList (extendVarSetList s vs1) vs2.
Proof.
  intros.
  set_b_iff.
  rewrite Foldable_foldl'_app.
  auto.
Qed.

(** ** [elemVarSet]  *)

Lemma elemVarSet_emptyVarSet : forall v, elemVarSet v emptyVarSet = false.
  intro v.
  set_b_iff.
  fsetdec.
Qed.

Lemma elemVarSet_unionVarSet:
  forall v vs1 vs2,
  elemVarSet v (unionVarSet vs1 vs2) = elemVarSet v vs1 || elemVarSet v vs2.
Admitted.

Lemma elemVarSet_extendVarSetList_r:
  forall v vs1 vs2,
  elemVarSet v (mkVarSet vs2) = true ->
  elemVarSet v (extendVarSetList vs1 vs2) = true.
Admitted.


(** ** [extendVarSet]  *)



Lemma extendVarSet_elemVarSet_true : forall set v, 
    elemVarSet v set = true -> extendVarSet set v [=] set.
Proof. 
  intros.
  apply add_equal.
  auto.
Qed.


Lemma elemVarSet_extendVarSet:
  forall v vs v',
  elemVarSet v (extendVarSet vs v') = (v' GHC.Base.== v) || elemVarSet v vs.
Proof.
  intros.
  unfold_zeze.
  replace (realUnique v' =? realUnique v)%N with 
      (F.eqb v' v).
  eapply F.add_b.
  unfold F.eqb.
  destruct F.eq_dec.
  - unfold Var_as_DT.eq in e.
    rewrite <- realUnique_eq in e; auto.
  - unfold Var_as_DT.eq in n.
    rewrite <- realUnique_eq in n; apply not_true_is_false in n; auto.
Qed.


Lemma elemVarSet_mkVarSet_cons:
  forall v v' vs,
  elemVarSet v (mkVarSet (v' :: vs)) = false
  <-> (v' == v) = false /\ elemVarSet v (mkVarSet vs) = false.
Proof.
  intros.
  rewrite !mkVarSet_extendVarSetList.
  rewrite extendVarSetList_cons.
Admitted.

(** ** [delVarSet]  *)

Lemma delVarSet_elemVarSet_false : forall v set, 
    elemVarSet v set = false -> delVarSet set v [=] set.
intros.
set_b_iff.
apply remove_equal.
auto.
Qed.


Lemma delVarSet_extendVarSet : 
  forall set v, 
    elemVarSet v set = false -> 
    (delVarSet (extendVarSet set v) v) [=] set.
Proof.
  intros.
  set_b_iff.
  apply remove_add.
  auto.
Qed.

Lemma elemVarSet_delVarSet: forall v1 fvs v2,
  elemVarSet v1 (delVarSet fvs v2) = negb (v2 == v1) && elemVarSet v1 fvs.
Proof.
  intros.
  set_b_iff.
Admitted.

(** ** [delVarSetList]  *)

Lemma delVarSetList_nil:
  forall e, delVarSetList e [] = e.
Proof.
  intros. unfold delVarSetList, delVarSet.
  unfold UniqSet.delListFromUniqSet, UniqSet.delOneFromUniqSet.
  destruct e; reflexivity.
Qed.

Lemma delVarSetList_single:
  forall e a, delVarSetList e [a] = delVarSet e a.
Proof.
  intros. unfold delVarSetList, delVarSet.
  unfold UniqSet.delListFromUniqSet, UniqSet.delOneFromUniqSet.
  destruct e; reflexivity.
Qed.

Lemma delVarSetList_cons:
  forall e a vs, delVarSetList e (a :: vs) = delVarSetList (delVarSet e a) vs.
Proof.
  induction vs; try revert IHvs;
    unfold delVarSetList, UniqSet.delListFromUniqSet; destruct e;
      try reflexivity.
Qed.

Lemma delVarSetList_cons2:
  forall e a vs, delVarSetList e (a :: vs) = delVarSet (delVarSetList e vs) a.
Admitted.

Lemma delVarSetList_app:
  forall e vs vs', delVarSetList e (vs ++ vs') = delVarSetList (delVarSetList e vs) vs'.
Proof.
  induction vs'.
  - rewrite app_nil_r.
    unfold delVarSetList, UniqSet.delListFromUniqSet.
    destruct e; reflexivity.
  - intros.
    unfold delVarSetList, UniqSet.delListFromUniqSet; destruct e.
    unfold UniqFM.delListFromUFM.
Admitted.
(*
    repeat rewrite hs_coq_foldl_list. rewrite fold_left_app. reflexivity.
Qed. *)


Lemma delVarSetList_rev:
  forall vs1 vs2,
  delVarSetList vs1 (rev vs2) = delVarSetList vs1 vs2.
Admitted.


Lemma elemVarSet_delVarSetList_false_l:
  forall v vs vs2,
  elemVarSet v vs = false ->
  elemVarSet v (delVarSetList vs vs2) = false.
Proof.
  intros.
  revert vs H; induction vs2; intros.
  * rewrite delVarSetList_nil.
    assumption.
  * rewrite delVarSetList_cons.
    apply IHvs2.
    set_b_iff; fsetdec.
Qed.

(**************************************)


(** ** [subVarSet]  *)
  
Lemma subVarSet_refl:
  forall vs1,
  subVarSet vs1 vs1 = true.
Proof.
  intros.
  set_b_iff.
  fsetdec.
Qed.

Lemma subVarSet_trans:
  forall vs1 vs2 vs3,
  subVarSet vs1 vs2 = true ->
  subVarSet vs2 vs3 = true ->
  subVarSet vs1 vs3 = true.
Proof.
  intros.
  set_b_iff.
  fsetdec.
Qed.


Lemma subVarSet_emptyVarSet:
  forall vs,
  subVarSet emptyVarSet vs = true.
Proof.
  intros.
  set_b_iff.
  fsetdec.
Qed.

Lemma elemVarSet_unitVarSet: forall v1 v2,
  (elemVarSet v1 (unitVarSet v2) = true) <-> (varUnique v1 = varUnique v2).
Proof.
  intros v1 v2.
  set_b_iff.
  rewrite singleton_iff.
  unfold Var_as_DT.eqb.
  unfold_zeze.
Admitted.
  

Lemma elemVarSet_false_true:
  forall v1 fvs v2,
  elemVarSet v1 fvs = false ->
  elemVarSet v2 fvs = true ->
  varUnique v1 <> varUnique v2.
Proof.
  intros v1 fvs v2.
  set_b_iff.
  intros.
Admitted.
  

Lemma subVarSet_elemVarSet_true:
  forall v vs vs',
  subVarSet vs vs' = true ->
  elemVarSet v vs = true ->
  elemVarSet v vs' = true.
Proof.
  intros v vs vs'.
  set_b_iff.
  fsetdec.
Qed.

Lemma subVarSet_elemVarSet_false:
  forall v vs vs',
  subVarSet vs vs' = true ->
  elemVarSet v vs' = false ->
  elemVarSet v vs = false.
Proof.
  intros v vs vs'.
  set_b_iff.
  fsetdec.
Qed.

Lemma subVarSet_extendVarSetList_l:
  forall vs1 vs2 vs,
  subVarSet vs1 vs2 = true ->
  subVarSet vs1 (extendVarSetList vs2 vs) = true.
Proof.
  intros vs1 vs2 vs.
  generalize vs2. clear vs2.
  induction vs.
  - intro vs2. rewrite extendVarSetList_nil. auto.
  - intro vs2. intro h. 
    rewrite extendVarSetList_cons. 
    rewrite IHvs. auto. 
    set_b_iff. fsetdec.
Qed.

Lemma subVarSet_extendVarSetList_r:
  forall vs vs1 vs2,
  subVarSet vs1 (mkVarSet vs) = true ->
  subVarSet vs1 (extendVarSetList vs2 vs) = true.
Proof.
  intros vs. 
  induction vs; intros vs1 vs2.
  - set_b_iff.
    unfold_Foldable_foldl'.
    simpl.
    fsetdec.
  - intro h. 
    rewrite mkVarSet_extendVarSetList in h.
    rewrite extendVarSetList_cons in *.
Admitted.
    


Lemma subVarSet_extendVarSet_both:
  forall vs1 vs2 v,
  subVarSet vs1 vs2 = true ->
  subVarSet (extendVarSet vs1 v) (extendVarSet vs2 v) = true.
Proof.
  intros.
  set_b_iff.
  fsetdec.
Qed.

Lemma subVarSet_extendVarSet:
  forall vs1 vs2 v,
  subVarSet vs1 vs2 = true ->
  subVarSet vs1 (extendVarSet vs2 v) = true.
Proof.
  intros.
  set_b_iff.
  fsetdec.
Qed.

Lemma subVarSet_extendVarSetList:
  forall vs1 vs2 vs3,
  subVarSet vs1 vs2 = true ->
  subVarSet vs1 (extendVarSetList vs2 vs3) = true.
Admitted.

Lemma subVarSet_extendVarSet_l:
  forall vs1 vs2 v v',
  subVarSet vs1 vs2 = true ->
  lookupVarSet vs2 v = Some v' ->
  subVarSet (extendVarSet vs1 v) vs2 = true.
Admitted.

Lemma subVarSet_delVarSet:
  forall vs1 v,
  subVarSet (delVarSet vs1 v) vs1 = true.
Proof.
  intros.
  set_b_iff.
  fsetdec.
Qed.


Lemma subVarSet_delVarSetList:
  forall vs1 vl,
  subVarSet (delVarSetList vs1 vl) vs1 = true.
Proof.
  intros.
  set_b_iff.
  generalize vs1. clear vs1. induction vl.
  - intros vs1. unfold_Foldable_foldl.
    simpl.
    fsetdec.
  - intros vs1. revert IHvl.
    unfold_Foldable_foldl.
    simpl.
    intro IH. 
    rewrite IH with (vs1 := delVarSet vs1 a).
    set_b_iff.
    fsetdec.
Qed.


Lemma subVarSet_delVarSetList_both:
  forall vs1 vs2 vl,
  subVarSet vs1 vs2 = true ->
  subVarSet (delVarSetList vs1 vl) (delVarSetList vs2 vl) = true.
Proof.
  intros.
  revert vs1 vs2 H. induction vl; intros.
  - rewrite !delVarSetList_nil.
    assumption.
  - rewrite !delVarSetList_cons.
    apply IHvl.
    set_b_iff.
    fsetdec.
Qed.

Lemma subVarSet_delVarSet_extendVarSet:
  forall jps isvs v,
  subVarSet jps isvs = true ->
  subVarSet (delVarSet jps v) (extendVarSet isvs v) = true.
Proof.
  intros.
  eapply subVarSet_trans.
  apply subVarSet_delVarSet.
  apply subVarSet_extendVarSet.
  assumption.
Qed.

Lemma subVarSet_delVarSetList_extendVarSetList:
  forall jps isvs vs,
  subVarSet jps isvs = true ->
  subVarSet (delVarSetList jps vs) (extendVarSetList isvs vs) = true.
Proof.
  intros.
  eapply subVarSet_trans.
  apply subVarSet_delVarSetList.
  apply subVarSet_extendVarSetList.
  assumption.
Qed.


Lemma mapUnionVarSet_In_subVarSet:
  forall a (x : a) xs f,
  List.In x xs ->
  subVarSet (f x) (mapUnionVarSet f xs) = true.
Admitted.

(** ** [mkVarSet]  *)


Lemma elemVarSet_mkVarset_iff_In:
  forall v vs,
  elemVarSet v (mkVarSet vs) = true <->  List.In (varUnique v) (map varUnique vs).
Proof.
  intros.
  set_b_iff.
  remember (mkVarSet vs) as vss.
  unfold_VarSet.
  rewrite <- getUnique_varUnique.
  rewrite unique_In.
  set (key := (Unique.getWordKey (Unique.getUnique v))).
  (* Need theory about IntMap. *)
Admitted. 

(** ** [disjointVarSet]  *)


Axiom disjointVarSet_mkVarSet:
  forall vs1 vs2,
  disjointVarSet vs1 (mkVarSet vs2) = true <->
  Forall (fun v => elemVarSet v vs1 = false) vs2.

Axiom disjointVarSet_mkVarSet_append:
  forall vs1 vs2 vs3,
  disjointVarSet vs1 (mkVarSet (vs2 ++ vs3)) = true <->
  disjointVarSet vs1 (mkVarSet vs2) = true /\ disjointVarSet vs1 (mkVarSet vs3) = true.

Axiom disjointVarSet_mkVarSet_cons:
  forall v vs1 vs2,
  disjointVarSet vs1 (mkVarSet (v :: vs2)) = true <->
  elemVarSet v vs1 = false /\ disjointVarSet vs1 (mkVarSet vs2) = true.


Axiom disjointVarSet_subVarSet_l:
  forall vs1 vs2 vs3,
  disjointVarSet vs2 vs3 = true ->
  subVarSet vs1 vs2 = true ->
  disjointVarSet vs1 vs3 = true.

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

(** ** [uniqAway] *)

Axiom isJoinId_maybe_uniqAway:
  forall s v, 
  isJoinId_maybe (uniqAway s v) = isJoinId_maybe v.

(* See discussion of [isLocalUnique] in [Proofs.Unique] *)
Axiom isLocalUnique_uniqAway:
  forall iss v,
  isLocalUnique (varUnique (uniqAway iss v)) = true.


Lemma elemVarSet_uniqAway:
  forall v iss vs,
  subVarSet vs (getInScopeVars iss) = true ->
  elemVarSet (uniqAway iss v) vs = false.
Proof.
  intros.
  safe_unfold_VarSet.
  destruct vs.
  destruct iss.
  destruct v0.
  destruct u.
  destruct u0.
  simpl in *.
  unfold uniqAway.
  unfold elemInScopeSet.
  unfold elemVarSet.
  unfold uniqAway'.
  unfold realUnique.
Admitted.

(** ** [lookupVarSet] *)

Lemma lookupVarSet_elemVarSet : 
  forall v1 v2 vs, lookupVarSet vs v1 = Some v2 -> elemVarSet v1 vs = true.
Admitted.

Lemma lookupVarSet_None_elemVarSet: 
  forall v1 vs, lookupVarSet vs v1 = None <-> elemVarSet v1 vs = false.
Admitted.

Lemma elemVarSet_lookupVarSet :
  forall v1 vs, elemVarSet v1 vs = true -> exists v2, lookupVarSet vs v1 = Some v2.
Admitted.



Lemma lookupVarSet_extendVarSet_self:
  forall v vs,
  lookupVarSet (extendVarSet vs v) v = Some v.
Admitted.

(** ** Compatibility with [GHC.Base.==] *)

Lemma lookupVarSet_extendVarSet_eq :
      forall v1 v2 vs,
      v1 GHC.Base.== v2 = true ->
      lookupVarSet (extendVarSet vs v1) v2 = Some v1.
Proof.
  intros.
  unfold lookupVarSet, extendVarSet.
  unfold UniqSet.lookupUniqSet, UniqSet.addOneToUniqSet.
  destruct vs.
  unfold UniqFM.lookupUFM, UniqFM.addToUFM.
  destruct u.
  unfold GHC.Base.op_zeze__, Eq___Var, Base.op_zeze____, 
  Core.Eq___Var_op_zeze__ in H.
Admitted.

Axiom lookupVarSet_extendVarSet_neq :
      forall v1 v2 vs,
      not (v1 GHC.Base.== v2 = true) ->
      lookupVarSet (extendVarSet vs v1) v2 = lookupVarSet vs v2.

Axiom lookupVarSet_delVarSet_neq :
      forall v1 v2 vs,
      not (v1 GHC.Base.== v2 = true) ->
      lookupVarSet (delVarSet vs v1) v2 = lookupVarSet vs v2.


(*
Lemma lookupVarSet_eq :
  forall v1 v2 vs var,
    (v1 GHC.Base.== v2) = true ->
    lookupVarSet vs v1 = Some var ->
    lookupVarSet vs v2 = Some var. 
Proof.
  intros.
  unfold lookupVarSet in *.
  unfold UniqSet.lookupUniqSet in *. destruct vs. 
  unfold UniqFM.lookupUFM in *. destruct u.
Admitted.
*)

Axiom lookupVarSet_eq :
  forall v1 v2 vs,
    (v1 GHC.Base.== v2) = true ->
    lookupVarSet vs v1 = lookupVarSet vs v2.

Lemma elemVarSet_eq : forall v1 v2 vs,
  (v1 GHC.Base.== v2) = true -> 
  elemVarSet v1 vs = elemVarSet v2 vs.
Admitted.


(** ** [filterVarSet] *)

Lemma filterVarSet_comp : forall f f' vs,
    filterVarSet f (filterVarSet f' vs) = filterVarSet (fun v => f v && f' v) vs.
Proof.
  intros. destruct vs; destruct u. simpl. do 2 f_equal.
Admitted.

(** ** Compatibility with [almostEqual] *)

Lemma lookupVarSet_ae : 
  forall vs v1 v2, 
    almostEqual v1 v2 -> 
    lookupVarSet vs v1 = lookupVarSet vs v2.
Proof. 
  induction 1; simpl; unfold UniqFM.lookupUFM; simpl; auto.
Qed.

Lemma delVarSet_ae:
  forall vs v1 v2,
  almostEqual v1 v2 ->
  delVarSet vs v1 = delVarSet vs v2.
Proof.
  induction 1; simpl;
  unfold UniqFM.delFromUFM; simpl; auto.
Qed.

Lemma elemVarSet_ae:
  forall vs v1 v2,
  almostEqual v1 v2 ->
  elemVarSet v1 vs = elemVarSet v2 vs.
Proof.
  induction 1; simpl;
  unfold UniqFM.delFromUFM; simpl; auto.
Qed.

(** ** [StrongSubset] *)


(* A strong subset doesn't just have a subset of the uniques, but 
     also requires that the variables in common be almostEqual. *)
Definition StrongSubset (vs1 : VarSet) (vs2: VarSet) := 
  forall var, match lookupVarSet vs1 var with 
           | Some v =>  match lookupVarSet vs2 var with
                          | Some v' => almostEqual v v'
                          | None => False
                       end
           | None => True 
         end.

Require Import Coq.Classes.RelationClasses.

Axiom StrongSubset_refl : forall vs, 
    StrongSubset vs vs.

Instance StrongSubset_Reflexive : Reflexive StrongSubset := StrongSubset_refl.

Axiom StrongSubset_trans : forall vs1 vs2 vs3, 
    StrongSubset vs1 vs2 -> StrongSubset vs2 vs3 -> StrongSubset vs1 vs3.

Instance StrongSubset_Transitive : Transitive StrongSubset := StrongSubset_trans.


Lemma strongSubset_implies_subset :
  forall vs1 vs2 , 
    StrongSubset vs1 vs2 -> vs1 [<=] vs2.
Proof. 
  intros vs1 vs2.
  unfold StrongSubset, Subset.
  intros SS var IN.
  unfold In in *.
  specialize (SS var). 
  destruct (lookupVarSet vs1 var) eqn:VS1;
  destruct (lookupVarSet vs2 var) eqn:VS2; try contradiction.
  - apply lookupVarSet_elemVarSet in VS2.   
    auto.
  - apply elemVarSet_lookupVarSet in IN. destruct IN.
    rewrite VS1 in H. discriminate.
  - apply elemVarSet_lookupVarSet in IN. destruct IN.
    rewrite VS1 in H. discriminate.
Qed.



Lemma StrongSubset_extend_fresh :
  forall vs v,
  lookupVarSet vs v = None ->
  StrongSubset vs (extendVarSet vs v).
Proof.
  intros.
  unfold StrongSubset.
  intros var.
  destruct (var == v) eqn:EQV.
  rewrite lookupVarSet_eq with (v2 := v); auto.
  rewrite H. auto.
  destruct (lookupVarSet vs var) eqn:Lvar; auto.
  rewrite lookupVarSet_extendVarSet_neq.
  rewrite Lvar.
  apply almostEqual_refl.
  unfold CoreBndr in *. intro h. rewrite Base.Eq_sym in h. rewrite h in EQV. discriminate.
Qed.

Lemma StrongSubset_extendList_fresh :
  forall vs vs2,
  disjointVarSet vs (mkVarSet vs2) = true ->
  StrongSubset vs (extendVarSetList vs vs2).
Proof.
  intros.
  unfold StrongSubset.
  intros v.
  destruct_match; try trivial.
  destruct_match.
  * admit.
  * admit.
Admitted.


Lemma StrongSubset_extend :
  forall vs1 vs2 v,
  StrongSubset vs1 vs2 ->
  StrongSubset (extendVarSet vs1 v) (extendVarSet vs2 v).
Proof.
  intros.
  unfold StrongSubset in *.
  intro var.
  destruct (v == var) eqn:EQv.
  rewrite lookupVarSet_extendVarSet_eq; auto.  
  rewrite lookupVarSet_extendVarSet_eq.
  apply almostEqual_refl.
  auto.
  rewrite lookupVarSet_extendVarSet_neq; auto.
  rewrite lookupVarSet_extendVarSet_neq; auto.
  eapply H.
  unfold CoreBndr in *.
  unfold not. intro. rewrite EQv in H0. discriminate.
  unfold CoreBndr in *.
  unfold not. intro. rewrite EQv in H0. discriminate.
Qed.


Lemma StrongSubset_extendVarSetList :
  forall l vs1 vs2,
  StrongSubset vs1 vs2 ->
  StrongSubset (extendVarSetList vs1 l) (extendVarSetList vs2 l).
Proof.
  induction l; intros vs1 vs2 h.
  repeat rewrite extendVarSetList_nil.
  auto.
  rewrite extendVarSetList_cons.
  rewrite extendVarSetList_cons.
  eapply IHl.
  unfold StrongSubset.
  intro var.
  destruct (a GHC.Base.== var) eqn:Eq.
  + rewrite lookupVarSet_extendVarSet_eq; auto.
    rewrite lookupVarSet_extendVarSet_eq; auto.
    eapply almostEqual_refl.
  + rewrite lookupVarSet_extendVarSet_neq.
    destruct (lookupVarSet vs1 var) eqn:IN; auto.
    rewrite lookupVarSet_extendVarSet_neq.
    unfold StrongSubset in h. 
    specialize (h var). rewrite IN in h. auto.
    intro h1;
      rewrite h1 in Eq; discriminate.
    intro h1;
      rewrite h1 in Eq; discriminate.
Qed.


Lemma StrongSubset_delVarSet :
  forall vs1 vs2 v,
  StrongSubset vs1 vs2 ->
  StrongSubset (delVarSet vs1 v) (delVarSet vs2 v).
Admitted.

Lemma StrongSubset_delete_fresh :
  forall vs v,
  lookupVarSet vs v = None ->
  StrongSubset vs (delVarSet vs v).
Admitted.

Definition Respects_StrongSubset P :=
  forall (vs1 vs2 : VarSet),
  StrongSubset vs1 vs2 ->
  P vs1 -> P vs2.
Existing Class Respects_StrongSubset.

(* Is this weakening? *)
Lemma weaken:
  forall {P : VarSet -> Prop} {R : Respects_StrongSubset P},
  forall {vs1} {vs2},
  StrongSubset vs1 vs2 ->
  P vs1 -> P vs2.
Proof. intros. unfold Respects_StrongSubset in R. eapply R; eassumption. Qed.

Lemma weakenb:
  forall {P : VarSet -> bool} {R : Respects_StrongSubset (fun x => P x = true)},
  forall {vs1} {vs2},
  StrongSubset vs1 vs2 ->
  P vs1 = true -> P vs2 = true.
Proof. intros. unfold Respects_StrongSubset in R. eapply R; eassumption. Qed.
