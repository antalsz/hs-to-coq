Require Import GHC.Base.
Require Import CoreFVs.
Require Import Id.
Require Import Core.

Require Import Proofs.GHC.Base.
Require Import Proofs.GHC.List.

Require Import Psatz.
Require Import Coq.Lists.List.
Require Import Coq.NArith.BinNat.

Import ListNotations.

Open Scope Z_scope.

Set Bullet Behavior "Strict Subproofs".

Require Import Proofs.GhcTactics.
Require Import Proofs.Base.
Require Import Proofs.ContainerAxioms.
Require Import Proofs.Unique.
Require Import Proofs.Var.

Require Import IntSetProofs.
(* Require Import IntMapProofs. *)


(** ** [VarSet] *)

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


Lemma extendVarSetList_nil:
  forall s,
  extendVarSetList s [] = s.
Proof.
  intro s. 
  repeat unfold_VarSet.
  unfold_Foldable_foldl'.
  reflexivity.
Qed.

Lemma extendVarSetList_cons:
  forall s v vs,
  extendVarSetList s (v :: vs) = extendVarSetList (extendVarSet s v) vs.
Proof.
  intros.
  repeat unfold_VarSet.
  unfold_Foldable_foldl'.
  reflexivity.
Qed.



Lemma extendVarSetList_append:
  forall s vs1 vs2,
  extendVarSetList s (vs1 ++ vs2) = extendVarSetList (extendVarSetList s vs1) vs2.
Proof.
  intros.
  repeat unfold_VarSet.
  rewrite Foldable_foldl'_app.
  auto.
Qed.

Lemma elemVarSet_mkVarset_iff_In:
  forall v vs,
  elemVarSet v (mkVarSet vs) = true <->  In (varUnique v) (map varUnique vs).
Proof.
  intros.
  remember (mkVarSet vs) as vss.
  unfold_VarSet.
  rewrite <- getUnique_varUnique.
  rewrite unique_In.
  set (key := (Unique.getWordKey (Unique.getUnique v))).
  (* Need theory about IntMap. *)
Admitted. 

Lemma lookupVarSet_extendVarSet_self:
  forall v vs,
  lookupVarSet (extendVarSet vs v) v = Some v.
Admitted.


Lemma elemVarSet_extendVarSet:
  forall v vs v',
  elemVarSet v (extendVarSet vs v') = (varUnique v == varUnique v') || elemVarSet v vs.
Proof.
  intros.
  safe_unfold_VarSet.
  destruct vs.
  destruct u.
  rewrite unique_word.
  rewrite <- getUnique_varUnique.
  apply member_insert.
Qed.
  
Lemma subVarSet_refl:
  forall vs1,
  subVarSet vs1 vs1 = true.
Proof.
  intros.
  safe_unfold_VarSet.
  destruct vs1.
  destruct u.
  rewrite difference_self.
  apply null_empty.
Qed.

Axiom elemVarSet_unitVarSet: forall v1 v2,
  (elemVarSet v1 (unitVarSet v2) = true) <-> (varUnique v1 = varUnique v2).
Axiom elemVarSet_delVarSet: forall v1 fvs v2,
  elemVarSet v1 (delVarSet fvs v2) = true <-> (varUnique v1 <> varUnique v2 /\ elemVarSet v1 fvs = true).
Axiom elemVarSet_false_true:
  forall v1 fvs v2,
  elemVarSet v1 fvs = false ->
  elemVarSet v2 fvs = true ->
  varUnique v1 <> varUnique v2.


Lemma subVarSet_elemVarSet_true:
  forall v vs vs',
  subVarSet vs vs' = true ->
  elemVarSet v vs = true ->
  elemVarSet v vs' = true.
Proof.
  intros.
  safe_unfold_VarSet.
  destruct vs.
  destruct vs'.
  destruct u.
  destruct u0.
  set (key := Unique.getWordKey (Unique.getUnique v)) in *.
Admitted.

Axiom subVarSet_elemVarSet_false:
  forall v vs vs',
  subVarSet vs vs' = true ->
  elemVarSet v vs' = false ->
  elemVarSet v vs = false.

Axiom subVarSet_extendVarSetList_l:
  forall vs1 vs2 vs,
  subVarSet vs1 vs2 = true ->
  subVarSet vs1 (extendVarSetList vs2 vs) = true.

Axiom subVarSet_extendVarSetList_r:
  forall vs1 vs2 vs,
  subVarSet vs1 (mkVarSet vs) = true ->
  subVarSet vs1 (extendVarSetList vs2 vs) = true.


Axiom subVarSet_extendVarSet:
  forall vs1 vs2 v,
  subVarSet vs1 vs2 = true ->
  subVarSet vs1 (extendVarSet vs2 v) = true.

Axiom subVarSet_delVarSetList:
  forall vs1 vs2,
  subVarSet (delVarSetList vs1 vs2) vs1 = true.

Axiom disjointVarSet_mkVarSet:
  forall vs1 vs2,
  disjointVarSet vs1 (mkVarSet vs2) = true <->
  Forall (fun v => elemVarSet v vs1 = false) vs2.

Axiom disjointVarSet_subVarSet_l:
  forall vs1 vs2 vs3,
  disjointVarSet vs2 vs3 = true ->
  subVarSet vs1 vs2 = true ->
  disjointVarSet vs1 vs3 = true.

(** ** [InScopeVars] *)

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
  unfold_VarSet.
  destruct iss.
  unfold_Foldable_foldl'.
  unfold_Foldable_foldl.
  f_equal.
Qed.

(** ** [uniqAway] *)

Axiom isJoinId_maybe_uniqAway:
  forall s v, 
  isJoinId_maybe (uniqAway s v) = isJoinId_maybe v.



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

