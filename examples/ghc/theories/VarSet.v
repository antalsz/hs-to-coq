Require Import GHC.Base.
Require Import CoreFVs.
Require Import Id.
Require Import Core.
Require UniqFM.

Import GHC.Base.ManualNotations.

Require Import Proofs.GHC.Base.
Require Import Proofs.GHC.List.
Require Import Proofs.Data.Foldable.

Require Import Psatz.
Require Import Coq.Lists.List.
Require Import Coq.NArith.BinNat.

Import ListNotations.

Require Import Proofs.GhcTactics.
Require Import Proofs.Unique.
Require Import Proofs.Var.

(* Require Import Proofs.ContainerAxioms.
   Require Import IntSetProofs.  *)

Require Import Proofs.VarSetFSet.


Require Import Coq.Classes.RelationClasses.


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

Lemma extendVarSetList_singleton:
  forall vs v, extendVarSetList vs [v] = extendVarSet vs v.
Proof. intros. reflexivity. Qed.


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

Lemma delVarSetList_unionVarSet:
  forall vs1 vs2 vs3,
  delVarSetList (unionVarSet vs1 vs2) vs3 [=] 
  unionVarSet (delVarSetList vs1 vs3) (delVarSetList vs2 vs3).
Admitted.


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

Lemma subVarSet_unitVarSet:
  forall v vs,
  subVarSet (unitVarSet v) vs = elemVarSet v vs.
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

Lemma subVarSet_delVarSetList_extendVarSetList_dual:
  forall jps isvs vs,
  subVarSet jps (extendVarSetList isvs vs) = true ->
  subVarSet (delVarSetList jps vs) isvs = true.
Admitted.

Lemma mapUnionVarSet_In_subVarSet:
  forall a (x : a) xs f,
  List.In x xs ->
  subVarSet (f x) (mapUnionVarSet f xs) = true.
Admitted.

Lemma subVarSet_mapUnionVarSet:
  forall a (xs : list a) f vs,
  Forall (fun x => subVarSet (f x) vs = true) xs ->
  subVarSet (mapUnionVarSet f xs) vs = true.
Admitted.


Lemma subVarSet_unionVarSet:
  forall vs1 vs2 vs3,
  subVarSet (unionVarSet vs1 vs2) vs3 = subVarSet vs1 vs3 && subVarSet vs2 vs3.
Proof.
  intros.
  apply eq_iff_eq_true.
  rewrite andb_true_iff.
  set_b_iff.
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

Axiom disjointVarSet_mkVarSet_nil:
  forall vs,
  disjointVarSet vs (mkVarSet []) = true.


Axiom disjointVarSet_mkVarSet_cons:
  forall v vs1 vs2,
  disjointVarSet vs1 (mkVarSet (v :: vs2)) = true <->
  elemVarSet v vs1 = false /\ disjointVarSet vs1 (mkVarSet vs2) = true.

Axiom disjointVarSet_mkVarSet_append:
  forall vs1 vs2 vs3,
  disjointVarSet vs1 (mkVarSet (vs2 ++ vs3)) = true <->
  disjointVarSet vs1 (mkVarSet vs2) = true /\ disjointVarSet vs1 (mkVarSet vs3) = true.


Axiom disjointVarSet_subVarSet_l:
  forall vs1 vs2 vs3,
  disjointVarSet vs2 vs3 = true ->
  subVarSet vs1 vs2 = true ->
  disjointVarSet vs1 vs3 = true.


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


Lemma lookupVarSet_extendVarSetList_l:
  forall v vs1 vs2,
  elemVarSet v (mkVarSet vs2) = false ->
  lookupVarSet (extendVarSetList vs1 vs2) v = lookupVarSet vs1 v.
Admitted.

Lemma lookupVarSet_extendVarSetList_r_self:
  forall v vs1 vs2,
  List.In v vs2 ->
  NoDup (map varUnique vs2) ->
  lookupVarSet (extendVarSetList vs1 vs2) v = Some v.
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


Notation "s1 {<=} s2" := (StrongSubset s1 s2) (at level 70, no associativity).
Notation "s1 {=} s2" := (StrongSubset s1 s2 /\ StrongSubset s2 s1) (at level 70, no associativity).


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


Lemma StrongSubset_extend_ae :
  forall vs1 vs2 v1 v2,
  StrongSubset vs1 vs2 ->
  almostEqual v1 v2 ->
  StrongSubset (extendVarSet vs1 v1) (extendVarSet vs2 v2).
Proof.
  intros.
  unfold StrongSubset in *.
  intro var.
  destruct (v1 == var) eqn:EQv.
  rewrite lookupVarSet_extendVarSet_eq; auto.  
  rewrite lookupVarSet_extendVarSet_eq.
  assumption.
  apply almostEqual_eq in H0. eapply Eq_trans; try eassumption; try symmetry; assumption.
  rewrite lookupVarSet_extendVarSet_neq; auto.
  rewrite lookupVarSet_extendVarSet_neq; auto.
  eapply H.
  rewrite <- not_true_iff_false in EQv. contradict EQv.
  apply almostEqual_eq in H0. eapply Eq_trans; try eassumption; try symmetry; assumption.
  rewrite not_true_iff_false. assumption.
Qed.


Lemma StrongSubset_extend :
  forall vs1 vs2 v,
  StrongSubset vs1 vs2 ->
  StrongSubset (extendVarSet vs1 v) (extendVarSet vs2 v).
Proof.
  intros.
  apply StrongSubset_extend_ae.
  * assumption.
  * apply almostEqual_refl.
Qed.

Lemma StrongSubset_extendVarSetList_ae :
  forall l1 l2 vs1 vs2,
  Forall2 almostEqual l1 l2 ->
  StrongSubset vs1 vs2 ->
  StrongSubset (extendVarSetList vs1 l1) (extendVarSetList vs2 l2).
Proof.
  intros.
  revert vs1 vs2 H0. induction H; intros.
  * apply H0.
  * rewrite extendVarSetList_cons.
    apply IHForall2.
    apply StrongSubset_extend_ae; assumption.
Qed.

Lemma Forall2_diag:
  forall a P (xs: list a),
  Forall2 P xs xs <-> Forall (fun x => P x x) xs.
Proof.
  intros.
  induction xs.
  * split; intro; constructor.
  * split; intro H; constructor; inversion H; intuition.
Qed.

Lemma StrongSubset_extendVarSetList :
  forall l vs1 vs2,
  StrongSubset vs1 vs2 ->
  StrongSubset (extendVarSetList vs1 l) (extendVarSetList vs2 l).
Proof.
  intros.
  apply StrongSubset_extendVarSetList_ae; only 2: assumption.
  apply Forall2_diag.
  rewrite Forall_forall. intros. apply almostEqual_refl.
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

(* Respects_StrongSubset *)

Definition Respects_StrongSubset (P : VarSet -> Prop) : Prop :=
  forall (vs1 vs2 : VarSet),
  StrongSubset vs1 vs2 ->
  P vs1 -> P vs2.
Existing Class Respects_StrongSubset.

Require Import Coq.Classes.Morphisms.
Global Instance Respects_StrongSubset_iff_morphism:
  Proper (pointwise_relation VarSet iff ==> iff) Respects_StrongSubset.
Proof.
  intros ???.
  split; intros ?????;
  unfold pointwise_relation in H;
  firstorder.
Qed.

Lemma Respects_StrongSubset_const:
  forall P, Respects_StrongSubset (fun _ => P).
Proof. intros ?????. assumption. Qed.

Lemma Respects_StrongSubset_and:
  forall P Q,
    Respects_StrongSubset P ->
    Respects_StrongSubset Q ->
    Respects_StrongSubset (fun x => P x /\ Q x).
Proof.
  unfold Respects_StrongSubset in *.
  intros ????????.
  firstorder.
Qed.


Lemma Respects_StrongSubset_andb:
  forall P Q,
    Respects_StrongSubset (fun x => P x = true) ->
    Respects_StrongSubset (fun x => Q x = true) ->
    Respects_StrongSubset (fun x => P x && Q x = true).
Proof.
  unfold Respects_StrongSubset in *.
  intros ????????.
  simpl_bool.
  firstorder.
Qed.


Lemma Respects_StrongSubset_forall:
  forall a (xs : list a) P,
    Forall (fun x => Respects_StrongSubset (fun vs => P vs x)) xs ->
    Respects_StrongSubset (fun vs => Forall (P vs) xs).
Proof.
  unfold Respects_StrongSubset in *.
  intros.
  rewrite Forall_forall in *.
  firstorder.
Qed.

Lemma Respects_StrongSubset_forallb:
  forall a (xs : list a) P,
    Forall (fun x => Respects_StrongSubset (fun vs => P vs x = true)) xs ->
    Respects_StrongSubset (fun vs => forallb (P vs) xs = true).
Proof.
  unfold Respects_StrongSubset in *.
  intros.
  rewrite forallb_forall in *.
  rewrite Forall_forall in *.
  firstorder.
Qed.


Lemma Respects_StrongSubset_elemVarSet:
  forall v,
  Respects_StrongSubset (fun vs => elemVarSet v vs = true).
Proof.
  intros ????.
  simpl_bool; intuition.
  apply strongSubset_implies_subset in H.
  set_b_iff; fsetdec.
Qed.

Lemma Respects_StrongSubset_delVarSet:
  forall v P,
  Respects_StrongSubset (fun vs : VarSet => P vs) ->
  Respects_StrongSubset (fun vs : VarSet => P (delVarSet vs v)).
Admitted.

Lemma Respects_StrongSubset_delVarSetList:
  forall vs2 P,
  Respects_StrongSubset (fun vs : VarSet => P vs) ->
  Respects_StrongSubset (fun vs : VarSet => P (delVarSetList vs vs2)).
Admitted. (* This is tricky, because of rewriting under a binder :-( *)

Lemma Respects_StrongSubset_extendVarSet:
  forall v P,
  Respects_StrongSubset (fun vs : VarSet => P vs) ->
  Respects_StrongSubset (fun vs : VarSet => P (extendVarSet vs v)).
Admitted.

Lemma Respects_StrongSubset_extendVarSetList:
  forall v P,
  Respects_StrongSubset (fun vs : VarSet => P vs) ->
  Respects_StrongSubset (fun vs : VarSet => P (extendVarSetList vs v)).
Admitted. (* This is tricky, because of rewriting under a binder :-( *)


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

Lemma Respects_StrongSubset_extendVarSet_ae:
  forall {P : VarSet -> Prop} {R : Respects_StrongSubset P},
  forall vs v1 v2,
  almostEqual v1 v2 ->
  P (extendVarSet vs v1) <-> P (extendVarSet vs v2).
Proof.
  intros.
  split; apply R; (apply StrongSubset_extend_ae;
    [ reflexivity | assumption + (apply almostEqual_sym; assumption) ]).
Qed.


Lemma Respects_StrongSubset_extendVarSetList_ae:
  forall {P : VarSet -> Prop} {R : Respects_StrongSubset P},
  forall vs vs1 vs2,
  Forall2 almostEqual vs1 vs2 ->
  P (extendVarSetList vs vs1) <-> P (extendVarSetList vs vs2).
Proof.
  split; apply R; apply StrongSubset_extendVarSetList_ae.
  * assumption.
  * reflexivity.
  * clear -H.
    induction H; constructor.
    + apply almostEqual_sym; assumption.
    + assumption.
  * reflexivity.
Qed.



(* We could axiomatize these in terms of In, but that would not be strong 
   enough. As lookup is keyed on the uniques only, we need to specify 
   list membership via Var's == only. *)

Lemma lookupVarSet_extendVarSetList_self:
  forall (vars:list Var) v vs,
    Foldable.elem v vars = true -> 
    lookupVarSet (extendVarSetList vs vars) v = Some v.
Admitted.

Lemma lookupVarSet_extendVarSetList_false:
  forall (vars:list Var) v vs,
    not (Foldable.elem v vars = true) -> 
    lookupVarSet (extendVarSetList vs vars) v = lookupVarSet vs v.
Admitted.


(* A list of variables is fresh for a given varset when 
   any variable with a unique found in the list is not found 
   in the set. i.e. this is list membership using GHC.Base.==
   for vars. 
*)

Definition freshList (vars: list Var) (vs :VarSet) :=
  (forall (v:Var), Foldable.elem v vars = true -> 
              lookupVarSet vs v = None).

Lemma freshList_nil : forall v,  freshList nil v.
Proof.
  unfold freshList. intros v v0 H. inversion H.
Qed.

Lemma freshList_cons : forall (x:Var) l (v:VarSet),  
    lookupVarSet v x= None /\ freshList l v <-> freshList (x :: l) v.
Proof.
  unfold freshList. intros. 
  split. 
  + intros [? ?] ? ?.
    rewrite elem_cons in H1.
    destruct (orb_prop _ _ H1) as [EQ|IN].
    rewrite lookupVarSet_eq with (v2 := x); auto.
    eauto.
  + intros. split.
    eapply H. 
    rewrite elem_cons.
    eapply orb_true_intro.
    left. eapply Base.Eq_refl.
    intros.
    eapply H.
    rewrite elem_cons.
    eapply orb_true_intro.
    right. auto.
Qed.


Lemma freshList_app :
  forall v l1 l2, freshList (l1 ++ l2) v <-> freshList l1 v /\ freshList l2 v.
Proof.
  intros.
  induction l1; simpl.
  split.
  intros. split. apply freshList_nil. auto.
  tauto.
  split.
  + intros.
    rewrite <- freshList_cons in *. tauto. 
  + intros.
    rewrite <- freshList_cons in *. tauto.
Qed.
    
Lemma StrongSubset_extendVarSet_fresh : 
  forall vs var, lookupVarSet vs var = None ->
            StrongSubset vs (extendVarSet vs var).
Admitted.

Lemma StrongSubset_extendVarSetList_fresh : 
  forall vs vars, freshList vars vs ->
             StrongSubset vs (extendVarSetList vs vars).
Admitted.

Lemma filterVarSet_extendVarSet : 
  forall f v vs,
    filterVarSet f (extendVarSet vs v) = 
    if (f v) then extendVarSet (filterVarSet f vs) v 
    else (filterVarSet f vs).
Proof.  
Admitted.

Lemma lookupVarSet_filterVarSet_true : forall f v vs,
  f v = true ->
  lookupVarSet (filterVarSet f vs) v = lookupVarSet vs v.
Proof.
  intros.
Admitted.

Lemma lookupVarSet_filterVarSet_false : forall f v vs,
  f v = false ->
  lookupVarSet (filterVarSet f vs) v = None.
Proof.
  intros.
Admitted.


Lemma StrongSubset_filterVarSet : 
  forall f1 f2 vs,
  (forall v, f1 v = true -> f2 v = true) ->
  filterVarSet f1 vs {<=} filterVarSet f2 vs.
Proof.  
Admitted.
