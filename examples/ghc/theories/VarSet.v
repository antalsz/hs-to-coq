(* Disable notation conflict warnings *)
Set Warnings "-notation-overridden".

From Coq Require Import ssreflect ssrfun ssrbool.
Require Import Psatz.
Require Import Coq.Lists.List.
Require Import Coq.NArith.BinNat.
Import ListNotations.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import SetoidList.
Require Import Coq.Logic.ProofIrrelevance.

Require Import GHC.Base.

Require Import Proofs.Prelude.

Require Import CoreFVs.
Require Import Id.
Require Import Core.
Require UniqFM.

Require Import Proofs.Axioms.
Require Import Proofs.ContainerAxioms.
Require Import Proofs.GhcTactics.
Require Import Proofs.Unique.
Require Import Proofs.Var.
Require Import Proofs.VarSetFSet.
Require Import Proofs.Base.

Open Scope Z_scope.


Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Bullet Behavior "Strict Subproofs".



(* Stephanie's hack. *)
Lemma fold_is_true : forall b, b = true <-> b.
Proof. intros. unfold is_true. reflexivity. Qed.

Lemma false_is_not_true :
  forall b, b = false <-> b <> true.
Proof.
  destruct b; intuition.
Qed.

(* Why is this not part of ssr? *)
Lemma eqE : forall (a b:bool), a = b <-> (a <-> b).
Proof.  
  move=> a b.
  elim Ea: a;
  elim Eb: b;
  try tauto.
  intuition.
  symmetry.
  rewrite fold_is_true.
  apply H0. auto.
  intuition.
Qed.

Lemma andE a b : a && b <-> a /\ b.
Proof. 
  elim: a; elim: b; try tauto.
  split; move=> /andP; try done. 
  split; move=> /andP; try done. 
Qed.

Lemma orE : forall a b, (a || b) <-> a \/ b.
Proof. intros a b. unfold is_true. rewrite orb_true_iff. tauto. Qed.

Lemma notE : forall a, ~~a <-> ~ a.
Proof. move=>a. unfold is_true. rewrite negb_true_iff. 
split. move=>h. rewrite h. auto.
apply not_true_is_false.
Qed.



(** ** NOTE: VarSets and equality *)

(* VarSets have several different notions of equality. 
   In all three definitions, equal varsets must have the same domain. 
   Now suppose:
       lookupVarSet m1 x = Some v1 and
       lookupVarSet m2 x = Some v2
   The sets are equal when:
    - v1 = v2                (i.e. coq equality) 
    - almostEqual v1 v2      
    - v1 == v2               (i.e. same uniques ONLY)

   The last (coarsest) equality is the one used in the FSet signature, 
   and denoted by the [=] notation. 

   The almostEqual equality is denoted by {=}.

   Because of this distinction, we have to do some lemmas twice: once 
   for [=] equality, and once for {=} equality.
  
*)


(** ** VarSet operations respect GHC.Base.==  *)

Lemma elemVarSet_eq : forall v1 v2 vs,
  (v1 == v2) -> 
  elemVarSet v1 vs = elemVarSet v2 vs.
Proof.
  intros v1 v2 vs h.
  unfold elemVarSet, UniqSet.elementOfUniqSet.
  destruct vs.
  unfold UniqFM.elemUFM.
  destruct getUniqSet'.
  move: h.
  rewrite eq_unique.
  move=> h.
  f_equal.
  auto.
Qed.

Lemma lookupVarSet_eq :
  forall v1 v2 vs,
    (v1 == v2) ->
    lookupVarSet vs v1 = lookupVarSet vs v2.
Proof. 
  intros v1 v2 vs.
  unfold lookupVarSet.
  unfold UniqSet.lookupUniqSet.
  destruct vs.
  unfold UniqFM.lookupUFM.
  destruct getUniqSet'.
  intro h.
  rewrite -> eq_unique in h.
  rewrite h.
  reflexivity.
Qed.

Lemma extendVarSet_eq : 
  forall x y vs, x == y -> extendVarSet vs x [=] extendVarSet vs y.
Proof.
  move => x y vs Eq.
  set_b_iff.
  move: (add_m) => h.
  unfold Proper,respectful in h.
  apply h.
  assumption.
  reflexivity.
Qed.


Lemma delVarSet_eq : 
  forall x y vs, x == y -> delVarSet vs x = delVarSet vs y.
Proof.
  move => x y vs Eq.
  unfold delVarSet.
  move: vs => [i].
  move: i => [m].
  rewrite -> eq_unique in Eq.
  unfold UniqSet.delOneFromUniqSet.
  unfold UniqFM.delFromUFM.
  rewrite Eq.
  reflexivity.
Qed.






(** ** List based operations in terms of folds *)

Lemma extendVarSetList_foldl' : forall x xs, 
    extendVarSetList x xs = Foldable.foldl' (fun x y => add y x) x xs.
Proof.
  intros.
  unfold extendVarSetList, UniqSet.addListToUniqSet;
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
    destruct vs. destruct getUniqSet'.
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
    rewrite (IHvl (UniqSet.Mk_UniqSet (UniqFM.delFromUFM getUniqSet' a))).
    auto.
Qed.


Lemma mkVarSet_extendVarSetList : forall xs,
    mkVarSet xs = extendVarSetList emptyVarSet xs.
Proof.
  reflexivity.
Qed.


Hint Rewrite mkVarSet_extendVarSetList : hs_simpl.


(** ** [lookupVarSet] and [elemVarSet] correspondence *)

Lemma lookupVarSet_In:
  forall vs v, (exists v', lookupVarSet vs v = Some v') <-> In v vs.
Proof.
  unfold lookupVarSet, UniqSet.lookupUniqSet,
    UniqFM.lookupUFM, Unique.getWordKey, Unique.getKey.
  intros.
  destruct vs.
  destruct getUniqSet'.
  destruct (Unique.getUnique v) as [n] eqn:Hv.
  unfold In, elemVarSet, UniqSet.elementOfUniqSet,
  UniqFM.elemUFM, Unique.getKey, Unique.getWordKey,
  Unique.getKey.
  rewrite Hv.
  rewrite <- member_lookup.
  reflexivity.
Qed.

Lemma lookupVarSet_elemVarSet : 
  forall v1 v2 vs, lookupVarSet vs v1 = Some v2 -> elemVarSet v1 vs.
Proof.
  intros.
  unfold lookupVarSet, elemVarSet in *.
  unfold UniqSet.lookupUniqSet, UniqSet.elementOfUniqSet in *.
  destruct vs.
  unfold UniqFM.lookupUFM, UniqFM.elemUFM in *.
  destruct getUniqSet'. 
  set (key := Unique.getWordKey (Unique.getUnique v1)) in *.
  rewrite member_lookup.
  exists v2. auto.
Qed.

Lemma lookupVarSet_None_elemVarSet: 
  forall v1 vs, lookupVarSet vs v1 = None <-> elemVarSet v1 vs = false.
Proof.
  intros.
  unfold lookupVarSet, elemVarSet in *.
  unfold UniqSet.lookupUniqSet, UniqSet.elementOfUniqSet in *.
  destruct vs.
  unfold UniqFM.lookupUFM, UniqFM.elemUFM in *.
  destruct getUniqSet'.
  set (key := Unique.getWordKey (Unique.getUnique v1)) in *.
  rewrite non_member_lookup.
  intuition.
Qed.

Lemma elemVarSet_lookupVarSet :
  forall v1 vs, elemVarSet v1 vs -> exists v2, lookupVarSet vs v1 = Some v2.
Proof.
  intros.
  unfold lookupVarSet, elemVarSet in *.
  unfold UniqSet.lookupUniqSet, UniqSet.elementOfUniqSet in *.
  destruct vs.
  unfold UniqFM.lookupUFM, UniqFM.elemUFM in *.
  destruct getUniqSet'.
  set (key := Unique.getWordKey (Unique.getUnique v1)) in *.
  rewrite <- member_lookup.
  auto.
Qed.

(** ** [lookupVarSet] is Proper  *)

Instance lookupVarSet_m : 
  Proper (Equal ==> (fun x y => x == y) ==> (fun x y => x == y)) lookupVarSet.
Proof.
  unfold Equal.
  intros x y H v1 v2 EV.
  erewrite lookupVarSet_eq; eauto.
  pose (h1 := H v1).
  pose (h2 := H v2).
  repeat rewrite -> mem_iff in h1.
  repeat rewrite -> mem_iff in h2.
  destruct (lookupVarSet x v2) eqn:LX;
  destruct (lookupVarSet y v2) eqn:LY;
  hs_simpl.
  - apply ValidVarSet_Axiom in LX.
    apply ValidVarSet_Axiom in LY.
    eapply Eq_trans.
    rewrite Eq_sym.
    eapply LX.
    eapply LY.
  - apply lookupVarSet_elemVarSet in LX.
    rewrite -> lookupVarSet_None_elemVarSet in LY.
    set_b_iff.
    intuition.
  - apply lookupVarSet_elemVarSet in LY.
    rewrite -> lookupVarSet_None_elemVarSet in LX.
    set_b_iff.
    intuition.
  - auto.
Qed.


(** ** [lookupVarSet . extendVarSet ] simplification *)

Lemma lookupVarSet_extendVarSet_self:
  forall v vs,
  lookupVarSet (extendVarSet vs v) v = Some v.
Proof.
  intros.
  unfold lookupVarSet, extendVarSet in *.
  unfold UniqSet.lookupUniqSet, UniqSet.addOneToUniqSet in *.
  destruct vs.
  unfold UniqFM.lookupUFM, UniqFM.addToUFM in *.
  destruct getUniqSet'.
  set (key := Unique.getWordKey (Unique.getUnique v)) in *.
  apply lookup_insert.
Qed.

Hint Rewrite lookupVarSet_extendVarSet_self : hs_simpl.

Lemma lookupVarSet_extendVarSet_eq :
      forall v1 v2 vs,
      v1 == v2  ->
      lookupVarSet (extendVarSet vs v1) v2 = Some v1.
Proof.
  intros v1 v2 vs H.
  rewrite Eq_sym in H.
  rewrite (lookupVarSet_eq _ H).
  unfold lookupVarSet, extendVarSet.
  unfold UniqSet.lookupUniqSet, UniqSet.addOneToUniqSet.
  destruct vs.
  unfold UniqFM.lookupUFM, UniqFM.addToUFM.
  destruct getUniqSet'.
  set (k1 := Unique.getWordKey (Unique.getUnique v1)).
  rewrite lookup_insert.
  reflexivity.
Qed.

Lemma lookupVarSet_extendVarSet_neq :
      forall v1 v2 vs,
      not (v1 == v2) ->
      lookupVarSet (extendVarSet vs v1) v2 = lookupVarSet vs v2.
Proof.
  intros v1 v2 vs H.
  assert (Unique.getWordKey (Unique.getUnique v1) <> 
          Unique.getWordKey (Unique.getUnique v2)).
  { intro h.
    eapply H.
    rewrite eq_unique.
    auto.
  }
  unfold lookupVarSet, extendVarSet.
  unfold UniqSet.lookupUniqSet, UniqSet.addOneToUniqSet.
  destruct vs.
  unfold UniqFM.lookupUFM, UniqFM.addToUFM.
  destruct getUniqSet'.
  eapply lookup_insert_neq.
  auto.
Qed.


(* --------------------------------- *)

(* Tactics that don't really work. *)
                                   
Local Ltac unfold_VarSet_to_IntMap :=
  repeat match goal with
         | [vs : VarSet |- _ ] =>
           let u := fresh "u" in
           destruct vs as [u]; destruct u; simpl
         | [ |- UniqSet.Mk_UniqSet _ = UniqSet.Mk_UniqSet _ ] =>
           f_equal
         | [ |- UniqFM.UFM _ = UniqFM.UFM _ ] =>
           f_equal
         end.

(*
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
         UniqFM.elemUFM in *. *)

(**************************************)

(** ** [extendVarSetList] simplifications *)

Lemma extendVarSetList_nil:
  forall s,
  extendVarSetList s [] = s.
Proof.
  intro s.
  reflexivity.
Qed.

Lemma extendVarSetList_cons:
  forall s v vs,
  extendVarSetList s (v :: vs) = extendVarSetList (extendVarSet s v) vs.
Proof.
  intros.
  rewrite extendVarSetList_foldl'.
  autorewrite with hs_simpl.
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
  rewrite extendVarSetList_foldl'.
  autorewrite with hs_simpl.
  reflexivity.
Qed.

Hint Rewrite extendVarSetList_nil 
             extendVarSetList_cons
             extendVarSetList_singleton
             extendVarSetList_append : hs_simpl.



(** ** [delVarSetList] simplification  *)

Lemma delVarSetList_nil:
  forall e, delVarSetList e [] = e.
Proof.
  intros.
  rewrite delVarSetList_foldl.
  reflexivity.
Qed.

Lemma delVarSetList_single:
  forall e a, delVarSetList e [a] = delVarSet e a.
Proof.
  intros.
  rewrite delVarSetList_foldl.
  autorewrite with hs_simpl.
  reflexivity.
Qed.

Lemma delVarSetList_cons:
  forall e a vs, delVarSetList e (a :: vs) = delVarSetList (delVarSet e a) vs.
Proof.
  intros.
  repeat rewrite delVarSetList_foldl.
  autorewrite with hs_simpl.
  reflexivity.
Qed.

Lemma delVarSetList_app:
  forall e vs vs', delVarSetList e (vs ++ vs') = delVarSetList (delVarSetList e vs) vs'.
Proof.
  intros.
  repeat rewrite delVarSetList_foldl.
  autorewrite with hs_simpl.
  reflexivity.
Qed.

Hint Rewrite delVarSetList_nil 
             delVarSetList_cons
             delVarSetList_single
             delVarSetList_app : hs_simpl.


(** ** [elemVarSet] simplification *)

Lemma elemVarSet_emptyVarSet : forall v, (elemVarSet v emptyVarSet) = false.
  intro v.
  set_b_iff.
  fsetdec.
Qed.

Lemma elemVarSet_unionVarSet:
  forall v vs1 vs2,
    elemVarSet v (unionVarSet vs1 vs2) = elemVarSet v vs1 || elemVarSet v vs2.
Proof.
  move => v [[i]] [[i0]] /=.
  rewrite member_union.
  auto.
Qed.

Hint Rewrite elemVarSet_emptyVarSet elemVarSet_unionVarSet : hs_simpl.


(** ** [extendVarSet]  *)

Lemma extendVarSet_elemVarSet_true : forall set v, 
    elemVarSet v set -> extendVarSet set v [=] set.
Proof. 
  intros.
  apply add_equal.
  auto.
Qed.


Lemma elemVarSet_extendVarSet:
  forall v vs v',
  elemVarSet v (extendVarSet vs v') = (v' == v) || elemVarSet v vs.
Proof.
  intros.
  rewrite var_eq_realUnique.
  replace (realUnique v' == realUnique v)%N with 
      (F.eqb v' v). 

  eapply F.add_b.
  unfold F.eqb.
  cbn.
  destruct F.eq_dec.
  - unfold Var_as_DT.eq in e.
    rewrite <- realUnique_eq in e; auto.
  - unfold Var_as_DT.eq in n.
    rewrite <- realUnique_eq in n; apply not_true_is_false in n; auto.
Qed.

Hint Rewrite elemVarSet_extendVarSet : hs_simpl.

Lemma elemVarSet_extendVarSetList:
  forall v vs vs',
  elemVarSet v (extendVarSetList vs vs') = Foldable.elem v vs' || elemVarSet v vs.
Proof.
  intros.
  generalize vs.
  induction vs'.
  + intros vs0. hs_simpl.
    simpl.
    auto.
  + intros vs0. hs_simpl.
    rewrite IHvs'.
    hs_simpl.
    rewrite Eq_sym.
    ssrbool.bool_congr.
    reflexivity.
Qed.

Hint Rewrite elemVarSet_extendVarSetList : hs_simpl.

Lemma extendVarSet_commute : forall x y vs, 
    extendVarSet (extendVarSet vs y) x  [=] extendVarSet (extendVarSet vs x) y.
Proof.
  intros.
  set_b_iff.
  fsetdec.
Qed.



(** ** [extendVarSetList] and [delVarSetList] are Proper **)

(* These lemmas show that extendVarSetList respects [=] *)

Lemma extendVarSetList_iff : forall l x vs,
  In x (extendVarSetList vs l) <->
  In x vs \/ Foldable.elem x l.
Proof.
  induction l.
  - intros x vs.
    hs_simpl.
    intuition.
    inversion H0.
  - intros x vs.
    hs_simpl.
    rewrite IHl.
    set_b_iff.
    rewrite add_iff.
    unfold Var_as_DT.eqb.
    rewrite Eq_sym.
    rewrite orE.
    intuition.
Qed.

Lemma delVarSetList_iff : forall l x vs,
  In x (delVarSetList vs l) <->
  In x vs /\ ~ (Foldable.elem x l).
Proof.
  induction l.
  - intros x vs. 
    hs_simpl.
    intuition.
  - intros x vs.
    hs_simpl.
    rewrite IHl.
    rewrite delVarSet_remove. rewrite remove_iff.
    unfold Var_as_DT.eqb.
    rewrite Eq_sym.
    rewrite orE.
    intuition.
Qed.

Instance extendVarSetList_m : 
  Proper (Equal ==> (eqlistA (fun x y => x == y)) ==> Equal) extendVarSetList.
Proof.
  unfold Equal.
  intros x y H s s' H0 a.
  do 2 rewrite extendVarSetList_iff.
  rewrite H.
  intuition; right.
  erewrite <- eqlist_Foldable_elem; eauto.
  eapply EqLaws_Var.
  erewrite eqlist_Foldable_elem; eauto.
  eapply EqLaws_Var.
Qed.

Instance delVarSetList_m : 
  Proper (Equal ==> (eqlistA (fun x y => x == y)) ==> Equal) delVarSetList.
Proof.
  unfold Equal.
  intros x y H s s' H0 a.
  do 2 rewrite delVarSetList_iff.
  rewrite H.
  intuition.
  apply H3.
  erewrite eqlist_Foldable_elem; eauto using EqLaws_Var.
  apply H3.
  erewrite <- eqlist_Foldable_elem; eauto using EqLaws_Var.
Qed.


(* We can commute the order of addition to varsets. 
   This is only true for [=] *)
Lemma extendVarSetList_extendVarSet_iff: forall l x vs,
  extendVarSetList (extendVarSet vs x) l [=]
  extendVarSet (extendVarSetList vs l) x.
Proof.
  induction l.
  - intros.
    hs_simpl.
    reflexivity.
  - intros.
    hs_simpl.
    rewrite extendVarSet_commute.
    rewrite IHl.
    reflexivity.
Qed.


Lemma elemVarSet_extend_add : forall v s vs a,
  elemVarSet v (extendVarSetList s vs) ->
  elemVarSet v (extendVarSetList (add a s) vs).
Proof. 
  intros v s vs a.
  rewrite InE.
  rewrite InE.
  rewrite extendVarSetList_iff.
  rewrite extendVarSetList_iff.
  intuition.
  left.
  fsetdec.
Qed.

Lemma elemVarSet_extendVarSetList_r:
  forall v s vs,
  elemVarSet v (mkVarSet vs)  ->
  elemVarSet v (extendVarSetList s vs) .
Proof.
  intros v s vs.
  rewrite mkVarSet_extendVarSetList.
  rewrite InE.
  rewrite InE.
  rewrite extendVarSetList_iff.
  rewrite extendVarSetList_iff.
  intuition.
Qed.


Lemma elemVarSet_mkVarSet_cons:
  forall v v' vs,
  elemVarSet v (mkVarSet (v' :: vs)) = false
  <-> (v' == v) = false /\ elemVarSet v (mkVarSet vs) = false.
Proof.
  intros v v' vs.
  rewrite mkVarSet_extendVarSetList.
  rewrite extendVarSetList_cons.
  rewrite mkVarSet_extendVarSetList.
  rewrite <- not_mem_iff.
  rewrite <- not_mem_iff.
  rewrite extendVarSetList_iff.
  rewrite extendVarSetList_iff.
  set_b_iff.
  rewrite add_iff.
  unfold Var_as_DT.eqb.
  intuition.
  apply not_true_is_false.
  unfold not. auto.
  destruct H.
  rewrite H1 in H0.
  done.
Qed.


(* ** Properties about [lookupVarSet (extendVarSetList vs vars) v]

   Note, we can specify what happens when v is an Foldable.elem of vars with
   varying degrees of precision. When we lookup v, we won't get [Some v]
   exactly, but we will get something == to v, and that was the most recently
   added var in vars.
   
*)


Lemma lookupVarSet_extendVarSetList_false:
  forall (vars:list Var) v vs,
    ~~ (Foldable.elem v vars ) -> 
    lookupVarSet (extendVarSetList vs vars) v = lookupVarSet vs v.
Proof.
  elim=> [|x xs IH] //.   (* // is try done. *)
  - move => v vs.
    hs_simpl.
    rewrite negb_or.     (* de morgan law to push ~~ in *)
    move => /andP [h1 h2]. (* split && into two hypotheses *)
    rewrite IH //.
    rewrite lookupVarSet_extendVarSet_neq //.
    rewrite Eq_sym. by apply /negP.
Qed.


Lemma lookupVarSet_extendVarSetList_l
  v vs vars :
  ~~ elemVarSet v (mkVarSet vars) ->
  lookupVarSet (extendVarSetList vs vars) v = lookupVarSet vs v.
Proof.
  hs_simpl.
  elim: vars vs => [|a vars IH] vs //.
  hs_simpl.

  rewrite negb_orb => /andP [? ?].

  rewrite lookupVarSet_extendVarSetList_false //.
  rewrite lookupVarSet_extendVarSet_neq //.

  apply /negP.
  rewrite Eq_sym //. 
Qed.


Lemma lookupVarSet_extendVarSetList_self_in:
  forall (vars:list Var) v vs,
    List.In v vars -> 
    NoDup (map varUnique vars) -> 
    lookupVarSet (extendVarSetList vs vars) v = Some v.
Proof.
  induction vars.
  - intros v vs H.
    inversion H.
  - intros v vs H ND.
    hs_simpl.
    simpl in ND.
    inversion ND. subst.
    inversion H; subst.
    + rewrite lookupVarSet_extendVarSetList_false.
      by hs_simpl.
      apply /negP.
      by rewrite -In_varUnique_elem.
    + eauto. 
Qed.      


Lemma lookupVarSet_extendVarSetList_self:
  forall (vars:list Var) v vs,
    (Foldable.elem v vars) -> 
    lookupVarSet (extendVarSetList vs vars) v == Some v.
Proof.
  induction vars.
  - intros v vs H.
    rewrite elem_nil in H.
    done.
  - intros v vs H.
    rewrite elem_cons in H.
    hs_simpl.
    rewrite -> orE in H.
    elim: H.
    move => H.
    case Hv: (Foldable.elem v vars).
    + specialize (IHvars v (extendVarSet vs a)).
      unfold is_true in *.
      apply IHvars. 
      done.
    + rewrite (lookupVarSet_eq _ H).
      rewrite lookupVarSet_extendVarSetList_false.
      rewrite lookupVarSet_extendVarSet_self.
      hs_simpl.
      symmetry. done.
      setoid_rewrite H in Hv.
      rewrite Hv. done.
    + move=> h.
      apply IHvars.
      auto.
Qed.

Inductive LastIn : Var -> list Var -> Prop :=
  | LastIn_head: forall v1 vs, 
      Foldable.elem v1 vs = false ->
      LastIn v1 (v1 :: vs)
  | LastIn_tail: forall v1 v2 vs,
      LastIn v1 vs ->
      LastIn v1 (v2 :: vs).

Lemma LastIn_elem : forall v vs, 
    LastIn v vs -> Foldable.elem v vs.
Proof.
  move => v vs h. 
  induction h; hs_simpl; apply /orP. 
  left. reflexivity.
  right. assumption.
Qed.  
  
Lemma LastIn_inj : forall v1 v2 vs, 
    LastIn v1 vs -> v1 == v2 -> LastIn v2 vs -> v1 = v2.
Proof.    
  move=> v1 v2 vs h. induction h.
  - move=> eq FI.
    inversion FI. auto. 
    subst. 
    move: (LastIn_elem H2) => h.
    rewrite -> HSUtil.elem_resp_eq with (a:= v2) in H; try done.
    rewrite Eq_sym. done.
  - move=> eq FI. inversion FI.
    subst. 
    move: (LastIn_elem h) => h0.
    rewrite -> HSUtil.elem_resp_eq with (a:= v1) in H1; try done.
    subst. eauto.
Qed.



Lemma lookupVarSet_extendVarSetList_self_exists_LastIn:
  forall (vars:list Var) v vs,
    (Foldable.elem v vars) -> 
    exists v', and3 (lookupVarSet (extendVarSetList vs vars) v = Some v')
               (v == v')
               (LastIn v' vars).
Proof.
  elim => // a vars IH.       (* Do induction on first var, 
                                then trivially discharge goal. *)
                          (* Then introduce names for list components *)
  move=> v vs.
  hs_simpl.

  move => /orP [h1 | h1].  (* case analysis on boolean || *)

  case IN: (Foldable.elem v vars). 

  + unfold is_true in *.
    move: (IH v (extendVarSet vs a) IN) => [v' [p q r]].
    exists v'; split; eauto.
    eapply LastIn_tail. auto.
  + rewrite lookupVarSet_extendVarSetList_false ; try by rewrite IN.
    exists a. split; eauto.
    rewrite lookupVarSet_extendVarSet_eq //. 
    symmetry => //.
    eapply LastIn_head.
    rewrite <- (elem_eq vars _ _ h1).
    done.
  + unfold is_true in *.
    move: (IH v (extendVarSet vs a) h1) => [v' [p q r]].
    exists v'; split; eauto.
    eapply LastIn_tail. auto.
Qed.


(*
Lemma lookupVarSet_extendVarSetList_self_exists_in:
  forall (vars:list Var) v vs,
    (Foldable.elem v vars) -> 
    exists v', and3 (lookupVarSet (extendVarSetList vs vars) v = Some v')
               (v == v')
               (List.In v' vars).
Proof.
  elim => // a vars IH.       (* Do induction on first var, 
                                then trivially discharge goal. *)
                          (* Then introduce names for list components *)
  move=> v vs.
  hs_simpl.

  move => /orP [h1 | h1].  (* case analysis on boolean || *)

  case IN: (Foldable.elem v vars). 

  all: try ( unfold is_true in * ; match goal with 
      [ H : Foldable.elem ?v ?vars = true |- _ ] =>
        move: (IH v (extendVarSet vs a) H) => [v'[]]* ;
        exists v'; split; eauto using in_cons
     end ).

   + rewrite lookupVarSet_extendVarSetList_false ; try by rewrite IN.
     exists a. split; eauto.
       rewrite lookupVarSet_extendVarSet_eq //. 
       symmetry => //.
       eapply in_eq.
Qed.
*)


Lemma extendVarSetList_same v vars : forall vs1 vs2 ,
  Foldable.elem v vars ->
  lookupVarSet (extendVarSetList  vs1 vars) v = 
  lookupVarSet (extendVarSetList vs2 vars)  v.
Proof.
  elim: vars => // a vars IHvars. 
  - move => vs1 vs2.
    hs_simpl.  
    move=> /orP [h1|h2].
    + case h: (Foldable.elem v vars); eauto.
      (* ! rewrites one or more times. *)
      rewrite !lookupVarSet_extendVarSetList_false; try (rewrite h; done).
      rewrite !lookupVarSet_extendVarSet_eq // ; symmetry ; done.
    + auto.
Qed.



(** ** [mkVarSet]  *)


Lemma elemVarSet_mkVarset_iff_In:
  forall v vs,
  elemVarSet v (mkVarSet vs)  <->  List.In (varUnique v) (map varUnique vs).
Proof.
  intros.
  rewrite mkVarSet_extendVarSetList.
  induction vs.
  - hs_simpl.
    simpl.
    done.
  - hs_simpl.
    simpl map.
    split.
    + move /orP.        
      rewrite -> varUnique_iff.
      rewrite -In_varUnique_elem //. 
      move => [h1|h2] //.
      rewrite h1.
      apply in_eq.
      apply in_cons => //.
    + move => h.
      apply /orP.
      inversion h.
      ++ left.
         rewrite varUnique_iff //.
      ++ right.
         apply In_varUnique_elem => //.
Qed.

(** ** [delVarSet]  *)

Lemma delVarSet_elemVarSet_false : forall v set, 
    elemVarSet v set = false -> delVarSet set v [=] set.
intros.
set_b_iff.
apply remove_equal.
auto.
Qed.


Lemma delVarSet_emptyVarSet x :
  delVarSet emptyVarSet x = emptyVarSet.
Proof.
  unfold delVarSet, emptyVarSet.
  unfold  UniqSet.delOneFromUniqSet , UniqSet.emptyUniqSet.
  unfold UniqFM.delFromUFM, UniqFM.emptyUFM.
  repeat f_equal. unfold IntMap.delete, IntMap.empty.
  f_equal. apply proof_irrelevance.
Qed.
Hint Rewrite delVarSet_emptyVarSet : hs_simpl. 


Lemma delVarSet_extendVarSet : 
  forall set v, 
    elemVarSet v set = false -> (delVarSet (extendVarSet set v) v) [=] set.
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
  destruct elemVarSet eqn:EL.
  + symmetry.
    apply andb_true_intro.
    set_b_iff.
    rewrite -> remove_iff in EL.
    unfold Var_as_DT.eqb in EL. unfold not in EL.
    rewrite negb_true_iff.
    intuition.
    apply not_true_is_false.
    auto.
  + symmetry.
    apply not_true_is_false.
    intro H.
    apply andb_prop in H.
    set_b_iff.
    rewrite -> remove_iff in EL.
    unfold Var_as_DT.eqb in *.
    intuition.
    rewrite -> negb_true_iff in H0.
    apply H2.
    intro h.
    unfold Var_as_DT.t in *.
    rewrite h in H0.
    inversion H0.
Qed.

Hint Rewrite elemVarSet_delVarSet : hs_simpl.

Lemma lookupVarSet_delVarSet_neq :
      forall v1 v2 vs,
      not (v1 == v2) ->
      lookupVarSet (delVarSet vs v1) v2 = lookupVarSet vs v2.
Proof.
  intros v1 v2 vs H.
  unfold lookupVarSet,delVarSet.
  unfold UniqSet.lookupUniqSet, UniqSet.delOneFromUniqSet.
  destruct vs.
  unfold UniqFM.lookupUFM, UniqFM.delFromUFM.
  destruct getUniqSet'.
  assert (Unique.getWordKey (Unique.getUnique v1) <>
          Unique.getWordKey (Unique.getUnique v2)).
  { intro h. apply H. rewrite eq_unique. done. }
  rewrite delete_neq.
  auto.
  auto.
Qed.



Lemma elemVarSet_delVarSet_eq x y vs :
  (x == y) -> elemVarSet x (delVarSet vs y) = false.
Proof.
  rewrite -> eq_unique.
  move => Eq.
  unfold elemVarSet, delVarSet.
  unfold UniqSet.elementOfUniqSet, UniqSet.delOneFromUniqSet.
  move: vs => [i].
  move: i => [m].
  unfold UniqFM.elemUFM, UniqFM.delFromUFM.
  rewrite Eq.
  set key :=  Unique.getWordKey (Unique.getUnique y).
  move: (@delete_eq key Var m).
  rewrite <- non_member_lookup.
  move => h. rewrite h.
  done.
Qed.


(** ** [delVarSetList]  *)

(* These next two rely on this strong property about the unique 
   representations of IntMaps. *)
Lemma delVarSet_commute : forall x y vs, 
    delVarSet (delVarSet vs x) y = delVarSet (delVarSet vs y) x.
Proof.
  intros.
  unfold delVarSet.
  unfold UniqSet.delOneFromUniqSet.
  destruct vs.
  f_equal.
  unfold UniqFM.delFromUFM.
  destruct getUniqSet'.
  f_equal.
  set (kx := Unique.getWordKey (Unique.getUnique x)).
  set (ky := Unique.getWordKey (Unique.getUnique y)).
  eapply delete_commute; eauto.
Qed.

Lemma delVarSetList_cons2:
  forall vs e a, delVarSetList e (a :: vs) = delVarSet (delVarSetList e vs) a.
Proof.
  induction vs; intros e a1;
  rewrite -> delVarSetList_cons in *.
  - set_b_iff.
    hs_simpl.
    reflexivity.
  - rewrite delVarSetList_cons.
    rewrite delVarSetList_cons.
    rewrite delVarSet_commute.
    rewrite <- IHvs.
    rewrite delVarSetList_cons.
    auto.
Qed.

Lemma delVarSetList_rev:
  forall vs1 vs2,
  delVarSetList vs1 (rev vs2) = delVarSetList vs1 vs2.
Proof.
  induction vs2.
  - simpl. auto.
  - simpl rev.
    rewrite delVarSetList_cons.
    rewrite delVarSetList_app.
    rewrite IHvs2.
    rewrite delVarSetList_cons.
    rewrite delVarSetList_nil.
    rewrite <- delVarSetList_cons2.
    rewrite delVarSetList_cons.
    reflexivity.
Qed.


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

Lemma delVarSet_unionVarSet:
  forall vs1 vs2 x,
  delVarSet (unionVarSet vs1 vs2) x [=] 
  unionVarSet (delVarSet vs1 x) (delVarSet vs2 x).
Proof.
  intros.
  set_b_iff.
  fsetdec.
Qed.

Lemma delVarSetList_unionVarSet:
  forall vs3 vs1 vs2,
  delVarSetList (unionVarSet vs1 vs2) vs3 [=] 
  unionVarSet (delVarSetList vs1 vs3) (delVarSetList vs2 vs3).
Proof.
  induction vs3; intros.
  - repeat rewrite delVarSetList_nil.
    reflexivity.
  - repeat rewrite delVarSetList_cons.
    rewrite delVarSet_unionVarSet.
    rewrite IHvs3.
    reflexivity.
Qed.


(**************************************)


(** ** [subVarSet]  *)
  
Lemma subVarSet_refl:
  forall vs1,
  subVarSet vs1 vs1 .
Proof.
  intros.
  set_b_iff.
  fsetdec.
Qed.

Lemma subVarSet_trans:
  forall vs1 vs2 vs3,
  subVarSet vs1 vs2  ->
  subVarSet vs2 vs3  ->
  subVarSet vs1 vs3 .
Proof.
  intros.
  set_b_iff.
  fsetdec.
Qed.


Lemma subVarSet_emptyVarSet:
  forall vs,
  subVarSet emptyVarSet vs .
Proof.
  intros.
  set_b_iff.
  fsetdec.
Qed.

Lemma subVarSet_unitVarSet:
  forall v vs,
  subVarSet (unitVarSet v) vs = elemVarSet v vs.
Proof.
  intros.
  destruct subVarSet eqn:SV; symmetry.
  + set_b_iff.
    fsetdec.
  + rewrite -> false_is_not_true in *.
    set_b_iff.
    intro h.
    unfold Subset in SV.
    apply SV.
    intros.
    rewrite In_eq_iff; eauto.
    apply singleton_1 in H; symmetry; auto.
Qed.

Lemma elemVarSet_false_true:
  forall v1 fvs v2,
  elemVarSet v1 fvs = false ->
  elemVarSet v2 fvs  ->
  varUnique v1 <> varUnique v2.
Proof.
  intros v1 fvs v2.
  intros.
  assert (not (v2 == v1 )).
  intro h. 
  set_b_iff.
  rewrite -> In_eq_iff in H0; eauto.
  intro h.
  rewrite <- varUnique_iff in h.
  apply H1.
  rewrite Eq_sym.
  auto.
Qed.

Lemma subVarSet_elemVarSet_true:
  forall v vs vs',
  subVarSet vs vs'  ->
  elemVarSet v vs  ->
  elemVarSet v vs' .
Proof.
  intros v vs vs'.
  set_b_iff.
  fsetdec.
Qed.

Lemma subVarSet_elemVarSet_false:
  forall v vs vs',
  subVarSet vs vs'  ->
  elemVarSet v vs' = false ->
  elemVarSet v vs = false.
Proof.
  intros v vs vs'.
  set_b_iff.
  fsetdec.
Qed.

Lemma subVarSet_extendVarSetList_l:
  forall vs1 vs2 vs,
  subVarSet vs1 vs2  ->
  subVarSet vs1 (extendVarSetList vs2 vs) .
Proof.
  intros vs1 vs2 vs.
  generalize dependent vs2.
  induction vs.
  - intro vs2. rewrite extendVarSetList_nil. auto.
  - intro vs2. intro h. 
    rewrite extendVarSetList_cons. 
    rewrite IHvs. auto. 
    set_b_iff. fsetdec.
Qed.


    

Lemma subVarSet_extendVarSet_both:
  forall vs1 vs2 v,
  subVarSet vs1 vs2  ->
  subVarSet (extendVarSet vs1 v) (extendVarSet vs2 v) .
Proof.
  intros.
  set_b_iff.
  fsetdec.
Qed.


Lemma subVarSet_extendVarSet:
  forall vs1 vs2 v,
  subVarSet vs1 vs2  ->
  subVarSet vs1 (extendVarSet vs2 v) .
Proof.
  intros.
  set_b_iff.
  fsetdec.
Qed.


Lemma subVarSet_extendVarSetList:
  forall vs1 vs2 vs3,
  subVarSet vs1 vs2  ->
  subVarSet vs1 (extendVarSetList vs2 vs3) .
Proof.

  induction vs3; autorewrite with hs_simpl.
  - auto.
  - intro h. 
    rewrite extendVarSetList_extendVarSet_iff.
    rewrite subVarSet_extendVarSet; auto.
Qed.

Lemma subVarSet_extendVarSet_l:
  forall vs1 vs2 v v',
  subVarSet vs1 vs2  ->
  lookupVarSet vs2 v = Some v' ->
  subVarSet (extendVarSet vs1 v) vs2 .
Proof.
  intros.
  set_b_iff.
  apply MP.subset_add_3; try assumption.
  apply lookupVarSet_In.
  eauto.
Qed.

Lemma extendVarSet_subset: forall v1 v2 x,
  v1 [<=] v2 ->
  extendVarSet v1 x [<=] extendVarSet v2 x.
Proof.
  intros.
  set_b_iff.
  fsetdec.
Qed.
  
Lemma extendVarSetList_subset: forall x y vs,
  x [<=] y ->
  extendVarSetList x vs [<=] extendVarSetList y vs.
Proof.
  intros.
  induction vs; hs_simpl; [assumption|].
  do 2 rewrite extendVarSetList_extendVarSet_iff.
  apply extendVarSet_subset.
  assumption.
Qed.

Lemma subVarSet_extendVarSetList_r:
  forall vs vs1 vs2,
  subVarSet vs1 (mkVarSet vs)  ->
  subVarSet vs1 (extendVarSetList vs2 vs) .
Proof.
  intros vs. 
  rewrite mkVarSet_extendVarSetList.
  induction vs; intros vs1 vs2.
  - autorewrite with hs_simpl.
    set_b_iff.
    fsetdec.
  - intro h.     
    autorewrite with hs_simpl in *.
    rewrite -> extendVarSetList_extendVarSet_iff in *.
    destruct (mem a (extendVarSetList empty vs)) eqn:Hd;
    [|destruct (mem a vs1) eqn:Hd'].
    + specialize (IHvs vs1 vs2). 
      set_b_iff.
      assert (Hvs2: In a (extendVarSetList vs2 vs)).
      * clear -Hd.
        eapply MP.in_subset.
        apply Hd. clear Hd a.
        apply extendVarSetList_subset.
        fsetdec.
      * pose proof (subset_equal
                     (equal_sym (add_equal Hvs2))).
        eapply (Subset_trans); [apply IHvs| apply H].
        pose proof (subset_equal (add_equal Hd)).
        fsetdec.
    + specialize (IHvs (remove a vs1) vs2). 
      set_b_iff.
      apply remove_s_m with (x:= a) (y:=a) in h;
        [|fsetdec].
      assert (Hs: remove a (add a
                                (extendVarSetList empty vs))
                         [<=] (extendVarSetList empty vs)).
      { apply subset_equal.
        apply remove_add.
        assumption. }
        specialize (IHvs (Subset_trans h Hs)).
      apply add_s_m with (x:= a) (y:=a) in IHvs;
        [|fsetdec].
      assert (Hs': vs1 [<=] add a (remove a vs1)).
      { apply subset_equal.
        apply equal_sym.
        apply add_remove.
        assumption. }
      eapply Subset_trans.
      apply Hs'.
      assumption.
    + specialize (IHvs vs1 vs2). 
      set_b_iff.
      apply subset_add_2.
      apply IHvs.
      eapply remove_s_m with (x:= a) (y:=a) in h;
        [|fsetdec].
      apply remove_equal in Hd'.
      fsetdec.
Qed.

    

Lemma subVarSet_delVarSet:
  forall vs1 v,
  subVarSet (delVarSet vs1 v) vs1 .
Proof.
  intros.
  set_b_iff.
  fsetdec.
Qed.


Lemma subVarSet_delVarSetList:
  forall vs1 vl,
  subVarSet (delVarSetList vs1 vl) vs1 .
Proof.
  intros.
  set_b_iff.
  generalize vs1. clear vs1. induction vl.
  - intros vs1. hs_simpl. 
    fsetdec.
  - intros vs1. revert IHvl.
    hs_simpl.
    simpl.
    intro IH. 
    rewrite -> IH with (vs1 := delVarSet vs1 a).
    set_b_iff.
    fsetdec.
Qed.


Lemma subVarSet_delVarSetList_both:
  forall vs1 vs2 vl,
  subVarSet vs1 vs2  ->
  subVarSet (delVarSetList vs1 vl) (delVarSetList vs2 vl) .
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
  subVarSet jps isvs  ->
  subVarSet (delVarSet jps v) (extendVarSet isvs v) .
Proof.
  intros.
  eapply subVarSet_trans.
  apply subVarSet_delVarSet.
  apply subVarSet_extendVarSet.
  assumption.
Qed.

Lemma subVarSet_delVarSetList_extendVarSetList:
  forall jps isvs vs,
  subVarSet jps isvs  ->
  subVarSet (delVarSetList jps vs) (extendVarSetList isvs vs) .
Proof.
  intros.
  eapply subVarSet_trans.
  apply subVarSet_delVarSetList.
  apply subVarSet_extendVarSetList.
  assumption.
Qed.


Lemma subVarSet_delVarSetList_extendVarSetList_dual:
  forall jps isvs vs,
  subVarSet jps (extendVarSetList isvs vs)  ->
  subVarSet (delVarSetList jps vs) isvs .
Proof.
  intros.
  revert jps isvs H.
  induction vs; intros.
  - rewrite !delVarSetList_nil.
    rewrite !extendVarSetList_nil in H.
    assumption.
  - rewrite delVarSetList_cons2.
    revert H.
    hs_simpl.
    intro H.
    apply IHvs in H.
    set_b_iff.
    fsetdec.
Qed.


Lemma mapUnionVarSet_In_subVarSet:
  forall a (x : a) xs f,
  List.In x xs ->
  subVarSet (f x) (mapUnionVarSet f xs).
Proof.
  intros a x xs f H.
  generalize dependent x.
  induction xs; intros x H.
  - inversion H.
  - 
    inversion H as [H'|H'].
    + unfold mapUnionVarSet.
      unfold_Foldable_foldr.
      subst.
      simpl.
      set_b_iff.
      fsetdec.
    + apply IHxs in H'.
      clear H IHxs.
      revert H'.
      unfold mapUnionVarSet.
      unfold_Foldable_foldr.
      intros H'.
      eapply subVarSet_trans.
      apply H'.
      clear H'.
      set_b_iff.
      simpl.
      fsetdec.
Qed.


Lemma subVarSet_mapUnionVarSet:
  forall a (xs : list a) f vs,
  Forall (fun x => subVarSet (f x) vs ) xs ->
  subVarSet (mapUnionVarSet f xs) vs.
Proof.
  intros a xs f vs H.
  induction xs.
  - unfold mapUnionVarSet.
    unfold_Foldable_foldr.
    simpl.
    apply subVarSet_emptyVarSet.
  - inversion H.
    subst.
    apply IHxs in H3.
    clear IHxs.
    revert H3.
    unfold mapUnionVarSet.
    unfold_Foldable_foldr.
    intros H3.
    set_b_iff.
    simpl.
    fsetdec.
Qed.


Lemma subVarSet_unionVarSet:
  forall vs1 vs2 vs3,
  subVarSet (unionVarSet vs1 vs2) vs3 = subVarSet vs1 vs3 && subVarSet vs2 vs3.
Proof.
  intros.
  apply eq_iff_eq_true.
  rewrite andb_true_iff.
  set_b_iff.
  split; intro H.
  - split; fsetdec.
  - destruct H; fsetdec.
Qed.


(** ** [disjointVarSet]  *)

Instance disjointVarSet_m : Proper (Equal ==> Equal ==> Logic.eq) disjointVarSet.
Proof. 
  move => x1 y1.  
  move: (@ValidVarSet_Axiom x1).
  move: (@ValidVarSet_Axiom y1).
  move: x1 => [x1]. move: y1=> [y1].
  move: x1 => [x1]. move: y1=> [y1].
  move=> vx1 vy1 Eq1.
  move=> x2 y2. 
  move: (@ValidVarSet_Axiom x2).   move: (@ValidVarSet_Axiom y2).
  move: x2 => [x2]. move: y2=> [y2].
  move: x2 => [x2]. move: y2=> [y2].
  move=> vx2 vy2 Eq2.  

  unfold ValidVarSet, disjointVarSet,
         UniqFM.disjointUFM,
         UniqSet.getUniqSet, 
         UniqSet.getUniqSet' in *.
  unfold lookupVarSet, UniqSet.lookupUniqSet,UniqFM.lookupUFM in *.
  unfold Equal, In, elemVarSet, UniqSet.elementOfUniqSet, UniqFM.elemUFM in Eq1.
  unfold Equal, In, elemVarSet, UniqSet.elementOfUniqSet, UniqFM.elemUFM in Eq2.
  apply null_intersection_eq; eauto.
  move=> k1.  
  split. move=> Ink1.
Admitted.


(*
Lemma foldl'_simplify (a b c :Type) (f:c -> b) (g:b->c) (h:b -> a -> b)
      (xb:b) (xs : list a):
  (forall x, f (g x) = x) ->
  Foldable.foldl' (fun x y => g (h (f x) y)) (g xb) xs = 
  g (Foldable.foldl' h xb xs).
Proof.  
  move => eq.
  induction xs.
  hs_simpl. auto.
  hs_simpl.
  rewrite eq.
*)

Lemma UniqSet_Mk_UniqSet_eta :
  forall a b (x : UniqSet.UniqSet a) (f : UniqSet.UniqSet a -> b), 
    match x with
    | UniqSet.Mk_UniqSet set => f (UniqSet.Mk_UniqSet set)
    end = f x.
Proof.            
  move => a b [set] //.
Qed.


Lemma disjointVarSet_empytVarSet:
  forall vs,
  disjointVarSet vs emptyVarSet.
Proof.
  move => vs1.
  elim: vs1 => [i].
  unfold disjointVarSet, emptyVarSet, elemVarSet.
  simpl.
  elim: i => [j].
  simpl.
  apply intersection_empty.
  done.
Qed.
Hint Rewrite disjointVarSet_empytVarSet:hs_simpl.

Lemma disjointVarSet_mkVarSet_nil:
  forall vs,
  disjointVarSet vs (mkVarSet []).
Proof.
  rewrite mkVarSet_extendVarSetList.
  hs_simpl.
  apply disjointVarSet_empytVarSet.
Qed.

Lemma disjointVarSet_extendVarSet vs1 var vs2 : 
  disjointVarSet vs1 (extendVarSet vs2 var) <->
  elemVarSet var vs1 = false /\ disjointVarSet vs1 vs2.
Proof.
  move: vs1 vs2 => [[i1]] [[i2]].
  unfold disjointVarSet, elemVarSet, extendVarSet.
  unfold UniqSet.getUniqSet,UniqSet.getUniqSet',
         UniqSet.elementOfUniqSet, UniqSet.addOneToUniqSet.
  unfold UniqFM.disjointUFM, UniqFM.elemUFM, UniqFM.addToUFM.
  set k:=  (Unique.getWordKey (Unique.getUnique var)).
  apply null_intersection_non_member.
Qed.

Lemma disjointVarSet_mkVarSet_cons:
  forall v vs1 vs2,
  disjointVarSet vs1 (mkVarSet (v :: vs2))  <->
  elemVarSet v vs1 = false /\ disjointVarSet vs1 (mkVarSet vs2) .
Proof.
  move=> v vs1 vs2.
  rewrite mkVarSet_extendVarSetList.
  hs_simpl.
  rewrite extendVarSetList_extendVarSet_iff.
  rewrite disjointVarSet_extendVarSet.
  tauto.
Qed.

      
Lemma disjointVarSet_mkVarSet_append:
  forall vs1 vs2 vs3,
  disjointVarSet vs1 (mkVarSet (vs2 ++ vs3))  <->
  disjointVarSet vs1 (mkVarSet vs2)  /\ disjointVarSet vs1 (mkVarSet vs3).
Proof.  
  move=> vs1 vs2 vs3.
  rewrite mkVarSet_extendVarSetList.
  hs_simpl.
  elim: vs3 => [|var vars IH]; hs_simpl.
  + rewrite mkVarSet_extendVarSetList.
    intuition.
  + rewrite disjointVarSet_mkVarSet_cons.
    rewrite and_comm.
    rewrite and_assoc.
    rewrite -> and_comm in IH.
    rewrite <- IH.
    rewrite extendVarSetList_extendVarSet_iff.
    rewrite disjointVarSet_extendVarSet.
    tauto.
Qed. 


Lemma disjointVarSet_mkVarSet:
  forall vs1 vs2,
  disjointVarSet vs1 (mkVarSet vs2)  <->
  Forall (fun v => elemVarSet v vs1 = false) vs2.
Proof.
  move => vs1 vs2.
  elim: vs2 => [|v vars IH].
  rewrite disjointVarSet_mkVarSet_nil. intuition.
  rewrite disjointVarSet_mkVarSet_cons. rewrite IH.
  intuition.
  - inversion H1. auto.
  - inversion H1. auto.
Qed.


Lemma disjointVarSet_subVarSet_l:
  forall vs1 vs2 vs3,
  disjointVarSet vs2 vs3  ->
  subVarSet vs1 vs2  ->
  disjointVarSet vs1 vs3 .
Proof.
  move=> [[i1]][[i2]][[i3]].
  unfold disjointVarSet, subVarSet, isEmptyVarSet,minusVarSet.
  unfold UniqSet.getUniqSet,UniqSet.getUniqSet',
  UniqSet.isEmptyUniqSet, UniqSet.minusUniqSet.
  unfold UniqFM.disjointUFM, UniqFM.isNullUFM, UniqFM.minusUFM.
  apply disjoint_difference.
Qed.


(** ** [filterVarSet] *)

Lemma filterVarSet_comp : forall f f' vs,
    filterVarSet f (filterVarSet f' vs) [=] filterVarSet (fun v => f v && f' v) vs.
Proof.
  intros.
  destruct vs; destruct getUniqSet'. simpl. do 2 f_equal.
  rewrite filter_comp.
  reflexivity.
Qed.


Lemma filterSingletonTrue : forall f x,
  RespectsVar f ->
  f x = true -> 
  filterVarSet f (unitVarSet x) [=] unitVarSet x.
Proof. 
  move=> f x RR TR.
  set_b_iff.
  replace (singleton x) with (add x empty).
  - rewrite -> filter_add_1; auto.
    fsetdec.
  - simpl. unfold singleton, unitVarSet, UniqSet.unitUniqSet.
    f_equal. unfold UniqFM.unitUFM; f_equal.
    unfold IntMap.insert, IntMap.singleton; f_equal.
    apply proof_irrelevance.
Qed.

Lemma filterSingletonFalse : forall f x,
  RespectsVar f ->
  f x = false -> 
  filterVarSet f (unitVarSet x) [=] emptyVarSet.
Proof. 
  move=> f x RR TR.
  set_b_iff.
  replace (singleton x) with (add x empty).
  - rewrite -> filter_add_2; auto.
    fsetdec.
  - simpl. unfold singleton, unitVarSet, UniqSet.unitUniqSet.
    f_equal. unfold UniqFM.unitUFM; f_equal.
    unfold IntMap.insert, IntMap.singleton; f_equal.
    apply proof_irrelevance.
Qed.

Lemma filterVarSet_emptyVarSet f :
  filterVarSet f emptyVarSet = emptyVarSet.
Proof.
  set_b_iff.
  simpl. unfold empty, emptyVarSet, UniqSet.emptyUniqSet.
  f_equal. unfold UniqFM.emptyUFM. f_equal.
  unfold IntMap.filter, IntMap.empty. simpl.
  f_equal. apply proof_irrelevance.
Qed.
Hint Rewrite filterVarSet_emptyVarSet : hs_simpl.


Lemma filterVarSet_constTrue vs : 
  filterVarSet (const true) vs = vs.
Proof. 
  unfold filterVarSet.
  elim: vs => [i].
  elim: i => [m].
  unfold UniqSet.filterUniqSet.
  unfold UniqFM.filterUFM.
  f_equal.
  f_equal.
  rewrite filter_true.
  reflexivity.
Qed.
Hint Rewrite filterVarSet_constTrue : hs_simpl.

Lemma elemVarSet_filterVarSet x f vs :
  RespectsVar f ->
  elemVarSet x (filterVarSet f vs) = f x && elemVarSet x vs.
Proof.
  move => h.
  rewrite eqE.
  set_b_iff.
  rewrite andE.
  unfold is_true.
  set_b_iff.
  rewrite and_comm.
  apply F.filter_iff.
  auto.
Qed.

Lemma filterVarSet_iff (f1 f2 : Var -> bool) vs : 
  (forall x, (f1 x) <-> (f2 x)) -> 
  filterVarSet f1 vs [=] filterVarSet f2 vs.
Admitted.

Lemma filterVarSet_equal f vs1 vs2 :
  RespectsVar f -> 
  vs1 [=] vs2 ->
  filterVarSet f vs1 [=] filterVarSet f vs2.
Proof.
  move => RF EQ.
  set_b_iff.
  eapply filter_equal; eauto.
Qed.

Lemma filterVarSet_extendVarSet : 
  forall f v vs,
    RespectsVar f ->
    filterVarSet f (extendVarSet vs v) [=] 
    if (f v) then extendVarSet (filterVarSet f vs) v 
    else (filterVarSet f vs).
Proof.
  intros.
  set_b_iff.
  destruct (f v) eqn:Hfv; auto.
  rewrite -> filter_add_1; try done.
  rewrite -> filter_add_2; try done.
Qed.


Lemma lookupVarSet_filterVarSet_true : forall f v vs,
  RespectsVar f ->
  f v = true ->
  lookupVarSet (filterVarSet f vs) v = lookupVarSet vs v.
Proof.
  intros.
  destruct (lookupVarSet (filterVarSet f vs) v) eqn:Hl.
  - revert Hl.
    unfold_VarSet_to_IntMap.
    unfold IntMap.filter.
    symmetry.
    erewrite lookup_filterWithKey.
    + reflexivity.
    + apply Hl.
  - apply lookupVarSet_None_elemVarSet in Hl.
    symmetry.
    apply lookupVarSet_None_elemVarSet.
    set_b_iff.
    intros Hin.
    eapply filter_3 in Hin; eauto.
Qed.

Lemma lookupVarSet_filterVarSet_false : forall f v vs,
  RespectsVar f ->
  f v = false ->
  lookupVarSet (filterVarSet f vs) v = None.
Proof.
  intros.
  apply lookupVarSet_None_elemVarSet.
  set_b_iff.
  rewrite filter_iff; [|auto].
  intros [H1 H2].
  rewrite H0 in H2.
  inversion H2.
Qed.

Lemma unionVarSet_filterVarSet f vs1 vs2 :
  RespectsVar f ->
  unionVarSet (filterVarSet f vs1) (filterVarSet f vs2) [=] filterVarSet f (unionVarSet vs1 vs2).
Proof.
  move=> g.
  set_b_iff.
  rewrite <- filter_union.
  reflexivity.
  eauto.
Qed.

Lemma filterVarSet_delVarSet f vs v :
  RespectsVar f ->
  filterVarSet f (delVarSet vs v) [=]
  delVarSet (filterVarSet f vs) v.
Proof.
  move=> Ff. unfold RespectsVar in Ff.
  set_b_iff. 
Admitted.


Lemma filterVarSet_delVarSetList:
  forall (f : Var -> bool)  (vars : list Var) (vs : VarSet),
  RespectsVar f ->
  filterVarSet f (delVarSetList  vs vars) [=] delVarSetList (filterVarSet f vs) vars.
Proof.
  induction vars.
  - move=> vs h. hs_simpl. reflexivity.
  - move=> vs h.  hs_simpl. 
    rewrite IHvars; try done.
    rewrite <- filterVarSet_delVarSet; try done.
Qed.


(** ** [unionVarSet] *)

Lemma unionVarSet_sym vs1 vs2 : unionVarSet vs1 vs2 [=] unionVarSet vs2 vs1.
Proof. set_b_iff. fsetdec. Qed.


Lemma unionEmpty_l : forall vs,
    unionVarSet emptyVarSet vs [=] vs.
Proof. set_b_iff. fsetdec. Qed.
Lemma unionEmpty_r : forall vs,
    unionVarSet vs emptyVarSet [=] vs.
Proof. set_b_iff. fsetdec. Qed.
Lemma unionSingle_l : forall x s,
    unionVarSet (unitVarSet x) s [=] extendVarSet s x.
Proof. intros. set_b_iff. fsetdec. Qed.
Lemma unionSingle_r : forall x s,
    unionVarSet s (unitVarSet x) [=] extendVarSet s x.
Proof. intros. set_b_iff. fsetdec. Qed.

Hint Rewrite unionEmpty_l unionEmpty_r 
     unionSingle_l unionSingle_r :
  hs_simpl.


(** ** [minusVarSet] *)

Lemma minusVarSet_emptyVarSet vs : 
  minusVarSet vs emptyVarSet = vs.
Proof.
  unfold minusVarSet, emptyVarSet.
  unfold UniqSet.minusUniqSet, UniqSet.emptyUniqSet.
  elim: vs => [i].
  elim: i => [m].
  unfold UniqFM.minusUFM, UniqFM.emptyUFM.
  f_equal.
  f_equal.
  unfold IntMap.empty.
  rewrite difference_nil_r.
  reflexivity.
Qed.

Hint Rewrite minusVarSet_emptyVarSet : hs_simpl.

Lemma minusVarSet_emptyVarSet_l vs : 
  minusVarSet emptyVarSet vs = emptyVarSet.
Proof.
  unfold minusVarSet, emptyVarSet.
  unfold UniqSet.minusUniqSet, UniqSet.emptyUniqSet.
  elim: vs => [i].
  elim: i => [m].
  unfold UniqFM.minusUFM, UniqFM.emptyUFM.
  f_equal.
  f_equal.
  unfold IntMap.empty.
  rewrite difference_nil_l.
  reflexivity.
Qed.

Hint Rewrite minusVarSet_emptyVarSet_l : hs_simpl.



Lemma elemVarSet_minusVarSetTrue : forall x s,
  elemVarSet x s = true -> 
  minusVarSet (unitVarSet x) s [=] emptyVarSet.
Proof. intros. set_b_iff.
       split; try fsetdec.
       move=> h.
       move: (diff_1 _ _ _ h) => h1.
       move: (diff_2 _ _ _ h) => h2.
       inversion h1. clear h1.
       unfold IntMap.member, Internal.member in H1; simpl in H1.
       destruct (compare _ _) eqn:H2 in H1;
         try solve [inversion H1].
       apply Bounds.compare_Eq in H2.
       rewrite <- var_eq_realUnique in H2.
       rewrite -> fold_is_true in H2.
       unfold In in H, h2.
       rewrite (@elemVarSet_eq a x) in h2; done.
Qed.


Lemma elemVarSet_minusVarSetFalse : forall x s,
  elemVarSet x s = false -> 
  minusVarSet (unitVarSet x) s [=] unitVarSet x.
Proof.
  intros. 
  set_b_iff.
  split; try fsetdec.
  move=> h.
  apply diff_3; try done.
  inversion h.
  unfold In, singleton in *.
  rewrite  (@elemVarSet_eq x a) in H; try done.
  rewrite var_eq_realUnique.
  unfold IntMap.member, Internal.member in H1; simpl in H1.
  destruct (compare _ _) eqn:H2 in H1; try solve [inversion H1].
  apply Bounds.compare_Eq in H2.
  rewrite Eq_sym; done.
Qed.



Lemma elemVarSet_minusVarSet x vs1 vs2 :
  elemVarSet x (minusVarSet vs1 vs2) = elemVarSet x vs1 && ~~ elemVarSet x vs2.
Proof.
  rewrite eqE.
  set_b_iff.
  rewrite F.diff_iff.
  split.
  move => [h1 h2]. apply /andP. split. auto.
  apply /negPf.
  set_b_iff. auto.
  move => /andP [h1 h2].
  move: h2 => /negPf => h2.
  set_b_iff. auto.
Qed.


Lemma unionVarSet_minusVarSet vs1 vs2 vs :
  unionVarSet (minusVarSet vs1 vs) (minusVarSet vs2 vs) [=]
  minusVarSet (unionVarSet vs1 vs2) vs.
Proof.
  unfold Equal.
  move=> x.
  unfold In.
  rewrite! elemVarSet_minusVarSet.
  rewrite! elemVarSet_unionVarSet.
  rewrite! elemVarSet_minusVarSet.
  rewrite! andb_orb_distrib_l.
  reflexivity.
Qed.


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


Lemma StrongSubset_refl : forall vs, 
    StrongSubset vs vs.
Proof.
  unfold StrongSubset.
  move=> vs var.
  elim h: (lookupVarSet vs var) => //.
  eapply almostEqual_refl.
Qed.

Instance StrongSubset_Reflexive : Reflexive StrongSubset := StrongSubset_refl.

Lemma StrongSubset_trans : forall vs1 vs2 vs3, 
    StrongSubset vs1 vs2 -> StrongSubset vs2 vs3 -> StrongSubset vs1 vs3.
Proof.
  move => vs1 vs2 vs3 h1 h2 var.
  specialize (h1 var).
  specialize (h2 var).
  move: h1 h2.
  elim p1: (lookupVarSet vs1 var) => //;
  elim p2: (lookupVarSet vs2 var) => //;
  elim p3: (lookupVarSet vs3 var) => //.
  eapply almostEqual_trans.
Qed.


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
  rewrite -> lookupVarSet_eq with (v2 := v); auto.
  rewrite H. auto.
  destruct (lookupVarSet vs var) eqn:Lvar; auto.
  rewrite lookupVarSet_extendVarSet_neq.
  rewrite Lvar.
  apply almostEqual_refl.
  unfold CoreBndr in *. intro h. rewrite Base.Eq_sym in h. rewrite h in EQV. discriminate.
Qed.

Lemma elemNegbDisjoint : forall vs vs2, 
    disjointVarSet vs (mkVarSet vs2) ->
    forall v, Foldable.elem v vs2 -> negb (elemVarSet v vs).
Proof.
  move=> vs.
  elim => [|x xs IHxs].
  - move => ? v. hs_simpl. done.
  - rewrite disjointVarSet_mkVarSet_cons.
    move => [h1 h2] v.
    hs_simpl.
    move => /orP [h3|h3].
    erewrite (@elemVarSet_eq x v) in h1.
    rewrite h1. done.
    symmetry. done.
    apply IHxs; try done.
Qed.



Lemma StrongSubset_extendList_fresh :
  forall vs vs2,
  disjointVarSet vs (mkVarSet vs2)  ->
  StrongSubset vs (extendVarSetList vs vs2).
Proof.
  intros.
  unfold StrongSubset.
  intros v.
  destruct_match; try trivial.
  case in2: (Foldable.elem v vs2).  
  * eapply elemNegbDisjoint in in2; eauto.
    eapply lookupVarSet_elemVarSet in Heq; eauto. 
    erewrite Heq in in2. done.
  * rewrite lookupVarSet_extendVarSetList_false; try done.
    rewrite Heq.
    eapply almostEqual_refl.
    rewrite in2. done.
Qed.


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

Lemma lookupVarSet_delVarSet_None:
  forall v vs, lookupVarSet (delVarSet vs v) v = None.
Proof.
  intros.
  unfold lookupVarSet,
  UniqSet.lookupUniqSet,
  UniqFM.lookupUFM.
  unfold delVarSet,
  UniqSet.delOneFromUniqSet,
  UniqFM.delFromUFM.
  destruct vs.
  destruct getUniqSet'.
  simpl.
  apply delete_eq.
Qed.

Lemma StrongSubset_delVarSet :
  forall vs1 vs2 v,
  StrongSubset vs1 vs2 ->
  StrongSubset (delVarSet vs1 v) (delVarSet vs2 v).
Proof.
  intros.
  unfold StrongSubset in *.
  intro var.
  specialize (H var).
  destruct (v == var) eqn:EQv.
  - rewrite Base.Eq_sym in EQv.
    erewrite lookupVarSet_eq;
      [|eassumption].
    rewrite lookupVarSet_delVarSet_None.
    trivial.
  - rewrite lookupVarSet_delVarSet_neq;
      [|rewrite EQv; auto].
    destruct (lookupVarSet vs1 var) eqn:Hl; auto.
    rewrite lookupVarSet_delVarSet_neq;
      [|rewrite EQv; auto].
    auto.
Qed.

Lemma StrongSubset_delete_fresh :
  forall vs v,
  lookupVarSet vs v = None ->
  StrongSubset vs (delVarSet vs v).
Proof.
  intros.
  unfold StrongSubset in *.
  intro var.
  destruct (v == var) eqn:EQv.
  - rewrite Base.Eq_sym in EQv.
    erewrite lookupVarSet_eq;
      [|eassumption].
    rewrite H.
    trivial.
  - rewrite lookupVarSet_delVarSet_neq;
      [|rewrite EQv; auto].
    destruct (lookupVarSet vs var) eqn:Hl; auto.
    apply almostEqual_refl.
Qed.

Lemma StrongSubset_delVarSetList:
  forall vs1 vs2 vs,
  StrongSubset vs1 vs2 ->
  StrongSubset (delVarSetList vs1 vs) (delVarSetList vs2 vs).
Proof.
  intros vs1 vs2 vs.
  generalize dependent vs2.
  generalize dependent vs1.
  induction vs;
    intros vs1 vs2 H; hs_simpl;
      [assumption|].
  eapply StrongSubset_delVarSet in H.
  eauto.
Qed.

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
  forall (P Q : VarSet -> bool),
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
  rewrite -> Forall_forall in *.
  firstorder.
Qed.

Lemma Respects_StrongSubset_forallb:
  forall a (xs : list a) P,
    Forall (fun x => Respects_StrongSubset (fun vs => P vs x = true)) xs ->
    Respects_StrongSubset (fun vs => forallb (P vs) xs = true).
Proof.
  unfold Respects_StrongSubset in *.
  intros.
  rewrite -> forallb_forall in *.
  rewrite -> Forall_forall in *.
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
Proof.
  intros v P H vs1 vs2 Hs Hvs1.
  apply StrongSubset_delVarSet with (v:=v) in Hs.
  unfold Respects_StrongSubset in H.  
  apply H in Hs; auto.
Qed.

Lemma Respects_StrongSubset_delVarSetList:
  forall vs2 P,
  Respects_StrongSubset (fun vs : VarSet => P vs) ->
  Respects_StrongSubset (fun vs : VarSet => P (delVarSetList vs vs2)).
Proof.
  intros vs2 P H vs vs' Hs Hvs2.
  apply StrongSubset_delVarSetList with (vs:=vs2) in Hs.
  unfold Respects_StrongSubset in H.  
  apply H in Hs; auto.
Qed.


Lemma Respects_StrongSubset_extendVarSet:
  forall v P,
  Respects_StrongSubset (fun vs : VarSet => P vs) ->
  Respects_StrongSubset (fun vs : VarSet => P (extendVarSet vs v)).
Proof.
  intros v P H vs vs' Hs Hvs.
  apply StrongSubset_extend with (v:=v) in Hs.
  unfold Respects_StrongSubset in H.
  apply H in Hs; auto.
Qed.


Lemma Respects_StrongSubset_extendVarSetList:
  forall vs' P,
  Respects_StrongSubset (fun vs : VarSet => P vs) ->
  Respects_StrongSubset (fun vs : VarSet => P (extendVarSetList vs vs')).
Proof.
  intros vs P H vs1 vs2 Hs Hvs1.
  eapply StrongSubset_extendVarSetList with (l:=vs) in Hs.
  unfold Respects_StrongSubset in H.
  apply H in Hs; auto.
Qed. 

Lemma StrongSubset_filterVarSet: 
  forall f1 f2 vs,
    RespectsVar f1 -> RespectsVar f2 ->
  (forall v, f1 v = true  -> f2 v = true) ->
  filterVarSet f1 vs {<=} filterVarSet f2 vs.
Proof.
  intros.
  unfold StrongSubset.
  intros var.
  destruct (f1 var) eqn:Heq1.
  - rewrite lookupVarSet_filterVarSet_true; auto.
    destruct (lookupVarSet vs var) eqn:Hl; [|trivial].
    rewrite lookupVarSet_filterVarSet_true; auto.
    rewrite Hl.
    apply almostEqual_refl.
  - rewrite lookupVarSet_filterVarSet_false; auto.
Qed.

(* Is this weakening? *)
Lemma weaken:
  forall {P : VarSet -> Prop} {R : Respects_StrongSubset P},
  forall {vs1} {vs2},
  StrongSubset vs1 vs2 ->
  P vs1 -> P vs2.
Proof. intros. unfold Respects_StrongSubset in R. eapply R; eassumption. Qed.

Lemma weakenb:
  forall {P : VarSet -> bool} {R : Respects_StrongSubset (fun x => P x )},
  forall {vs1} {vs2},
  StrongSubset vs1 vs2 ->
  P vs1  -> P vs2 .
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





(* A list of variables is fresh for a given varset when 
   any variable with a unique found in the list is not found 
   in the set. i.e. this is list membership using GHC.Base.==
   for vars. 
*)

Definition freshList (vars: list Var) (vs :VarSet) :=
  (forall (v:Var), Foldable.elem v vars  -> 
              lookupVarSet vs v = None).

Lemma freshList_nil : forall v,  freshList nil v.
Proof.
  unfold freshList. intros v v0 H. inversion H.
Qed.

Lemma freshList_cons : forall (x:Var) l (v:VarSet),  
    lookupVarSet v x = None /\ freshList l v <-> freshList (x :: l) v.
Proof.
  unfold freshList. intros. 
  split. 
  + intros [? ?] ? ?.
    rewrite elem_cons in H1.
    destruct (orb_prop _ _ H1) as [EQ|IN].
    rewrite -> lookupVarSet_eq with (v2 := x); auto.
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
Proof.
  apply StrongSubset_extend_fresh.
Qed.

Lemma StrongSubset_extendVarSetList_fresh : 
  forall vs vars, freshList vars vs ->
             StrongSubset vs (extendVarSetList vs vars).
Proof.
  intros.
  apply StrongSubset_extendList_fresh.
  apply disjointVarSet_mkVarSet.
  induction vars; auto.
  apply freshList_cons in H as [H1 H2].
  apply Forall_cons; auto.
  apply lookupVarSet_None_elemVarSet.
  assumption.
Qed.


Lemma elemVarSet_unitVarSet_is_eq :
  forall x v, elemVarSet x (unitVarSet v) = GHC.Base.op_zeze__ x v.
Proof.
  intros.
  destruct (GHC.Base.op_zeze__ x v) eqn:Hcomp.
  - apply varUnique_iff in Hcomp; inversion Hcomp.
    cbn. rewrite H0 N.compare_refl =>//.
  - apply ssrbool.negbT, notE in Hcomp.
    cbn. apply not_true_iff_false.
    destruct (N.compare _ _) eqn:Hcomp'; auto.
    contradiction Hcomp.
    apply varUnique_iff. rewrite /varUnique.
    f_equal. apply N.compare_eq_iff =>//.
Qed.
