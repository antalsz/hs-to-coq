From Coq Require Import ssreflect ssrfun ssrbool.
Require Import Psatz.
Require Import Coq.Lists.List.
Require Import Coq.NArith.BinNat.
Import ListNotations.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import SetoidList.

Require Import GHC.Base.

Require Import Proofs.GHC.Base.
Require Import Proofs.GHC.List.
Require Import Proofs.Data.Foldable.

Require Import CoreFVs.
Require Import Id.
Require Import Core.
Require UniqFM.

Require Import Proofs.ContainerAxioms.
Require Import Proofs.GhcTactics.
Require Import Proofs.Unique.
Require Import Proofs.Var.
Require Import Proofs.VarSetFSet.

Open Scope Z_scope.


Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Bullet Behavior "Strict Subproofs".

(* Stephanie's hack. *)
Lemma fold_is_true : forall b, b = true <-> is_true b.
Proof. intros. unfold is_true. reflexivity. Qed.

(* Move to base *)

Ltac unfold_zeze :=
  repeat unfold op_zeze__, op_zeze____, 
  Eq___option, Base.Eq___option_op_zeze__,
  Eq_Int___, 
  Eq_Integer___, 
  Eq_Word___, 
  Eq_Char___, 
  Eq_bool___, 
  Eq_unit___ , 
  Eq_comparison___, 
  Eq_pair___ , 
  Eq_list, 
  Eq___NonEmpty, Base.Eq___NonEmpty_op_zeze__.

Lemma simpl_option_some_eq a `{Eq_ a} (x y :a) :
  (Some x == Some y) = (x == y).
Proof.  
    repeat unfold Eq___option, op_zeze__, op_zeze____, 
           Base.Eq___option_op_zeze__, op_zeze____.
    auto.
Qed.

Lemma simpl_option_none_eq a `{Eq_ a} :
  ((None : option a) == None) = true.
Proof.  
    repeat unfold Eq___option, op_zeze__, op_zeze____, 
           Base.Eq___option_op_zeze__, op_zeze____.
    auto.
Qed.


Lemma simpl_list_cons_eq a `{Eq_ a} (x y :a) xs ys :
  (cons x xs) == (cons y ys) = (x == y) && (xs == ys).
Proof.  
    unfold op_zeze__, op_zeze____, Eq_list.
    simpl.
    auto.
Qed.

Lemma simpl_list_nil_eq a `{Eq_ a} :
  (nil : list a) == nil = true.
Proof.  
    unfold op_zeze__, op_zeze____, Eq_list.
    simpl.
    auto.
Qed.

Hint Rewrite @simpl_option_some_eq @simpl_option_none_eq 
             @simpl_list_cons_eq @simpl_list_nil_eq : hs_simpl.

Lemma var_eq_realUnique v1 v2 : 
  (v1 == v2) = (realUnique v1 == realUnique v2).
Proof.
  repeat unfold op_zeze__, op_zeze____,Core.Eq___Var_op_zeze__,Core.Eq___Var.
  auto.
Qed.



(* I would love to be able to use rewriting instead of this 
   lemma to do this. Why doesn't it work??? *)
Lemma eq_replace_r : forall a (v1 v2 v3 : a) `{EqLaws a}, 
    (v2 == v3) -> (v1 == v2) = (v1 == v3).
Proof.
  intros.
  rewrite -> H1. (* why does the ssreflect rewriting tactic not work here. *)
  reflexivity.
Qed.

Lemma eq_replace_l : forall a (v1 v2 v3 : a) `{EqLaws a}, 
    (v2 == v3) -> (v2 == v1) = (v3 == v1).
Proof.
  intros.
  eapply Eq_m.
  eauto.
  eapply Eq_refl.
Qed.


(* Some cargo culting here. I'm not sure if we need to do all of this.*)

Local Lemma parametric_eq_trans : forall (a : Type) (H : Eq_ a),
  EqLaws a -> Transitive (fun x y : a => x == y).
Proof.
  intros.
  intros x y z.
  pose (k := Eq_trans).
  eapply k.
Defined. 

Local Lemma parametric_eq_sym : forall (a : Type) (H : Eq_ a),
  EqLaws a -> Symmetric (fun x y : a => x == y).
Proof.
  intros.
  intros x y.
  rewrite Eq_sym.
  auto.
Defined. 


Add Parametric Relation {a}`{H: EqLaws a} : a 
  (fun x y => x == y) 
    reflexivity proved by Eq_refl 
    symmetry proved by (@parametric_eq_sym a _ H)
    transitivity proved by (@parametric_eq_trans a _ H) as parametric_eq.

Instance: RewriteRelation (fun x y => x == y).


Lemma eqlist_Foldable_elem : forall a (s s' : list a) `{EqLaws a}, 
      eqlistA (fun x y => x == y) s s' ->
      (forall a, Foldable.elem a s = Foldable.elem a s').
Proof.
  intros a s s' EQ EQL. intro H. induction H.
  intro x.
  rewrite elem_nil. auto.
  intro y. 
  repeat rewrite -> elem_cons.
  rewrite IHeqlistA.
  erewrite eq_replace_r; eauto.
Qed.


Lemma memE : forall (s : t) (x : elt), mem x s <-> In x s.
Proof.
  intros. unfold is_true. rewrite <- mem_iff. reflexivity. Qed.


Lemma subsetE : forall (s s' : t), subset s s' <->  s [<=] s'.
Proof.
  intros. unfold is_true. rewrite <- subset_iff. reflexivity. Qed.




(** ** Valid VarSets *)

(* This property is an invariant of the VarSet/UniqFM type. We may want to either 
   axiomatize it or add it to a sigma type in one of the definitions. *)

Definition ValidVarSet (vs : VarSet) : Prop :=
  forall v1 v2, lookupVarSet vs v1 = Some v2 -> (v1 == v2).

Axiom ValidVarSet_Axiom : forall vs, ValidVarSet vs.

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
  intros. destruct x; destruct getUniqSet'.
  destruct y; destruct getUniqSet'.
  reflexivity. Qed.

Lemma filterVarSet_filter : forall f x, filterVarSet f x = filter f x.
  reflexivity. Qed.


(* This tactic rewrites the boolean functions into the 
   set properties to make them more suitable for fsetdec. *)

Ltac set_b_iff :=
  repeat
   progress
    rewrite <- not_mem_iff in *
  || rewrite <- mem_iff in *
  || rewrite -> memE in *
  || rewrite <- subset_iff in *
  || rewrite -> subsetE in *
  || rewrite <- is_empty_iff in *
  || rewrite -> emptyVarSet_empty in *
  || rewrite -> delVarSet_remove in *
  || rewrite -> extendVarSet_add in *
  || rewrite -> unionVarSet_union in *
  || rewrite -> minusVarSet_diff in *
  || rewrite -> filterVarSet_filter in *
  || rewrite -> empty_b in *
  || rewrite -> unitVarSet_singleton in *.



(** List based operations in terms of folds *)

Lemma extendVarSetList_foldl' : forall x xs, 
    extendVarSetList x xs = Foldable.foldl' (fun x y => add y x) x xs.
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

(** ** [lookupVarSet] respects GHC.Base.== *)

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


(*
Ltac unfold_zeze_option := 
    repeat unfold_zeze;
           unfold Eq___option,
           Base.Eq___option_op_zeze__. *)

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

(** ** [elemVarSet] respects GHC.Base.== *)

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

(*
Lemma  In_hd_cons: forall v vs,
  In v (UniqSet.mkUniqSet (v :: vs)).
Proof.
  intros v vs.
  
Abort.
    
Lemma hd_VarSet_subset: forall v vs,
  UniqSet.mkUniqSet [v]
  [<=] UniqSet.mkUniqSet (v :: vs).
Proof.
  intros v vs.
  apply subset_2.
  unfold subset.
  apply subset_mem_1.
  intros a Hm.
  rewrite <- mem_iff.
  rewrite <- mem_iff in Hm.
  apply singleton_iff in Hm.
  rewrite singleton_iff in Hm.
  eapply In_eq_iff in Hm.
  rewrite Hm.
  clear Hm.
  unfold In, elemVarSet, UniqSet.elementOfUniqSet,
  UniqFM.elemUFM.
  simpl.
  destruct (UniqSet.mkUniqSet (v :: vs)) as [u] eqn:Hus.
  destruct u.
Abort.
  
Lemma elemVarSet_cons_hd:
   forall v1 v2 vs, (v1 == v2) = true ->
  (elemVarSet v1 (mkVarSet (v2 :: vs))) = true.
Proof.
  intros.
  set_b_iff.
  unfold mkVarSet.
  eapply in_subset with (s1:= mkVarSet [v2]).
  - apply singleton_iff.
    unfold Var_as_DT.eqb.
    rewrite Eq_sym.
    assumption.
  - unfold mkVarSet.
    simpl.
Abort.

  
Lemma elemVarSet_cons: forall v1 v2 vs,
  (elemVarSet v1 (mkVarSet (v2 :: vs))) =
  (v1 == v2) ||  (negb (v1 == v2) && elemVarSet v1 (mkVarSet vs)).
Proof.
  intros.
  unfold_VarSet.
  simpl.
  unfold mkVarSet.
  unfold UniqSet.mkUniqSet.
  unfold elemVarSet.
  unfold UniqSet.elementOfUniqSet.
  unfold UniqFM.elemUFM.
  destruct (v1 == v2) eqn:Heq; simpl.
  - rewrite eq_unique in Heq.
    simpl in *.
    rewrite Heq.
    destruct (mkVarSet (v2 :: vs)) as [u] eqn:Hv.
    destruct u.
Abort.
*)



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


Lemma orE : forall a b, (a || b) <-> a \/ b.
Proof. intros a b. unfold is_true. rewrite orb_true_iff. tauto. Qed.

(** ** [extendVarSetList] **)

(* These lemmas show that extendVarSetList respects [=] 
    *)

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
  rewrite memE.
  rewrite memE.
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
  rewrite memE.
  rewrite memE.
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

(* We could axiomatize these in terms of In, but that would not be strong 
   enough. As lookup is keyed on the uniques only, we need to specify 
   list membership via Var's == only. *)

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




Instance Foldable_proper : forall {a}`{EqLaws a},  
  Proper ((fun (x y:a) => x == y) ==> (fun (x y:list a) => x == y) ==> Logic.eq)
         Foldable.elem.
Proof.
  intros a E1 E2 x1 x2 Hx.
  move => y1. induction y1.
  - unfold_zeze. move => y2 Hy.
    destruct y2.
    auto.
    simpl in Hy.
    done.
  - case;
    unfold_zeze;
    simpl.
    done.
    move => a1 l.
    hs_simpl.
    move/andP => [h0 h1].
    rewrite (eq_replace_l a0 Hx).
    rewrite (eq_replace_r x2 h0).
    ssrbool.bool_congr.
    eapply IHy1.
    unfold_zeze.
    auto.
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


Lemma lookupVarSet_extendVarSetList_self_exists:
  forall (vars:list Var) v vs,
    (Foldable.elem v vars) -> 
    exists v', lookupVarSet (extendVarSetList vs vars) v = Some v' 
          /\ v == v'.
Proof.
  move=> vars v vs E. 
  move: (lookupVarSet_extendVarSetList_self vs E) => h0.
  unfold op_zeze__, Eq___option,op_zeze____ , Base.Eq___option_op_zeze__ in h0.
  destruct (lookupVarSet (extendVarSetList vs vars) v) eqn:h1.
  - exists v0. split; auto.
    rewrite Eq_sym.
    auto.
  - done.
Qed.


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


Lemma lookupVarSet_extendVarSetList_l
  v vs1 vs2 :
  ~~ elemVarSet v (mkVarSet vs2) ->
  lookupVarSet (extendVarSetList vs1 vs2) v = lookupVarSet vs1 v.
Proof.
  hs_simpl.
  elim: vs2 vs1 => [|a vars IH] vs1 //.
  - 
    rewrite elem_cons. (* why does hs_simpl not do this?? *)
    hs_simpl.

    rewrite orbF.  (* F comes last and it is false *)
    rewrite negb_orb => /andP [? ?].

    rewrite lookupVarSet_extendVarSetList_false //.
    rewrite lookupVarSet_extendVarSet_neq //.

    apply /negP.       (* update lookupVarSet_extendVarSet_neq *)
    rewrite Eq_sym //. 
Qed.
    

Lemma lookupVarSet_extendVarSetList_r_self:
  forall v vs1 vs2,
  List.In v vs2 ->
  NoDup (map varUnique vs2) ->
  lookupVarSet (extendVarSetList vs1 vs2) v = Some v.
Proof.
  move=> v vs1 vs2.
  apply lookupVarSet_extendVarSetList_self_in.
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
    rewrite orbF.
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

Lemma lookupVarSet_delVarSet_neq :
      forall v1 v2 vs,
      not (v1 == v2 ) ->
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

(*
Lemma elemVarSet_unitVarSet: forall v1 v2,
  (elemVarSet v1 (unitVarSet v2) ) <-> (varUnique v1 = varUnique v2).
Proof.
  intros v1 v2.
  set_b_iff.
  rewrite singleton_iff.
  unfold Var_as_DT.eqb.
  unfold_zeze.
Admitted. *)

Lemma false_is_not_true :
  forall b, b = false <-> b <> true.
Proof.
  destruct b; intuition.
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
  subVarSet (f x) (mapUnionVarSet f xs) .
Admitted.

Lemma subVarSet_mapUnionVarSet:
  forall a (xs : list a) f vs,
  Forall (fun x => subVarSet (f x) vs ) xs ->
  subVarSet (mapUnionVarSet f xs) vs .
Admitted.


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


Axiom disjointVarSet_mkVarSet:
  forall vs1 vs2,
  disjointVarSet vs1 (mkVarSet vs2)  <->
  Forall (fun v => elemVarSet v vs1 = false) vs2.

Axiom disjointVarSet_mkVarSet_nil:
  forall vs,
  disjointVarSet vs (mkVarSet []) .


Axiom disjointVarSet_mkVarSet_cons:
  forall v vs1 vs2,
  disjointVarSet vs1 (mkVarSet (v :: vs2))  <->
  elemVarSet v vs1 = false /\ disjointVarSet vs1 (mkVarSet vs2) .

Axiom disjointVarSet_mkVarSet_append:
  forall vs1 vs2 vs3,
  disjointVarSet vs1 (mkVarSet (vs2 ++ vs3))  <->
  disjointVarSet vs1 (mkVarSet vs2)  /\ disjointVarSet vs1 (mkVarSet vs3) .


Axiom disjointVarSet_subVarSet_l:
  forall vs1 vs2 vs3,
  disjointVarSet vs2 vs3  ->
  subVarSet vs1 vs2  ->
  disjointVarSet vs1 vs3 .



(** ** [filterVarSet] *)

Lemma filterVarSet_comp : forall f f' vs,
    filterVarSet f (filterVarSet f' vs) = filterVarSet (fun v => f v && f' v) vs.
Proof.
  intros.
  destruct vs; destruct getUniqSet'. simpl. do 2 f_equal.
  apply filter_comp.
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
  rewrite -> lookupVarSet_eq with (v2 := v); auto.
  rewrite H. auto.
  destruct (lookupVarSet vs var) eqn:Lvar; auto.
  rewrite lookupVarSet_extendVarSet_neq.
  rewrite Lvar.
  apply almostEqual_refl.
  unfold CoreBndr in *. intro h. rewrite Base.Eq_sym in h. rewrite h in EQV. discriminate.
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
  intros.
Admitted.

Lemma Respects_StrongSubset_delVarSetList:
  forall vs2 P,
  Respects_StrongSubset (fun vs : VarSet => P vs) ->
  Respects_StrongSubset (fun vs : VarSet => P (delVarSetList vs vs2)).
Proof.
  
Admitted. (* This is tricky, because of rewriting under a binder :-( *)

Lemma Respects_StrongSubset_extendVarSet:
  forall v P,
  Respects_StrongSubset (fun vs : VarSet => P vs) ->
  Respects_StrongSubset (fun vs : VarSet => P (extendVarSet vs v)).
Proof.
  
Admitted.

Lemma Respects_StrongSubset_extendVarSetList:
  forall v P,
  Respects_StrongSubset (fun vs : VarSet => P vs) ->
  Respects_StrongSubset (fun vs : VarSet => P (extendVarSetList vs v)).
Proof.
  
Admitted. (* This is tricky, because of rewriting under a binder :-( *)


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
    lookupVarSet v x= None /\ freshList l v <-> freshList (x :: l) v.
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

Lemma filterVarSet_extendVarSet : 
  forall f v vs,
    filterVarSet f (extendVarSet vs v) = 
    if (f v) then extendVarSet (filterVarSet f vs) v 
    else (filterVarSet f vs).
Proof.
  intros.
  unfold_VarSet_to_IntMap.
  do 2 f_equal.
  rewrite filter_insert.
  destruct (f v) eqn:Hfv; auto.
Qed.


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
  (forall v, f1 v = true  -> f2 v = true) ->
  filterVarSet f1 vs {<=} filterVarSet f2 vs.
Proof.
  intros.
  induction vs.

  
Admitted.


Axiom Subset_extend
     : forall (vs1 vs2 : VarSet) (v : Var),
       vs1 [<=] vs2 -> extendVarSet vs1 v [<=] extendVarSet vs2 v.


