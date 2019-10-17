(* Disable notation conflict warnings *)
Set Warnings "-notation-overridden".

From Coq Require Import ssreflect ssrfun ssrbool.

Require Import GHC.Base.
Import GHC.Base.ManualNotations.
Require Import Core.
Require UniqFM.


Require Import Coq.Lists.List.
Require Import Coq.NArith.BinNat.

Require Import Coq.FSets.FSetInterface.
Require Import Coq.Structures.Equalities.

Require Coq.FSets.FSetDecide.
Require Coq.FSets.FSetProperties.
Require Coq.FSets.FSetEqProperties.

(* base-thy *)
Require Import Proofs.GHC.Base.
Require Import Proofs.GHC.List.

(* containers theory *)
Require Import IntSetProofs.

(* ghc theory (incl. some that should move above. *)
Require Import Proofs.Base.
Require Import Proofs.Axioms.
Require Import Proofs.ContainerAxioms.
Require Import Proofs.GhcTactics.
Require Import Proofs.Unique.
Require Import Proofs.Var.

Import ListNotations.

Set Bullet Behavior "Strict Subproofs".


(** ** [VarSet as FSet] *)

(* This part creates an instance of the FSetInterface for VarSets.

   This allows us to experiment with some of the metalib automation
   for reasoning about sets of variable names.

   This file use the FSet instance to define modules of facts about VarSets
   including:

     VarSetFacts
     VarSetProperties
     VarSetDecide     [fsetdec tactic]
     VarSetNotin      [destruct_notin and solve_notin tactics]


   *)

(** Note: This module is actually *more* than what we need for fsetdec.  Maybe
    we want to redesign fsetdec to state only the properties and operations
    that it uses?

    Also the fsetdec reasoning uses "Prop" based statement of facts instead of
    operational "bool" based reasoning. This interface captures the
    relationship between those two statements, but it still can be tricky.
    Regardless, we are using the "weak" signature for this module as it
    doesn't require an ordering on elements.  *)

Module VarSetFSet <: WSfun(Var_as_DT) <: WS.

  Module E := Var_as_DT.

  Definition elt := Var.

  Definition t   := VarSet.

  (* These are specified exactly by the signature. *)
  Definition In x (s : VarSet) := elemVarSet x s = true.

  Definition Equal s s' := forall a : elt, In a s <-> In a s'.

  Definition Subset s s' := forall a : elt, In a s -> In a s'.

  Definition Empty s := forall a : elt, ~ In a s.

  Definition For_all (P : elt -> Prop) s := forall x, In x s -> P x.

  Definition Exists (P : elt -> Prop) s := exists x, In x s /\ P x.

  Notation "s [=] t" := (Equal s t) (at level 70, no associativity).
  Notation "s [<=] t" := (Subset s t) (at level 70, no associativity).

  Definition eq : t -> t -> Prop := Equal.

  Definition empty : t := emptyVarSet.

  Definition is_empty : t -> bool := isEmptyVarSet.

  Definition mem : elt -> t -> bool := elemVarSet.

  Definition add x s := extendVarSet s x.

  Definition singleton x := unitVarSet x.

  Definition remove x s := delVarSet s x.

  Definition union := unionVarSet.

  Definition diff := minusVarSet.

  Definition subset := subVarSet.

  Definition exists_ := anyVarSet.

   (* available but unused. *)

  Definition fold (A : Type) (f : elt -> A -> A) (ws : VarSet) (x : A) : A.
    destruct ws.
    apply (@UniqFM.foldUFM elt A); eauto.
  Defined.

  Definition for_all := allVarSet.

  Definition filter  := filterVarSet.

  Definition cardinal := sizeVarSet.

  Definition inter := intersectVarSet.


  (* PROOFS *)

  Lemma mem_1 : forall (s : t) (x : elt), In x s -> mem x s = true.
  Proof. unfold In; intros; destruct s as [s]; auto. Qed.

  Lemma mem_2 : forall (s : t) (x : elt), mem x s = true -> In x s.
  Proof. unfold In; intros; destruct s as [s]; auto. Qed.

  Lemma In_1 :
    forall (s : t) (x y : elt), E.eq x y -> In x s -> In y s.
  Proof.
    unfold E.eq, E.eqb, In.
    move => [u].
    move: u => [i].
    move=> x y Eq.
    unfold elemVarSet, UniqSet.elementOfUniqSet, UniqFM.elemUFM.
    erewrite member_eq with (k' := (Unique.getWordKey (Unique.getUnique y))). auto.
    rewrite -> eq_unique in Eq.
    rewrite Eq.
    reflexivity.
  Qed.

  Lemma eq_refl : forall s : t, eq s s.
  Proof. destruct s. unfold eq. unfold Equal. intro. reflexivity. Qed.

  Lemma eq_sym : forall s s' : t, eq s s' -> eq s' s.
  Proof. destruct s; destruct s';
    unfold eq, Equal in *. intros. rewrite H. intuition. Qed.

  Lemma eq_trans :
    forall s s' s'' : t, eq s s' -> eq s' s'' -> eq s s''.
  Proof.
    destruct s; destruct s'; destruct s''; simpl.
    unfold eq, Equal. intros ???. rewrite H. rewrite H0. reflexivity.
  Qed.

  Require Import MapProofs.

  Lemma subset_1 : forall s s' : t, Subset s s' -> subset s s' = true.
  Proof.
    move => [[i]] [[i']].
    unfold subset,Subset in *.
    unfold In in *.
    unfold subVarSet, minusVarSet, isEmptyVarSet.
    destruct i; destruct i'. simpl.
    unfold IntMap.difference, IntMap.null, IntMap.member. simpl.
    intros. eapply difference_Desc; try eassumption.
    unfold diffo'. intros.
    assert (forall i, sem s i = None).
    { intros. specialize (H3 i).
      specialize (H (Mk_Id GHC.Err.default
                           i
                           GHC.Err.default
                           GHC.Err.default
                           GHC.Err.default
                           GHC.Err.default)).
      simpl in H.
      destruct (sem x0 i) eqn:Hsem0.
      - assumption.
      - destruct (sem x i) eqn:Hsem.
        + assert (exists v, sem x i = Some v) by (eapply ex_intro; apply Hsem).
          rewrite <- member_spec in H4; [|eassumption].
          apply H in H4. rewrite -> member_spec in H4; [|eassumption].
          destruct H4. rewrite Hsem0 in H4. inversion H4.
        + assumption.
    }
    destruct s.
    - simpl in H4. specialize (H4 w1).
      rewrite Eq_refl in H4. simpl in H4.
      rewrite oro_assoc oro_Some_l in H4.
      destruct (sem s2 w1); simpl in H4; inversion H4.
    - reflexivity.
  Qed.

  Lemma subset_2 : forall s s' : t, subset s s' = true -> Subset s s'.
  Proof.
    move => [i]. move => [i'].
    move: i => [j]. move: i' => [j'].
    unfold subset,Subset in *.
    unfold In in *.
    unfold subVarSet, minusVarSet, isEmptyVarSet.
    destruct j, j'. simpl.
    unfold IntMap.null, IntMap.difference, IntMap.member. simpl.
    eapply difference_Desc; eauto.
    intros. 
    rewrite -> null_spec' in H3; [|assumption].
    rewrite member_spec; [|eassumption].
    rewrite -> member_spec in H4; [|eassumption].
    specialize (H2 (realUnique a)).
    specialize (H3 (realUnique a)).
    rewrite H3 in H2. destruct H4. rewrite H4 in H2.
    destruct (sem x0 (realUnique a)) eqn:Hx0.
    - exists v. assumption.
    - simpl in H2. inversion H2.
  Qed.

  Lemma empty_1 : Empty empty.
  Proof. unfold Empty; intros a H. inversion H. Qed.

  Lemma is_empty_1 : forall s : t, Empty s -> is_empty s = true.
  Proof.
    move=>[[i]]. unfold Empty, In. simpl.
    rewrite /IntMap.member /IntMap.null.
    move=> h. destruct i. simpl.
    destruct x.
    - specialize (h (Mk_Id GHC.Err.default
                           w0
                           GHC.Err.default
                           GHC.Err.default
                           GHC.Err.default
                           GHC.Err.default)).
      simpl in h.
      replace (compare w0 w0) with Eq in h.
      contradiction. cbn. symmetry. apply N.compare_refl.
    - simpl. reflexivity.
  Qed.

  Lemma is_empty_2 : forall s : t, is_empty s = true -> Empty s.
  Proof.
    move=>s. destruct s. simpl. destruct getUniqSet'. destruct i.
    cbn. rewrite /Empty /In. cbn. rewrite /IntMap.null /IntMap.member.
    simpl. move=>h a.
    rewrite member_spec; [|eassumption]. intro.
    rewrite -> null_spec in h; [|assumption]; subst.
    simpl in H. destruct H. inversion H.
  Qed.

  Lemma add_1 :
    forall (s : t) (x y : elt), E.eq x y -> In y (add x s).
  Proof.
    unfold E.eq, In.
    intros; subst.
    destruct s, getUniqSet', i. cbn.
    eapply insert_Desc; eauto.
    intros. rewrite member_spec; [|eassumption].
    specialize (H2 (realUnique y)).
    exists x. rewrite H2.
    assert (realUnique y == realUnique x).
    { cbn. rewrite realUnique_eq. symmetry. assumption. }
    rewrite H3. reflexivity.
  Qed.

  Lemma add_2 : forall (s : t) (x y : elt), In y s -> In y (add x s).
  Proof.
    move=>s. destruct s, getUniqSet', i. cbn.
    rewrite /In. cbn. intros.
    eapply insert_Desc; eauto.
    intros. rewrite member_spec; [|eassumption].
    rewrite -> member_spec in H; [|eassumption].
    destruct H. specialize (H2 (realUnique y)).
    destruct (realUnique y == realUnique x0).
    - exists x0. rewrite H2. reflexivity.
    - exists x1. rewrite H2 H. reflexivity.
  Qed.

  Lemma add_3 :
    forall (s : t) (x y : elt), ~ E.eq x y -> In y (add x s) -> In y s.
  Proof.
    move=>s. destruct s, getUniqSet', i. cbn.
    rewrite /In. cbn. intros.
    rewrite member_spec; [|eassumption].
    rewrite -> member_spec in H0.
    - destruct H0. exists x1. rewrite <- H0.
      eapply insert_Desc; eauto.
      intros. specialize (H3 (realUnique y)).
      rewrite H3.
      assert (realUnique y == realUnique x0 = false).
      { cbn. rewrite realUnique_eq.
        apply not_true_is_false. intro.
        apply H. symmetry. apply H4. }
      rewrite H4. reflexivity.
    - apply insert_WF; assumption.
  Qed.

  Lemma remove_1 :
    forall (s : t) (x y : elt), E.eq x y -> ~ In y (remove x s).
  Proof.
    move=>s. destruct s, getUniqSet', i. cbn.
    rewrite /In. cbn. intros.
    eapply delete_Desc; eauto.
    intros. rewrite member_spec; [|eassumption]. intro.
    specialize (H2 (realUnique y)). destruct H3.
    assert (realUnique y == realUnique x0).
    { cbn. rewrite realUnique_eq. symmetry. assumption. }
    rewrite H4 in H2. rewrite H2 in H3. inversion H3.
  Qed.

  Lemma remove_2 :
    forall (s : t) (x y : elt), ~ E.eq x y -> In y s -> In y (remove x s).
  Proof.
    move=>s. destruct s, getUniqSet', i. cbn.
    rewrite /In. cbn. intros.
    eapply delete_Desc; eauto.
    intros. rewrite member_spec; [|eassumption].
    rewrite -> member_spec in H0; [|eassumption]. destruct H0.
    specialize (H3 (realUnique y)).
    assert (realUnique y == realUnique x0 = false).
    { cbn. rewrite realUnique_eq.
      apply not_true_is_false. intro.
      apply H. symmetry. assumption. }
    rewrite H4 in H3. exists x1. rewrite H3 H0. reflexivity.
  Qed.

  Lemma remove_3 :
    forall (s : t) (x y : elt), In y (remove x s) -> In y s.
  Proof.
    move=>s. destruct s, getUniqSet', i. cbn.
    rewrite /In. cbn. intros.
    rewrite member_spec; [|eassumption].
    rewrite -> member_spec in H.
    - destruct H. exists x1. rewrite -H.
      move: H. eapply delete_Desc; eauto.
      intros. specialize (H1 (realUnique y)).
      destruct (realUnique y == realUnique x0).
      + rewrite H1 in H2. inversion H2.
      + symmetry. assumption.
    - eapply delete_Desc; eauto.
  Qed.

  Lemma singleton_1 :
    forall x y : elt, In y (singleton x) -> E.eq x y.
  Proof.
    rewrite /In. cbn. move=>x y.
    destruct (realUnique y ?= realUnique x)%N eqn:Heq; intros.
    - apply N.compare_eq in Heq.
      rewrite -E.eqb_eq -realUnique_eq Heq.
      apply N.eqb_refl.
    - inversion H.
    - inversion H.
  Qed.

  Lemma singleton_2 :
    forall x y : elt, E.eq x y -> In y (singleton x).
  Proof.
    rewrite /In. cbn. move=>x y. inversion 1.
    rewrite -realUnique_eq in H1.
    assert ((realUnique y ?= realUnique x)%N = Eq).
    { apply N.compare_eq_iff. symmetry. apply N.eqb_eq; assumption. }
    rewrite H0. reflexivity.
  Qed.

  Lemma union_1 :
    forall (s s' : t) (x : elt), In x (union s s') -> In x s \/ In x s'.
  Proof.
    rewrite /In. cbn. move=> s s'.
    destruct s, getUniqSet', i, s', getUniqSet', i.
    cbn. move=>e.
    eapply union_Desc; eauto. move=>s HB _ Hsem.
    rewrite !member_spec; try eassumption.
    move=>[v Hs]. specialize (Hsem (realUnique e)).
    destruct (sem x0 (realUnique e)) eqn:Hx0.
    - simpl in Hsem. right. exists v0. assumption.
    - simpl in Hsem. left. exists v. rewrite -Hsem; assumption.
  Qed.

  Lemma union_2 :
    forall (s s' : t) (x : elt), In x s -> In x (union s s').
  Proof.
    intros.
    destruct s, s'.
  Admitted.

  Lemma union_3 :
    forall (s s' : t) (x : elt), In x s' -> In x (union s s').
  Proof.
    intros.
    destruct s, s'.
  Admitted.

  Lemma inter_1 :
    forall (s s' : t) (x : elt), In x (inter s s') -> In x s.
  Proof.
    intros.
    destruct s, s'.
  Admitted.

  Lemma inter_2 :
    forall (s s' : t) (x : elt), In x (inter s s') -> In x s'.
  Proof.
    intros.
    destruct s, s'.
  Admitted.

  Lemma inter_3 :
    forall (s s' : t) (x : elt), In x s -> In x s' -> In x (inter s s').
  Proof.
    intros.
    destruct s, s'.
  Admitted.

  Lemma diff_1 :
    forall (s s' : t) (x : elt), In x (diff s s') -> In x s.
  Proof.
    intros.
    destruct s, s'.
  Admitted.

  Lemma diff_2 :
    forall (s s' : t) (x : elt), In x (diff s s') -> ~ In x s'.
  Proof.
    intros.
    destruct s, s'.
  Admitted.

  Lemma diff_3 :
    forall (s s' : t) (x : elt), In x s -> ~ In x s' -> In x (diff s s').
  Proof.
    intros.
    destruct s, s'.
  Admitted.

  Lemma fold_left_map:
    forall {a b c} f (g : a -> b) (x : c) xs,
    fold_left (fun a e => f a e) (List.map g xs) x
      = fold_left (fun a e => f a (g e)) xs x.
  Proof.
    intros.
    revert x.
    induction xs; intros.
    * reflexivity.
    * simpl. rewrite IHxs. reflexivity.
  Qed.


  Lemma filter_1 :
    forall (s : t) (x : elt) (f : elt -> bool),
    compat_bool E.eq f -> In x (filter f s) -> In x s.
  Proof.
    intros s x P Heq Hin.
  Admitted.

  Lemma filter_2 :
    forall (s : t) (x : elt) (f : elt -> bool),
    compat_bool E.eq f -> In x (filter f s) -> f x = true.
  Proof.
    intros s x P Heq Hin.
  Admitted.

  Lemma filter_3 :
    forall (s : t) (x : elt) (f : elt -> bool),
    compat_bool E.eq f -> In x s -> f x = true -> In x (filter f s).
  Proof.
    intros s x P Heq Hin HP.
  Admitted.


  Lemma for_all_1 :
    forall (s : t) (f : elt -> bool),
    compat_bool E.eq f ->
    For_all (fun x : elt => f x = true) s -> for_all f s = true.
  Proof.
    intros.
    unfold For_all, for_all in *.
  Admitted.

  Lemma for_all_2 :
    forall (s : t) (f : elt -> bool),
    compat_bool E.eq f ->
    for_all f s = true -> For_all (fun x : elt => f x = true) s.
  Proof.
    intros.
    unfold For_all, for_all in *.
  Admitted.

  Lemma exists_1 :
    forall (s : t) (f : elt -> bool),
    compat_bool E.eq f ->
    Exists (fun x : elt => f x = true) s -> exists_ f s = true.
  Proof.
    intros.
    unfold Exists, exists_ in *.
  Admitted.

  Lemma exists_2 :
    forall (s : t) (f : elt -> bool),
    compat_bool E.eq f ->
    exists_ f s = true -> Exists (fun x : elt => f x = true) s.
  Proof.
    intros.
    unfold Exists, exists_ in *.
  Admitted.


  (* Not needed after this line ---------------------- *)

  (* Everything else comes from our particular implementation *)

  Definition lt (s s' : Var) := GHC.Base.compare s s' = Lt.

  (* Equality must be decidable, but doesn't necessarily need to be Coq
     equality. For VarSets, in fact, that is not the case.

     However, GHC does not include an equality instance for VarSets,
     so we don't actually need to define this.
   *)

  Definition equal  : t -> t -> bool :=
    fun x y : t =>
      match x with
      | UniqSet.Mk_UniqSet u =>
        match y with
        | UniqSet.Mk_UniqSet u0 =>
          match u with
          | UniqFM.UFM i =>
            match u0 with
            | UniqFM.UFM i0 => _GHC.Base.==_ i i0
            end
          end
        end
      end.

  (* These operations are part of the FSet interface but are not
     supported by GHC VarSets. *)

  Definition min_elt : t -> option elt := GHC.Err.default.
  Definition max_elt : t -> option elt := GHC.Err.default.


  Definition partition : (elt -> bool) -> t -> t * t := GHC.Err.default.

  Definition elements : t -> list elt := GHC.Err.default.

  Definition choose : t -> option elt := GHC.Err.default.



  Definition eq_dec : forall s s' : t,  {eq s s'} + {~ eq s s'}.
  Admitted.



  Lemma equal_1 : forall s s' : t, Equal s s' -> equal s s' = true.
  Proof.
    intros.
    unfold Equal, equal in *.
    unfold In in *.
  Admitted.


  Lemma equal_2 : forall s s' : t, equal s s' = true -> Equal s s'.
  Proof.
  Admitted.

  Lemma fold_1 :
    forall (s : t) (A : Type) (i : A) (f : elt -> A -> A),
    fold A f s i =
    fold_left (fun (a : A) (e : elt) => f e a) (elements s) i.
  Proof.
    intros.
    simpl.
  Admitted.


  Lemma cardinal_1 : forall s : t, cardinal s = length (elements s).
  Proof.
    intros.
  Admitted.

  Lemma partition_1 :
    forall (s : t) (f : elt -> bool),
    compat_bool E.eq f -> Equal (fst (partition f s)) (filter f s).
  Proof.
    intros.
    destruct s.
    unfold Equal, partition; simpl.
  Admitted.

  Lemma partition_2 :
    forall (s : t) (f : elt -> bool),
    compat_bool E.eq f ->
    Equal (snd (partition f s)) (filter (fun x : elt => negb (f x)) s).
  Proof.
    intros.
    destruct s.
    unfold Equal, partition; simpl.
  Admitted.

  Lemma elements_1 :
    forall (s : t) (x : elt), In x s -> InA E.eq x (elements s).
  Proof.
    intros.
  Admitted.

  Lemma elements_2 :
    forall (s : t) (x : elt), InA E.eq x (elements s) -> In x s.
  Proof.
    intros.
  Admitted.

  Lemma choose_1 :
    forall (s : t) (x : elt), choose s = Some x -> In x s.
  Proof.
    intros.
    unfold choose in *.
(*    destruct (elements s) eqn:?; try congruence.
    inversion H; subst.
    apply elements_2.
    rewrite Heql.
    left.
    reflexivity. *)
  Admitted.

  Lemma choose_2 : forall s : t, choose s = None -> Empty s.
  Proof.
    intros.
    unfold choose in *.
(*    destruct (elements s) eqn:?; try congruence.
    intros x ?.
    apply elements_1 in H0.
    rewrite Heql in H0.
    inversion H0. *)
  Admitted.

  Lemma choose_3 (s1 s2 : t) (x1 x2 : elt) :
    choose s1 = Some x1 ->
    choose s2 = Some x2 ->
    Equal s1 s2         ->
    E.eq  x1 x2.
  Proof.
  Admitted.

  Lemma elements_3w (s : t) : NoDupA E.eq (elements s).
  Admitted.


End VarSetFSet.
Export VarSetFSet.

(* *********************************************************************** *)

(** These two modules provide additional reasoning principles, proved in terms
    of the basic signature. *)

(** This functor derives additional facts from the interface. These facts are
    mainly the specifications of FSetInterface.S written using different styles:
    equivalence and boolean equalities.

    Notably, see tactic [set_iff].
*)

Module VarSetFacts        := FSetFacts.WFacts_fun Var_as_DT VarSetFSet.
Export VarSetFacts.

(** This functor gives us properties about the boolean function specification
    of sets.

    It adds some of these lemmas to a hint database called 'sets'.

*)

Module VarSetEqProperties := FSetEqProperties.WEqProperties_fun Var_as_DT VarSetFSet.
Export VarSetEqProperties.

(** This functor gives us properties about the "prop" specification of
    sets. *)

Module VarSetProperties   := FSetProperties.WProperties_fun Var_as_DT VarSetFSet.
Export VarSetProperties.

(** The [VarSetDecide] module provides the [fsetdec] tactic for
    solving facts about finite sets of vars. *)

Module VarSetDecide      := FSets.FSetDecide.WDecide_fun Var_as_DT VarSetFSet.
Export VarSetDecide.


(* *********************************************************************** *)
(* The next part is taken from Metalib/FSetWeakNotin.v

   SCW note: I didn't want to draw in a dependency on Metalib before determining
   whether the tactics are useful in this development.

   Furthermore, metalib assumes that Atom equality is =. But we need more
   flexibility for GHC. I had to edit some of the lemmas and proofs below
   because of that.
*)
(* *********************************************************************** *)
(** * Implementation *)


Module Notin.

Module E := Var_as_DT.


(* *********************************************************************** *)
(** * Facts about set non-membership *)

Section Lemmas.

Variables x y  : elt.
Variable  s s' : VarSet.

Lemma notin_empty_1 :
  ~ In x empty.
Proof. fsetdec. Qed.

Lemma notin_add_1 :
  ~ In y (add x s) ->
  ~ E.eq x y.
Proof. fsetdec. Qed.

Lemma notin_add_1' :
  ~ In y (add x s) ->
  ~ (E.eq x y).
Proof. fsetdec. Qed.

Lemma notin_add_2 :
  ~ In y (add x s) ->
  ~ In y s.
Proof. fsetdec. Qed.

Lemma notin_add_3 :
  ~ E.eq x y ->
  ~ In y s ->
  ~ In y (add x s).
Proof.
  set_iff. tauto. Qed.

Lemma notin_singleton_1 :
  ~ In y (singleton x) ->
  ~ E.eq x y.
Proof. fsetdec. Qed.

Lemma notin_singleton_1' :
  ~ In y (singleton x) ->
  ~ (E.eq x y).
Proof. fsetdec. Qed.

Lemma notin_singleton_2 :
  ~ E.eq x y ->
  ~ In y (singleton x).
Proof. set_iff. auto. Qed.

Lemma notin_remove_1 :
  ~ In y (remove x s) ->
  E.eq x y \/ ~ In y s.
Proof. fsetdec. Qed.

Lemma notin_remove_2 :
  ~ In y s ->
  ~ In y (remove x s).
Proof. fsetdec. Qed.

Lemma notin_remove_3 :
  E.eq x y ->
  ~ In y (remove x s).
Proof.
  set_iff. tauto.
 Qed.

Lemma notin_remove_3' :
  x = y ->
  ~ In y (remove x s).
Proof. fsetdec. Qed.

Lemma notin_union_1 :
  ~ In x (union s s') ->
  ~ In x s.
Proof. fsetdec. Qed.

Lemma notin_union_2 :
  ~ In x (union s s') ->
  ~ In x s'.
Proof. fsetdec. Qed.

Lemma notin_union_3 :
  ~ In x s ->
  ~ In x s' ->
  ~ In x (union s s').
Proof. fsetdec. Qed.

Lemma notin_inter_1 :
  ~ In x (inter s s') ->
  ~ In x s \/ ~ In x s'.
Proof. fsetdec. Qed.

Lemma notin_inter_2 :
  ~ In x s ->
  ~ In x (inter s s').
Proof. fsetdec. Qed.

Lemma notin_inter_3 :
  ~ In x s' ->
  ~ In x (inter s s').
Proof. fsetdec. Qed.

Lemma notin_diff_1 :
  ~ In x (diff s s') ->
  ~ In x s \/ In x s'.
Proof. fsetdec. Qed.

Lemma notin_diff_2 :
  ~ In x s ->
  ~ In x (diff s s').
Proof. fsetdec. Qed.

Lemma notin_diff_3 :
  In x s' ->
  ~ In x (diff s s').
Proof. fsetdec. Qed.

End Lemmas.


(* *********************************************************************** *)
(** * Hints *)

Hint Resolve
  @notin_empty_1 @notin_add_3 @notin_singleton_2 @notin_remove_2
  @notin_remove_3 @notin_remove_3' @notin_union_3 @notin_inter_2
  @notin_inter_3 @notin_diff_2 @notin_diff_3.


(* *********************************************************************** *)
(** * Tactics for non-membership *)

(** [destruct_notin] decomposes all hypotheses of the form [~ In x s]. *)

Ltac destruct_notin :=
  match goal with
    | H : In ?x ?s -> False |- _ =>
      change (~ In x s) in H;
      destruct_notin
    | |- In ?x ?s -> False =>
      change (~ In x s);
      destruct_notin
    | H : ~ In _ empty |- _ =>
      clear H;
      destruct_notin
    | H : ~ In ?y (add ?x ?s) |- _ =>
      let J1 := fresh "NotInTac" in
      let J2 := fresh "NotInTac" in
      pose proof H as J1;
      pose proof H as J2;
      apply notin_add_1 in H;
      apply notin_add_1' in J1;
      apply notin_add_2 in J2;
      destruct_notin
    | H : ~ In ?y (singleton ?x) |- _ =>
      let J := fresh "NotInTac" in
      pose proof H as J;
      apply notin_singleton_1 in H;
      apply notin_singleton_1' in J;
      destruct_notin
    | H : ~ In ?y (remove ?x ?s) |- _ =>
      let J := fresh "NotInTac" in
      apply notin_remove_1 in H;
      destruct H as [J | J];
      destruct_notin
    | H : ~ In ?x (union ?s ?s') |- _ =>
      let J := fresh "NotInTac" in
      pose proof H as J;
      apply notin_union_1 in H;
      apply notin_union_2 in J;
      destruct_notin
    | H : ~ In ?x (inter ?s ?s') |- _ =>
      let J := fresh "NotInTac" in
      apply notin_inter_1 in H;
      destruct H as [J | J];
      destruct_notin
    | H : ~ In ?x (diff ?s ?s') |- _ =>
      let J := fresh "NotInTac" in
      apply notin_diff_1 in H;
      destruct H as [J | J];
      destruct_notin
    | _ =>
      idtac
  end.

(** [solve_notin] decomposes hypotheses of the form [~ In x s] and
    then tries some simple heuristics for solving the resulting
    goals. *)

Ltac solve_notin :=
  intros;
  destruct_notin;
  repeat first [ apply notin_union_3
               | apply notin_add_3
               | apply notin_singleton_2
               | apply notin_empty_1
               ];
  auto;
  try tauto;
  fail "Not solvable by [solve_notin]; try [destruct_notin]".

End Notin.

(* --------------------------------------------------------- *)

(* Do we actually need this ??? It is never used in the code.  Why not the
   more extensional definition of equality between VarSets? *)

(*
Instance Eq_VarSet : Eq_ VarSet :=
  fun _ k => k {|
              op_zeze____ := VarSetFSet.eq_dec;
              op_zsze____ := fun x y => negb (VarSetFSet.eq_dec x y);
            |}.

Instance EqLaws_VarSet : EqLaws VarSet.
Proof.
  constructor.
  - red. intros. cbn. destruct (VarSetFSet.eq_dec x x); try reflexivity.
    exfalso. apply n. reflexivity.
  - red. cbn. intros.
    destruct (VarSetFSet.eq_dec x y);
      destruct (VarSetFSet.eq_dec y x); try reflexivity.
    + exfalso. apply VarSetFSet.eq_sym in e. contradiction.
    + exfalso. apply VarSetFSet.eq_sym in e. contradiction.
  - red. cbn. intros.
    destruct (VarSetFSet.eq_dec x y); try discriminate.
    destruct (VarSetFSet.eq_dec y z); try discriminate.
    destruct (VarSetFSet.eq_dec x z); try reflexivity.
    clear H. clear H0. apply (VarSetFSet.eq_trans _ _ _ e) in e0.
    contradiction.
  - intros. cbn. destruct (VarSetFSet.eq_dec x y); reflexivity.
Qed.
*)


(* -------------------------------------------------------- *)

(* Bridge definitions *)

Lemma InE : forall (s : t) (x : elt), elemVarSet x s <-> In x s.
Proof. intros. unfold is_true. rewrite <- mem_iff. reflexivity. Qed.


Lemma SubsetE : forall (s s' : t), subVarSet s s' <->  s [<=] s'.
Proof. intros. unfold is_true. rewrite <- subset_iff. reflexivity. Qed.

Lemma EmptyE: forall s, isEmptyVarSet s <-> Empty s.
Proof. intros. unfold is_true. split.
       apply is_empty_2. apply is_empty_1. Qed.

(* Note: ForallE and ExistsE require a condition on the predicate *)

(* These lemmas relate the GHC VarSet operations to more general
   operations on finite sets. *)

Lemma emptyVarSet_empty : emptyVarSet = empty.
  reflexivity. Qed.

(* need to swap argument order (should we use flip instead ??) *)
Lemma delVarSet_remove : forall x s, delVarSet s x = remove x s.
  reflexivity. Qed.

Lemma extendVarSet_add : forall x s, extendVarSet s x = add x s.
  reflexivity. Qed.

Lemma unitVarSet_singleton : unitVarSet = singleton.
  reflexivity. Qed.

Lemma unionVarSet_union : unionVarSet = union.
  reflexivity. Qed.

Lemma minusVarSet_diff : minusVarSet = diff.
  reflexivity. Qed.

Lemma filterVarSet_filter : filterVarSet = filter.
  reflexivity. Qed.

(* This tactic rewrites the boolean functions into the
   set properties to make them suitable for fsetdec. *)

Ltac set_b_iff :=
  repeat
   progress

    rewrite <- not_mem_iff in *
  || rewrite <- mem_iff in *
  || rewrite <- subset_iff in *
  || rewrite <- is_empty_iff in *

  || rewrite -> InE in *
  || rewrite -> SubsetE in *
  || rewrite -> EmptyE in *

  || rewrite -> emptyVarSet_empty in *
  || rewrite -> delVarSet_remove in *
  || rewrite -> extendVarSet_add in *
  || rewrite -> unionVarSet_union in *
  || rewrite -> minusVarSet_diff in *
  || rewrite -> filterVarSet_filter in *
  || rewrite -> unitVarSet_singleton in *.

(** ** VarSet operations from FSetInterface are Proper *)

(* Restating these instances helps type class resolution during rewriting.  *)


Instance delVarSet_m :
  Proper (Equal ==> (fun x y => x == y) ==> Equal) delVarSet.
Proof.
  move => x1 y1 Eq1 x2 y2 Eq2.
  set_b_iff.
  eapply remove_m; eauto.
Qed.

Instance extendVarSet_m :
  Proper (Equal ==> (fun x y => x == y) ==> Equal) extendVarSet.
Proof.
  move => x1 y1 Eq1 x2 y2 Eq2.
  set_b_iff.
  eapply add_m; eauto.
Qed.

Instance unionVarSet_m :
  Proper (Equal ==> Equal ==> Equal) unionVarSet.
Proof.
  move => x1 y1 Eq1 x2 y2 Eq2.
  set_b_iff.
  eapply union_m; eauto.
Qed.

Instance minusVarSet_m :
  Proper (Equal ==> Equal ==> Equal) minusVarSet.
Proof.
  move => x1 y1 Eq1 x2 y2 Eq2.
  set_b_iff.
  eapply diff_m; eauto.
Qed.
