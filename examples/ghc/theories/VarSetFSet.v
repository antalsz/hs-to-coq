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

(** The interface only requires that the key type has a decidable equality.
    
 *)

Ltac unfold_zeze :=
  unfold GHC.Base.op_zeze__, Core.Eq___Var, op_zeze____, Core.Eq___Var_op_zeze__;
  unfold GHC.Base.op_zeze__, Nat.Eq_nat, op_zeze____.  


Module Var_as_DT <: BooleanDecidableType <: DecidableType.
  Definition t := Var.

  Definition eqb : t -> t -> bool := _GHC.Base.==_.

  Definition eq : t -> t -> Prop := fun x y => eqb x y = true.

  Definition eq_equiv : Equivalence eq.
  split. 
  - unfold eq, eqb, Reflexive. 
    unfold_zeze.
    intro x. destruct x; simpl; apply Nat.eqb_refl.
  - unfold eq, eqb, Symmetric.
    unfold_zeze.
    intros x y. 
    destruct x; destruct y; simpl; rewrite Nat.eqb_sym; auto.
  - unfold eq, eqb, Transitive.
    unfold_zeze.
    intros x y z. 
    destruct x; destruct y; destruct z; simpl;
    repeat erewrite Nat.eqb_eq; intro h; rewrite h; auto.
  Defined.

  Definition eq_dec : forall x y : t, { eq x y } + { ~ (eq x y) }.
  intros x y.
  unfold eq, eqb.
  unfold_zeze.
  destruct x eqn:X; destruct y eqn:Y;  simpl.
  all: destruct (Nat.eqb n0 n2) eqn:EQ ; [left; auto | right; auto].
  Defined.

  Lemma eqb_eq : forall x y, eqb x y = true <-> eq x y.
    unfold eq. tauto.
  Qed. 

 Definition eq_refl := eq_equiv.(@Equivalence_Reflexive _ _).
 Definition eq_sym := eq_equiv.(@Equivalence_Symmetric _ _).
 Definition eq_trans := eq_equiv.(@Equivalence_Transitive _ _).

End Var_as_DT.

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

  (* Everything else comes from our particular implementation *)

  (* Equality must be decidable, but doesn't necessarily need to be Coq
     equality. For VarSets, that is actually case, so we can think about
     making a signature that is stricter than this one. *)

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

  Definition eq_dec : forall s s' : t,  {eq s s'} + {~ eq s s'}.
  Admitted.

  Definition empty : t := emptyVarSet.

  Definition is_empty : t -> bool := isEmptyVarSet.

  Definition lt (s s' : Var) := GHC.Base.compare s s' = Lt.

  Definition min_elt : t -> option elt := GHC.Err.default.
  Definition max_elt : t -> option elt := GHC.Err.default.

  Definition mem : elt -> t -> bool := elemVarSet.

  Definition add x s := extendVarSet s x.

  Definition singleton x := unitVarSet x.

  Definition remove x s := delVarSet s x.

  Definition union := unionVarSet.

  Definition inter := intersectVarSet.

  Definition diff : t -> t -> t := 
    fun x y : t =>
      match x with
      | UniqSet.Mk_UniqSet u =>
        match y with
        | UniqSet.Mk_UniqSet u0 =>
          match u with
          | UniqFM.UFM i =>
            match u0 with
            | UniqFM.UFM i0 =>
              UniqSet.Mk_UniqSet (UniqFM.UFM (IntMap.Internal.difference i i0))
            end
          end
        end
      end.

  Definition subset := subVarSet.

  Definition fold (A : Type) (f : elt -> A -> A) (ws : VarSet) (x : A) : A.
    destruct ws.
    apply (@UniqFM.foldUFM elt A); eauto.
  Defined.

  Definition for_all := allVarSet.

  Definition exists_ := anyVarSet.

  Definition filter  := filterVarSet.

  Definition partition := partitionVarSet.

  Definition cardinal := sizeVarSet.

  Definition elements : t -> list elt := GHC.Err.default.

  Definition choose : t -> option elt := GHC.Err.default.

  (* PROOFS *)

  Lemma mem_1 : forall (s : t) (x : elt), In x s -> mem x s = true.
  Proof. unfold In; intros; destruct s as [s]; auto. Qed.

  Lemma mem_2 : forall (s : t) (x : elt), mem x s = true -> In x s.
  Proof. unfold In; intros; destruct s as [s]; auto. Qed.

  Lemma In_1 :
    forall (s : t) (x y : elt), E.eq x y -> In x s -> In y s.
  Proof. 
  Admitted.

  Lemma eq_refl : forall s : t, eq s s.
  Proof. destruct s. unfold eq. unfold Equal. intro. reflexivity. Qed.

  Lemma eq_sym : forall s s' : t, eq s s' -> eq s' s.
  Proof. destruct s; destruct s'; 
    unfold eq, Equal in *. intros. rewrite H. intuition. Qed.

  Lemma eq_trans :
    forall s s' s'' : t, eq s s' -> eq s' s'' -> eq s s''.
  Proof.
    destruct s; destruct s'; destruct s''; simpl.
    unfold eq, Equal. intros ???. rewrite H, H0. reflexivity.
  Qed.

  Lemma equal_1 : forall s s' : t, Equal s s' -> equal s s' = true.
  Proof.
    intros.
  Admitted.


  Lemma equal_2 : forall s s' : t, equal s s' = true -> Equal s s'.
  Proof.
  Admitted.

  Lemma subset_1 : forall s s' : t, Subset s s' -> subset s s' = true.
  Proof.
    intros.
    unfold subset,Subset in *.
  Admitted.

  Lemma subset_2 : forall s s' : t, subset s s' = true -> Subset s s'.
  Proof.
    intros.
  Admitted.

  Lemma empty_1 : Empty empty.
  Proof. unfold Empty; intros a H. inversion H. Qed.

  Lemma is_empty_1 : forall s : t, Empty s -> is_empty s = true.
  Proof.
    intros. unfold Empty, In, is_empty in *.
  Admitted.

  Lemma is_empty_2 : forall s : t, is_empty s = true -> Empty s.
  Proof.
    intros ????.
    unfold In in *. destruct s. simpl in *.
  Admitted.

  Lemma add_1 :
    forall (s : t) (x y : elt), E.eq x y -> In y (add x s).
  Proof.
    unfold E.eq, In.
    intros; subst.
  Admitted.

  Lemma add_2 : forall (s : t) (x y : elt), In y s -> In y (add x s).
  Proof.
    intros.
  Admitted.

  Lemma add_3 :
    forall (s : t) (x y : elt), ~ E.eq x y -> In y (add x s) -> In y s.
  Proof.
    intros.
  Admitted.

  Lemma remove_1 :
    forall (s : t) (x y : elt), E.eq x y -> ~ In y (remove x s).
  Proof.
  Admitted.

  Lemma remove_2 :
    forall (s : t) (x y : elt), ~ E.eq x y -> In y s -> In y (remove x s).
  Proof.
  Admitted.

  Lemma remove_3 :
    forall (s : t) (x y : elt), In y (remove x s) -> In y s.
  Proof.
    intros.
  Admitted.

  Lemma singleton_1 :
    forall x y : elt, In y (singleton x) -> E.eq x y.
  Proof.
    intros.
  Admitted.

  Lemma singleton_2 :
    forall x y : elt, E.eq x y -> In y (singleton x).
  Proof.
    intros.
  Admitted.

  Lemma union_1 :
    forall (s s' : t) (x : elt), In x (union s s') -> In x s \/ In x s'.
  Proof.
    intros.
  Admitted.

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
Import Var_as_DT.


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