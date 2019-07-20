(* Disable notation conflict warnings *)
Set Warnings "-notation-overridden".

From mathcomp.ssreflect
Require Import ssreflect ssrnat prime ssrbool.

Require Import Name.
Require Import Id.
Require Import Core.
Require Import CoreFVs.
Require Import CoreUtils.

Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Import ListNotations.

Require Import Proofs.GHC.Base.

Require Import Proofs.Axioms.

Require Import Proofs.Base.
Require Import Proofs.GhcTactics.
Require Import Proofs.Forall.
Require Import Proofs.Unique.
Require Import Proofs.Var.
Require Import Proofs.VarSet.
Require Import Proofs.VarEnv.
Require Import Proofs.CoreInduct.


Import GHC.Base.Notations.

Set Bullet Behavior "Strict Subproofs".
Opaque GHC.Base.hs_string__.


(** * Core invariants related to variables and scope *)

(** ** The invariants *)

(* These are the original definitions of isGlobalScope and isLocalScope *)
Definition isGlobalScope : Var -> bool :=
  fun arg_0__ =>
    match arg_0__ with
    | Mk_Id _ _ _ GlobalId _ _ => true
    | _ => false
    end.

Definition isLocalScope : Var -> bool :=
  fun arg_0__ =>
    match arg_0__ with
    | Mk_Id _ _ _ (LocalId _) _ _ => true
    | _ => false
    end.

(**
First we define invariants for [Var] that are independent of scope, namely:
- It is a localVar iff the unique is local.
- The [Unique] cached in the [Var] is the same as the [Unique] of the name
  of the var.
- The var must be an identifier (i.e. a term variable)
- but not one that is a coercion variable.
*)
Definition GoodVar (v : Var) : Prop :=
  isLocalVar v = isLocalScope v /\ 
  varUnique v = nameUnique (varName v).

Definition GoodLocalVar (v : Var) : Prop :=
  GoodVar v /\ isLocalVar v = true.

(**

Next we define when a variable occurrence is ok in a given scope.
 * Global variables are always ok (not yet tracked).
 * Local variables are ok if they are in scope, and
   are almost the same as the binder; i.e., only the 
   [idInfo] may vary

*)

Definition WellScopedVar (v : Var) (in_scope : VarSet) : Prop :=
   match lookupVarSet in_scope v with
    | None => False
    | Some v' => almostEqual v v' /\ GoodVar v
    end.


(**

Finally, we lift this to whole expressions, keeping track of the variables
that are in [in_scope]. Remember that GHC allows shadowing!

*)

(* We don't care about ticks, and I'm not sure this case is correct *)

(* Definition WellScopedTickish (x : Tickish Var)(in_scope : VarSet) : Prop :=
  match x with
  | Breakpoint _ ids => Forall (fun e => WellScopedVar e in_scope) ids
  | _ => True
  end. *)


Fixpoint WellScoped (e : CoreExpr) (in_scope : VarSet) {struct e} : Prop :=
  match e with
  | Mk_Var v => WellScopedVar v in_scope
  | Lit l => True
  | App e1 e2 => WellScoped e1 in_scope /\  WellScoped e2 in_scope
  | Lam v e => GoodLocalVar v /\ WellScoped e (extendVarSet in_scope v)
  | Let bind body =>
      WellScopedBind bind in_scope /\
      WellScoped body (extendVarSetList in_scope (bindersOf bind))
  | Case scrut bndr ty alts  => 
    WellScoped scrut in_scope /\
    GoodLocalVar bndr /\
    Forall' (fun alt =>
      Forall GoodLocalVar (snd (fst alt)) /\
      let in_scope' := extendVarSetList in_scope (bndr :: snd (fst alt)) in
      WellScoped (snd alt) in_scope') alts
  | Cast e _ =>   WellScoped e in_scope
(*  | Tick _ e =>   WellScoped e in_scope *) (* /\ WellScopedTickish t in_scope *) 
  | Mk_Type _  =>   True
  | Mk_Coercion _ => True 
  end
with WellScopedBind (bind : CoreBind) (in_scope : VarSet) : Prop :=
  match bind with
  | NonRec v rhs =>
    GoodLocalVar v /\
    WellScoped rhs in_scope
  | Rec pairs => 
    Forall (fun p => GoodLocalVar (fst p)) pairs /\
    NoDup (map varUnique (map fst pairs)) /\
    Forall' (fun p => WellScoped (snd p) (extendVarSetList in_scope (map fst pairs))) pairs
  end.

Definition WellScopedAlt bndr (alt : CoreAlt) in_scope  :=
    Forall GoodLocalVar (snd (fst alt)) /\
    let in_scope' := extendVarSetList in_scope (bndr :: snd (fst alt)) in
    WellScoped (snd alt) in_scope'.

(**

A [CoreProgram] can be treated like one big recursive group, despite that it
is a sequence of [Rec] and [NonRec] bindings.

*)
Definition WellScopedProgram (pgm : CoreProgram) : Prop :=
   NoDup (map varUnique (bindersOfBinds pgm)) /\
   Forall' (fun p => WellScoped (snd p) (mkVarSet (bindersOfBinds pgm))) (flattenBinds pgm).



(** ** Lemmas *)


(** *** Lemmas about [GoodLocalVar] *)

Lemma GoodLocalVar_uniqAway:
  forall vss v, GoodLocalVar v -> GoodLocalVar (uniqAway vss v).
Proof.
  intros.
  unfold GoodLocalVar, GoodVar in *.
  destruct H. destruct H. (* destruct H2. *)
  rewrite isLocalVar_uniqAway.
  (* rewrite isLocalUnique_uniqAway. *)
  (* rewrite isId_uniqAway. *)
  (*  rewrite isCoVar_uniqAway. *)
  repeat split; auto.
  move: (idScope_uniqAway vss v) => h.   rewrite H. 
  unfold isLocalScope. destruct v. destruct uniqAway eqn:m. simpl in h. rewrite h. done.
  rewrite nameUnique_varName_uniqAway; auto.
Qed.

Lemma GoodLocalVar_asJoinId_mkSysLocal:
  forall s u ty n,
  Unique.isLocalUnique u = true ->
  GoodLocalVar (asJoinId (mkSysLocal s u ty) n).
Proof.
  move=> s u ty n h1.
  unfold mkSysLocal.
  rewrite andb_false_r.
  split; destruct u. split.
  - cbv. rewrite h1. rewrite h1. done.
  - cbv. rewrite h1. done.
  - cbv. rewrite h1. rewrite h1. done.
Qed.


Lemma GoodLocalVar_almostEqual:
  forall v1 v2,
  GoodLocalVar v1 ->
  almostEqual v1 v2 ->
  GoodLocalVar v2.
Proof.
  intros.
  destruct H. 
  induction H0.
  * split; only 1: assumption.
    destruct ids; simpl in *; done.
(*   * split; only 1: split; assumption. *)
(*  * split; only 1: split; assumption.  *)
Qed.

Lemma GoodVar_almostEqual : 
  forall v1 v2, 
    GoodVar v1 -> almostEqual v1 v2 -> GoodVar v2.
Proof.
  move => v1 v2 h1 h2.
  destruct h2. 
  all: unfold GoodVar in *.
  simpl in *. auto.
Qed.
(*  elim => h1 h2. 
  move => h. inversion h. 
  all: unfold GoodVar.
  all: repeat split.
  all: rewrite <- H in *.
  all: simpl in *.
  all: try done.
Qed. *)


(** *** Structural lemmas *)

Lemma WellScopedVar_extendVarSet:
  forall v vs,
  GoodVar v ->
  WellScopedVar v (extendVarSet vs v).
Proof.
  intros.
  unfold WellScopedVar.
  rewrite lookupVarSet_extendVarSet_self.
  split. apply almostEqual_refl. trivial.
Qed.

Lemma WellScoped_varToCoreExpr:
  forall v isvs,
  WellScopedVar v isvs -> WellScoped (varToCoreExpr v) isvs.
Proof.
  intros.
  destruct v; simpl; try trivial.
(*  + unfold WellScopedVar in H. simpl in H.
    destruct lookupVarSet; try done.
    move: H => [h0 h1]. unfold GoodVar in h1; simpl in h1.
    move: h1 => [_ [_ [h2 _]]]. done. *)
  + unfold varToCoreExpr; simpl.
    rewrite andb_false_r; try done.
Qed. 


Lemma WellScoped_Lam:
  forall v e isvs,
  WellScoped (Lam v e) isvs <-> GoodLocalVar v /\ WellScoped e (extendVarSet isvs v).
Proof. intros. reflexivity. Qed.


Lemma WellScoped_mkLams:
  forall vs e isvs,
  WellScoped (mkLams vs e) isvs <-> Forall GoodLocalVar vs /\ WellScoped e (extendVarSetList isvs vs).
Proof.
  induction vs; intros.
  * intuition.
  * simpl.
    rewrite extendVarSetList_cons.
    rewrite Forall_cons_iff.
    rewrite and_assoc.
    rewrite <- (IHvs _ _).
    reflexivity.
Qed.

Lemma WellScoped_mkVarApps:
  forall e vs isvs,
  WellScoped e isvs -> 
  Forall (fun v => WellScopedVar v isvs) vs ->
  WellScoped (mkVarApps e vs) isvs.
Proof.
  intros.
  unfold mkVarApps.
  rewrite Foldable.hs_coq_foldl_list.
  revert e H.
  induction H0; intros.
  * simpl. intuition.
  * simpl.
    apply IHForall; clear IHForall.
    simpl.
    split; try assumption.
    apply WellScoped_varToCoreExpr; assumption.
Qed.

Lemma WellScoped_MkLetRec: forall pairs body isvs,
  WellScoped (mkLetRec pairs body) isvs <-> WellScoped (Let (Rec pairs) body) isvs .
Proof.
  intros.
  unfold mkLetRec.
  destruct pairs; try reflexivity.
  simpl.
  rewrite extendVarSetList_nil.
  split; intro; repeat split; try constructor; intuition.
Qed.

Lemma WellScoped_MkLet: forall bind body isvs,
  WellScoped (mkLet bind body) isvs <-> WellScoped (Let bind body) isvs .
Proof.
  intros.
  unfold mkLet.
  destruct bind; try reflexivity.
  destruct l; try reflexivity.
  simpl.
  rewrite extendVarSetList_nil.
  split; intro; repeat split; try constructor; intuition.
Qed.

(** *** Freshness *)

Lemma WellScopedVar_extendVarSetList_l:
  forall v vs1 vs2,
  WellScopedVar v vs1 ->
  elemVarSet v (mkVarSet vs2) = false ->
  WellScopedVar v (extendVarSetList vs1 vs2).
Proof.
  intros.
  unfold WellScopedVar in *.
  destruct_match; only 2: contradiction.
  rewrite lookupVarSet_extendVarSetList_l. 
  rewrite Heq.
  assumption.
  rewrite H0. 
  auto.
Qed.

Lemma WellScopedVar_extendVarSetList_r:
  forall v vs1 vs2,
  Forall GoodVar vs2 ->
  List.In v vs2 ->
  NoDup (map varUnique vs2) ->
  WellScopedVar v (extendVarSetList vs1 vs2).
Proof.
  intros.
  unfold WellScopedVar in *.
  assert (Gv: GoodVar v). 
   { rewrite -> Forall_forall in *. auto. }
  rewrite -> lookupVarSet_extendVarSetList_self_in by assumption. 
  intuition.
Qed.


(** *** The invariants respect [StrongSubset] *)



