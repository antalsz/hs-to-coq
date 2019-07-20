(* Disable notation conflict warnings *)
Set Warnings "-notation-overridden".


From mathcomp.ssreflect
Require Import ssreflect ssrnat prime ssrbool eqtype.


Require Import GHC.Base.
Require Import CoreFVs.
Require Import Id.
Require Import Core.
Require Import CoreTidy.

Require Import Proofs.Prelude.

Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.NArith.BinNat.
Require Import Coq.Program.Equality. (* for dependent destruction *)
 
Require Import Coq.Logic.FunctionalExtensionality.

Require Import Proofs.Axioms.
Require Import Proofs.Base.
Require Import Proofs.ScopeInvariant.
Require Import Proofs.CoreInduct.
Require Import Proofs.Core.
Require Import Proofs.CoreFVs.
Require Import Proofs.GhcTactics.
Require Import Proofs.Var.
Require Import Proofs.VarSet.
Require Import Proofs.VarEnv.
Require Import Unique.Proofs.
Require Import Proofs.GhcUtils.
Require Import Proofs.Util.

Set Bullet Behavior "Strict Subproofs".

Close Scope Z_scope.

Definition WellScoped_VarEnv ( venv : VarEnv Var) (vs:VarSet) : Prop :=
  forall var,  match lookupVarEnv venv var with
        | Some v' => WellScopedVar v' vs
        | None => True
        end.


Definition WellScoped_TidyEnv : Core.TidyEnv -> VarSet -> Prop :=
  fun env vs => match env with 
             | (oenv, venv) => WellScoped_VarEnv venv vs
             end.
  

Lemma coreTidy_wellScoped : forall e env vs,
    WellScoped_TidyEnv env vs -> 
    WellScoped e vs -> 
    WellScoped (tidyExpr env e) vs.
Proof.
  intros e.
  apply (core_induct e); unfold tidyExpr.
  - move=> v [oenv venv] vs WSenv WSe.
    simpl. 
    destruct (lookupVarEnv venv v) eqn:IN; simpl. 
    simpl in WSenv, WSe. unfold WellScoped_VarEnv in WSenv. specialize (WSenv v). rewrite IN in WSenv. auto. 
    simpl in WSe. auto.
  - intros. auto.
Admitted.
