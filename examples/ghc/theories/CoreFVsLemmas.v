Require Import CoreFVs.
Require Import Id.
Require Import Exitify.
Require Import Core.

Require Import GhcProofs.Tactics.

Set Bullet Behavior "Strict Subproofs".

Axiom freeVarsBind1_freeVarsBind: freeVarsBind1 = freeVarsBind.

Import GHC.Base.Notations.

Lemma exprFreeVars_mkLams:
  forall vs e,
  exprFreeVars (mkLams vs e) = delVarSetList (exprFreeVars e) vs.
Proof.
  intros. 
  induction vs.
  - unfold mkLams. unfold_Foldable.
    unfold delVarSetList.
    unfold UniqSet.delListFromUniqSet.
    unfold UniqFM.delListFromUFM.
    destruct (exprFreeVars e).
    f_equal.
  - revert IHvs.
    unfold mkLams.
    unfold_Foldable.
    unfold exprFreeVars.
    unfold Base.op_z2218U__.
    unfold exprFVs.
    unfold Base.op_z2218U__.
    simpl.
Admitted.


Lemma collectNAnnBndrs_freeVars_mkLams:
  forall vs rhs,
  collectNAnnBndrs (length vs) (freeVars (mkLams vs rhs)) = (vs, freeVars rhs).
Admitted.

Axiom deAnnotate_freeVars:
  forall e, deAnnotate (freeVars e) = e.
