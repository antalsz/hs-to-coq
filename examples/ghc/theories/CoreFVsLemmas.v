Require Import CoreFVs.
Require Import Id.
Require Import Exitify.
Require Import Core.

Set Bullet Behavior "Strict Subproofs".

Axiom freeVarsBind1_freeVarsBind: freeVarsBind1 = freeVarsBind.


Lemma exprFreeVars_mkLams:
  forall vs e,
  exprFreeVars (mkLams vs e) = delVarSetList (exprFreeVars e) vs.
Admitted.

Axiom deAnnotate'_snd_freeVars:
  forall e, deAnnotate' (snd (freeVars e)) = e.


Axiom deAnnotate_freeVars:
  forall e, deAnnotate (freeVars e) = e.
