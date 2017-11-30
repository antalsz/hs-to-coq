(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Coq.Program.Tactics.
Require Coq.Program.Wf.

(* Converted imports: *)

Require UniqFM.

(* Converted type declarations: *)

Definition UniqSet :=
  UniqFM.UniqFM%type.
(* Converted value declarations: *)

Axiom unionManyUniqSets : forall {A : Type}, A.

Axiom mkUniqSet : forall {A : Type}, A.

Axiom emptyUniqSet : forall {A : Type}, A.

Axiom unitUniqSet : forall {A : Type}, A.

Axiom addListToUniqSet : forall {A : Type}, A.

Axiom addOneToUniqSet : forall {A : Type}, A.

Axiom addOneToUniqSet_C : forall {A : Type}, A.

Axiom delOneFromUniqSet : forall {A : Type}, A.

Axiom delOneFromUniqSet_Directly : forall {A : Type}, A.

Axiom delListFromUniqSet : forall {A : Type}, A.

Axiom unionUniqSets : forall {A : Type}, A.

Axiom minusUniqSet : forall {A : Type}, A.

Axiom intersectUniqSets : forall {A : Type}, A.

Axiom foldUniqSet : forall {A : Type}, A.

Axiom mapUniqSet : forall {A : Type}, A.

Axiom elementOfUniqSet : forall {A : Type}, A.

Axiom elemUniqSet_Directly : forall {A : Type}, A.

Axiom filterUniqSet : forall {A : Type}, A.

Axiom partitionUniqSet : forall {A : Type}, A.

Axiom sizeUniqSet : forall {A : Type}, A.

Axiom isEmptyUniqSet : forall {A : Type}, A.

Axiom lookupUniqSet : forall {A : Type}, A.

Axiom uniqSetToList : forall {A : Type}, A.

(* Unbound variables:
     UniqFM.UniqFM
*)
