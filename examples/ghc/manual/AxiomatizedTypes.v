Require GHC.Base.
Require GHC.Err.

Axiom Coercion           : Type.
Axiom Type_              : Type.
Axiom ThetaType          : Type.
Axiom TyBinder           : Type.
Axiom TyThing            : Type.

Definition Kind          : Type := Type_.
Definition PredType      : Type := Type_.

Axiom CoAxiom            : Type -> Type.
Axiom Branched           : Type.
Axiom Unbranched         : Type.
Axiom BuiltInSynFamily   : Type.
Axiom BranchIndex        : Type.
Axiom CoAxiomRule        : Type.
Axiom CoAxBranch         : Type.
Inductive Role           : Type := Representational | Nominal | Phantom.

Axiom TcTyVarDetails     : Type.
Axiom liftedTypeKind     : Kind.
Axiom constraintKind     : Kind.

Axiom PrimOp             : Type.
Axiom ForeignCall        : Type.
Axiom CType              : Type.
Axiom CostCentre         : Type.
Axiom DataConBoxer       : Type.


(* -------------------- assumed default instances ------------------- *)

Instance Default__Coercion
   : GHC.Err.Default Coercion := {}.
Admitted.

Instance Default__Type_
   : GHC.Err.Default Type_ := {}.
Admitted.

Instance Default__ThetaType
   : GHC.Err.Default ThetaType := {}.
Admitted.


Instance Default__TyBinder
   : GHC.Err.Default TyBinder := {}.
Admitted.

Instance Default__TyThing
   : GHC.Err.Default TyThing := {}.
Admitted.

Instance Default__CoAxiom
   : forall {a}, GHC.Err.Default (CoAxiom a) := {}.
Admitted.


Instance Default__Branched
   : GHC.Err.Default Branched := {}.
Admitted.

Instance Default__Unbranched
   : GHC.Err.Default Unbranched := {}.
Admitted.

Instance Default__BuiltInSynFamily
   : GHC.Err.Default BuiltInSynFamily := {}.
Admitted.


Instance Default__TcTyVarDetails
   : GHC.Err.Default TcTyVarDetails := {}.
Admitted.

Instance Default__Role
   : GHC.Err.Default Role := {}.
Admitted.


Instance Default__BranchIndex
   : GHC.Err.Default BranchIndex := {}.
Admitted.

Instance Default__CoAxiomRule
   : GHC.Err.Default CoAxiomRule := {}.
Admitted.

Instance Default__CoAxiomBranch
   : GHC.Err.Default CoAxBranch := {}.
Admitted.


Instance Default__CostCentre
   : GHC.Err.Default CostCentre := {}.
Admitted.

Instance Default__DataConBoxer
   : GHC.Err.Default DataConBoxer := {}.
Admitted.


Instance Default__PrimOp
   : GHC.Err.Default PrimOp := {}.
Admitted.
Instance Default__ForeignCall
   : GHC.Err.Default ForeignCall := {}.
Admitted.
Instance Default__CType
   : GHC.Err.Default CType := {}.
Admitted.


(* ---------------- Eq -------------- *)

Instance Eq___CoAxiomRule
   : GHC.Base.Eq_ CoAxiomRule := {}.
Admitted.

Instance Eq___Role
   : GHC.Base.Eq_ Role := {}.
Admitted.

Instance Eq___CostCentre
   : GHC.Base.Eq_ CostCentre := {}.
Admitted.

Instance Ord___CostCentre
   : GHC.Base.Ord CostCentre := {}.
Admitted.
