Require GHC.Base.
Require GHC.Err.

Axiom Coercion      : Type.
Axiom Type_         : Type.
Axiom ThetaType     : Type.
Axiom TyBinder      : Type.
Axiom TyThing       : Type.

Definition Kind     : Type := Type_.
Axiom PredType      : Type.

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

Instance Default__PredType
   : GHC.Err.Default PredType := {}.
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
