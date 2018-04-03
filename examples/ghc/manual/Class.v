(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Coq.Program.Tactics.
Require Coq.Program.Wf.

Require BasicTypes.
Require BooleanFormula.
Require Coq.Init.Datatypes.
Require Coq.Lists.List.
Require Data.Foldable.
Require GHC.Base.
Require Name.
Require SrcLoc.
Require Unique.
(* Require Var. *)
Import GHC.Base.Notations.

Parameter Class : Type.
Parameter className : Class -> Name.Name.
Parameter classKey : Class -> Unique.Unique.


Local Definition Eq___Class_op_zeze__ : Class -> Class -> bool :=
  fun c1 c2 => classKey c1 GHC.Base.== classKey c2.

Local Definition Eq___Class_op_zsze__ : Class -> Class -> bool :=
  fun c1 c2 => classKey c1 GHC.Base./= classKey c2.

Program Instance Eq___Class : GHC.Base.Eq_ Class := fun _ k =>
    k {|GHC.Base.op_zeze____ := Eq___Class_op_zeze__ ;
      GHC.Base.op_zsze____ := Eq___Class_op_zsze__ |}.

