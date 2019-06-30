(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Coq.Program.Tactics.
Require Coq.Program.Wf.

(* Converted imports: *)

Require BasicTypes.
Require Core.
Require GHC.Base.
Require Name.
Require OccName.
Require Unique.
Import GHC.Base.Notations.

(* Converted type declarations: *)

Inductive ConLike : Type
  := | RealDataCon : Core.DataCon -> ConLike
  |  PatSynCon : Core.PatSyn -> ConLike.

(* Converted value declarations: *)

Local Definition Uniquable__ConLike_getUnique : ConLike -> Unique.Unique :=
  fun arg_0__ =>
    match arg_0__ with
    | RealDataCon dc => Unique.getUnique dc
    | PatSynCon ps => Unique.getUnique ps
    end.

Program Instance Uniquable__ConLike : Unique.Uniquable ConLike :=
  fun _ k__ => k__ {| Unique.getUnique__ := Uniquable__ConLike_getUnique |}.

Definition eqConLike : ConLike -> ConLike -> bool :=
  fun x y => Unique.getUnique x GHC.Base.== Unique.getUnique y.

Definition conLikeName : ConLike -> Name.Name :=
  fun arg_0__ =>
    match arg_0__ with
    | RealDataCon data_con => Core.dataConName data_con
    | PatSynCon pat_syn => Core.patSynName pat_syn
    end.

Definition conLikeArity : ConLike -> BasicTypes.Arity :=
  fun arg_0__ =>
    match arg_0__ with
    | RealDataCon data_con => Core.dataConSourceArity data_con
    | PatSynCon pat_syn => Core.patSynArity pat_syn
    end.

(* Skipping all instances of class `Data.Data.Data', including
   `ConLike.Data__ConLike' *)

(* Skipping all instances of class `Outputable.OutputableBndr', including
   `ConLike.OutputableBndr__ConLike' *)

(* Skipping all instances of class `Outputable.Outputable', including
   `ConLike.Outputable__ConLike' *)

Local Definition NamedThing__ConLike_getName : ConLike -> Name.Name :=
  fun arg_0__ =>
    match arg_0__ with
    | RealDataCon dc => Name.getName dc
    | PatSynCon ps => Name.getName ps
    end.

Local Definition NamedThing__ConLike_getOccName : ConLike -> OccName.OccName :=
  fun n => Name.nameOccName (NamedThing__ConLike_getName n).

Program Instance NamedThing__ConLike : Name.NamedThing ConLike :=
  fun _ k__ =>
    k__ {| Name.getName__ := NamedThing__ConLike_getName ;
           Name.getOccName__ := NamedThing__ConLike_getOccName |}.

Local Definition Eq___ConLike_op_zeze__ : ConLike -> ConLike -> bool :=
  eqConLike.

Local Definition Eq___ConLike_op_zsze__ : ConLike -> ConLike -> bool :=
  fun x y => negb (Eq___ConLike_op_zeze__ x y).

Program Instance Eq___ConLike : GHC.Base.Eq_ ConLike :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zeze____ := Eq___ConLike_op_zeze__ ;
           GHC.Base.op_zsze____ := Eq___ConLike_op_zsze__ |}.

(* External variables:
     bool negb BasicTypes.Arity Core.DataCon Core.PatSyn Core.dataConName
     Core.dataConSourceArity Core.patSynArity Core.patSynName GHC.Base.Eq_
     GHC.Base.op_zeze__ GHC.Base.op_zeze____ GHC.Base.op_zsze____ Name.Name
     Name.NamedThing Name.getName Name.getName__ Name.getOccName__ Name.nameOccName
     OccName.OccName Unique.Uniquable Unique.Unique Unique.getUnique
     Unique.getUnique__
*)
