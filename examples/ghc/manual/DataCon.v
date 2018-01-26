(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Coq.Program.Tactics.
Require Coq.Program.Wf.

(* Preamble *)


(* Converted imports: *)

Require BasicTypes.
Require Coq.Init.Datatypes.
Require Coq.Lists.List.
Require Data.Foldable.
Require Data.Traversable.
Require Data.Tuple.
Require FieldLabel.
Require GHC.Base.
Require GHC.List.
Require Name.
Require NameEnv.

(* Require Var. *)
Import GHC.Base.Notations.

(* Converted type declarations: *)

Inductive StrictnessMark : Type := MarkedStrict : StrictnessMark
                                |  NotMarkedStrict : StrictnessMark.

Inductive SrcUnpackedness : Type := SrcUnpack : SrcUnpackedness
                                 |  SrcNoUnpack : SrcUnpackedness
                                 |  NoSrcUnpack : SrcUnpackedness.

Inductive SrcStrictness : Type := SrcLazy : SrcStrictness
                               |  SrcStrict : SrcStrictness
                               |  NoSrcStrict : SrcStrictness.

Inductive HsSrcBang : Type := Mk_HsSrcBang : (option BasicTypes.SourceText) -> SrcUnpackedness -> SrcStrictness -> HsSrcBang.

Parameter HsImplBang : Type.

Parameter EqSpec : Type.

Parameter DataConRep : Type.

Parameter DataCon : Type.

Import FieldLabel.

Parameter dataConSourceArity  : DataCon -> BasicTypes.Arity.
Parameter dataConFieldLabels  : DataCon -> list FieldLabel.FieldLabel.
Parameter dataConImplBangs    : DataCon -> HsImplBang.
Parameter dataConName         : DataCon -> Name.Name.
Parameter dataConTag          : DataCon -> BasicTypes.ConTag.

Parameter dataConRepStrictness : DataCon -> SrcStrictness.
(* Midamble *)


Require GHC.Err.
Instance Default_DataCon : GHC.Err.Default DataCon := {}.
Admitted.


Instance Uniqable_DataCon : Unique.Uniquable DataCon := {}.
Admitted.



Local Definition Eq___DataCon_op_zeze__ : DataCon -> DataCon -> bool :=
  fun a b => Unique.getUnique a GHC.Base.== Unique.getUnique b.

Local Definition Eq___DataCon_op_zsze__ : DataCon -> DataCon -> bool :=
  fun a b => Unique.getUnique a GHC.Base./= Unique.getUnique b.

Program Instance Eq___DataCon : GHC.Base.Eq_ DataCon := fun _ k =>
    k {|GHC.Base.op_zeze____ := Eq___DataCon_op_zeze__ ;
      GHC.Base.op_zsze____ := Eq___DataCon_op_zsze__ |}.

Local Definition Ord__DataCon_compare : DataCon -> DataCon -> comparison :=
  fun a b => GHC.Base.compare (Unique.getUnique a) (Unique.getUnique b).

Local Definition Ord__DataCon_op_zg__ : DataCon -> DataCon -> bool :=
  fun a b => Unique.getUnique a GHC.Base.> Unique.getUnique b.

Local Definition Ord__DataCon_op_zgze__ : DataCon -> DataCon -> bool :=
  fun a b => Unique.getUnique a GHC.Base.>= Unique.getUnique b.

Local Definition Ord__DataCon_op_zl__ : DataCon -> DataCon -> bool :=
  fun a b => Unique.getUnique a GHC.Base.< Unique.getUnique b.

Local Definition Ord__DataCon_op_zlze__ : DataCon -> DataCon -> bool :=
  fun a b => Unique.getUnique a GHC.Base.<= Unique.getUnique b.

Local Definition Ord__DataCon_min : DataCon -> DataCon -> DataCon :=
  fun x y => if Ord__DataCon_op_zlze__ x y : bool then x else y.

Local Definition Ord__DataCon_max : DataCon -> DataCon -> DataCon :=
  fun x y => if Ord__DataCon_op_zlze__ x y : bool then y else x.

Program Instance Ord__DataCon : GHC.Base.Ord DataCon := fun _ k =>
    k {|GHC.Base.op_zl____ := Ord__DataCon_op_zl__ ;
      GHC.Base.op_zlze____ := Ord__DataCon_op_zlze__ ;
      GHC.Base.op_zg____ := Ord__DataCon_op_zg__ ;
      GHC.Base.op_zgze____ := Ord__DataCon_op_zgze__ ;
      GHC.Base.compare__ := Ord__DataCon_compare ;
      GHC.Base.max__ := Ord__DataCon_max ;
      GHC.Base.min__ := Ord__DataCon_min |}.

(* Translating `instance Unique.Uniquable DataCon.DataCon' failed: OOPS! Cannot
   find information for class Qualified "Unique" "Uniquable" unsupported *)

(* Translating `instance Name.NamedThing DataCon.DataCon' failed: OOPS! Cannot
   find information for class Qualified "Name" "NamedThing" unsupported *)

(* Translating `instance Outputable.Outputable DataCon.DataCon' failed: OOPS!
   Cannot find information for class Qualified "Outputable" "Outputable"
   unsupported *)

(* Translating `instance Outputable.OutputableBndr DataCon.DataCon' failed:
   OOPS! Cannot find information for class Qualified "Outputable" "OutputableBndr"
   unsupported *)

(* Translating `instance Data.Data.Data DataCon.DataCon' failed: OOPS! Cannot
   find information for class Qualified "Data.Data" "Data" unsupported *)

(* Translating `instance Outputable.Outputable DataCon.HsSrcBang' failed: OOPS!
   Cannot find information for class Qualified "Outputable" "Outputable"
   unsupported *)

(* Translating `instance Outputable.Outputable DataCon.HsImplBang' failed: OOPS!
   Cannot find information for class Qualified "Outputable" "Outputable"
   unsupported *)

(* Translating `instance Outputable.Outputable DataCon.SrcStrictness' failed:
   OOPS! Cannot find information for class Qualified "Outputable" "Outputable"
   unsupported *)

(* Translating `instance Outputable.Outputable DataCon.SrcUnpackedness' failed:
   OOPS! Cannot find information for class Qualified "Outputable" "Outputable"
   unsupported *)

(* Translating `instance Outputable.Outputable DataCon.StrictnessMark' failed:
   OOPS! Cannot find information for class Qualified "Outputable" "Outputable"
   unsupported *)

(* Translating `instance Binary.Binary DataCon.SrcStrictness' failed: OOPS!
   Cannot find information for class Qualified "Binary" "Binary" unsupported *)

(* Translating `instance Binary.Binary DataCon.SrcUnpackedness' failed: OOPS!
   Cannot find information for class Qualified "Binary" "Binary" unsupported *)

(* Translating `instance Data.Data.Data DataCon.HsSrcBang' failed: OOPS! Cannot
   find information for class Qualified "Data.Data" "Data" unsupported *)

(* Translating `instance Data.Data.Data DataCon.SrcUnpackedness' failed: OOPS!
   Cannot find information for class Qualified "Data.Data" "Data" unsupported *)

Local Definition Eq___SrcUnpackedness_op_zeze__
    : SrcUnpackedness -> SrcUnpackedness -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__ , arg_1__ with
      | SrcUnpack , SrcUnpack => true
      | SrcNoUnpack , SrcNoUnpack => true
      | NoSrcUnpack , NoSrcUnpack => true
      | _ , _ => false
    end.

Local Definition Eq___SrcUnpackedness_op_zsze__
    : SrcUnpackedness -> SrcUnpackedness -> bool :=
  fun a b => negb (Eq___SrcUnpackedness_op_zeze__ a b).

Program Instance Eq___SrcUnpackedness : GHC.Base.Eq_ SrcUnpackedness := fun _
                                                                            k =>
    k {|GHC.Base.op_zeze____ := Eq___SrcUnpackedness_op_zeze__ ;
      GHC.Base.op_zsze____ := Eq___SrcUnpackedness_op_zsze__ |}.

(* Translating `instance Data.Data.Data DataCon.SrcStrictness' failed: OOPS!
   Cannot find information for class Qualified "Data.Data" "Data" unsupported *)

Local Definition Eq___SrcStrictness_op_zeze__
    : SrcStrictness -> SrcStrictness -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__ , arg_1__ with
      | SrcLazy , SrcLazy => true
      | SrcStrict , SrcStrict => true
      | NoSrcStrict , NoSrcStrict => true
      | _ , _ => false
    end.

Local Definition Eq___SrcStrictness_op_zsze__
    : SrcStrictness -> SrcStrictness -> bool :=
  fun a b => negb (Eq___SrcStrictness_op_zeze__ a b).

Program Instance Eq___SrcStrictness : GHC.Base.Eq_ SrcStrictness := fun _ k =>
    k {|GHC.Base.op_zeze____ := Eq___SrcStrictness_op_zeze__ ;
      GHC.Base.op_zsze____ := Eq___SrcStrictness_op_zsze__ |}.

(* Translating `instance Data.Data.Data DataCon.HsImplBang' failed: OOPS! Cannot
   find information for class Qualified "Data.Data" "Data" unsupported *)
