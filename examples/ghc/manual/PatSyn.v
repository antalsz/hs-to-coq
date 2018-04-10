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
Require Data.Foldable.
Require Data.Function.
Require Data.Tuple.
Require FieldLabel.
Require GHC.Base.
Require GHC.List.
Require Name.
Require OccName.
Require Panic.
Require Unique.
Require Var.
Import GHC.Base.Notations.

(* Converted type declarations: *)

Inductive PatSyn : Type
  := MkPatSyn
   : Name.Name ->
     Unique.Unique ->
     list unit ->
     BasicTypes.Arity ->
     bool ->
     list FieldLabel.FieldLabel ->
     list Var.TyVarBinder ->
     unit ->
     list Var.TyVarBinder ->
     unit -> unit -> (Var.Id * bool)%type -> option (Var.Id * bool)%type -> PatSyn.

Definition psArgs (arg_0__ : PatSyn) :=
  let 'MkPatSyn _ _ psArgs _ _ _ _ _ _ _ _ _ _ := arg_0__ in
  psArgs.

Definition psArity (arg_0__ : PatSyn) :=
  let 'MkPatSyn _ _ _ psArity _ _ _ _ _ _ _ _ _ := arg_0__ in
  psArity.

Definition psBuilder (arg_0__ : PatSyn) :=
  let 'MkPatSyn _ _ _ _ _ _ _ _ _ _ _ _ psBuilder := arg_0__ in
  psBuilder.

Definition psExTyVars (arg_0__ : PatSyn) :=
  let 'MkPatSyn _ _ _ _ _ _ _ _ psExTyVars _ _ _ _ := arg_0__ in
  psExTyVars.

Definition psFieldLabels (arg_0__ : PatSyn) :=
  let 'MkPatSyn _ _ _ _ _ psFieldLabels _ _ _ _ _ _ _ := arg_0__ in
  psFieldLabels.

Definition psInfix (arg_0__ : PatSyn) :=
  let 'MkPatSyn _ _ _ _ psInfix _ _ _ _ _ _ _ _ := arg_0__ in
  psInfix.

Definition psMatcher (arg_0__ : PatSyn) :=
  let 'MkPatSyn _ _ _ _ _ _ _ _ _ _ _ psMatcher _ := arg_0__ in
  psMatcher.

Definition psName (arg_0__ : PatSyn) :=
  let 'MkPatSyn psName _ _ _ _ _ _ _ _ _ _ _ _ := arg_0__ in
  psName.

Definition psProvTheta (arg_0__ : PatSyn) :=
  let 'MkPatSyn _ _ _ _ _ _ _ _ _ psProvTheta _ _ _ := arg_0__ in
  psProvTheta.

Definition psReqTheta (arg_0__ : PatSyn) :=
  let 'MkPatSyn _ _ _ _ _ _ _ psReqTheta _ _ _ _ _ := arg_0__ in
  psReqTheta.

Definition psResultTy (arg_0__ : PatSyn) :=
  let 'MkPatSyn _ _ _ _ _ _ _ _ _ _ psResultTy _ _ := arg_0__ in
  psResultTy.

Definition psUnique (arg_0__ : PatSyn) :=
  let 'MkPatSyn _ psUnique _ _ _ _ _ _ _ _ _ _ _ := arg_0__ in
  psUnique.

Definition psUnivTyVars (arg_0__ : PatSyn) :=
  let 'MkPatSyn _ _ _ _ _ _ psUnivTyVars _ _ _ _ _ _ := arg_0__ in
  psUnivTyVars.
(* Midamble *)


(* Converted value declarations: *)

Local Definition Uniquable__PatSyn_getUnique : PatSyn -> Unique.Unique :=
  psUnique.

Program Instance Uniquable__PatSyn : Unique.Uniquable PatSyn :=
  fun _ k => k {| Unique.getUnique__ := Uniquable__PatSyn_getUnique |}.

Local Definition Eq___PatSyn_op_zeze__ : PatSyn -> PatSyn -> bool :=
  Data.Function.on _GHC.Base.==_ Unique.getUnique.

Local Definition Eq___PatSyn_op_zsze__ : PatSyn -> PatSyn -> bool :=
  Data.Function.on _GHC.Base./=_ Unique.getUnique.

Program Instance Eq___PatSyn : GHC.Base.Eq_ PatSyn :=
  fun _ k =>
    k {| GHC.Base.op_zeze____ := Eq___PatSyn_op_zeze__ ;
         GHC.Base.op_zsze____ := Eq___PatSyn_op_zsze__ |}.

(* Skipping instance Outputable__PatSyn of class Outputable *)

(* Skipping instance OutputableBndr__PatSyn of class OutputableBndr *)

(* Skipping instance Data__PatSyn of class Data *)

Definition mkPatSyn
   : Name.Name ->
     bool ->
     (list Var.TyVarBinder * unit)%type ->
     (list Var.TyVarBinder * unit)%type ->
     list unit ->
     unit ->
     (Var.Id * bool)%type ->
     option (Var.Id * bool)%type -> list FieldLabel.FieldLabel -> PatSyn :=
  fun arg_0__ arg_1__ arg_2__ arg_3__ arg_4__ arg_5__ arg_6__ arg_7__ arg_8__ =>
    match arg_0__
        , arg_1__
        , arg_2__
        , arg_3__
        , arg_4__
        , arg_5__
        , arg_6__
        , arg_7__
        , arg_8__ with
    | name
    , declared_infix
    , pair univ_tvs req_theta
    , pair ex_tvs prov_theta
    , orig_args
    , orig_res_ty
    , matcher
    , builder
    , field_labels =>
        MkPatSyn name (Unique.getUnique name) orig_args (Data.Foldable.length orig_args)
                 declared_infix field_labels univ_tvs req_theta ex_tvs prov_theta orig_res_ty
                 matcher builder
    end.

Definition patSynArgs : PatSyn -> list unit :=
  psArgs.

Definition patSynArity : PatSyn -> BasicTypes.Arity :=
  psArity.

Definition patSynBuilder : PatSyn -> option (Var.Id * bool)%type :=
  psBuilder.

Definition patSynExTyVarBinders : PatSyn -> list Var.TyVarBinder :=
  psExTyVars.

Definition patSynExTyVars : PatSyn -> list Var.TyVar :=
  fun ps => Var.binderVars (psExTyVars ps).

Definition patSynFieldLabels : PatSyn -> list FieldLabel.FieldLabel :=
  psFieldLabels.

Definition patSynFieldType : PatSyn -> FieldLabel.FieldLabelString -> unit :=
  fun ps label =>
    match Data.Foldable.find ((fun arg_0__ => arg_0__ GHC.Base.== label) GHC.Base.∘
                              (FieldLabel.flLabel GHC.Base.∘ Data.Tuple.fst)) (GHC.List.zip (psFieldLabels ps)
                                                                                            (psArgs ps)) with
    | Some (pair _ ty) => ty
    | None =>
        Panic.panicStr (GHC.Base.hs_string__ "dataConFieldType") (GHC.Base.mappend
                                                                  (Panic.noString ps) (Panic.noString label))
    end.

Definition patSynIsInfix : PatSyn -> bool :=
  psInfix.

Definition patSynMatcher : PatSyn -> (Var.Id * bool)%type :=
  psMatcher.

Definition patSynName : PatSyn -> Name.Name :=
  psName.

Local Definition NamedThing__PatSyn_getName : PatSyn -> Name.Name :=
  patSynName.

Local Definition NamedThing__PatSyn_getOccName : PatSyn -> OccName.OccName :=
  fun n => Name.nameOccName (NamedThing__PatSyn_getName n).

Program Instance NamedThing__PatSyn : Name.NamedThing PatSyn :=
  fun _ k =>
    k {| Name.getName__ := NamedThing__PatSyn_getName ;
         Name.getOccName__ := NamedThing__PatSyn_getOccName |}.

Definition patSynSig
   : PatSyn ->
     (list Var.TyVar * unit * list Var.TyVar * unit * list unit * unit)%type :=
  fun '(MkPatSyn _ _ arg_tys _ _ _ univ_tvs req ex_tvs prov res_ty _ _) =>
    pair (pair (pair (pair (pair (Var.binderVars univ_tvs) req) (Var.binderVars
                            ex_tvs)) prov) arg_tys) res_ty.

Definition patSynUnivTyVarBinders : PatSyn -> list Var.TyVarBinder :=
  psUnivTyVars.

Definition tidyPatSynIds : (Var.Id -> Var.Id) -> PatSyn -> PatSyn :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | tidy_fn, (MkPatSyn _ _ _ _ _ _ _ _ _ _ _ matcher builder as ps) =>
        let tidy_pr := fun '(pair id dummy) => pair (tidy_fn id) dummy in
        let 'MkPatSyn psName_5__ psUnique_6__ psArgs_7__ psArity_8__ psInfix_9__
           psFieldLabels_10__ psUnivTyVars_11__ psReqTheta_12__ psExTyVars_13__
           psProvTheta_14__ psResultTy_15__ psMatcher_16__ psBuilder_17__ := ps in
        MkPatSyn psName_5__ psUnique_6__ psArgs_7__ psArity_8__ psInfix_9__
                 psFieldLabels_10__ psUnivTyVars_11__ psReqTheta_12__ psExTyVars_13__
                 psProvTheta_14__ psResultTy_15__ (tidy_pr matcher) (GHC.Base.fmap tidy_pr
                  builder)
    end.

(* External variables:
     None Some bool list op_zt__ option pair unit BasicTypes.Arity Data.Foldable.find
     Data.Foldable.length Data.Function.on Data.Tuple.fst FieldLabel.FieldLabel
     FieldLabel.FieldLabelString FieldLabel.flLabel GHC.Base.Eq_ GHC.Base.fmap
     GHC.Base.mappend GHC.Base.op_z2218U__ GHC.Base.op_zeze__ GHC.Base.op_zeze____
     GHC.Base.op_zsze__ GHC.Base.op_zsze____ GHC.List.zip Name.Name Name.NamedThing
     Name.getName__ Name.getOccName__ Name.nameOccName OccName.OccName Panic.noString
     Panic.panicStr Unique.Uniquable Unique.Unique Unique.getUnique
     Unique.getUnique__ Var.Id Var.TyVar Var.TyVarBinder Var.binderVars
*)
