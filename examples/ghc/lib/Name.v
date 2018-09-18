(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Coq.Program.Tactics.
Require Coq.Program.Wf.

(* Converted imports: *)

Require Coq.Init.Datatypes.
Require FastString.
Require GHC.Base.
Require GHC.Err.
Require Maybes.
Require Module.
Require OccName.
Require Panic.
Require SrcLoc.
Require Unique.
Require Util.
Import GHC.Base.Notations.

(* Converted type declarations: *)

Inductive BuiltInSyntax : Type
  := Mk_BuiltInSyntax : BuiltInSyntax
  |  UserSyntax : BuiltInSyntax.

Inductive NameSort : Type
  := External : Module.Module -> NameSort
  |  WiredIn : Module.Module -> unit -> BuiltInSyntax -> NameSort
  |  Internal : NameSort
  |  System : NameSort.

Inductive Name : Type
  := Mk_Name (n_sort : NameSort) (n_occ : OccName.OccName) (n_uniq
    : Unique.Unique) (n_loc : SrcLoc.SrcSpan)
   : Name.

Record NamedThing__Dict a := NamedThing__Dict_Build {
  getName__ : a -> Name ;
  getOccName__ : a -> OccName.OccName }.

Definition NamedThing a :=
  forall r, (NamedThing__Dict a -> r) -> r.

Existing Class NamedThing.

Definition getName `{g : NamedThing a} : a -> Name :=
  g _ (getName__ a).

Definition getOccName `{g : NamedThing a} : a -> OccName.OccName :=
  g _ (getOccName__ a).

Instance Default__BuiltInSyntax : GHC.Err.Default BuiltInSyntax :=
  GHC.Err.Build_Default _ Mk_BuiltInSyntax.

Instance Default__NameSort : GHC.Err.Default NameSort :=
  GHC.Err.Build_Default _ Internal.

Definition n_loc (arg_0__ : Name) :=
  let 'Mk_Name _ _ _ n_loc := arg_0__ in
  n_loc.

Definition n_occ (arg_0__ : Name) :=
  let 'Mk_Name _ n_occ _ _ := arg_0__ in
  n_occ.

Definition n_sort (arg_0__ : Name) :=
  let 'Mk_Name n_sort _ _ _ := arg_0__ in
  n_sort.

Definition n_uniq (arg_0__ : Name) :=
  let 'Mk_Name _ _ n_uniq _ := arg_0__ in
  n_uniq.
(* Midamble *)

(* BUG: record selctors are not fully qualified. *)
Import OccName.
Import Module.

(* Default values *)
Require Import GHC.Err.
Instance Default__Name : Default Name := Build_Default _ (Mk_Name default default default default).

Instance Unique_Name : Unique.Uniquable Name := {}.
Admitted.

(* Converted value declarations: *)

Local Definition NamedThing__Name_getName : Name -> Name :=
  fun n => n.

Local Definition NamedThing__GenLocated_getName {inst_e} {inst_l} `{NamedThing
  inst_e}
   : (SrcLoc.GenLocated inst_l inst_e) -> Name :=
  getName GHC.Base.∘ SrcLoc.unLoc.

(* Skipping instance NFData__Name of class NFData *)

(* Skipping instance Data__Name of class Data *)

(* Skipping instance Binary__Name of class Binary *)

(* Skipping instance Outputable__Name of class Outputable *)

(* Skipping instance OutputableBndr__Name of class OutputableBndr *)

(* Skipping instance Outputable__NameSort of class Outputable *)

(* Skipping instance NFData__NameSort of class NFData *)

Definition cmpName : Name -> Name -> comparison :=
  fun n1 n2 => Unique.nonDetCmpUnique (n_uniq n1) (n_uniq n2).

Local Definition Ord__Name_compare : Name -> Name -> comparison :=
  fun a b => cmpName a b.

Local Definition Ord__Name_op_zl__ : Name -> Name -> bool :=
  fun a b =>
    match (Ord__Name_compare a b) with
    | Lt => true
    | Eq => false
    | Gt => false
    end.

Local Definition Ord__Name_op_zlze__ : Name -> Name -> bool :=
  fun a b =>
    match (Ord__Name_compare a b) with
    | Lt => true
    | Eq => true
    | Gt => false
    end.

Local Definition Ord__Name_max : Name -> Name -> Name :=
  fun x y => if Ord__Name_op_zlze__ x y : bool then y else x.

Local Definition Ord__Name_min : Name -> Name -> Name :=
  fun x y => if Ord__Name_op_zlze__ x y : bool then x else y.

Local Definition Ord__Name_op_zg__ : Name -> Name -> bool :=
  fun a b =>
    match (Ord__Name_compare a b) with
    | Lt => false
    | Eq => false
    | Gt => true
    end.

Local Definition Ord__Name_op_zgze__ : Name -> Name -> bool :=
  fun a b =>
    match (Ord__Name_compare a b) with
    | Lt => false
    | Eq => true
    | Gt => true
    end.

Local Definition Eq___Name_op_zeze__ : Name -> Name -> bool :=
  fun a b => match cmpName a b with | Eq => true | _ => false end.

Local Definition Eq___Name_op_zsze__ : Name -> Name -> bool :=
  fun a b => match cmpName a b with | Eq => false | _ => true end.

Program Instance Eq___Name : GHC.Base.Eq_ Name :=
  fun _ k =>
    k {| GHC.Base.op_zeze____ := Eq___Name_op_zeze__ ;
         GHC.Base.op_zsze____ := Eq___Name_op_zsze__ |}.

Program Instance Ord__Name : GHC.Base.Ord Name :=
  fun _ k =>
    k {| GHC.Base.op_zl____ := Ord__Name_op_zl__ ;
         GHC.Base.op_zlze____ := Ord__Name_op_zlze__ ;
         GHC.Base.op_zg____ := Ord__Name_op_zg__ ;
         GHC.Base.op_zgze____ := Ord__Name_op_zgze__ ;
         GHC.Base.compare__ := Ord__Name_compare ;
         GHC.Base.max__ := Ord__Name_max ;
         GHC.Base.min__ := Ord__Name_min |}.

Definition getOccFS {a} `{NamedThing a} : a -> FastString.FastString :=
  OccName.occNameFS GHC.Base.∘ getOccName.

Definition getOccString {a} `{NamedThing a} : a -> GHC.Base.String :=
  OccName.occNameString GHC.Base.∘ getOccName.

Definition isBuiltInSyntax : Name -> bool :=
  fun arg_0__ =>
    match arg_0__ with
    | Mk_Name (WiredIn _ _ Mk_BuiltInSyntax) _ _ _ => true
    | _ => false
    end.

Definition isExternalName : Name -> bool :=
  fun arg_0__ =>
    match arg_0__ with
    | Mk_Name (External _) _ _ _ => true
    | Mk_Name (WiredIn _ _ _) _ _ _ => true
    | _ => false
    end.

Definition isInternalName : Name -> bool :=
  fun name => negb (isExternalName name).

Definition isSystemName : Name -> bool :=
  fun arg_0__ =>
    match arg_0__ with
    | Mk_Name System _ _ _ => true
    | _ => false
    end.

Definition isWiredInName : Name -> bool :=
  fun arg_0__ =>
    match arg_0__ with
    | Mk_Name (WiredIn _ _ _) _ _ _ => true
    | _ => false
    end.

Definition localiseName : Name -> Name :=
  fun '(Mk_Name n_sort_0__ n_occ_1__ n_uniq_2__ n_loc_3__) =>
    Mk_Name Internal n_occ_1__ n_uniq_2__ n_loc_3__.

Definition mkClonedInternalName : Unique.Unique -> Name -> Name :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | uniq, Mk_Name _ occ _ loc => Mk_Name Internal occ uniq loc
    end.

Definition mkDerivedInternalName
   : (OccName.OccName -> OccName.OccName) -> Unique.Unique -> Name -> Name :=
  fun arg_0__ arg_1__ arg_2__ =>
    match arg_0__, arg_1__, arg_2__ with
    | derive_occ, uniq, Mk_Name _ occ _ loc =>
        Mk_Name Internal (derive_occ occ) uniq loc
    end.

Definition mkExternalName
   : Unique.Unique ->
     Module.Module -> OccName.OccName -> SrcLoc.SrcSpan -> Name :=
  fun uniq mod_ occ loc => Mk_Name (External mod_) occ uniq loc.

Definition mkInternalName
   : Unique.Unique -> OccName.OccName -> SrcLoc.SrcSpan -> Name :=
  fun uniq occ loc => Mk_Name Internal occ uniq loc.

Definition mkFCallName : Unique.Unique -> GHC.Base.String -> Name :=
  fun uniq str => mkInternalName uniq (OccName.mkVarOcc str) SrcLoc.noSrcSpan.

Definition mkSystemNameAt
   : Unique.Unique -> OccName.OccName -> SrcLoc.SrcSpan -> Name :=
  fun uniq occ loc => Mk_Name System occ uniq loc.

Definition mkSystemName : Unique.Unique -> OccName.OccName -> Name :=
  fun uniq occ => mkSystemNameAt uniq occ SrcLoc.noSrcSpan.

Definition mkSystemVarName : Unique.Unique -> FastString.FastString -> Name :=
  fun uniq fs => mkSystemName uniq (OccName.mkVarOccFS fs).

Definition mkSysTvName : Unique.Unique -> FastString.FastString -> Name :=
  fun uniq fs => mkSystemName uniq (OccName.mkTyVarOccFS fs).

Definition nameIsHomePackage : Module.Module -> Name -> bool :=
  fun this_mod =>
    let this_pkg := Module.moduleUnitId this_mod in
    fun nm =>
      match n_sort nm with
      | External nm_mod => Module.moduleUnitId nm_mod GHC.Base.== this_pkg
      | WiredIn nm_mod _ _ => Module.moduleUnitId nm_mod GHC.Base.== this_pkg
      | Internal => true
      | System => false
      end.

Definition nameModule_maybe : Name -> option Module.Module :=
  fun arg_0__ =>
    match arg_0__ with
    | Mk_Name (External mod_) _ _ _ => Some mod_
    | Mk_Name (WiredIn mod_ _ _) _ _ _ => Some mod_
    | _ => None
    end.

Definition nameModule : Name -> Module.Module :=
  fun name => Maybes.orElse (nameModule_maybe name) (Panic.panic default).

Definition nameIsLocalOrFrom : Module.Module -> Name -> bool :=
  fun from name =>
    match nameModule_maybe name with
    | Some mod_ => orb (from GHC.Base.== mod_) (Module.isInteractiveModule mod_)
    | _ => true
    end.

Definition nameIsHomePackageImport : Module.Module -> Name -> bool :=
  fun this_mod =>
    let this_pkg := Module.moduleUnitId this_mod in
    fun nm =>
      match nameModule_maybe nm with
      | None => false
      | Some nm_mod =>
          andb (nm_mod GHC.Base./= this_mod) (Module.moduleUnitId nm_mod GHC.Base.==
                this_pkg)
      end.

Definition nameIsFromExternalPackage : Module.UnitId -> Name -> bool :=
  fun this_pkg name =>
    match nameModule_maybe name with
    | Some mod_ =>
        if andb (Module.moduleUnitId mod_ GHC.Base./= this_pkg) (negb
                 (Module.isInteractiveModule mod_)) : bool
        then true else
        false
    | _ => false
    end.

Definition nameOccName : Name -> OccName.OccName :=
  fun name => n_occ name.

Definition mkLocalisedOccName
   : Module.Module ->
     (option GHC.Base.String -> OccName.OccName -> OccName.OccName) ->
     Name -> OccName.OccName :=
  fun this_mod mk_occ name =>
    let origin :=
      if nameIsLocalOrFrom this_mod name : bool then None else
      Some ((Module.moduleNameColons GHC.Base.∘
             (Module.moduleName GHC.Base.∘ nameModule)) name) in
    mk_occ origin (nameOccName name).

Definition isVarName : Name -> bool :=
  OccName.isVarOcc GHC.Base.∘ nameOccName.

Definition isValName : Name -> bool :=
  fun name => OccName.isValOcc (nameOccName name).

Definition isTyVarName : Name -> bool :=
  fun name => OccName.isTvOcc (nameOccName name).

Definition isTyConName : Name -> bool :=
  fun name => OccName.isTcOcc (nameOccName name).

Definition isDataConName : Name -> bool :=
  fun name => OccName.isDataOcc (nameOccName name).

Local Definition HasOccName__Name_occName : Name -> OccName.OccName :=
  nameOccName.

Program Instance HasOccName__Name : OccName.HasOccName Name :=
  fun _ k => k {| OccName.occName__ := HasOccName__Name_occName |}.

Local Definition NamedThing__GenLocated_getOccName {inst_e} {inst_l}
  `{NamedThing inst_e}
   : (SrcLoc.GenLocated inst_l inst_e) -> OccName.OccName :=
  fun n => nameOccName (NamedThing__GenLocated_getName n).

Program Instance NamedThing__GenLocated {e} {l} `{NamedThing e}
   : NamedThing (SrcLoc.GenLocated l e) :=
  fun _ k =>
    k {| getName__ := NamedThing__GenLocated_getName ;
         getOccName__ := NamedThing__GenLocated_getOccName |}.

Local Definition NamedThing__Name_getOccName : Name -> OccName.OccName :=
  fun n => nameOccName (NamedThing__Name_getName n).

Program Instance NamedThing__Name : NamedThing Name :=
  fun _ k =>
    k {| getName__ := NamedThing__Name_getName ;
         getOccName__ := NamedThing__Name_getOccName |}.

Definition nameSortStableString : NameSort -> GHC.Base.String :=
  fun arg_0__ =>
    match arg_0__ with
    | System => GHC.Base.hs_string__ "$_sys"
    | Internal => GHC.Base.hs_string__ "$_in"
    | External mod_ => Module.moduleStableString mod_
    | WiredIn mod_ _ _ => Module.moduleStableString mod_
    end.

Definition nameStableString : Name -> GHC.Base.String :=
  fun '(Mk_Name n_sort n_occ n_uniq n_loc) =>
    Coq.Init.Datatypes.app (nameSortStableString n_sort) (Coq.Init.Datatypes.app
                            (GHC.Base.hs_string__ "$") (OccName.occNameString n_occ)).

Definition nameSrcLoc : Name -> SrcLoc.SrcLoc :=
  fun name => SrcLoc.srcSpanStart (n_loc name).

Definition getSrcLoc {a} `{NamedThing a} : a -> SrcLoc.SrcLoc :=
  nameSrcLoc GHC.Base.∘ getName.

Definition nameSrcSpan : Name -> SrcLoc.SrcSpan :=
  fun name => n_loc name.

Definition getSrcSpan {a} `{NamedThing a} : a -> SrcLoc.SrcSpan :=
  nameSrcSpan GHC.Base.∘ getName.

Definition nameUnique : Name -> Unique.Unique :=
  fun name => n_uniq name.

Local Definition Uniquable__Name_getUnique : Name -> Unique.Unique :=
  nameUnique.

Program Instance Uniquable__Name : Unique.Uniquable Name :=
  fun _ k => k {| Unique.getUnique__ := Uniquable__Name_getUnique |}.

Definition setNameLoc : Name -> SrcLoc.SrcSpan -> Name :=
  fun name loc =>
    let 'Mk_Name n_sort_0__ n_occ_1__ n_uniq_2__ n_loc_3__ := name in
    Mk_Name n_sort_0__ n_occ_1__ n_uniq_2__ loc.

Definition setNameUnique : Name -> Unique.Unique -> Name :=
  fun name uniq =>
    let 'Mk_Name n_sort_0__ n_occ_1__ n_uniq_2__ n_loc_3__ := name in
    Mk_Name n_sort_0__ n_occ_1__ uniq n_loc_3__.

Definition stableNameCmp : Name -> Name -> comparison :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | Mk_Name s1 occ1 _ _, Mk_Name s2 occ2 _ _ =>
        let sort_cmp :=
          fun arg_2__ arg_3__ =>
            match arg_2__, arg_3__ with
            | External m1, External m2 => Module.stableModuleCmp m1 m2
            | External _, _ => Lt
            | WiredIn _ _ _, External _ => Gt
            | WiredIn m1 _ _, WiredIn m2 _ _ => Module.stableModuleCmp m1 m2
            | WiredIn _ _ _, _ => Lt
            | Internal, External _ => Gt
            | Internal, WiredIn _ _ _ => Gt
            | Internal, Internal => Eq
            | Internal, System => Lt
            | System, System => Eq
            | System, _ => Gt
            end in
        Util.thenCmp (sort_cmp s1 s2) (GHC.Base.compare occ1 occ2)
    end.

Definition tidyNameOcc : Name -> OccName.OccName -> Name :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | (Mk_Name System _ _ _ as name), occ =>
        let 'Mk_Name n_sort_2__ n_occ_3__ n_uniq_4__ n_loc_5__ := name in
        Mk_Name Internal occ n_uniq_4__ n_loc_5__
    | name, occ =>
        let 'Mk_Name n_sort_9__ n_occ_10__ n_uniq_11__ n_loc_12__ := name in
        Mk_Name n_sort_9__ occ n_uniq_11__ n_loc_12__
    end.

(* External variables:
     Eq Gt Lt None Some andb bool comparison default false negb option orb true unit
     Coq.Init.Datatypes.app FastString.FastString GHC.Base.Eq_ GHC.Base.Ord
     GHC.Base.String GHC.Base.compare GHC.Base.compare__ GHC.Base.max__
     GHC.Base.min__ GHC.Base.op_z2218U__ GHC.Base.op_zeze__ GHC.Base.op_zeze____
     GHC.Base.op_zg____ GHC.Base.op_zgze____ GHC.Base.op_zl____ GHC.Base.op_zlze____
     GHC.Base.op_zsze__ GHC.Base.op_zsze____ GHC.Err.Build_Default GHC.Err.Default
     Maybes.orElse Module.Module Module.UnitId Module.isInteractiveModule
     Module.moduleName Module.moduleNameColons Module.moduleStableString
     Module.moduleUnitId Module.stableModuleCmp OccName.HasOccName OccName.OccName
     OccName.isDataOcc OccName.isTcOcc OccName.isTvOcc OccName.isValOcc
     OccName.isVarOcc OccName.mkTyVarOccFS OccName.mkVarOcc OccName.mkVarOccFS
     OccName.occNameFS OccName.occNameString OccName.occName__ Panic.panic
     SrcLoc.GenLocated SrcLoc.SrcLoc SrcLoc.SrcSpan SrcLoc.noSrcSpan
     SrcLoc.srcSpanStart SrcLoc.unLoc Unique.Uniquable Unique.Unique
     Unique.getUnique__ Unique.nonDetCmpUnique Util.thenCmp
*)
