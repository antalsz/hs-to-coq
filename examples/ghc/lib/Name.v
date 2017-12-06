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
Require GHC.Num.
Require Maybes.
Require Module.
Require OccName.
Require Panic.
Require SrcLoc.
Require Unique.
Import GHC.Base.Notations.

(* Converted type declarations: *)

Inductive BuiltInSyntax : Type := Mk_BuiltInSyntax : BuiltInSyntax
                               |  UserSyntax : BuiltInSyntax.

Inductive NameSort : Type := External : Module.Module -> NameSort
                          |  WiredIn : Module.Module -> unit -> BuiltInSyntax -> NameSort
                          |  Internal : NameSort
                          |  System : NameSort.

Inductive Name : Type := Mk_Name
                        : NameSort -> OccName.OccName -> GHC.Num.Int -> SrcLoc.SrcSpan -> Name.

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

Definition n_loc (arg_1__ : Name) :=
  match arg_1__ with
    | Mk_Name _ _ _ n_loc => n_loc
  end.

Definition n_occ (arg_2__ : Name) :=
  match arg_2__ with
    | Mk_Name _ n_occ _ _ => n_occ
  end.

Definition n_sort (arg_3__ : Name) :=
  match arg_3__ with
    | Mk_Name n_sort _ _ _ => n_sort
  end.

Definition n_uniq (arg_4__ : Name) :=
  match arg_4__ with
    | Mk_Name _ _ n_uniq _ => n_uniq
  end.
(* Midamble *)

(* BUG: record selctors are not fully qualified. *)
Import OccName.
Import Module.

(* Default values *)
Import Panic.
Instance Default_NameSort : Default NameSort := Build_Default _ System.
Instance Default_Name : Default Name := Build_Default _ (Mk_Name default default default default).


Instance Unique_Name : Unique.Uniquable Name.Name := {}.
Admitted.

(* Converted value declarations: *)

(* The Haskell code containes partial or untranslateable code, which needs the
   following *)

Axiom missingValue : forall {a}, a.

(* Translating `instance Outputable.Outputable Name.NameSort' failed: OOPS!
   Cannot find information for class Qualified "Outputable" "Outputable"
   unsupported *)

(* Translating `instance Control.DeepSeq.NFData Name.Name' failed: OOPS! Cannot
   find information for class Qualified "Control.DeepSeq" "NFData" unsupported *)

(* Translating `instance Control.DeepSeq.NFData Name.NameSort' failed: OOPS!
   Cannot find information for class Qualified "Control.DeepSeq" "NFData"
   unsupported *)

(* Translating `instance OccName.HasOccName Name.Name' failed: OOPS! Cannot find
   information for class Qualified "OccName" "HasOccName" unsupported *)

(* Translating `instance Unique.Uniquable Name.Name' failed: OOPS! Cannot find
   information for class Qualified "Unique" "Uniquable" unsupported *)

Local Definition NamedThing__Name_getName : Name -> Name :=
  fun n => n.

(* Translating `instance Data.Data.Data Name.Name' failed: OOPS! Cannot find
   information for class Qualified "Data.Data" "Data" unsupported *)

(* Translating `instance Binary.Binary Name.Name' failed: using a record pattern
   for the unknown constructor `UserData' unsupported *)

(* Translating `instance Outputable.Outputable Name.Name' failed: OOPS! Cannot
   find information for class Qualified "Outputable" "Outputable" unsupported *)

(* Translating `instance Outputable.OutputableBndr Name.Name' failed: OOPS!
   Cannot find information for class Qualified "Outputable" "OutputableBndr"
   unsupported *)

Definition cmpName : Name -> Name -> comparison :=
  fun n1 n2 => GHC.Base.compare (n_uniq n1) (n_uniq n2).

Local Definition Ord__Name_compare : Name -> Name -> comparison :=
  fun a b => cmpName a b.

Local Definition Ord__Name_op_zg__ : Name -> Name -> bool :=
  fun a b =>
    let scrut_120__ := (Ord__Name_compare a b) in
    match scrut_120__ with
      | Lt => false
      | Eq => false
      | Gt => true
    end.

Local Definition Ord__Name_op_zgze__ : Name -> Name -> bool :=
  fun a b =>
    let scrut_117__ := (Ord__Name_compare a b) in
    match scrut_117__ with
      | Lt => false
      | Eq => true
      | Gt => true
    end.

Local Definition Ord__Name_op_zl__ : Name -> Name -> bool :=
  fun a b =>
    let scrut_114__ := (Ord__Name_compare a b) in
    match scrut_114__ with
      | Lt => true
      | Eq => false
      | Gt => false
    end.

Local Definition Ord__Name_op_zlze__ : Name -> Name -> bool :=
  fun a b =>
    let scrut_111__ := (Ord__Name_compare a b) in
    match scrut_111__ with
      | Lt => true
      | Eq => true
      | Gt => false
    end.

Local Definition Ord__Name_max : Name -> Name -> Name :=
  fun x y => if Ord__Name_op_zlze__ x y : bool then y else x.

Local Definition Ord__Name_min : Name -> Name -> Name :=
  fun x y => if Ord__Name_op_zlze__ x y : bool then x else y.

Local Definition Eq___Name_op_zeze__ : Name -> Name -> bool :=
  fun a b => match cmpName a b with | Eq => true | _ => false end.

Local Definition Eq___Name_op_zsze__ : Name -> Name -> bool :=
  fun a b => match cmpName a b with | Eq => false | _ => true end.

Program Instance Eq___Name : GHC.Base.Eq_ Name := fun _ k =>
    k {|GHC.Base.op_zeze____ := Eq___Name_op_zeze__ ;
      GHC.Base.op_zsze____ := Eq___Name_op_zsze__ |}.

Program Instance Ord__Name : GHC.Base.Ord Name := fun _ k =>
    k {|GHC.Base.op_zl____ := Ord__Name_op_zl__ ;
      GHC.Base.op_zlze____ := Ord__Name_op_zlze__ ;
      GHC.Base.op_zg____ := Ord__Name_op_zg__ ;
      GHC.Base.op_zgze____ := Ord__Name_op_zgze__ ;
      GHC.Base.compare__ := Ord__Name_compare ;
      GHC.Base.max__ := Ord__Name_max ;
      GHC.Base.min__ := Ord__Name_min |}.

Definition getOccFS {a} `{NamedThing a} : a -> FastString.FastString :=
  occNameFS GHC.Base.∘ getOccName.

Definition getOccString {a} `{NamedThing a} : a -> GHC.Base.String :=
  OccName.occNameString GHC.Base.∘ getOccName.

Definition isBuiltInSyntax : Name -> bool :=
  fun arg_90__ =>
    match arg_90__ with
      | Mk_Name (WiredIn _ _ Mk_BuiltInSyntax) _ _ _ => true
      | _ => false
    end.

Definition isExternalName : Name -> bool :=
  fun arg_87__ =>
    match arg_87__ with
      | Mk_Name (External _) _ _ _ => true
      | Mk_Name (WiredIn _ _ _) _ _ _ => true
      | _ => false
    end.

Definition isInternalName : Name -> bool :=
  fun name => negb (isExternalName name).

Definition isSystemName : Name -> bool :=
  fun arg_72__ =>
    match arg_72__ with
      | Mk_Name System _ _ _ => true
      | _ => false
    end.

Definition isWiredInName : Name -> bool :=
  fun arg_95__ =>
    match arg_95__ with
      | Mk_Name (WiredIn _ _ _) _ _ _ => true
      | _ => false
    end.

Definition localiseName : Name -> Name :=
  fun n =>
    match n with
      | Mk_Name n_sort_17__ n_occ_18__ n_uniq_19__ n_loc_20__ => Mk_Name Internal
                                                                         n_occ_18__ n_uniq_19__ n_loc_20__
    end.

Definition mkClonedInternalName : Unique.Unique -> Name -> Name :=
  fun arg_66__ arg_67__ =>
    match arg_66__ , arg_67__ with
      | uniq , Mk_Name _ occ _ loc => Mk_Name missingValue missingValue missingValue
                                              missingValue
    end.

Definition mkDerivedInternalName
    : (OccName.OccName -> OccName.OccName) -> Unique.Unique -> Name -> Name :=
  fun arg_61__ arg_62__ arg_63__ =>
    match arg_61__ , arg_62__ , arg_63__ with
      | derive_occ , uniq , Mk_Name _ occ _ loc => Mk_Name missingValue missingValue
                                                           missingValue missingValue
    end.

Definition mkExternalName
    : Unique.Unique -> Module.Module -> OccName.OccName -> SrcLoc.SrcSpan -> Name :=
  fun uniq mod_ occ loc =>
    Mk_Name missingValue missingValue missingValue missingValue.

Definition mkInternalName
    : Unique.Unique -> OccName.OccName -> SrcLoc.SrcSpan -> Name :=
  fun uniq occ loc => Mk_Name missingValue missingValue missingValue missingValue.

Definition mkFCallName : Unique.Unique -> GHC.Base.String -> Name :=
  fun uniq str => mkInternalName uniq (OccName.mkVarOcc str) SrcLoc.noSrcSpan.

Definition mkSystemNameAt
    : Unique.Unique -> OccName.OccName -> SrcLoc.SrcSpan -> Name :=
  fun uniq occ loc => Mk_Name missingValue missingValue missingValue missingValue.

Definition mkSystemName : Unique.Unique -> OccName.OccName -> Name :=
  fun uniq occ => mkSystemNameAt uniq occ SrcLoc.noSrcSpan.

Definition mkSystemVarName : Unique.Unique -> FastString.FastString -> Name :=
  fun uniq fs => mkSystemName uniq (OccName.mkVarOccFS fs).

Definition mkSysTvName : Unique.Unique -> FastString.FastString -> Name :=
  fun uniq fs => mkSystemName uniq (OccName.mkOccNameFS OccName.tvName fs).

Definition mkWiredInName
    : Module.Module -> OccName.OccName -> Unique.Unique -> unit -> BuiltInSyntax -> Name :=
  fun mod_ occ uniq thing built_in =>
    Mk_Name missingValue missingValue missingValue missingValue.

Definition nameModule_maybe : Name -> option Module.Module :=
  fun arg_74__ =>
    match arg_74__ with
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
    let this_pkg := moduleUnitId this_mod in
    fun nm =>
      let scrut_80__ := nameModule_maybe nm in
      match scrut_80__ with
        | None => false
        | Some nm_mod => andb (nm_mod GHC.Base./= this_mod) (moduleUnitId nm_mod
                              GHC.Base.== this_pkg)
      end.

Definition nameIsFromExternalPackage : Module.UnitId -> Name -> bool :=
  fun this_pkg name =>
    match nameModule_maybe name with
      | Some mod_ => if andb (moduleUnitId mod_ GHC.Base./= this_pkg) (negb
                             (Module.isInteractiveModule mod_)) : bool
                     then true
                     else false
      | _ => false
    end.

Definition nameOccName : Name -> OccName.OccName :=
  fun name => n_occ name.

Definition mkLocalisedOccName : Module.Module -> (option
                                GHC.Base.String -> OccName.OccName -> OccName.OccName) -> Name -> OccName.OccName :=
  fun this_mod mk_occ name =>
    let origin :=
      let j_107__ :=
        Some ((Module.moduleNameColons GHC.Base.∘ (moduleName GHC.Base.∘ nameModule))
             GHC.Base.$ name) in
      if nameIsLocalOrFrom this_mod name : bool
      then None
      else j_107__ in
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

Local Definition NamedThing__Name_getOccName : Name -> OccName.OccName :=
  fun n => nameOccName (NamedThing__Name_getName n).

Program Instance NamedThing__Name : NamedThing Name := fun _ k =>
    k {|getName__ := NamedThing__Name_getName ;
      getOccName__ := NamedThing__Name_getOccName |}.

Definition nameSortStableString : NameSort -> GHC.Base.String :=
  fun arg_7__ =>
    match arg_7__ with
      | System => GHC.Base.hs_string__ "$_sys"
      | Internal => GHC.Base.hs_string__ "$_in"
      | External mod_ => Module.moduleStableString mod_
      | WiredIn mod_ _ _ => Module.moduleStableString mod_
    end.

Definition nameStableString : Name -> GHC.Base.String :=
  fun arg_13__ =>
    match arg_13__ with
      | Mk_Name n_sort n_occ n_uniq n_loc => Coq.Init.Datatypes.app
                                             (nameSortStableString n_sort) (Coq.Init.Datatypes.app (GHC.Base.hs_string__
                                                                                                   "$")
                                                                                                   (OccName.occNameString
                                                                                                   n_occ))
    end.

Definition nameSrcLoc : Name -> SrcLoc.SrcLoc :=
  fun name => SrcLoc.srcSpanStart (n_loc name).

Definition getSrcLoc {a} `{NamedThing a} : a -> SrcLoc.SrcLoc :=
  nameSrcLoc GHC.Base.∘ getName.

Definition nameSrcSpan : Name -> SrcLoc.SrcSpan :=
  fun name => n_loc name.

Definition getSrcSpan {a} `{NamedThing a} : a -> SrcLoc.SrcSpan :=
  nameSrcSpan GHC.Base.∘ getName.

Definition nameUnique : Name -> Unique.Unique :=
  fun name => Unique.mkUniqueGrimily (n_uniq name).

Definition setNameLoc : Name -> SrcLoc.SrcSpan -> Name :=
  fun name loc =>
    match name with
      | Mk_Name n_sort_41__ n_occ_42__ n_uniq_43__ n_loc_44__ => Mk_Name n_sort_41__
                                                                         n_occ_42__ n_uniq_43__ loc
    end.

Definition setNameUnique : Name -> Unique.Unique -> Name :=
  fun name uniq =>
    match name with
      | Mk_Name n_sort_48__ n_occ_49__ n_uniq_50__ n_loc_51__ => Mk_Name n_sort_48__
                                                                         n_occ_49__ (Unique.getKey uniq) n_loc_51__
    end.

Definition tidyNameOcc : Name -> OccName.OccName -> Name :=
  fun arg_24__ arg_25__ =>
    match arg_24__ , arg_25__ with
      | (Mk_Name System _ _ _ as name) , occ => match name with
                                                  | Mk_Name n_sort_26__ n_occ_27__ n_uniq_28__ n_loc_29__ => Mk_Name
                                                                                                             Internal
                                                                                                             occ
                                                                                                             n_uniq_28__
                                                                                                             n_loc_29__
                                                end
      | name , occ => match name with
                        | Mk_Name n_sort_33__ n_occ_34__ n_uniq_35__ n_loc_36__ => Mk_Name n_sort_33__
                                                                                           occ n_uniq_35__ n_loc_36__
                      end
    end.

Definition wiredInNameTyThing_maybe : Name -> option unit :=
  fun arg_92__ =>
    match arg_92__ with
      | Mk_Name (WiredIn _ thing _) _ _ _ => Some thing
      | _ => None
    end.

(* Unbound variables:
     None Some andb bool comparison default false moduleName moduleUnitId negb
     occNameFS option orb true unit Coq.Init.Datatypes.app FastString.FastString
     GHC.Base.Eq_ GHC.Base.Ord GHC.Base.String GHC.Base.compare GHC.Base.op_z2218U__
     GHC.Base.op_zd__ GHC.Base.op_zeze__ GHC.Base.op_zsze__ GHC.Num.Int Maybes.orElse
     Module.Module Module.UnitId Module.isInteractiveModule Module.moduleNameColons
     Module.moduleStableString OccName.OccName OccName.isDataOcc OccName.isTcOcc
     OccName.isTvOcc OccName.isValOcc OccName.isVarOcc OccName.mkOccNameFS
     OccName.mkVarOcc OccName.mkVarOccFS OccName.occNameString OccName.tvName
     Panic.panic SrcLoc.SrcLoc SrcLoc.SrcSpan SrcLoc.noSrcSpan SrcLoc.srcSpanStart
     Unique.Unique Unique.getKey Unique.mkUniqueGrimily
*)
