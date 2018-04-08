
(*
Require Name.
Require Class.

(* Record selectors *)
Parameter tyConName    : TyCon -> Name.Name.
Parameter tyConKind    : TyCon -> Kind.
Parameter tyConResKind : TyCon -> Kind.
Parameter tyConBinders : TyCon -> list TyBinder.
Parameter tyConTyVars  : TyCon -> list TyVar.

Parameter isLiftedTypeKindTyConName : Name.Name -> bool.

(* Need to skip tyConAssoc_maybe *)
Parameter isTyConAssoc : TyCon -> bool.
Parameter makeTyConAbstract : TyCon -> TyCon.
Parameter mkClassTyCon : Name.Name -> list TyBinder -> list TyVar
                          -> list Role -> AlgTyConRhs -> Class.Class
                          -> BasicTypes.RecFlag -> Name.Name -> TyCon.
Parameter algTcFields : TyCon -> FieldLabel.FieldLabelEnv.

(* record label flLabel is not qualified. *)
Parameter fieldsOfAlgTcRhs : AlgTyConRhs -> FieldLabel.FieldLabelEnv.
*)