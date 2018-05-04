(* We might put these elsewhere, but these are some types that we 
   can use for untying the knots in DataCon/Class/PatSyn/TyCon *)

Require GHC.Err.
Require GHC.Nat.
Require GHC.Base.

Parameter DataConId : Type.
Parameter ClassId   : Type.
Parameter PatSynId  : Type.
Parameter TyConId   : Type.

Parameter Default_DataConId : GHC.Err.Default DataConId.
Parameter Default_ClassId   : GHC.Err.Default ClassId.
Parameter Default_PatSynId  : GHC.Err.Default PatSynId.
Parameter Default_TyConId   : GHC.Err.Default TyConId.

Parameter Eq_PatSynId  : Base.Eq_ PatSynId.
Parameter Eq_ClassId   : Base.Eq_ ClassId.
Parameter Eq_DataConId : Base.Eq_ DataConId.
Parameter Eq_TyConId   : Base.Eq_ TyConId.

Parameter Ord_PatSynId  : Base.Ord PatSynId.
Parameter Ord_ClassId   : Base.Ord ClassId.
Parameter Ord_DataConId : Base.Ord DataConId.
Parameter Ord_TyConId   : Base.Ord TyConId.

