(* We might put these elsewhere, but these are some types that we 
   can use for untying the knots in DataCon/Class/PatSyn/TyCon *)

Require GHC.Err.
Require GHC.Nat.
Require GHC.Base.

Parameter DataConId : Type.
Parameter ClassId   : Type.
Parameter PatSynId  : Type.
Parameter TyConId   : Type.

Parameter Default_PatSynId  : GHC.Err.Default PatSynId.  Existing Instance Default_PatSynId.
Parameter Default_ClassId   : GHC.Err.Default ClassId.   Existing Instance Default_ClassId.
Parameter Default_DataConId : GHC.Err.Default DataConId. Existing Instance Default_DataConId.
Parameter Default_TyConId   : GHC.Err.Default TyConId.   Existing Instance Default_TyConId.

Parameter Eq_PatSynId  : Base.Eq_ PatSynId.  Existing Instance Eq_PatSynId.
Parameter Eq_ClassId   : Base.Eq_ ClassId.   Existing Instance Eq_ClassId.
Parameter Eq_DataConId : Base.Eq_ DataConId. Existing Instance Eq_DataConId.
Parameter Eq_TyConId   : Base.Eq_ TyConId.   Existing Instance Eq_TyConId.

Parameter Ord_PatSynId  : Base.Ord PatSynId.  Existing Instance Ord_PatSynId.
Parameter Ord_ClassId   : Base.Ord ClassId.   Existing Instance Ord_ClassId.
Parameter Ord_DataConId : Base.Ord DataConId. Existing Instance Ord_DataConId.
Parameter Ord_TyConId   : Base.Ord TyConId.   Existing Instance Ord_TyConId.
