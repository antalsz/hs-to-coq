(* Cannot automatically translate b/c
   top-level pattern binding unsupported. *)

Require Import Module.
Require Unique.
Require Name.

Parameter gHC_PRIM  : Module.
Parameter gHC_TYPES : Module.

Parameter liftedTypeKindTyConKey  : Unique.Unique.
Parameter starKindTyConKey        : Unique.Unique.
Parameter unicodeStarKindTyConKey : Unique.Unique.
Parameter constraintKindTyConKey  : Unique.Unique.
Parameter tYPETyConKey            : Unique.Unique.
Parameter ptrRepLiftedDataConKey  : Unique.Unique.
Parameter eqReprPrimTyConKey      : Unique.Unique.
Parameter eqPrimTyConKey          : Unique.Unique.
Parameter runtimeRepTyConKey      : Unique.Unique.

Parameter makeStaticName : Name.Name.