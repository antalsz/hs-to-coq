

Instance Default__AlgTyConFlav : Err.Default AlgTyConFlav :=
  Err.Build_Default _ (VanillaAlgTyCon Err.default).

Instance Default__RuntimRepInfo : Err.Default RuntimeRepInfo :=
  Err.Build_Default _ Mk_RuntimeRepInfo_Dummy.                                 

Instance Uniquable_Tycon : Unique.Uniquable TyCon. 
Admitted.