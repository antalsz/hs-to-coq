Instance Unpeel_IgnorePackageFlag : Prim.Unpeel IgnorePackageFlag GHC.Base.String :=
  Prim.Build_Unpeel _ _ (fun x => match x with | IgnorePackage y => y end) IgnorePackage.


Instance Default__DynFlags
   : GHC.Err.Default DynFlags := {}.
Admitted.
