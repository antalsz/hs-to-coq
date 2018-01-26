Instance Default_Literal : GHC.Err.Default Literal :=
  GHC.Err.Build_Default _ MachNullAddr.

Parameter absent_lits :  UniqFM.UniqFM Literal.

Parameter inCharRange : GHC.Char.Char -> bool.
