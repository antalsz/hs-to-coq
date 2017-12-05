Instance Default_Literal : Panic.Default Literal :=
  Panic.Build_Default _ MachNullAddr.

Parameter absent_lits :  UniqFM.UniqFM Literal.

Parameter inCharRange : GHC.Char.Char -> bool.
