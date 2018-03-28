Import GHC.Prim.
Instance Unpeel_Const a b : Unpeel (Const a b) a := Build_Unpeel _ _ getConst Mk_Const
