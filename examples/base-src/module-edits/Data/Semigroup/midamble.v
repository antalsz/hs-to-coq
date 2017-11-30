Require Import GHC.Prim.
Instance Unpeel_WrappedMonoid a : Unpeel (WrappedMonoid a) a := Build_Unpeel _ _ unwrapMonoid WrapMonoid.
Instance Unpeel_Last  a : Unpeel (Last a) a := Build_Unpeel _ _ getLast Mk_Last.
Instance Unpeel_First  a : Unpeel (First a) a := Build_Unpeel _ _ getFirst Mk_First.
Instance Unpeel_Max  a : Unpeel (Max a) a := Build_Unpeel _ _ getMax Mk_Max.
Instance Unpeel_Min  a : Unpeel (Min a) a := Build_Unpeel _ _ getMin Mk_Min.
Instance Unpeel_Option  a : Unpeel (Option a) (option a) := Build_Unpeel _ _ getOption Mk_Option.
