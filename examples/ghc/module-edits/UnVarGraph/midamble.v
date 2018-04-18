Instance Default_UnVarSet : GHC.Err.Default UnVarSet :=
  GHC.Err.Build_Default _ (Mk_UnVarSet GHC.Err.default).
Instance Default_UnVarGraph : GHC.Err.Default UnVarGraph :=
  GHC.Err.Build_Default _ (Mk_UnVarGraph GHC.Err.default).


Instance Unpeel_UnVarSet : Prim.Unpeel UnVarSet Data.IntSet.Internal.IntSet :=
  Prim.Build_Unpeel _ _ (fun x => match x with | Mk_UnVarSet y => y end) Mk_UnVarSet.
Instance Unpeel_UnVarGraph : Prim.Unpeel UnVarGraph (Bag.Bag Gen) :=
  Prim.Build_Unpeel _ _ (fun x => match x with | Mk_UnVarGraph y => y end) Mk_UnVarGraph.