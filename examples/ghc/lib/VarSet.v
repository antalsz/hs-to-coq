(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Coq.Program.Tactics.
Require Coq.Program.Wf.

(* Preamble *)

Require Import Core.

(* Converted imports: *)

Require CoreType.
Require Data.Foldable.
Require GHC.Base.
Require GHC.DeferredFix.
Require GHC.Num.
Require Name.
Require UniqDFM.
Require UniqDSet.
Require UniqFM.
Require UniqSet.
Require Unique.
Import GHC.Base.Notations.

(* Converted type declarations: *)

Definition VarSet :=
  (UniqSet.UniqSet CoreType.Var)%type.

Definition TyVarSet :=
  (UniqSet.UniqSet CoreType.TyVar)%type.

Definition TyCoVarSet :=
  (UniqSet.UniqSet CoreType.TyCoVar)%type.

Definition IdSet :=
  (UniqSet.UniqSet CoreType.Id)%type.

Definition DVarSet :=
  (UniqDSet.UniqDSet CoreType.Var)%type.

Definition DTyVarSet :=
  (UniqDSet.UniqDSet CoreType.TyVar)%type.

Definition DTyCoVarSet :=
  (UniqDSet.UniqDSet CoreType.TyCoVar)%type.

Definition DIdSet :=
  (UniqDSet.UniqDSet CoreType.Id)%type.

Definition CoVarSet :=
  (UniqSet.UniqSet CoreType.CoVar)%type.
(* Converted value declarations: *)

Definition allDVarSet : (CoreType.Var -> bool) -> DVarSet -> bool :=
  UniqDFM.allUDFM.

Definition allVarSet : (CoreType.Var -> bool) -> VarSet -> bool :=
  UniqSet.uniqSetAll.

Definition anyDVarSet : (CoreType.Var -> bool) -> DVarSet -> bool :=
  UniqDFM.anyUDFM.

Definition anyVarSet : (CoreType.Var -> bool) -> VarSet -> bool :=
  UniqSet.uniqSetAny.

Definition dVarSetElems : DVarSet -> list CoreType.Var :=
  UniqDSet.uniqDSetToList.

Definition dVarSetIntersectVarSet : DVarSet -> VarSet -> DVarSet :=
  UniqDSet.uniqDSetIntersectUniqSet.

Definition dVarSetMinusVarSet : DVarSet -> VarSet -> DVarSet :=
  UniqDSet.uniqDSetMinusUniqSet.

Definition dVarSetToVarSet : DVarSet -> VarSet :=
  UniqSet.unsafeUFMToUniqSet GHC.Base.∘ UniqDFM.udfmToUfm.

Definition delDVarSet : DVarSet -> CoreType.Var -> DVarSet :=
  UniqDSet.delOneFromUniqDSet.

Definition delDVarSetList : DVarSet -> list CoreType.Var -> DVarSet :=
  UniqDSet.delListFromUniqDSet.

Definition delVarSet : VarSet -> CoreType.Var -> VarSet :=
  UniqSet.delOneFromUniqSet.

Definition delVarSetByKey : VarSet -> Unique.Unique -> VarSet :=
  UniqSet.delOneFromUniqSet_Directly.

Definition delVarSetList : VarSet -> list CoreType.Var -> VarSet :=
  UniqSet.delListFromUniqSet.

Definition disjointDVarSet : DVarSet -> DVarSet -> bool :=
  fun s1 s2 => UniqDFM.disjointUDFM s1 s2.

Definition intersectsDVarSet : DVarSet -> DVarSet -> bool :=
  fun s1 s2 => negb (disjointDVarSet s1 s2).

Definition disjointVarSet : VarSet -> VarSet -> bool :=
  fun s1 s2 => UniqFM.disjointUFM (UniqSet.getUniqSet s1) (UniqSet.getUniqSet s2).

Definition intersectsVarSet : VarSet -> VarSet -> bool :=
  fun s1 s2 => negb (disjointVarSet s1 s2).

Definition elemDVarSet : CoreType.Var -> DVarSet -> bool :=
  UniqDSet.elementOfUniqDSet.

Definition elemVarSet : CoreType.Var -> VarSet -> bool :=
  UniqSet.elementOfUniqSet.

Definition elemVarSetByKey : Unique.Unique -> VarSet -> bool :=
  UniqSet.elemUniqSet_Directly.

Definition emptyDVarSet : DVarSet :=
  UniqDSet.emptyUniqDSet.

Definition emptyVarSet : VarSet :=
  UniqSet.emptyUniqSet.

Definition extendDVarSet : DVarSet -> CoreType.Var -> DVarSet :=
  UniqDSet.addOneToUniqDSet.

Definition extendDVarSetList : DVarSet -> list CoreType.Var -> DVarSet :=
  UniqDSet.addListToUniqDSet.

Definition extendVarSet : VarSet -> CoreType.Var -> VarSet :=
  UniqSet.addOneToUniqSet.

Definition extendVarSetList : VarSet -> list CoreType.Var -> VarSet :=
  UniqSet.addListToUniqSet.

Definition filterDVarSet : (CoreType.Var -> bool) -> DVarSet -> DVarSet :=
  UniqDSet.filterUniqDSet.

Definition filterVarSet : (CoreType.Var -> bool) -> VarSet -> VarSet :=
  UniqSet.filterUniqSet.

Definition foldDVarSet {a} : (CoreType.Var -> a -> a) -> a -> DVarSet -> a :=
  UniqDSet.foldUniqDSet.

Definition intersectDVarSet : DVarSet -> DVarSet -> DVarSet :=
  UniqDSet.intersectUniqDSets.

Definition intersectVarSet : VarSet -> VarSet -> VarSet :=
  UniqSet.intersectUniqSets.

Definition isEmptyDVarSet : DVarSet -> bool :=
  UniqDSet.isEmptyUniqDSet.

Definition isEmptyVarSet : VarSet -> bool :=
  UniqSet.isEmptyUniqSet.

Definition lookupVarSet : VarSet -> CoreType.Var -> option CoreType.Var :=
  UniqSet.lookupUniqSet.

Definition lookupVarSetByName : VarSet -> Name.Name -> option CoreType.Var :=
  UniqSet.lookupUniqSet.

Definition lookupVarSet_Directly
   : VarSet -> Unique.Unique -> option CoreType.Var :=
  UniqSet.lookupUniqSet_Directly.

Definition mapVarSet {b} {a} `{Unique.Uniquable b}
   : (a -> b) -> UniqSet.UniqSet a -> UniqSet.UniqSet b :=
  UniqSet.mapUniqSet.

Definition minusDVarSet : DVarSet -> DVarSet -> DVarSet :=
  UniqDSet.minusUniqDSet.

Definition subDVarSet : DVarSet -> DVarSet -> bool :=
  fun s1 s2 => isEmptyDVarSet (minusDVarSet s1 s2).

Definition minusVarSet : VarSet -> VarSet -> VarSet :=
  UniqSet.minusUniqSet.

Definition subVarSet : VarSet -> VarSet -> bool :=
  fun s1 s2 => isEmptyVarSet (minusVarSet s1 s2).

Definition fixVarSet : (VarSet -> VarSet) -> VarSet -> VarSet :=
  GHC.DeferredFix.deferredFix2 (fun fixVarSet fn vars =>
                                  let new_vars := fn vars in
                                  if subVarSet new_vars vars : bool then vars else
                                  fixVarSet fn new_vars).

Definition mkDVarSet : list CoreType.Var -> DVarSet :=
  UniqDSet.mkUniqDSet.

Definition mkVarSet : list CoreType.Var -> VarSet :=
  UniqSet.mkUniqSet.

Definition partitionDVarSet
   : (CoreType.Var -> bool) -> DVarSet -> (DVarSet * DVarSet)%type :=
  UniqDSet.partitionUniqDSet.

Definition partitionVarSet
   : (CoreType.Var -> bool) -> VarSet -> (VarSet * VarSet)%type :=
  UniqSet.partitionUniqSet.

Definition seqDVarSet : DVarSet -> unit :=
  fun s => tt.

Definition seqVarSet : VarSet -> unit :=
  fun s => tt.

Definition sizeDVarSet : DVarSet -> GHC.Num.Int :=
  UniqDSet.sizeUniqDSet.

Definition sizeVarSet : VarSet -> GHC.Num.Int :=
  UniqSet.sizeUniqSet.

Definition unionDVarSet : DVarSet -> DVarSet -> DVarSet :=
  UniqDSet.unionUniqDSets.

Definition transCloDVarSet : (DVarSet -> DVarSet) -> DVarSet -> DVarSet :=
  fun fn seeds =>
    let go : DVarSet -> DVarSet -> DVarSet :=
      GHC.DeferredFix.deferredFix2 (fun go acc candidates =>
                                      let new_vs := minusDVarSet (fn candidates) acc in
                                      if isEmptyDVarSet new_vs : bool then acc else
                                      go (unionDVarSet acc new_vs) new_vs) in
    go seeds seeds.

Definition mapUnionDVarSet {a} : (a -> DVarSet) -> list a -> DVarSet :=
  fun get_set xs =>
    Data.Foldable.foldr (unionDVarSet GHC.Base.∘ get_set) emptyDVarSet xs.

Definition unionDVarSets : list DVarSet -> DVarSet :=
  UniqDSet.unionManyUniqDSets.

Definition unionVarSet : VarSet -> VarSet -> VarSet :=
  UniqSet.unionUniqSets.

Definition transCloVarSet : (VarSet -> VarSet) -> VarSet -> VarSet :=
  fun fn seeds =>
    let go : VarSet -> VarSet -> VarSet :=
      GHC.DeferredFix.deferredFix2 (fun go acc candidates =>
                                      let new_vs := minusVarSet (fn candidates) acc in
                                      if isEmptyVarSet new_vs : bool then acc else
                                      go (unionVarSet acc new_vs) new_vs) in
    go seeds seeds.

Definition mapUnionVarSet {a} : (a -> VarSet) -> list a -> VarSet :=
  fun get_set xs =>
    Data.Foldable.foldr (unionVarSet GHC.Base.∘ get_set) emptyVarSet xs.

Definition unionVarSets : list VarSet -> VarSet :=
  UniqSet.unionManyUniqSets.

Definition unitDVarSet : CoreType.Var -> DVarSet :=
  UniqDSet.unitUniqDSet.

Definition unitVarSet : CoreType.Var -> VarSet :=
  UniqSet.unitUniqSet.

(* Unbound variables:
     bool list negb op_zt__ option tt unit CoreType.CoVar CoreType.Id
     CoreType.TyCoVar CoreType.TyVar CoreType.Var Data.Foldable.foldr
     GHC.Base.op_z2218U__ GHC.DeferredFix.deferredFix2 GHC.Num.Int Name.Name
     UniqDFM.allUDFM UniqDFM.anyUDFM UniqDFM.disjointUDFM UniqDFM.udfmToUfm
     UniqDSet.UniqDSet UniqDSet.addListToUniqDSet UniqDSet.addOneToUniqDSet
     UniqDSet.delListFromUniqDSet UniqDSet.delOneFromUniqDSet
     UniqDSet.elementOfUniqDSet UniqDSet.emptyUniqDSet UniqDSet.filterUniqDSet
     UniqDSet.foldUniqDSet UniqDSet.intersectUniqDSets UniqDSet.isEmptyUniqDSet
     UniqDSet.minusUniqDSet UniqDSet.mkUniqDSet UniqDSet.partitionUniqDSet
     UniqDSet.sizeUniqDSet UniqDSet.unionManyUniqDSets UniqDSet.unionUniqDSets
     UniqDSet.uniqDSetIntersectUniqSet UniqDSet.uniqDSetMinusUniqSet
     UniqDSet.uniqDSetToList UniqDSet.unitUniqDSet UniqFM.disjointUFM UniqSet.UniqSet
     UniqSet.addListToUniqSet UniqSet.addOneToUniqSet UniqSet.delListFromUniqSet
     UniqSet.delOneFromUniqSet UniqSet.delOneFromUniqSet_Directly
     UniqSet.elemUniqSet_Directly UniqSet.elementOfUniqSet UniqSet.emptyUniqSet
     UniqSet.filterUniqSet UniqSet.getUniqSet UniqSet.intersectUniqSets
     UniqSet.isEmptyUniqSet UniqSet.lookupUniqSet UniqSet.lookupUniqSet_Directly
     UniqSet.mapUniqSet UniqSet.minusUniqSet UniqSet.mkUniqSet
     UniqSet.partitionUniqSet UniqSet.sizeUniqSet UniqSet.unionManyUniqSets
     UniqSet.unionUniqSets UniqSet.uniqSetAll UniqSet.uniqSetAny UniqSet.unitUniqSet
     UniqSet.unsafeUFMToUniqSet Unique.Uniquable Unique.Unique
*)
