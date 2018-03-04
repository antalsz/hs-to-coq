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

Require Core.
Require Data.Foldable.
Require GHC.Base.
Require GHC.Num.
Require GHC.Prim.
Require Name.
Require UniqDFM.
Require UniqDSet.
Require UniqFM.
Require UniqSet.
Require Unique.
Require Var.
Import GHC.Base.Notations.

(* Converted type declarations: *)

Definition VarSet :=
  (UniqSet.UniqSet Core.Var)%type.

Definition TyVarSet :=
  (UniqSet.UniqSet TyVar)%type.

Definition TyCoVarSet :=
  (UniqSet.UniqSet Var.TyCoVar)%type.

Definition IdSet :=
  (UniqSet.UniqSet Var.Id)%type.

Definition DVarSet :=
  (UniqDSet.UniqDSet Core.Var)%type.

Definition DTyVarSet :=
  (UniqDSet.UniqDSet TyVar)%type.

Definition DTyCoVarSet :=
  (UniqDSet.UniqDSet Var.TyCoVar)%type.

Definition DIdSet :=
  (UniqDSet.UniqDSet Var.Id)%type.

Definition CoVarSet :=
  (UniqSet.UniqSet CoVar)%type.
(* Converted value declarations: *)

Definition dVarSetElems : DVarSet -> list Core.Var :=
  UniqDSet.uniqDSetToList.

Definition dVarSetMinusVarSet : DVarSet -> VarSet -> DVarSet :=
  UniqDSet.uniqDSetMinusUniqSet.

Definition dVarSetToVarSet : DVarSet -> VarSet :=
  UniqDFM.udfmToUfm.

Definition delDVarSet : DVarSet -> Core.Var -> DVarSet :=
  UniqDSet.delOneFromUniqDSet.

Definition delDVarSetList : DVarSet -> list Core.Var -> DVarSet :=
  UniqDSet.delListFromUniqDSet.

Definition delVarSet : VarSet -> Core.Var -> VarSet :=
  UniqSet.delOneFromUniqSet.

Definition delVarSetByKey : VarSet -> Unique.Unique -> VarSet :=
  UniqSet.delOneFromUniqSet_Directly.

Definition delVarSetList : VarSet -> list Core.Var -> VarSet :=
  UniqSet.delListFromUniqSet.

Definition disjointDVarSet : DVarSet -> DVarSet -> bool :=
  fun s1 s2 => UniqDFM.disjointUDFM s1 s2.

Definition intersectsDVarSet : DVarSet -> DVarSet -> bool :=
  fun s1 s2 => negb (disjointDVarSet s1 s2).

Definition disjointVarSet : VarSet -> VarSet -> bool :=
  fun s1 s2 => UniqFM.disjointUFM s1 s2.

Definition intersectsVarSet : VarSet -> VarSet -> bool :=
  fun s1 s2 => negb (disjointVarSet s1 s2).

Definition elemDVarSet : Core.Var -> DVarSet -> bool :=
  UniqDSet.elementOfUniqDSet.

Definition elemVarSet : Core.Var -> VarSet -> bool :=
  UniqSet.elementOfUniqSet.

Definition elemVarSetByKey : Unique.Unique -> VarSet -> bool :=
  UniqSet.elemUniqSet_Directly.

Definition emptyDVarSet : DVarSet :=
  UniqDSet.emptyUniqDSet.

Definition emptyVarSet : VarSet :=
  UniqSet.emptyUniqSet.

Definition extendDVarSet : DVarSet -> Core.Var -> DVarSet :=
  UniqDSet.addOneToUniqDSet.

Definition extendDVarSetList : DVarSet -> list Core.Var -> DVarSet :=
  UniqDSet.addListToUniqDSet.

Definition extendVarSet : VarSet -> Core.Var -> VarSet :=
  UniqSet.addOneToUniqSet.

Definition extendVarSetList : VarSet -> list Core.Var -> VarSet :=
  UniqSet.addListToUniqSet.

Definition extendVarSet_C
   : (Core.Var -> Core.Var -> Core.Var) -> VarSet -> Core.Var -> VarSet :=
  UniqSet.addOneToUniqSet_C.

Definition filterDVarSet : (Core.Var -> bool) -> DVarSet -> DVarSet :=
  UniqDSet.filterUniqDSet.

Definition filterVarSet : (Core.Var -> bool) -> VarSet -> VarSet :=
  UniqSet.filterUniqSet.

Definition foldDVarSet {a} : (Core.Var -> a -> a) -> a -> DVarSet -> a :=
  UniqDSet.foldUniqDSet.

Definition foldVarSet {a} : (Core.Var -> a -> a) -> a -> VarSet -> a :=
  UniqSet.foldUniqSet.

Definition intersectDVarSet : DVarSet -> DVarSet -> DVarSet :=
  UniqDSet.intersectUniqDSets.

Definition intersectVarSet : VarSet -> VarSet -> VarSet :=
  UniqSet.intersectUniqSets.

Definition isEmptyDVarSet : DVarSet -> bool :=
  UniqDSet.isEmptyUniqDSet.

Definition isEmptyVarSet : VarSet -> bool :=
  UniqSet.isEmptyUniqSet.

Definition lookupVarSet : VarSet -> Core.Var -> option Core.Var :=
  UniqSet.lookupUniqSet.

Definition lookupVarSetByName : VarSet -> Name.Name -> option Core.Var :=
  UniqSet.lookupUniqSet.

Definition mapVarSet : (Core.Var -> Core.Var) -> VarSet -> VarSet :=
  UniqSet.mapUniqSet.

Definition minusDVarSet : DVarSet -> DVarSet -> DVarSet :=
  UniqDSet.minusUniqDSet.

Definition subDVarSet : DVarSet -> DVarSet -> bool :=
  fun s1 s2 => isEmptyDVarSet (minusDVarSet s1 s2).

Definition minusVarSet : VarSet -> VarSet -> VarSet :=
  UniqSet.minusUniqSet.

Definition subVarSet : VarSet -> VarSet -> bool :=
  fun s1 s2 => isEmptyVarSet (minusVarSet s1 s2).

Definition mkDVarSet : list Core.Var -> DVarSet :=
  UniqDSet.mkUniqDSet.

Definition mkVarSet : list Core.Var -> VarSet :=
  UniqSet.mkUniqSet.

Definition partitionDVarSet
   : (Core.Var -> bool) -> DVarSet -> (DVarSet * DVarSet)%type :=
  UniqDSet.partitionUniqDSet.

Definition sizeDVarSet : DVarSet -> GHC.Num.Int :=
  UniqDSet.sizeUniqDSet.

Definition seqDVarSet : DVarSet -> unit :=
  fun s => GHC.Prim.seq (sizeDVarSet s) tt.

Definition sizeVarSet : VarSet -> GHC.Num.Int :=
  UniqSet.sizeUniqSet.

Definition seqVarSet : VarSet -> unit :=
  fun s => GHC.Prim.seq (sizeVarSet s) tt.

Definition unionDVarSet : DVarSet -> DVarSet -> DVarSet :=
  UniqDSet.unionUniqDSets.

Definition mapUnionDVarSet {a} : (a -> DVarSet) -> list a -> DVarSet :=
  fun get_set xs =>
    Data.Foldable.foldr (unionDVarSet GHC.Base.∘ get_set) emptyDVarSet xs.

Definition unionDVarSets : list DVarSet -> DVarSet :=
  UniqDSet.unionManyUniqDSets.

Definition unionVarSet : VarSet -> VarSet -> VarSet :=
  UniqSet.unionUniqSets.

Definition mapUnionVarSet {a} : (a -> VarSet) -> list a -> VarSet :=
  fun get_set xs =>
    Data.Foldable.foldr (unionVarSet GHC.Base.∘ get_set) emptyVarSet xs.

Definition unionVarSets : list VarSet -> VarSet :=
  UniqSet.unionManyUniqSets.

Definition unitDVarSet : Core.Var -> DVarSet :=
  UniqDSet.unitUniqDSet.

Definition unitVarSet : Core.Var -> VarSet :=
  UniqSet.unitUniqSet.

Definition varSetElems : VarSet -> list Core.Var :=
  UniqSet.uniqSetToList.

(* Unbound variables:
     CoVar TyVar bool list negb op_zt__ option tt unit Core.Var Data.Foldable.foldr
     GHC.Base.op_z2218U__ GHC.Num.Int GHC.Prim.seq Name.Name UniqDFM.disjointUDFM
     UniqDFM.udfmToUfm UniqDSet.UniqDSet UniqDSet.addListToUniqDSet
     UniqDSet.addOneToUniqDSet UniqDSet.delListFromUniqDSet
     UniqDSet.delOneFromUniqDSet UniqDSet.elementOfUniqDSet UniqDSet.emptyUniqDSet
     UniqDSet.filterUniqDSet UniqDSet.foldUniqDSet UniqDSet.intersectUniqDSets
     UniqDSet.isEmptyUniqDSet UniqDSet.minusUniqDSet UniqDSet.mkUniqDSet
     UniqDSet.partitionUniqDSet UniqDSet.sizeUniqDSet UniqDSet.unionManyUniqDSets
     UniqDSet.unionUniqDSets UniqDSet.uniqDSetMinusUniqSet UniqDSet.uniqDSetToList
     UniqDSet.unitUniqDSet UniqFM.disjointUFM UniqSet.UniqSet
     UniqSet.addListToUniqSet UniqSet.addOneToUniqSet UniqSet.addOneToUniqSet_C
     UniqSet.delListFromUniqSet UniqSet.delOneFromUniqSet
     UniqSet.delOneFromUniqSet_Directly UniqSet.elemUniqSet_Directly
     UniqSet.elementOfUniqSet UniqSet.emptyUniqSet UniqSet.filterUniqSet
     UniqSet.foldUniqSet UniqSet.intersectUniqSets UniqSet.isEmptyUniqSet
     UniqSet.lookupUniqSet UniqSet.mapUniqSet UniqSet.minusUniqSet UniqSet.mkUniqSet
     UniqSet.sizeUniqSet UniqSet.unionManyUniqSets UniqSet.unionUniqSets
     UniqSet.uniqSetToList UniqSet.unitUniqSet Unique.Unique Var.Id Var.TyCoVar
*)
