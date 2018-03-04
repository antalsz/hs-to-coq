(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Coq.Program.Tactics.
Require Coq.Program.Wf.

(* Converted imports: *)

Require Data.Foldable.
Require GHC.Num.
Require UniqFM.
Require Unique.

(* Converted type declarations: *)

Definition UniqSet :=
  UniqFM.UniqFM%type.
(* Converted value declarations: *)

Definition addOneToUniqSet {a} `{Unique.Uniquable a}
   : UniqSet a -> a -> UniqSet a :=
  fun set x => UniqFM.addToUFM set x x.

Definition addListToUniqSet {a} `{Unique.Uniquable a}
   : UniqSet a -> list a -> UniqSet a :=
  Data.Foldable.foldl addOneToUniqSet.

Definition addOneToUniqSet_C {a} `{Unique.Uniquable a}
   : (a -> a -> a) -> UniqSet a -> a -> UniqSet a :=
  fun f set x => UniqFM.addToUFM_C f set x x.

Definition delListFromUniqSet {a} `{Unique.Uniquable a}
   : UniqSet a -> list a -> UniqSet a :=
  UniqFM.delListFromUFM.

Definition delOneFromUniqSet {a} `{Unique.Uniquable a}
   : UniqSet a -> a -> UniqSet a :=
  UniqFM.delFromUFM.

Definition delOneFromUniqSet_Directly {a}
   : UniqSet a -> Unique.Unique -> UniqSet a :=
  UniqFM.delFromUFM_Directly.

Definition elemUniqSet_Directly {a} : Unique.Unique -> UniqSet a -> bool :=
  UniqFM.elemUFM_Directly.

Definition elementOfUniqSet {a} `{Unique.Uniquable a}
   : a -> UniqSet a -> bool :=
  UniqFM.elemUFM.

Definition emptyUniqSet {a} : UniqSet a :=
  UniqFM.emptyUFM.

Definition mkUniqSet {a} `{Unique.Uniquable a} : list a -> UniqSet a :=
  Data.Foldable.foldl addOneToUniqSet emptyUniqSet.

Definition filterUniqSet {a} : (a -> bool) -> UniqSet a -> UniqSet a :=
  UniqFM.filterUFM.

Definition foldUniqSet {a} {b} : (a -> b -> b) -> b -> UniqSet a -> b :=
  UniqFM.foldUFM.

Definition intersectUniqSets {a} : UniqSet a -> UniqSet a -> UniqSet a :=
  UniqFM.intersectUFM.

Definition isEmptyUniqSet {a} : UniqSet a -> bool :=
  UniqFM.isNullUFM.

Definition lookupUniqSet {a} {b} `{Unique.Uniquable a}
   : UniqSet b -> a -> option b :=
  UniqFM.lookupUFM.

Definition mapUniqSet {a} {b} : (a -> b) -> UniqSet a -> UniqSet b :=
  UniqFM.mapUFM.

Definition minusUniqSet {a} : UniqSet a -> UniqSet a -> UniqSet a :=
  UniqFM.minusUFM.

Definition sizeUniqSet {a} : UniqSet a -> GHC.Num.Int :=
  UniqFM.sizeUFM.

Definition unionUniqSets {a} : UniqSet a -> UniqSet a -> UniqSet a :=
  UniqFM.plusUFM.

Definition unionManyUniqSets {a} (xs : list (UniqSet a)) : UniqSet a :=
  match xs with
  | nil => emptyUniqSet
  | cons set sets => Data.Foldable.foldr unionUniqSets set sets
  end.

Definition uniqSetToList {a} : UniqSet a -> list a :=
  UniqFM.eltsUFM.

Definition unitUniqSet {a} `{Unique.Uniquable a} : a -> UniqSet a :=
  fun x => UniqFM.unitUFM x x.

(* Unbound variables:
     bool cons list option Data.Foldable.foldl Data.Foldable.foldr GHC.Num.Int
     UniqFM.UniqFM UniqFM.addToUFM UniqFM.addToUFM_C UniqFM.delFromUFM
     UniqFM.delFromUFM_Directly UniqFM.delListFromUFM UniqFM.elemUFM
     UniqFM.elemUFM_Directly UniqFM.eltsUFM UniqFM.emptyUFM UniqFM.filterUFM
     UniqFM.foldUFM UniqFM.intersectUFM UniqFM.isNullUFM UniqFM.lookupUFM
     UniqFM.mapUFM UniqFM.minusUFM UniqFM.plusUFM UniqFM.sizeUFM UniqFM.unitUFM
     Unique.Uniquable Unique.Unique
*)
