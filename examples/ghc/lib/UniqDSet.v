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
Require UniqDFM.
Require UniqSet.
Require Unique.

(* Converted type declarations: *)

Definition UniqDSet :=
  UniqDFM.UniqDFM%type.

(* Converted value declarations: *)

Definition unitUniqDSet {a} `{Unique.Uniquable a} : a -> UniqDSet a :=
  fun x => UniqDFM.unitUDFM x x.

Definition uniqDSetToList {a} : UniqDSet a -> list a :=
  UniqDFM.eltsUDFM.

Definition uniqDSetMinusUniqSet {a} {b}
   : UniqDSet a -> UniqSet.UniqSet b -> UniqDSet a :=
  fun xs ys => UniqDFM.udfmMinusUFM xs (UniqSet.getUniqSet ys).

Definition uniqDSetIntersectUniqSet {a} {b}
   : UniqDSet a -> UniqSet.UniqSet b -> UniqDSet a :=
  fun xs ys => UniqDFM.udfmIntersectUFM xs (UniqSet.getUniqSet ys).

Definition unionUniqDSets {a} : UniqDSet a -> UniqDSet a -> UniqDSet a :=
  UniqDFM.plusUDFM.

Definition sizeUniqDSet {a} : UniqDSet a -> nat :=
  UniqDFM.sizeUDFM.

Definition partitionUniqDSet {a}
   : (a -> bool) -> UniqDSet a -> (UniqDSet a * UniqDSet a)%type :=
  UniqDFM.partitionUDFM.

Definition minusUniqDSet {a} : UniqDSet a -> UniqDSet a -> UniqDSet a :=
  UniqDFM.minusUDFM.

Definition lookupUniqDSet {a} `{Unique.Uniquable a}
   : UniqDSet a -> a -> option a :=
  UniqDFM.lookupUDFM.

Definition isEmptyUniqDSet {a} : UniqDSet a -> bool :=
  UniqDFM.isNullUDFM.

Definition intersectsUniqDSets {a} : UniqDSet a -> UniqDSet a -> bool :=
  UniqDFM.intersectsUDFM.

Definition intersectUniqDSets {a} : UniqDSet a -> UniqDSet a -> UniqDSet a :=
  UniqDFM.intersectUDFM.

Definition foldUniqDSet {a} {b} : (a -> b -> b) -> b -> UniqDSet a -> b :=
  UniqDFM.foldUDFM.

Definition filterUniqDSet {a} : (a -> bool) -> UniqDSet a -> UniqDSet a :=
  UniqDFM.filterUDFM.

Definition emptyUniqDSet {a} : UniqDSet a :=
  UniqDFM.emptyUDFM.

Definition unionManyUniqDSets {a} (xs : list (UniqDSet a)) : UniqDSet a :=
  match xs with
  | nil => emptyUniqDSet
  | cons set sets => Data.Foldable.foldr unionUniqDSets set sets
  end.

Definition elementOfUniqDSet {a} `{Unique.Uniquable a}
   : a -> UniqDSet a -> bool :=
  UniqDFM.elemUDFM.

Definition delOneFromUniqDSet {a} `{Unique.Uniquable a}
   : UniqDSet a -> a -> UniqDSet a :=
  UniqDFM.delFromUDFM.

Definition delListFromUniqDSet {a} `{Unique.Uniquable a}
   : UniqDSet a -> list a -> UniqDSet a :=
  UniqDFM.delListFromUDFM.

Definition addOneToUniqDSet {a} `{Unique.Uniquable a}
   : UniqDSet a -> a -> UniqDSet a :=
  fun set x => UniqDFM.addToUDFM set x x.

Definition mkUniqDSet {a} `{Unique.Uniquable a} : list a -> UniqDSet a :=
  Data.Foldable.foldl addOneToUniqDSet emptyUniqDSet.

Definition addListToUniqDSet {a} `{Unique.Uniquable a}
   : UniqDSet a -> list a -> UniqDSet a :=
  Data.Foldable.foldl addOneToUniqDSet.

(* External variables:
     bool cons list nat op_zt__ option Data.Foldable.foldl Data.Foldable.foldr
     UniqDFM.UniqDFM UniqDFM.addToUDFM UniqDFM.delFromUDFM UniqDFM.delListFromUDFM
     UniqDFM.elemUDFM UniqDFM.eltsUDFM UniqDFM.emptyUDFM UniqDFM.filterUDFM
     UniqDFM.foldUDFM UniqDFM.intersectUDFM UniqDFM.intersectsUDFM UniqDFM.isNullUDFM
     UniqDFM.lookupUDFM UniqDFM.minusUDFM UniqDFM.partitionUDFM UniqDFM.plusUDFM
     UniqDFM.sizeUDFM UniqDFM.udfmIntersectUFM UniqDFM.udfmMinusUFM UniqDFM.unitUDFM
     UniqSet.UniqSet UniqSet.getUniqSet Unique.Uniquable
*)
