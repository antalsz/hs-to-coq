Require Data.IntSet.Internal.
Require Import Data.Map.Internal.
Require Import GHC.Num.

Definition IntMap := Map Word.

Section IntMap.

  Context {A B C: Type}.
  
  Definition empty : IntMap A := empty.

  Definition singleton : Word -> A -> IntMap A := singleton.

  Definition null : IntMap A -> bool := null.

  Definition keys : IntMap A -> list Word := keys.

  Definition keysSet (m : IntMap A) : Data.IntSet.Internal.IntSet :=
    Data.IntSet.Internal.fromList (keys m).

  Definition elems : IntMap A -> list A := elems.

  Definition member : Word -> IntMap A -> bool := member.

  Definition size : IntMap A -> nat := map_size.

  Definition insert : Word -> A -> IntMap A -> IntMap A := insert.

  Definition insertWith : (A -> A -> A) -> Word -> A -> IntMap A -> IntMap A :=
    insertWith.

  Definition delete : Word -> IntMap A -> IntMap A := delete.

  Definition alter : (option A -> option A) -> Word -> IntMap A -> IntMap A :=
    alter.

  Definition adjust : (A -> A) -> Word -> IntMap A -> IntMap A := adjust.

  Definition map : (A -> B) -> IntMap A -> IntMap B := map.

  Definition mapWithKey : (Word -> A -> B) -> IntMap A -> IntMap B := mapWithKey.

  Definition mergeWithKey : (Word -> A -> B -> option C) ->
                            (IntMap A -> IntMap C) ->
                            (IntMap B -> IntMap C) ->
                            IntMap A -> IntMap B -> IntMap C :=
    mergeWithKey.

  Definition filter : (A -> bool) -> IntMap A -> IntMap A := filter.

  Definition filterWithKey : (Word -> A -> bool) -> IntMap A -> IntMap A :=
    filterWithKey.

  Definition union : IntMap A -> IntMap A -> IntMap A := union.

  Definition unionWith : (A -> A -> A) -> IntMap A -> IntMap A -> IntMap A :=
    unionWith.

  Definition intersection : IntMap A -> IntMap B -> IntMap A := intersection.
  
  Definition intersectionWith : (A -> B -> C) -> IntMap A -> IntMap B -> IntMap C :=
    intersectionWith.

  Definition difference : IntMap A -> IntMap B -> IntMap A := difference.

  Definition partition : (A -> bool) -> IntMap A -> IntMap A * IntMap A :=
    partition.

  Definition toList : IntMap A -> list (Word * A) := toList.

  Definition foldr : (A -> B -> B) -> B -> IntMap A -> B := foldr.

  Definition foldrWithKey : (Word -> A -> B -> B) -> B -> IntMap A -> B := foldrWithKey.

  Definition findWithDefault : A -> Word -> IntMap A -> A := findWithDefault.

  Definition lookup : Word -> IntMap A -> option A := lookup.

End IntMap.
