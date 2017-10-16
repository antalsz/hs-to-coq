Require Import GHC.Base.
Require Import Data.IntMap.Base.

Definition foldWithKey {a}{b} : (Int -> a -> b -> b) -> b -> IntMap a -> b
  := Data.IntMap.Base.foldWithKey.

Definition fold {a}{b} : (a -> b -> b) -> b -> IntMap a -> b
  := Data.IntMap.Base.fold.
