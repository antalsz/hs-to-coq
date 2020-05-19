{-# LANGUAGE KindSignatures, GADTs, MultiParamTypeClasses #-}
module SetExtInd where

import qualified MySet

data SetExt :: * -> * where
  Empty :: SetExt a
  Singleton :: a -> SetExt a
  Add :: Eq a => a -> SetExt a -> SetExt a
  Union :: Eq a => SetExt a -> SetExt a -> SetExt a
  PowerSet :: SetExt a -> SetExt (MySet.Set a)

interp_ext :: SetExt a -> MySet.Set a
interp_ext Empty = MySet.empty
interp_ext (Singleton a) = MySet.singleton a
interp_ext (Add a s) = MySet.add a $ interp_ext s
interp_ext (Union s1 s2) = MySet.union (interp_ext s1) (interp_ext s2)
interp_ext (PowerSet s) = MySet.powerSet $ interp_ext s

empty :: SetExt a
empty = Empty

singleton :: a -> SetExt a
singleton = Singleton

add :: Eq a => a -> SetExt a -> SetExt a
add = Add

union :: Eq a => SetExt a -> SetExt a -> SetExt a
union = Union

powerSet :: SetExt a -> SetExt (MySet.Set a)
powerSet = PowerSet

member :: Eq a => a -> SetExt a -> Bool
member a s = MySet.member a (interp_ext s)
