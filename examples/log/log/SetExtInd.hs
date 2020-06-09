{-# LANGUAGE KindSignatures, GADTs, MultiParamTypeClasses, ExistentialQuantification #-}
module SetExtInd where

import qualified MySet

data SetMethod :: * -> * where
  Empty :: SetMethod a
  Singleton :: a -> SetMethod a
  Add :: Eq a => a -> FreerF SetMethod a -> SetMethod a
  Union :: Eq a => FreerF SetMethod a -> FreerF SetMethod a -> SetMethod a
  PowerSet :: Eq a => FreerF SetMethod a -> SetMethod (FreerF SetMethod a)

data FreerF e r = forall x. FMap (x -> r) (e x)

instance Functor (FreerF e) where
  fmap f (FMap g x) = FMap (f . g) x

type SetExt a = FreerF SetMethod a

reify_set :: Eq a => MySet.Set a -> SetExt a
reify_set s = go $ MySet.toList s
  where go :: Eq a => [a] -> SetExt a
        go []       = empty
        go (x : xs) = add x (go xs)

reflect_set :: Eq a => SetExt a -> MySet.Set a
reflect_set (FMap _ Empty) = MySet.empty
reflect_set (FMap f (Singleton a)) = MySet.singleton $ f a
reflect_set (FMap f (Add a s)) =
  MySet.add (f a) (reflect_set $ fmap f s)
reflect_set (FMap f (Union s1 s2)) =
  MySet.union (reflect_set $ fmap f s1) (reflect_set $ fmap f s2)
reflect_set (FMap f (PowerSet s)) =
  fmap (f . reify_set) $ MySet.powerSet $ reflect_set s

empty :: SetExt a
empty = FMap id Empty

singleton :: a -> SetExt a
singleton = FMap id . Singleton

add :: Eq a => a -> SetExt a -> SetExt a
add a = FMap id . Add a

union :: Eq a => SetExt a -> SetExt a -> SetExt a
union s1 =  FMap id . Union s1

powerSet :: Eq a => SetExt a -> SetExt (SetExt a)
powerSet = FMap id . PowerSet

member :: Eq a => a -> SetExt a -> Bool
member a s = MySet.member a (reflect_set s)
