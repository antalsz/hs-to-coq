module DList
  ( empty
  , singleton
  , append
  , cons
  , toList
  )
where

data DList a = DList { fromDList :: [a] -> [a] }

empty :: DList a
empty = DList id

singleton :: a -> DList a
singleton a = DList (a:)

append :: DList a -> DList a -> DList a
append (DList a) (DList b) = DList (a . b)

cons :: a -> DList a -> DList a
cons a (DList b) = DList $ (a:) . b

toList :: DList a -> [a]
toList (DList f) = f []
