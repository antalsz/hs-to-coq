module DList
  ( empty
  , singleton
  , append
  , cons
  , toList
  )
where

newtype DList a = DList { fromDList :: [a] -> [a] }

toList :: DList a -> [a]
toList (DList f) = f []

empty :: DList a
empty = DList id

singleton :: a -> DList a
singleton a = DList (a:)

cons :: a -> DList a -> DList a
cons a (DList b) = DList $ (a:) . b

append :: DList a -> DList a -> DList a
append (DList a) (DList b) = DList (a . b)
