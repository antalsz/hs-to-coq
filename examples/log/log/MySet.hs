module MySet (Set, empty, singleton, add, union, member, powerSet, toList) where

-- totally inefficient set
newtype Set a = Set [a]

instance Functor Set where
  fmap f (Set s) = Set $ fmap f s

empty :: Set a
empty = Set []

singleton :: a -> Set a
singleton a = Set [a]

add :: Eq a => a -> Set a -> Set a
add a (Set s) | member a (Set s) = Set s
              | otherwise        = Set $ a:s

union :: Eq a => Set a -> Set a -> Set a
union (Set s1) (Set s2) = Set $ s1 ++ filter (\x -> not $ member x (Set s1)) s2

member :: Eq a => a -> Set a -> Bool
member a (Set s) = any ((==) a) s

toList :: Set a -> [a]
toList (Set s) = s

-- totally faked power set
powerSet :: Set a -> Set (Set a)
powerSet s = singleton s

-- instance Eq a => Eq (Set a) where 
--   Set s1 == Set s2 = all (flip member (Set s2)) s1 && all (flip member (Set s1)) s2
