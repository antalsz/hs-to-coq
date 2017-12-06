module NestedRec where

-- Nats

data N = O | S N

-- Inlined list datatype

data List a = Nil | Cons a (List a)

-- higher order function

mapList :: (a -> b) -> List a -> List b
mapList f Nil = Nil
mapList f (Cons x xs) = Cons (f x) (mapList f xs)

goodMapList :: (a -> b) -> List a -> List b
goodMapList f = go
  where go Nil = Nil
        go (Cons x xs) = Cons (f x) (go xs)

-- Tree type

data Tree a = Node a (List (Tree a))

mx :: N -> N -> N
mx O n = n
mx n O = n
mx (S n) (S m) = S (mx n m)

maxmum :: List N -> N
maxmum (Cons x xs) = mx x (maxmum xs)
maxmum Nil         = O

height :: Tree a -> N
height (Node v ts) = S (maxmum (goodMapList height ts))

-- Nested recursion

mapTree :: (a -> b) -> Tree a -> Tree b
mapTree f (Node v ts) = Node (f v) (mapList (mapTree f) ts)
