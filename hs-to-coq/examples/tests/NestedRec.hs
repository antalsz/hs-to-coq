module NestedRec where

-- Inlined list datatype

data List a = Nil | Cons a (List a)

-- higher order function

mapList :: (a -> b) -> List a -> List b
mapList f Nil = Nil
mapList f (Cons x xs) = Cons (f x) (mapList f xs)


-- Tree type

data Tree a = Node a (List (Tree a))

-- Nested recursion

mapTree :: (a -> b) -> Tree a -> Tree b
mapTree f (Node v ts) = Node (f v) (mapList (mapTree f) ts)
