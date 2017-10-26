module NonStructuralRec where

-- Nats

data N = N | S N

mx :: N -> N -> N
mx N n = n
mx n N = n
mx (S n) (S m) = S (mx n m)

addd :: N -> N -> N
addd N m     = m
addd (S n) m = S (addd n m)

sm :: List N -> N
sm (Cons x xs) = addd x (sm xs)
sm Nil         = N

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

-- Size minus one, to avoid proving that the size is always positive
size :: Tree a -> N
size (Node v ts) = sm (goodMapList S (goodMapList size ts))

-- Nonstructurual recursion

mapTree2 :: (a -> b) -> Tree a -> Tree b
mapTree2 f (Node v Nil) = Node (f v) Nil
mapTree2 f (Node v (Cons t ts)) = case mapTree2 f (Node v ts) of
    Node v' ts' -> Node v' (Cons (mapTree2 f t) ts')
