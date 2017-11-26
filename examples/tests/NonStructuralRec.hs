module NonStructuralRec where

-- Nats

data N = N | S N

mx :: N -> N -> N
mx N n = n
mx n N = n
mx (S n) (S m) = S (mx n m)

addN :: N -> N -> N
addN N m     = m
addN (S n) m = S (addN n m)

-- Inlined list datatype

data List a = Nil | Cons a (List a)

-- Tree type

data Tree a = Node a (List (Tree a))

-- Size minus one, to avoid proving that the size is always positive
size :: Tree a -> N
size (Node v ts) = go ts
  where go Nil = N
        go (Cons t ts) = addN (S (size t)) (go ts)

-- Nonstructurual recursion

mapTree2 :: (a -> b) -> Tree a -> Tree b
mapTree2 f (Node v Nil) = Node (f v) Nil
mapTree2 f (Node v (Cons t ts)) = case mapTree2 f (Node v ts) of
    Node v' ts' -> Node v' (Cons (mapTree2 f t) ts')
