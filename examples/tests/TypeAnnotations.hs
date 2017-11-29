module TypeAnnotations where

comp :: (b -> c) -> (a -> b) -> a -> c
comp f g x = f (g x)

id2 :: (a -> a) -> (a -> a) -> a -> a
id2 = comp :: (a -> a) -> (a -> a) -> a -> a
