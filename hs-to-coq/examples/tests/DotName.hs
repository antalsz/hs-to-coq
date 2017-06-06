-- Example from Data.Function
-- uses an infix operator as a pattern variable

-- I think the only solution is to rename to normal variable and make all uses prefix

on :: (b -> b -> c) -> (a -> b) -> a -> a -> c
(.*.) `on` f = \x y -> f x .*. f y
