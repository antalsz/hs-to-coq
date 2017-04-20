module HsToCoq.Util.Function ((.:), (.*^)) where

(.:) :: (c -> d) -> (a -> b -> c) -> (a -> b -> d)
f .: g = (f .) . g
infixr 8 .:

-- Post (@^@) compose (@.@) with a pair (@*@)
(.*^) :: (a -> b' -> c) -> (b -> b') -> (a, b) -> c
(with .*^ f) (x, y) = with x $ f y
infix 9 .*^
