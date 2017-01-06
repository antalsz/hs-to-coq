module HsToCoq.Util.Function ((.*^)) where

-- Post (@^@) compose (@.@) with a pair (@*@)
(.*^) :: (a -> b' -> c) -> (b -> b') -> (a, b) -> c
(with .*^ f) (x, y) = with x $ f y
infix 9 .*^
