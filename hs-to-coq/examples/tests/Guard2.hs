-- Pattern guards: need to fill in the case when the guard fails.

data T = K { t :: T } | E

-- Otherwise in last alt
f :: T -> Maybe T
f (K {t = rhs}) | K { t = E} <- rhs = Just E
f _ = Nothing


f2 :: T -> Maybe T
f2 (K {t = rhs}) | K { t = E} <- rhs = Just E
                 | otherwise         = Nothing
f2 E = Nothing

f3 :: (T,T) -> Maybe T
f3 (K {t = rhs}, K _) | K {t=E} <- rhs = Just E
f3 (_,_) = Nothing
