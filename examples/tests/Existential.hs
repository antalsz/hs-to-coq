{-# LANGUAGE ExistentialQuantification #-}

module Existential where

data Step s a = Yield a s | Done

-- https://github.com/antalsz/hs-to-coq/issues/12
data Stream a = forall s. Stream (s -> Step s a) s

eq :: Eq a => Stream a -> [a] -> Bool
eq (Stream next1 s1) xs = loop (next1 s1) xs
    where
      loop Done []   = True
      loop Done _    = False
      loop _    []   = False
      loop (Yield x1 s1') (x:xs) = x1 == x && loop (next1 s1') xs

