{- |
Description : Successor Functor
Copyright   : © Joachim Breitner, 2017
License     : MIT
Maintainer  : mail@joachim-breitner.de

A value of type @'Succs' a@ represents a step in a graph with nodes of type @a@, or in other words, a node plus the list of its successors.

The 'Applicative' instance for @'Succs' a@ is such that the node represented by @a '<*>' b@ is the application of the node of @a@ applied to the node of @b@, and (more importantly) the successors modeled by @a '<*>' b@ are the node of @a@ applied to the succesors of @b@ in addition to the succesors of @a@ applied to the node of @b@. This way, at most one step is taken.

>>> (++) <$> Succs "0" ["1","2"] <*> Succs "A" ["B","C"]
Succs "0A" ["1A","2A","0B", "0C"]

>>> skip x = Succs [x] [[]]
>>> getSuccs $ (concat <$> traverse skip "Hello")
["ello","Hllo","Helo","Helo","Hell"]

This applicative functor can be useful to define shrink functions for QuickCheck, using the helper

> shrinkSuccs x = Succs x (shrink x)

as explained in a <http://stackoverflow.com/a/41944525/946226 StackExchange answer.>

-}
module Control.Applicative.Successors where

data Succs a = Succs a [a] deriving (Show, Eq)

instance Functor Succs where
    fmap f (Succs o s) = Succs (f o) (map f s)

instance Applicative Succs where
    pure x = Succs x []
    Succs f fs <*> Succs x xs = Succs (f x) (map ($x) fs ++ map f xs)


instance Monad Succs where
    Succs x xs >>= f = Succs y (map (getCurrent . f) xs ++ ys)
      where Succs y ys = f x

-- | Returns the represented node
--
-- Properties:
--
-- prop> getCurrent (pure x)  == x
-- prop> getCurrent (f <*> x) == (getCurrent f) (getCurrent x)
-- prop> getCurrent (x >>= k) == getCurrent (k (getCurrent x))
getCurrent :: Succs t -> t
getCurrent (Succs x _) = x

-- | Returns the represented successors
--
-- prop> getSuccs (pure x)  == []
-- prop> getSuccs (f <*> x) == map ($ getCurrent x) (getSuccs f) ++ map (getCurrent f) (getSuccs x)
-- prop> getSuccs (x >>= k) == map (getCurrent . k) (getSuccs x) ++ getSuccs k (getCurrent x)
getSuccs :: Succs t -> [t]
getSuccs (Succs _ xs) = xs

{-

The Applicative laws:

  pure id <*> Succs x xs
= Succs id [] <*> Succs x xs
= Succs (id x) (map ($x) [] ++ map id xs)
= Succs x xs

  pure (.) <*> Succs u us <*> Succs v vs <*> Succs w ws
= Succs (.) [] <*> Succs u us <*> Succs v vs <*> Succs w ws
= Succs (u .) (map (.) us) <*> Succs v vs <*> Succs w ws
= Succs (u . v) (map ($v) (map (.) us) ++ map (u .) vs) <*> Succs w ws
= Succs (u . v) (map (($v).(.)) us ++ map (u .) vs) <*> Succs w ws
= Succs ((u . v) w) (map ($w) (map (($v).(.)) us ++ map (u .) vs) ++ map (u.v) ws)
= Succs ((u . v) w) (map (($w).($v).(.)) us ++ map (($w).(u.)) vs ++ map (u.v) ws)
= Succs (u (v w)) (map (\u -> u (v w)) us ++ map (\v -> u (v w)) vs ++ map (\w -> u (v w)) ws)
= Succs (u (v w)) (map ($(v w)) us ++ map u (map ($w) vs ++ map v ws))
= Succs u us <*> Succs (v w) (map ($w) vs ++ map v ws)
= Succs u us <*> (Succs v vs <*> Succs w ws)

  pure f <*> pure x
= Succs f [] <*> Succs x []
= Succs (f x) []
= pure (f x)

  Succs u us <*> pure y
= Succs u us <*> Succs y []
= Succs (u y) (map ($y) us)
= Succs (($y) u) (map ($y) us)
= Succs ($y) [] <*> Succs u us
= pure ($ y) <*> u

The Monad laws:
  return a >>= k
= Succs a [] >>= k
= let Succs y ys = k a in Succs y (map (getCurrent . k) [] ++ ys)
= let Succs y ys = k a in Succs y ys
= k a

  Succs x xs >>= return
= let Succs y ys = return x in Succs y (map (getCurrent . return) xs ++ ys)
= let Succs y ys = Succs x [] in Succs y (map (getCurrent . return) xs ++ ys)
= Succs x (map (getCurrent . return) xs ++ [])
= Succs x xs

Lemma: getCurrent (s >>= k) = getCurrent (k (getCurrent s))
Proof:
  getCurrent (Succs x xs >>= k)
= getCurrent (let Succs y ys = k x in Succs y …)
= let Succs y ys = k x in y
= getCurrent (k x)
= getCurrent (k (getCurrent (Succs x xs)))

  Succs x xs >>= (\x -> k x >>= h)
= let Succs z zs = (\x -> k x >>= h) x in Succs z (map (getCurrent . (\x -> k x >>= h)) xs ++ zs)
= let Succs z zs = k x >>= h in Succs z (map (getCurrent . (\x -> k x >>= h)) xs ++ zs)
= let Succs z zs = k x >>= h in Succs z (map (getCurrent . (\x -> k x >>= h)) xs ++ zs)
= let Succs z zs = k x >>= h in Succs z (map (getCurrent . (\x -> k x >>= h)) xs ++ zs)
= let Succs z zs = (let Succs y ys = k x in Succs y ys >>= h) in Succs z (map (getCurrent . (\x -> k x >>= h)) xs ++ zs)
= let Succs z zs = (let Succs y ys = k x in let Succs z zs = h y in Succs z (map (getCurrent . h) ys ++ zs)) in Succs z (map (getCurrent . (\x -> k x >>= h)) xs ++ zs)
= let Succs y ys = k x in let Succs z zs = h y in let Succs z zs = Succs z (map (getCurrent . h) ys ++ zs) in Succs z (map (getCurrent . (\x -> k x >>= h)) xs ++ zs)
= let Succs y ys = k x in let Succs z zs = h y in Succs z (map (getCurrent . (\x -> k x >>= h)) xs ++ map (getCurrent . h) ys ++ zs)
= let Succs y ys = k x in let Succs z zs = h y in Succs z (map (\x -> getCurrent (k x >>= h)) xs ++ map (getCurrent . h) ys ++ zs)
= let Succs y ys = k x in let Succs z zs = h y in Succs z (map (\x -> getCurrent (h (getCurrent (k x)))) xs ++ map (getCurrent . h) ys ++ zs)
= let Succs y ys = k x in let Succs z zs = h y in Succs z (map (getCurrent . h . getCurrent . k) xs ++ map (getCurrent . h) ys ++ zs)
= let Succs y ys = k x in let Succs z zs = h y in Succs z (map (getCurrent . h) (map (getCurrent . k) xs ++ ys) ++ zs)
= let Succs y ys = k x in Succs y (map (getCurrent . k) xs ++ ys) >>= h
= (let Succs y ys = k x in Succs y (map (getCurrent . k) xs ++ ys)) >>= h
= (Succs x xs >>= k) >>= h

Lemma: (<*>) = ap
Proof:
  Succs f fs <*> Succs x xs
= Succs (f x) (map ($x) fs ++ map f xs)
= let Succs y ys = Succs (f x) (map f xs) in Succs y (map ($x) fs ++ ys)
= let Succs y ys = Succs (f x) (map (\x -> f x) xs) in Succs y (map ($x) fs ++ ys)
= let Succs y ys = Succs (f x) (map (getCurrent . (\x -> pure (f x)) xs)) in Succs y (map ($x) fs ++ ys)
= let Succs y ys = let Succs z zs = pure (f x) in Succs z (map (getCurrent . (\x -> pure (f x)) xs ++ zs)) in Succs y (map ($x) fs ++ ys)
= let Succs y ys = Succs x xs >>= \x -> pure (f x) in Succs y (map ($x) fs ++ ys)
= let Succs y ys = Succs x xs >>= \x -> pure (f x) in Succs y (map (\f -> getCurrent ((\x -> pure (f x)) (getCurrent (Succs x xs)))) fs ++ ys)
= let Succs y ys = Succs x xs >>= \x -> pure (f x) in Succs y (map (\f -> getCurrent (Succs x xs >>= (\x -> pure (f x)))) fs ++ ys)
= let Succs y ys = Succs x xs >>= \x -> pure (f x) in Succs y (map (getCurrent . (\f -> Succs x xs >>= (\x -> pure (f x)))) fs ++ ys)
= Succs f fs >>= (\f -> Succs x xs >>= (\x -> pure (f x)))
= Succs f fs `ap` Succs x xs

-}
