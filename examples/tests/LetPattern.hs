module LetPattern where

data M a = J a | N

bad_let :: M a -> a
bad_let xs = let (_, J x) = (xs,xs) in x

bad_fun :: M a -> a
bad_fun xs = let (J x) = xs in x

good_match :: M a -> a
good_match (J x) = x
