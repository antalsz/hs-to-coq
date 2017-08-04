module PatternGuard where

import Prelude hiding (take)

checkNum :: Int -> Bool
checkNum 2 = True
checkNum _ = False

-- Inline data structures, so that this test case
-- works independent of inter-module data flow
data Pair a b = Pair a b
data List a = Nil | Cons a (List a)


take :: Int -> List a -> List a
take n _      | n <= 0 =  Nil
take _ Nil             =  Nil
take n (Cons x xs)     =  Cons x (take (n-1) xs)


take2 :: Int -> List a -> List a
take2 n x = case Pair n x of
        Pair n _      | n <= 0 -> Nil
        Pair _ Nil             -> Nil
        Pair n (Cons x xs)     -> Cons x (take2 (n-1) xs)
