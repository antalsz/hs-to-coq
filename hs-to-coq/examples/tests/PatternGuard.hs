module PatternGuard where

import Prelude hiding (take)

checkNum :: Int -> Bool
checkNum 2 = True
checkNum _ = False

-- Inline data structures, so that this test case
-- works independent of inter-module data flow
data Pair a b = Pair a b
data List a = Nil | Cons a (List a)


-- Reverse order of arguments to make the termination checker happy
take :: List a -> Int -> List a
take _ n      | n <= 0 =  Nil
take Nil _             =  Nil
take (Cons x xs) n     =  Cons x (take xs (n-1))


take2 :: List a -> Int -> List a
take2 x n = case Pair n x of
        Pair n _      | n <= 0 -> Nil
        Pair _ Nil             -> Nil
        Pair n (Cons x xs)     -> Cons x (take2 xs (n-1))
