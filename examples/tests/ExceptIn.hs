module ExceptIn(Test1(..), Test2(..), test1_1, test1_2, foo, bar, baz) where

    data Test1 = A Int | B String
        deriving Show

    data Test2 = X Int | Y String
        deriving Show

    test1_1 :: Test1
    test1_1 = A 5

    test1_2 :: Test1
    test1_2 = B "hello"

    foo :: Test1 -> Test1
    foo (A n) = A (n + 1)
    foo (B str) = B $ str <> "."

    bar :: Test1 -> Test1
    bar (A n) = A (n + 2)
    bar (B str) = B $ str <> "!"

    baz :: Test1 -> Test1
    baz (A n) = A (2 * n)
    baz (B str) = B $ str <> "?"