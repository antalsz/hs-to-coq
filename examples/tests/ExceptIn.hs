module ExceptIn(Test1(..), Test2(..), test1_1, test1_2, foo, bar, baz) where

data I = I1 | I2
data S = S1 | S2

data Test1 = A I | B S

data Test2 = X I | Y S

test1_1 :: Test1
test1_1 = A I1

test1_2 :: Test1
test1_2 = B S1

foo :: Test1 -> Test1
foo (A I1) = A I2
foo (A I2) = A I1
foo (B S1) = B S2
foo (B S2) = B S1

bar :: Test1 -> Test1
bar (A I1) = A I2
bar (A I2) = A I1
bar (B S1) = B S2
bar (B S2) = B S1

baz :: Test1 -> Test1
baz (A _) = A I2
baz (B _) = B S2
