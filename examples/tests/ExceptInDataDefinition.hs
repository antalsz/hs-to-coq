module ExceptInDataDefinition(Test1(..), Test2(..), test1_1, test1_2) where

data I = I
data S = S

data Test1 = A I | B S

data Test2 = X I | Y S

test1_1 :: Test1
test1_1 = A I

test1_2 :: Test1
test1_2 = B S
