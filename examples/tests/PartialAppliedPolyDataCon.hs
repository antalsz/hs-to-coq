module PartialAppliedPolyDataCon where

-- See https://github.com/antalsz/hs-to-coq/issues/7

data Foo a = Foo a

myid :: a -> a
myid x = x

bar :: a -> Foo a
bar = myid Foo
