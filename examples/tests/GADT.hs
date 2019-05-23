{-# LANGUAGE GADTs          #-}
{-# LANGUAGE KindSignatures #-}

module GADT where

data O
data C

data MaybeO ex t where
  JustO    :: t -> MaybeO O t
  NothingO ::      MaybeO C t

data Foo a :: * -> * where
  Bar :: O -> Foo a O
  Baz :: a -> Foo a C

foo :: Foo Bool a -> Bool
foo (Bar _) = True
foo (Baz b) = b
