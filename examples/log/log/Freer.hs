{-# LANGUAGE ExistentialQuantification #-}
module Freer where

data Freer e r = Ret r | forall x. Vis (e x) (x -> Freer e r)

bind :: Freer e x -> (x -> Freer e y) -> Freer e y
bind (Ret x) f   = f x
bind (Vis e k) f = Vis e (\x -> bind (k x) f)

ret :: x -> Freer e x
ret = Ret

vis :: e x -> Freer e x
vis m = Vis m ret

instance Functor (Freer e) where
  fmap f x = bind x (ret . f)

instance Applicative (Freer e) where
  pure = ret
  fs <*> xs = bind fs (`fmap` xs)

instance Monad (Freer e) where
  xs >>= f = bind xs f
