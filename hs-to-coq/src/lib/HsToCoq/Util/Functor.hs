module HsToCoq.Util.Functor ((<&>), passThrough, (.<$)) where

(<&>) :: Functor f => f a -> (a -> b) -> f b
(<&>) = flip (<$>)
infixl 1 <&>
{-# INLINABLE (<&>) #-}

passThrough :: Functor f => (a -> f b) -> (a -> f a)
passThrough f = \x -> x <$ f x
{-# INLINABLE passThrough #-}

(.<$) :: Functor f => (f a -> c) -> (a -> f b) -> a -> c
f .<$ g = f . passThrough g
infixr 9 .<$
{-# INLINABLE (.<$) #-}
