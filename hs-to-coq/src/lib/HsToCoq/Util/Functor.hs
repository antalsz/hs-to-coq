module HsToCoq.Util.Functor ((<&>)) where

(<&>) :: Functor f => f a -> (a -> b) -> f b
(<&>) = flip (<$>)
infixl 1 <&>
