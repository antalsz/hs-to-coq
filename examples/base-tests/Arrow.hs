module Arrow where

class Arr a where
    -- | Lift a function to an arrow.
    arr :: (b -> c) -> a b c

    -- | Send the first component of the input through the argument
    --   arrow, and copy the rest unchanged to the output.
    first :: a b c -> a (b,d) (c,d)


instance Arr (->) where
    arr f = f
    first f (x,y) = (f x, y)

f :: (Bool, Bool) -> (Bool,Bool)
f x = first (\x -> x) x
