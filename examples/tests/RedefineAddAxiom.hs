module RedefineAddAxiom where

-- TODO this test could probably be more comprehensive

data Fix f a = Fix (f (Fix f a))

data Facts a = Truth a a

unroll :: Fix f a -> f (Fix f a)
unroll (Fix rolled) = rolled

roll :: f (Fix f a) -> Fix f a
roll = Fix

fine :: a -> Facts a
fine x = Truth x x
