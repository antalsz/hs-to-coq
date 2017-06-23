-- This test demonstrates the problem with recursive functions in instances

-- in the output, we don't know whether eqb is a member function or a recursive call

data A = A

class EqB a where
  eqb :: a -> a -> Bool

instance EqB A where
  eqb A A = True

instance EqB [A] where
  eqb [] []        = True
  eqb (x:xs)(y:ys) = eqb x y && eqb xs ys
  eqb _ _          = False
