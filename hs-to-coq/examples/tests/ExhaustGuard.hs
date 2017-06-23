
f :: Bool -> (Bool, Bool)
f t = (t,t)

g :: Bool -> Bool
g True  | (x,_) <- f True = x
g False = False
