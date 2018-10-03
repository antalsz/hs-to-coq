module TalkExample where

import Prelude hiding (elem)

elem :: (Eq a) => a -> [a] -> Bool
elem _ []       = False
elem x (y:ys)   = x==y || elem x ys
