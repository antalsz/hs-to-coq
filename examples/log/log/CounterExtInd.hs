{-# LANGUAGE KindSignatures, GADTs #-}
module CounterExtInd where

import qualified Counter
import Freer

data CounterMethods :: * -> * where
  Inc :: CounterMethods ()

type CounterExt = Freer CounterMethods

inc :: CounterExt ()
inc = Vis Inc Ret

interp_ext :: CounterExt a -> Counter.Counter a
interp_ext (Ret a) = return a
interp_ext (Vis Inc k) = do
  Counter.inc ;
  interp_ext $ k ()
