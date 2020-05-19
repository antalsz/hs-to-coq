{-# LANGUAGE KindSignatures, GADTs #-}
module LogExtInd where

import qualified Log
import Freer

data LogMethods :: * -> * where
  Out :: Char -> LogMethods ()

type OutputExt = Freer LogMethods

out :: Char -> OutputExt ()
out c = Vis (Out c) Ret 

interp_ext :: OutputExt a -> Log.Output a
interp_ext (Ret a) = return a
interp_ext (Vis (Out c) k) = do
  Log.out c;
  interp_ext $ k ()

collect :: OutputExt () -> String
collect o = Log.collect (interp_ext o)
