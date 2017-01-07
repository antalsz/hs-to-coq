module HsToCoq.ConvertHaskell.Literals (
  convertInteger, convertString, convertFastString,
  ) where

import Prelude hiding (Num)
import qualified Data.Text as T
import Control.Monad.IO.Class
import HsToCoq.Util.GHC.FastString
import HsToCoq.Coq.Gallina
import HsToCoq.ConvertHaskell.Monad

convertInteger :: MonadIO f => String -> Integer -> f Num
convertInteger what int | int >= 0  = pure $ fromInteger int
                        | otherwise = convUnsupported $ "negative " ++ what

convertFastString :: FastString -> Term
convertFastString = HsString . fsToText

convertString :: String -> Term
convertString = HsString . T.pack
