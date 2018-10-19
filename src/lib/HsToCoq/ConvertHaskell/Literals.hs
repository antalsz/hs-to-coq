{-# LANGUAGE OverloadedStrings #-}

module HsToCoq.ConvertHaskell.Literals (
  convertInteger, convertFastString, convertFractional
  ) where

import Prelude hiding (Num)
import Control.Monad.IO.Class
import HsToCoq.Util.GHC.FastString
import HsToCoq.Coq.Gallina
import HsToCoq.Coq.Gallina.Util

import BasicTypes
import Data.Ratio (numerator, denominator)

convertInteger :: String -> Integer -> Either String Num
convertInteger what int | int >= 0  = Right $ fromInteger int
                        | otherwise = Left  $ "negative " ++ what

convertFastString :: FastString -> Term
convertFastString = HsString . fsToText

convertFractional :: MonadIO f =>  FractionalLit -> f Term
convertFractional (FL _ _ fl_v) = do
   let fr = Var "fromRational"
   let qn = App2 (Var "Q.Qmake") (Num (fromInteger (numerator fl_v)))
                                 (Num (fromInteger (denominator fl_v)))
   pure $ App1 fr qn
