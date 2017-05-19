{-# LANGUAGE TupleSections, LambdaCase, RecordWildCards,
             OverloadedLists, OverloadedStrings,
             FlexibleContexts #-}

module HsToCoq.ConvertHaskell.Literals (
  convertInteger, convertString, convertFastString, convertFractional
  ) where

import Prelude hiding (Num)
import qualified Data.Text as T
import Control.Monad.IO.Class
import HsToCoq.Util.GHC.FastString
import HsToCoq.Coq.Gallina
import HsToCoq.Coq.Gallina.Util
import HsToCoq.ConvertHaskell.Monad

import BasicTypes
import Data.Ratio (numerator, denominator)


convertInteger :: MonadIO f => String -> Integer -> f Num
convertInteger what int | int >= 0  = pure $ fromInteger int
                        | otherwise = convUnsupported $ "negative " ++ what

convertFastString :: FastString -> Term
convertFastString = HsString . fsToText

convertString :: String -> Term
convertString = HsString . T.pack

convertFractional :: MonadIO f =>  FractionalLit -> f Term
convertFractional (FL _ fl_v) = do
   let fr = Var "fromRational"
   let qn = App2 (Var "Q.Qmake") (Num (fromInteger (numerator fl_v)))
                                 (Num (fromInteger (denominator fl_v)))
   pure $ App1 fr qn