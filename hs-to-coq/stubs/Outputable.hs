module Outputable where

data SDoc = SDoc

(<+>) :: SDoc -> SDoc -> SDoc
(<+>) _ _ = SDoc

char :: Char -> SDoc
char _ = SDoc


class Outputable a where
        ppr :: a -> SDoc
        pprPrec :: Rational -> a -> SDoc

        ppr = pprPrec 0
        pprPrec _ = ppr

