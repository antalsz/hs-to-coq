module Text.PrettyPrint.Util (maybeEmpty, pprListWith, pprAnnotated, yesNo) where

import Outputable
      
maybeEmpty :: SDoc -> (SDoc -> SDoc) -> SDoc -> SDoc
maybeEmpty whenEmpty whenNonempty doc = sdocWithDynFlags $ \df ->
  if isEmpty df doc
  then whenEmpty
  else whenNonempty doc

pprListWith :: (a -> SDoc) -> [a] -> SDoc
pprListWith f = brackets . pprWithCommas f

pprAnnotated :: Outputable a => SDoc -> (a, Bool) -> SDoc
pprAnnotated annot (obj, cond) = ppr obj <> if cond
                                            then space <> annot
                                            else empty

yesNo :: Bool -> SDoc
yesNo True  = text "Yes"
yesNo False = text "No"
