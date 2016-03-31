module HsToCoq.Util.GHC.FastString (module FastString, fsToText) where

import FastString
import Data.Text (Text)
import qualified Data.Text as T

fsToText :: FastString -> Text
fsToText = T.pack . unpackFS

