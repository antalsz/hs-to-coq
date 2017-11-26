module HsToCoq.Util.Char (isHSpace, isVSpace, isOpen, isClose) where

import Data.Char

isHSpace :: Char -> Bool
isHSpace '\t' = True
isHSpace c    = generalCategory c == Space

isVSpace :: Char -> Bool
isVSpace '\n'   = True
isVSpace '\v'   = True
isVSpace '\f'   = True
isVSpace '\r'   = True
isVSpace '\x85' = True -- NEL
isVSpace c      = case generalCategory c of
                    LineSeparator      -> True
                    ParagraphSeparator -> True
                    _                  -> False

isOpen :: Char -> Bool
isOpen c = generalCategory c == OpenPunctuation

isClose :: Char -> Bool
isClose c = generalCategory c == ClosePunctuation
