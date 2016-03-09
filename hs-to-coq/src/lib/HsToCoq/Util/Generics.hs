module HsToCoq.Util.Generics (everythingOfType, everythingOfType_) where

import Data.Maybe

import Data.Typeable
import Data.Data
import Data.Generics

everythingOfType :: (Data a, Typeable b) => proxy b -> a -> [b]
everythingOfType = const everythingOfType_

everythingOfType_ :: (Data a, Typeable b) => a -> [b]
everythingOfType_ = everything (++) $ maybeToList . cast
