{-# LANGUAGE OverloadedStrings #-}
module HsToCoq.ConvertHaskell.Declarations.Notations (buildInfixNotations) where

import Data.Bifunctor

import           Data.Map.Strict (Map)
import qualified Data.Map.Strict as M

import HsToCoq.Coq.Gallina
import HsToCoq.Coq.Gallina.Util

import HsToCoq.ConvertHaskell.InfixNames

--------------------------------------------------------------------------------

-- TODO: calculate op from def, instead of passing it around
buildInfixNotations :: Map Qualid Signature -> Qualid -> Qualid -> [Notation]
buildInfixNotations sigs op def = [ uncurry (InfixDefinition (qualidBase op) (Qualid def))
                                      . maybe hardCodedAssoc (first Just)
                                      $ sigFixity =<< M.lookup op sigs
                                  , NotationBinding $ NotationIdentBinding (qualidBase op) (Qualid def) ]
  where hardCodedAssoc | qualidBase op == "∘" = (Just LeftAssociativity, Level 40)
                       | otherwise            = (Nothing, Level 99)
