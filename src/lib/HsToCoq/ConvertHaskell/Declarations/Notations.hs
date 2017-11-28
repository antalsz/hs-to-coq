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
buildInfixNotations :: Map Qualid Signature -> Qualid -> [Notation]
buildInfixNotations sigs def
    | Just op <- identToOp (qualidBase def)
    = [ uncurry (InfixDefinition op (Qualid def))
      . maybe (hardCodedAssoc op) (first Just)
      $ sigFixity =<< M.lookup def sigs
      , NotationBinding $ NotationIdentBinding (infixToPrefix op) (Qualid def) ]
    | otherwise = []
  where
    hardCodedAssoc op | op == "∘" = (Just LeftAssociativity, Level 40)
                      | otherwise = (Nothing, Level 99)

