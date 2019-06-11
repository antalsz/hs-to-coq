{-# LANGUAGE OverloadedStrings #-}
module HsToCoq.ConvertHaskell.Declarations.Notations
    ( buildInfixNotations
    , qualifyNotation
    ) where

import Data.Bifunctor

import           Data.Map.Strict (Map)
import qualified Data.Map.Strict as M
import qualified Data.Text as T
import HsToCoq.Util.GHC.Module

import HsToCoq.Coq.Gallina
import HsToCoq.Coq.Gallina.Util

import HsToCoq.ConvertHaskell.InfixNames

--------------------------------------------------------------------------------

-- Doesn't use 'lookupSig' because the extra signature information is just
-- /type/ signature information, not fixity information.
buildInfixNotations :: Map Qualid Signature -> Qualid -> [Notation]
buildInfixNotations sigs def
    | Just op <- identToOp (qualidBase def)
    = -- Order matters: We want Coq to prefer the infix form
      [ NotationBinding $ NotationIdentBinding (infixToPrefix op) (RawQualid def)
      , uncurry (InfixDefinition op (Qualid def))
        . maybe (hardCodedAssoc op) (first Just)
        $ sigFixity =<< M.lookup def sigs
      ]
    | otherwise = []
  where
    hardCodedAssoc op | op == "∘"  = (Just LeftAssociativity, Level 40)
                      | op == "<>" = (Nothing, Level 70)
                      | otherwise  = (Nothing, Level 99)

qualifyNotation :: ModuleName -> Notation -> Maybe Notation
qualifyNotation mod (InfixDefinition inf def assoc lvl )
    = let inf' = moduleNameText mod <> "." <> inf
      in Just $ InfixDefinition inf' def assoc lvl
qualifyNotation mod (NotationBinding (NotationIdentBinding prefix def))
    | "_" `T.isPrefixOf` prefix
    = let prefix' = "_" <> moduleNameText mod <> "." <> T.drop 1 prefix
      in Just $ NotationBinding $ NotationIdentBinding prefix' def
qualifyNotation _ _ = Nothing

