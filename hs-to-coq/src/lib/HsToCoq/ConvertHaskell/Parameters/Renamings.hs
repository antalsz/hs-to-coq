{-# LANGUAGE RecordWildCards #-}

module HsToCoq.ConvertHaskell.Parameters.Renamings (
  Renamings ,HsNamespace(..), NamespacedIdent(..),
  buildRenamings,
  prettyNSIdent,
) where

import Data.Foldable
import Data.List
import Data.Validation
import qualified Data.Text as T

import Data.Map (Map)
import qualified Data.Map  as M

import HsToCoq.Coq.Gallina

----------------------------------------

data HsNamespace = ExprNS | TypeNS
                 deriving (Eq, Ord, Show, Read, Enum, Bounded)

data NamespacedIdent = NamespacedIdent { niNS :: !HsNamespace
                                       , niId :: !Ident }
                     deriving (Eq, Ord, Show, Read)

type Renamings = Map NamespacedIdent Ident

buildRenamings :: Foldable f => f (NamespacedIdent, Ident) -> Either String Renamings
buildRenamings rns =
  case sequenceA . M.fromListWithKey (\k _ _ -> AccFailure [k])
         $ fmap AccSuccess <$> toList rns
  of
    AccSuccess rs   -> Right rs
    AccFailure dups -> Left $ "Duplicate renamings for " ++ intercalate ", " (map prettyNSIdent dups)

prettyNSIdent :: NamespacedIdent -> String
prettyNSIdent NamespacedIdent{..} = prettyNS niNS ++ " " ++ T.unpack niId where
  prettyNS ExprNS = "value"
  prettyNS TypeNS = "type"
