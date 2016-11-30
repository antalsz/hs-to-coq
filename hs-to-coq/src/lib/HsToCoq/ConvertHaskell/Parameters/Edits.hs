{-# LANGUAGE LambdaCase, TemplateHaskell #-}

module HsToCoq.ConvertHaskell.Parameters.Edits (
  Edits(..), typeSynonymTypes, dataTypeArguments,
  DataTypeArguments(..), dtParameters, dtIndices,
  Edit(..), addEdit, buildEdits
) where

import Control.Lens
import Control.Monad
import Data.Semigroup
import qualified Data.Text as T
import Data.Map (Map)
import HsToCoq.Coq.Gallina


data DataTypeArguments = DataTypeArguments { _dtParameters :: ![Ident]
                                           , _dtIndices    :: ![Ident] }
                       deriving (Eq, Ord, Show, Read)
makeLenses ''DataTypeArguments


data Edit = TypeSynonymTypeEdit   Ident Ident
          | DataTypeArgumentsEdit Ident DataTypeArguments
          deriving (Eq, Ord, Show, Read)

addFresh :: At m
          => LensLike (Either e) s t m m
          -> (Index m -> e)
          -> Index m
          -> IxValue m
          -> s -> Either e t
addFresh lens err key val = lens.at key %%~ \case
                              Just  _ -> Left  $ err key
                              Nothing -> Right $ Just val


data Edits = Edits { _typeSynonymTypes  :: !(Map Ident Ident)
                   , _dataTypeArguments :: !(Map Ident DataTypeArguments) }
           deriving (Eq, Ord, Show, Read)
makeLenses ''Edits

instance Semigroup Edits where
  Edits tst1 dta1 <> Edits tst2 dta2 = Edits (tst1 <> tst2) (dta1 <> dta2)

instance Monoid Edits where
  mempty = Edits mempty mempty
  mappend = (<>)

-- Module-local
duplicate_for :: String -> Ident -> String
duplicate_for what x = "Duplciate " ++ what ++ " for " ++ T.unpack x

addEdit :: Edit -> Edits -> Either String Edits
addEdit (TypeSynonymTypeEdit   syn res)  = addFresh typeSynonymTypes  (duplicate_for "type synonym result types")         syn res
addEdit (DataTypeArgumentsEdit ty  args) = addFresh dataTypeArguments (duplicate_for "data type argument specifications") ty  args

buildEdits :: Foldable f => f Edit -> Either String Edits
buildEdits = foldM (flip addEdit) mempty
