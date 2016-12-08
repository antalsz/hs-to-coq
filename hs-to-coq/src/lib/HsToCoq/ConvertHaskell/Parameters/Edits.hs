{-# LANGUAGE LambdaCase, TemplateHaskell #-}

module HsToCoq.ConvertHaskell.Parameters.Edits (
  Edits(..), typeSynonymTypes, dataTypeArguments, redefinitions,
  DataTypeArguments(..), dtParameters, dtIndices,
  CoqDefinition(..), definitionSentence,
  Edit(..), addEdit, buildEdits,
  addFresh
) where

import Control.Lens
import Control.Monad
import Data.Semigroup
import Data.List.NonEmpty (NonEmpty(..))
import qualified Data.Text as T
import Data.Map (Map)
import HsToCoq.Coq.Gallina


data DataTypeArguments = DataTypeArguments { _dtParameters :: ![Ident]
                                           , _dtIndices    :: ![Ident] }
                       deriving (Eq, Ord, Show, Read)
makeLenses ''DataTypeArguments

data CoqDefinition = CoqDefinitionDef Definition
                   | CoqFixpointDef   Fixpoint
                   | CoqInductiveDef  Inductive
                   deriving (Eq, Ord, Show, Read)

definitionSentence :: CoqDefinition -> Sentence
definitionSentence (CoqDefinitionDef def) = DefinitionSentence def
definitionSentence (CoqFixpointDef   fix) = FixpointSentence   fix
definitionSentence (CoqInductiveDef  ind) = InductiveSentence  ind

data Edit = TypeSynonymTypeEdit   Ident Ident
          | DataTypeArgumentsEdit Ident DataTypeArguments
          | RedefinitionEdit      CoqDefinition
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
                   , _dataTypeArguments :: !(Map Ident DataTypeArguments)
                   , _redefinitions     :: !(Map Ident CoqDefinition) }
           deriving (Eq, Ord, Show, Read)
makeLenses ''Edits

instance Semigroup Edits where
  Edits tst1 dta1 rdf1 <> Edits tst2 dta2 rdf2 = Edits (tst1 <> tst2) (dta1 <> dta2) (rdf1 <> rdf2)

instance Monoid Edits where
  mempty = Edits mempty mempty mempty
  mappend = (<>)

-- Module-local
duplicate_for :: String -> Ident -> String
duplicate_for what x = "Duplciate " ++ what ++ " for " ++ T.unpack x

addEdit :: Edit -> Edits -> Either String Edits
addEdit (TypeSynonymTypeEdit   syn res)  = addFresh typeSynonymTypes  (duplicate_for "type synonym result types")         syn        res
addEdit (DataTypeArgumentsEdit ty  args) = addFresh dataTypeArguments (duplicate_for "data type argument specifications") ty         args
addEdit (RedefinitionEdit      def)      = addFresh redefinitions     (duplicate_for "redefinition")                      (name def) def
  where name (CoqDefinitionDef (DefinitionDef _ x _ _ _))                = x
        name (CoqDefinitionDef (LetDef          x _ _ _))                = x
        name (CoqFixpointDef   (Fixpoint    (FixBody   x _ _ _ _ :| _) _)) = x
        name (CoqFixpointDef   (CoFixpoint  (CofixBody x _ _ _   :| _) _)) = x
        name (CoqInductiveDef  (Inductive   (IndBody   x _ _ _   :| _) _)) = x
        name (CoqInductiveDef  (CoInductive (IndBody   x _ _ _   :| _) _)) = x

buildEdits :: Foldable f => f Edit -> Either String Edits
buildEdits = foldM (flip addEdit) mempty
