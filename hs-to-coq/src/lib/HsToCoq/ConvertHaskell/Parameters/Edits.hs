{-# LANGUAGE LambdaCase, TemplateHaskell #-}

module HsToCoq.ConvertHaskell.Parameters.Edits (
  Edits(..), typeSynonymTypes, dataTypeArguments, redefinitions, skipped, skippedMethods, moduleRenamings, additionalScopes, orders,
  DataTypeArguments(..), dtParameters, dtIndices,
  CoqDefinition(..), definitionSentence,
  ScopePlace(..),
  Edit(..), addEdit, buildEdits,
  addFresh
) where

import Prelude hiding (tail)

import Control.Lens

import Control.Monad
import Data.Semigroup
import Data.List.NonEmpty (NonEmpty(..), toList, tail)
import qualified Data.Text as T

import Data.Map (Map, singleton, unionWith)
import Data.Set (Set, singleton, union)
import Data.Tuple

import HsToCoq.Coq.Gallina
import HsToCoq.ConvertHaskell.Parameters.Renamings

--------------------------------------------------------------------------------

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

-- Add more as needed
data ScopePlace = SPValue | SPConstructor
                deriving (Eq, Ord, Enum, Bounded, Show, Read)

data Edit = TypeSynonymTypeEdit   Ident Ident
          | DataTypeArgumentsEdit Ident DataTypeArguments
          | RedefinitionEdit      CoqDefinition
          | SkipMethodEdit        Ident Ident
          | SkipEdit              Ident
          | ModuleRenamingEdit    Ident NamespacedIdent Ident
          | AdditionalScopeEdit   ScopePlace Ident Ident
          | OrderEdit             (NonEmpty Ident)
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

addEdge :: (Ord k, Ord v) => ASetter' s (Map k (Set v)) -> (k, v) -> s -> s
addEdge lens (from, to) = lens %~ unionWith union (Data.Map.singleton from (Data.Set.singleton to))

data Edits = Edits { _typeSynonymTypes  :: !(Map Ident Ident)
                   , _dataTypeArguments :: !(Map Ident DataTypeArguments)
                   , _redefinitions     :: !(Map Ident CoqDefinition)
                   , _skipped           :: !(Set Ident)
                   , _skippedMethods    :: !(Set (Ident,Ident))
                   , _moduleRenamings   :: !(Map Ident Renamings)
                   , _additionalScopes  :: !(Map (ScopePlace, Ident) Ident)
                   , _orders            :: !(Map Ident (Set Ident))
                   }
           deriving (Eq, Ord, Show, Read)
makeLenses ''Edits

instance Semigroup Edits where
  Edits tst1 dta1 rdf1 skp1 skpm1 mrns1 ads1 o1 <> Edits tst2 dta2 rdf2 skp2 skpm2 mrns2 ads2 o2 =
    Edits (tst1 <> tst2) (dta1 <> dta2) (rdf1 <> rdf2) (skp1 <> skp2) (skpm1 <> skpm2) (mrns1 <> mrns2) (ads1 <> ads2) (o1 <> o2)

instance Monoid Edits where
  mempty  = Edits mempty mempty mempty mempty mempty mempty mempty mempty
  mappend = (<>)

-- Module-local'
duplicate_for' :: String -> (a -> String) -> a -> String
duplicate_for' what disp x = "Duplicate " ++ what ++ " for " ++ disp x

-- Module-local
duplicate_for :: String -> Ident -> String
duplicate_for what = duplicate_for' what T.unpack

addEdit :: Edit -> Edits -> Either String Edits
addEdit = \case -- To bring the `where' clause into scope everywhere
  TypeSynonymTypeEdit   syn        res    -> addFresh typeSynonymTypes                    (duplicate_for  "type synonym result types")                   syn          res
  DataTypeArgumentsEdit ty         args   -> addFresh dataTypeArguments                   (duplicate_for  "data type argument specifications")           ty           args
  RedefinitionEdit      def               -> addFresh redefinitions                       (duplicate_for  "redefinition")                                (name def)   def
  SkipEdit              what              -> addFresh skipped                             (duplicate_for  "skip requests")                               what         ()
  SkipMethodEdit        cls meth          -> addFresh skippedMethods                      (duplicate_for' "skip method requests"          prettyClsMth)  (cls,meth)   ()
  ModuleRenamingEdit    mod        hs coq -> addFresh (moduleRenamings.at mod.non mempty) (duplicate_for' ("renaming in module " ++. mod) prettyNSIdent) hs           coq
  AdditionalScopeEdit   place name scope  -> addFresh additionalScopes                    (duplicate_for' "addition of a scope"           prettyScoped)  (place,name) scope
  OrderEdit             idents            -> Right . appEndo (foldMap (Endo . addEdge orders . swap) (adjacents idents))
  where
    name (CoqDefinitionDef (DefinitionDef _ x _ _ _))                = x
    name (CoqDefinitionDef (LetDef          x _ _ _))                = x
    name (CoqFixpointDef   (Fixpoint    (FixBody   x _ _ _ _ :| _) _)) = x
    name (CoqFixpointDef   (CoFixpoint  (CofixBody x _ _ _   :| _) _)) = x
    name (CoqInductiveDef  (Inductive   (IndBody   x _ _ _   :| _) _)) = x
    name (CoqInductiveDef  (CoInductive (IndBody   x _ _ _   :| _) _)) = x

    prettyScoped (place, name) = let pplace = case place of
                                       SPValue       -> "value"
                                       SPConstructor -> "constructor"
                                 in pplace ++ ' ' : T.unpack name

    prettyClsMth (cls, meth) = T.unpack cls <> "." <> T.unpack meth

    s ++. t = s ++ T.unpack t
    infixl 5 ++.

buildEdits :: Foldable f => f Edit -> Either String Edits
buildEdits = foldM (flip addEdit) mempty

adjacents :: NonEmpty a -> [(a,a)]
adjacents xs = zip (toList xs) (tail xs)
