{-# LANGUAGE LambdaCase, TemplateHaskell, RecordWildCards #-}

module HsToCoq.ConvertHaskell.Parameters.Edits (
  Edits(..), typeSynonymTypes, dataTypeArguments, redefinitions, skipped, skippedMethods, skippedModules, moduleRenamings, additionalScopes, orders, renamings,
  HsNamespace(..), NamespacedIdent(..), Renamings,
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

import HsToCoq.Util.GHC.Module

import HsToCoq.Coq.Gallina

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
          | SkipEdit              Ident
          | SkipModuleEdit        ModuleName
          | SkipMethodEdit        Ident Ident
          | ModuleRenamingEdit    Ident NamespacedIdent Ident
          | AdditionalScopeEdit   ScopePlace Ident Ident
          | OrderEdit             (NonEmpty Ident)
          | RenameEdit            NamespacedIdent Ident
          deriving (Eq, Ord, Show)

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

data HsNamespace = ExprNS | TypeNS
                 deriving (Eq, Ord, Show, Read, Enum, Bounded)

prettyNSIdent :: NamespacedIdent -> String
prettyNSIdent NamespacedIdent{..} = prettyNS niNS ++ " " ++ T.unpack niId where
  prettyNS ExprNS = "value"
  prettyNS TypeNS = "type"

data NamespacedIdent = NamespacedIdent { niNS :: !HsNamespace
                                       , niId :: !Ident }
                     deriving (Eq, Ord, Show, Read)

type Renamings = Map NamespacedIdent Ident

data Edits = Edits { _typeSynonymTypes  :: !(Map Ident Ident)
                   , _dataTypeArguments :: !(Map Ident DataTypeArguments)
                   , _redefinitions     :: !(Map Ident CoqDefinition)
                   , _skipped           :: !(Set Ident)
                   , _skippedMethods    :: !(Set (Ident,Ident))
                   , _skippedModules    :: !(Set ModuleName)
                   , _moduleRenamings   :: !(Map Ident Renamings)
                   , _additionalScopes  :: !(Map (ScopePlace, Ident) Ident)
                   , _orders            :: !(Map Ident (Set Ident))
                   , _renamings         :: !Renamings
                   }
           deriving (Eq, Ord, Show)
makeLenses ''Edits

instance Semigroup Edits where
  Edits tst1 dta1 rdf1 skp1 smth1 smod1 mrns1 ads1 o1 r1 <> Edits tst2 dta2 rdf2 skp2 smth2 smod2 mrns2 ads2 o2 r2 =
    Edits (tst1 <> tst2) (dta1 <> dta2) (rdf1 <> rdf2) (skp1 <> skp2) (smth1 <> smth2) (smod1 <> smod2) (mrns1 <> mrns2) (ads1 <> ads2) (o1 <> o2) (r1 <> r2)

instance Monoid Edits where
  mempty  = Edits mempty mempty mempty mempty mempty mempty mempty mempty mempty mempty
  mappend = (<>)

-- Module-local'
duplicate_for' :: String -> (a -> String) -> a -> String
duplicate_for' what disp x = "Duplicate " ++ what ++ " for " ++ disp x

-- Module-local
duplicate_for :: String -> Ident -> String
duplicate_for what = duplicate_for' what T.unpack

addEdit :: Edit -> Edits -> Either String Edits
addEdit = \case -- To bring the `where' clause into scope everywhere
  TypeSynonymTypeEdit   syn        res    -> addFresh typeSynonymTypes                    (duplicate_for  "type synonym result types")                       syn          res
  DataTypeArgumentsEdit ty         args   -> addFresh dataTypeArguments                   (duplicate_for  "data type argument specifications")               ty           args
  RedefinitionEdit      def               -> addFresh redefinitions                       (duplicate_for  "redefinition")                                    (name def)   def
  SkipEdit              what              -> addFresh skipped                             (duplicate_for  "skip requests")                                   what         ()
  SkipMethodEdit        cls meth          -> addFresh skippedMethods                      (duplicate_for' "skipped method requests"       prettyClsMth)      (cls,meth)   ()
  SkipModuleEdit        mod               -> addFresh skippedModules                      (duplicate_for' "skipped module requests"       moduleNameString)  mod          ()
  ModuleRenamingEdit    mod        hs coq -> addFresh (moduleRenamings.at mod.non mempty) (duplicate_for' ("renaming in module " ++. mod) prettyNSIdent)     hs           coq
  AdditionalScopeEdit   place name scope  -> addFresh additionalScopes                    (duplicate_for' "addition of a scope"           prettyScoped)      (place,name) scope
  OrderEdit             idents            -> Right . appEndo (foldMap (Endo . addEdge orders . swap) (adjacents idents))
  RenameEdit            hs to             -> addFresh renamings                           (duplicate_for' "renaming"                      prettyNSIdent)     hs           to
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
