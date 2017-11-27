{-# LANGUAGE LambdaCase, TemplateHaskell, RecordWildCards, OverloadedStrings #-}

module HsToCoq.ConvertHaskell.Parameters.Edits (
  Edits(..), typeSynonymTypes, dataTypeArguments, nonterminating, termination, redefinitions, additions, skipped, skippedMethods, skippedModules, axiomatizedModules, additionalScopes, orders, renamings, classKinds, dataKinds,
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
import Data.Text (Text)
import qualified Data.Text as T

import Data.Map (Map, singleton, unionWith)
import Data.Set (Set, singleton, union)
import Data.Tuple

import HsToCoq.Util.GHC.Module

import HsToCoq.Coq.Gallina
import HsToCoq.Coq.Gallina.Util

--------------------------------------------------------------------------------

data DataTypeArguments = DataTypeArguments { _dtParameters :: ![Ident]
                                           , _dtIndices    :: ![Ident] }
                       deriving (Eq, Ord, Show, Read)
makeLenses ''DataTypeArguments

data CoqDefinition = CoqDefinitionDef      Definition
                   | CoqFixpointDef        Fixpoint
                   | CoqProgramFixpointDef ProgramFixpoint
                   | CoqInductiveDef       Inductive
                   | CoqInstanceDef        InstanceDefinition
                   deriving (Eq, Ord, Show, Read)

definitionSentence :: CoqDefinition -> Sentence
definitionSentence (CoqDefinitionDef      def) = DefinitionSentence       def
definitionSentence (CoqFixpointDef        fix) = FixpointSentence         fix
definitionSentence (CoqProgramFixpointDef pfx) = ProgramFixpointSentence  pfx Nothing
definitionSentence (CoqInductiveDef       ind) = InductiveSentence        ind
definitionSentence (CoqInstanceDef        ind) = InstanceSentence         ind

-- Add more as needed
data ScopePlace = SPValue | SPConstructor
                deriving (Eq, Ord, Enum, Bounded, Show, Read)

data Edit = TypeSynonymTypeEdit   Ident Ident
          | DataTypeArgumentsEdit Qualid DataTypeArguments
          | NonterminatingEdit    Qualid
          | TerminationEdit       Qualid Order (Maybe Text)
          | RedefinitionEdit      CoqDefinition
          | AddEdit               ModuleName CoqDefinition
          | SkipEdit              Qualid
          | SkipMethodEdit        Qualid Ident
          | SkipModuleEdit        ModuleName
          | AxiomatizeModuleEdit  ModuleName
          | AdditionalScopeEdit   ScopePlace Qualid Ident
          | OrderEdit             (NonEmpty Qualid)
          | RenameEdit            NamespacedIdent Qualid
          | ClassKindEdit         Qualid (NonEmpty Term)
          | DataKindEdit          Qualid (NonEmpty Term)
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
prettyNSIdent NamespacedIdent{..} = prettyNS niNS ++ " " ++ T.unpack (qualidToIdent niId) where
  prettyNS ExprNS = "value"
  prettyNS TypeNS = "type"

data NamespacedIdent = NamespacedIdent { niNS :: !HsNamespace
                                       , niId :: !Qualid }
                     deriving (Eq, Ord, Show, Read)

type Renamings = Map NamespacedIdent Qualid

data Edits = Edits { _typeSynonymTypes   :: !(Map Ident Ident)
                   , _dataTypeArguments  :: !(Map Qualid DataTypeArguments)
                   , _nonterminating     :: !(Set Qualid)
                   , _termination        :: !(Map Qualid (Order, Maybe Text))
                   , _redefinitions      :: !(Map Qualid CoqDefinition)
                   , _additions          :: !(Map ModuleName [Sentence])
                   , _skipped            :: !(Set Qualid)
                   , _skippedMethods     :: !(Set (Qualid,Ident))
                   , _skippedModules     :: !(Set ModuleName)
                   , _axiomatizedModules :: !(Set ModuleName)
                   , _additionalScopes   :: !(Map (ScopePlace, Qualid) Ident)
                   , _orders             :: !(Map Qualid (Set Qualid))
                   , _classKinds         :: !(Map Qualid (NonEmpty Term))
                   , _dataKinds          :: !(Map Qualid (NonEmpty Term))
                   , _renamings          :: !Renamings
                   }
           deriving (Eq, Ord, Show)
makeLenses ''Edits

instance Semigroup Edits where
  (<>) (Edits tst1 dta1 ntm1 trm1 rdf1 add1 skp1 smth1 smod1 axm1 ads1 ord1 rnm1 clk1 dk1)
       (Edits tst2 dta2 ntm2 trm2 rdf2 add2 skp2 smth2 smod2 axm2 ads2 ord2 rnm2 clk2 dk2) =
    Edits (tst1 <> tst2) (dta1 <> dta2) (ntm1 <> ntm2) (trm1 <> trm2) (rdf1 <> rdf2) (add1 <> add2) (skp1 <> skp2) (smth1 <> smth2) (smod1 <> smod2) (axm1 <> axm2) (ads1 <> ads2) (ord1 <> ord2) (rnm1 <> rnm2) (clk1 <> clk2) (dk1 <> dk2)

instance Monoid Edits where
  mempty  = Edits mempty mempty mempty mempty mempty mempty mempty mempty mempty mempty mempty mempty mempty mempty mempty
  mappend = (<>)

-- Module-local'
duplicate_for' :: String -> (a -> String) -> a -> String
duplicate_for' what disp x = "Duplicate " ++ what ++ " for " ++ disp x

-- Module-local
duplicate_for :: String -> Ident -> String
duplicate_for what = duplicate_for' what T.unpack

duplicateQ_for :: String -> Qualid -> String
duplicateQ_for what = duplicate_for' what (T.unpack . qualidToIdent)

addEdit :: Edit -> Edits -> Either String Edits
addEdit = \case -- To bring the `where' clause into scope everywhere
  TypeSynonymTypeEdit   syn        res    -> addFresh typeSynonymTypes                    (duplicate_for  "type synonym result types")                       syn          res
  DataTypeArgumentsEdit ty         args   -> addFresh dataTypeArguments                   (duplicateQ_for "data type argument specifications")               ty           args
  NonterminatingEdit    what              -> addFresh nonterminating                      (duplicateQ_for "declarations of nontermination")                  what         ()
  TerminationEdit       what order tac    -> addFresh termination                         (duplicateQ_for  "termination requests")                            what         (order,tac)
  RedefinitionEdit      def               -> addFresh redefinitions                       (duplicateQ_for "redefinitions")                                   (Bare (name def))   def
  AddEdit               mod def           -> Right . (additions.at mod.non mempty %~ (definitionSentence def:))
  SkipEdit              what              -> addFresh skipped                             (duplicateQ_for "skips")                                           what         ()
  SkipMethodEdit        cls meth          -> addFresh skippedMethods                      (duplicate_for' "skipped method requests"       prettyClsMth)      (cls,meth)   ()
  SkipModuleEdit        mod               -> addFresh skippedModules                      (duplicate_for' "skipped module requests"       moduleNameString)  mod          ()
  AxiomatizeModuleEdit  mod               -> addFresh axiomatizedModules                  (duplicate_for' "module axiomatizations"        moduleNameString)  mod          ()
  AdditionalScopeEdit   place name scope  -> addFresh additionalScopes                    (duplicate_for' "additions of a scope"          prettyScoped)      (place,name) scope
  OrderEdit             idents            -> Right . appEndo (foldMap (Endo . addEdge orders . swap) (adjacents idents))
  RenameEdit            hs to             -> addFresh renamings                           (duplicate_for' "renamings"                     prettyNSIdent)     hs           to
  ClassKindEdit         cls kinds         -> addFresh classKinds                          (duplicateQ_for "class kinds")                                     cls          kinds
  DataKindEdit          cls kinds         -> addFresh dataKinds                           (duplicateQ_for "data kinds")                                      cls          kinds
  where
    name (CoqDefinitionDef (DefinitionDef _ x _ _ _))                  = x
    name (CoqDefinitionDef (LetDef          x _ _ _))                  = x
    name (CoqFixpointDef   (Fixpoint    (FixBody   x _ _ _ _ :| _) _)) = x
    name (CoqFixpointDef   (CoFixpoint  (CofixBody x _ _ _   :| _) _)) = x
    name (CoqProgramFixpointDef  (ProgramFixpoint x _ _ _ _))          = x
    name (CoqInductiveDef  (Inductive   (IndBody   x _ _ _   :| _) _)) = x
    name (CoqInductiveDef  (CoInductive (IndBody   x _ _ _   :| _) _)) = x
    name (CoqInstanceDef   (InstanceDefinition x _ _ _ _))             = x
    name (CoqInstanceDef   (InstanceTerm       x _ _ _ _))             = x

    prettyScoped (place, name) = let pplace = case place of
                                       SPValue       -> "value"
                                       SPConstructor -> "constructor"
                                 in pplace ++ ' ' : T.unpack (qualidToIdent name)

    prettyClsMth (cls, meth) = T.unpack (qualidToIdent cls) <> "." <> T.unpack meth

buildEdits :: Foldable f => f Edit -> Either String Edits
buildEdits = foldM (flip addEdit) mempty

adjacents :: NonEmpty a -> [(a,a)]
adjacents xs = zip (toList xs) (tail xs)
