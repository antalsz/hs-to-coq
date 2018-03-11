{-# LANGUAGE LambdaCase, TemplateHaskell, RecordWildCards, OverloadedStrings, FlexibleContexts, RankNTypes #-}

module HsToCoq.ConvertHaskell.Parameters.Edits (
  Edits(..), typeSynonymTypes, dataTypeArguments, termination,  local_termination, redefinitions, additions, skipped, hasManualNotation, skippedMethods, skippedModules, axiomatizedModules, additionalScopes, orders, renamings, classKinds, dataKinds, rewrites, obligations,
  HsNamespace(..), NamespacedIdent(..), Renamings,
  DataTypeArguments(..), dtParameters, dtIndices,
  CoqDefinition(..), definitionSentence,
  ScopePlace(..),
  TerminationArgument(..),
  Rewrite(..), Rewrites,
  Edit(..), addEdit, buildEdits,
  useProgram,
) where

import Prelude hiding (tail)

import Control.Lens

import Control.Monad
import Control.Monad.Except
import Data.Semigroup
import Data.List.NonEmpty (NonEmpty(..), toList, tail)
import qualified Data.Text as T

import Data.Map (Map, lookup, singleton, unionWith, member)
import Data.Set (Set, singleton, union)
import Data.Tuple

import HsToCoq.Util.GHC.Module

import HsToCoq.Coq.Gallina
import HsToCoq.Coq.Gallina.Util
import HsToCoq.Coq.Gallina.Rewrite (Rewrite(..), Rewrites)

--------------------------------------------------------------------------------

data DataTypeArguments = DataTypeArguments { _dtParameters :: ![Qualid]
                                           , _dtIndices    :: ![Qualid] }
                       deriving (Eq, Ord, Show, Read)
makeLenses ''DataTypeArguments

data CoqDefinition = CoqDefinitionDef      Definition
                   | CoqFixpointDef        Fixpoint
                   | CoqInductiveDef       Inductive
                   | CoqInstanceDef        InstanceDefinition
                   deriving (Eq, Ord, Show, Read)

definitionSentence :: CoqDefinition -> Sentence
definitionSentence (CoqDefinitionDef      def) = DefinitionSentence       def
definitionSentence (CoqFixpointDef        fix) = FixpointSentence         fix
definitionSentence (CoqInductiveDef       ind) = InductiveSentence        ind
definitionSentence (CoqInstanceDef        ind) = InstanceSentence         ind

-- Add more as needed
data ScopePlace = SPValue | SPConstructor
                deriving (Eq, Ord, Enum, Bounded, Show, Read)

data TerminationArgument = WellFounded Order | Deferred
                deriving (Eq, Ord, Show, Read)

data Edit = TypeSynonymTypeEdit     Ident Ident
          | DataTypeArgumentsEdit   Qualid DataTypeArguments
          | TerminationEdit         Qualid (Maybe Ident) TerminationArgument
          | ObligationsEdit         Qualid Tactics
          | RedefinitionEdit        CoqDefinition
          | AddEdit                 ModuleName CoqDefinition
          | SkipEdit                Qualid
          | SkipMethodEdit          Qualid Ident
          | SkipModuleEdit          ModuleName
          | AxiomatizeModuleEdit    ModuleName
          | HasManualNotationEdit   ModuleName
          | AdditionalScopeEdit     ScopePlace Qualid Ident
          | OrderEdit               (NonEmpty Qualid)
          | RenameEdit              NamespacedIdent Qualid
          | ClassKindEdit           Qualid (NonEmpty Term)
          | DataKindEdit            Qualid (NonEmpty Term)
          | RewriteEdit             Rewrite
          deriving (Eq, Ord, Show)

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

data Edits = Edits { _typeSynonymTypes    :: !(Map Ident Ident)
                   , _dataTypeArguments   :: !(Map Qualid DataTypeArguments)
                   , _termination         :: !(Map Qualid TerminationArgument)
                   , _local_termination   :: !(Map Qualid (Map Ident TerminationArgument))
                   , _redefinitions       :: !(Map Qualid CoqDefinition)
                   , _additions           :: !(Map ModuleName [Sentence])
                   , _skipped             :: !(Set Qualid)
                   , _skippedMethods      :: !(Set (Qualid,Ident))
                   , _skippedModules      :: !(Set ModuleName)
                   , _axiomatizedModules  :: !(Set ModuleName)
                   , _hasManualNotation   :: !(Set ModuleName)
                   , _additionalScopes    :: !(Map (ScopePlace, Qualid) Ident)
                   , _orders              :: !(Map Qualid (Set Qualid))
                   , _classKinds          :: !(Map Qualid (NonEmpty Term))
                   , _dataKinds           :: !(Map Qualid (NonEmpty Term))
                   , _renamings           :: !Renamings
                   , _rewrites            :: ![Rewrite]
                   , _obligations         :: !(Map Qualid Tactics)
                   }
           deriving (Eq, Ord, Show)
makeLenses ''Edits

-- Derived edits
useProgram :: Qualid -> Edits -> Bool
useProgram name edits = or
    [ any isWellFounded       (Data.Map.lookup name (_termination edits))
    , any (any isWellFounded) (Data.Map.lookup name (_local_termination edits))
    , name `member`_obligations edits
    ]
  where
   isWellFounded (WellFounded {}) = True
   isWellFounded _ = False


instance Semigroup Edits where
  (<>) (Edits tst1 dta1 trm1 ltm1 rdf1 add1 skp1 smth1 smod1 axm1 hmn1 ads1 ord1 rnm1 clk1 dk1 rws1 obl1)
       (Edits tst2 dta2 trm2 ltm2 rdf2 add2 skp2 smth2 smod2 axm2 hmn2 ads2 ord2 rnm2 clk2 dk2 rws2 obl2) =
    Edits (tst1 <> tst2) (dta1 <> dta2) (trm1 <> trm2) (ltm1 <> ltm2) (rdf1 <> rdf2) (add1 <> add2) (skp1 <> skp2) (smth1 <> smth2) (smod1 <> smod2) (axm1 <> axm2) (hmn1 <> hmn2) (ads1 <> ads2) (ord1 <> ord2) (rnm1 <> rnm2) (clk1 <> clk2) (dk1 <> dk2) (rws1 <> rws2) (obl1 <> obl2)

instance Monoid Edits where
  mempty  = Edits mempty mempty mempty mempty mempty mempty mempty mempty mempty mempty mempty mempty mempty mempty mempty mempty mempty mempty
  mappend = (<>)

-- Module-local'
duplicate_for' :: String -> (a -> String) -> a -> String
duplicate_for' what disp x = "Duplicate " ++ what ++ " for " ++ disp x

-- Module-local
duplicate_for :: String -> String -> String
duplicate_for what = duplicate_for' what id

duplicateI_for :: String -> Ident -> String
duplicateI_for what = duplicate_for' what T.unpack

duplicateQ_for :: String -> Qualid -> String
duplicateQ_for what = duplicate_for' what (T.unpack . qualidToIdent)

duplicateQL_for :: String -> Qualid -> Ident -> String
duplicateQL_for what qid lid = "Duplicate " ++ what ++ " for " ++ T.unpack lid ++ " in " ++ T.unpack (qualidToIdent qid)

descDuplEdit :: Edit -> String
descDuplEdit = \case
  TypeSynonymTypeEdit   syn        _       -> duplicateI_for  "type synonym result types"            syn
  DataTypeArgumentsEdit ty         _       -> duplicateQ_for  "data type argument specifications"    ty
  TerminationEdit       what Nothing _     -> duplicateQ_for  "termination requests"                 what
  TerminationEdit       what (Just lid) _  -> duplicateQL_for "local termination requests"           what lid
  RedefinitionEdit      def                -> duplicateQ_for  "redefinitions"                        (defName def)
  SkipEdit              what               -> duplicateQ_for  "skips"                                what
  SkipMethodEdit        cls meth           -> duplicate_for   "skipped method requests"              (prettyClsMth cls meth)
  SkipModuleEdit        mod                -> duplicate_for   "skipped module requests"              (moduleNameString mod)
  HasManualNotationEdit what               -> duplicate_for   "has manual notation"                  (moduleNameString what)
  AxiomatizeModuleEdit  mod                -> duplicate_for   "module axiomatizations"               (moduleNameString mod)
  AdditionalScopeEdit   place name _       -> duplicate_for   "additions of a scope"                 (prettyScoped place name)
  RenameEdit            hs _               -> duplicate_for   "renamings"                            (prettyNSIdent hs)
  ClassKindEdit         cls _              -> duplicateQ_for  "class kinds"                          cls
  DataKindEdit          dat _              -> duplicateQ_for  "data kinds"                           dat
  ObligationsEdit       what _             -> duplicateQ_for  "obligation kinds"                     what
  AddEdit               _ _                -> error "Add edits are never duplicate"
  RewriteEdit           _                  -> error "Rewrites are never duplicate"
  OrderEdit             _                  -> error "Order edits are never duplicate"
  where
    prettyScoped place name = let pplace = case place of
                                    SPValue       -> "value"
                                    SPConstructor -> "constructor"
                              in pplace ++ ' ' : T.unpack (qualidToIdent name)

    prettyClsMth cls meth = T.unpack (qualidToIdent cls) <> "." <> T.unpack meth

addEdit :: MonadError String m => Edit -> Edits -> m Edits
addEdit e = case e of
  TypeSynonymTypeEdit     syn        res     -> addFresh e typeSynonymTypes                       syn          res
  DataTypeArgumentsEdit   ty         args    -> addFresh e dataTypeArguments                      ty           args
  TerminationEdit         what Nothing ta    -> addFresh e termination                            what         ta
  TerminationEdit         what (Just lid) ta -> addFresh e (local_termination.at what.non mempty) lid          ta
  RedefinitionEdit        def                -> addFresh e redefinitions                          (defName def)   def
  SkipEdit                what               -> addFresh e skipped                                what         ()
  SkipMethodEdit          cls meth           -> addFresh e skippedMethods                         (cls,meth)   ()
  SkipModuleEdit          mod                -> addFresh e skippedModules                         mod          ()
  HasManualNotationEdit   what               -> addFresh e hasManualNotation                      what         ()
  AxiomatizeModuleEdit    mod                -> addFresh e axiomatizedModules                     mod          ()
  AdditionalScopeEdit     place name scope   -> addFresh e additionalScopes                       (place,name) scope
  RenameEdit              hs to              -> addFresh e renamings                              hs           to
  ObligationsEdit         what tac           -> addFresh e obligations                            what         tac
  ClassKindEdit           cls kinds          -> addFresh e classKinds                             cls          kinds
  DataKindEdit            cls kinds          -> addFresh e dataKinds                              cls          kinds
  AddEdit                 mod def            -> return . (additions.at mod.non mempty %~ (definitionSentence def:))
  OrderEdit               idents             -> return . appEndo (foldMap (Endo . addEdge orders . swap) (adjacents idents))
  RewriteEdit             rewrite            -> return . (rewrites %~ (rewrite:))


defName :: CoqDefinition -> Qualid
defName (CoqDefinitionDef (DefinitionDef _ x _ _ _))                  = x
defName (CoqDefinitionDef (LetDef          x _ _ _))                  = x
defName (CoqFixpointDef   (Fixpoint    (FixBody   x _ _ _ _ :| _) _)) = x
defName (CoqFixpointDef   (CoFixpoint  (CofixBody x _ _ _   :| _) _)) = x
defName (CoqInductiveDef  (Inductive   (IndBody   x _ _ _   :| _) _)) = x
defName (CoqInductiveDef  (CoInductive (IndBody   x _ _ _   :| _) _)) = x
defName (CoqInstanceDef   (InstanceDefinition x _ _ _ _))             = x
defName (CoqInstanceDef   (InstanceTerm       x _ _ _ _))             = x

buildEdits :: Foldable f => f Edit -> Either String Edits
buildEdits = foldM (flip addEdit) mempty

adjacents :: NonEmpty a -> [(a,a)]
adjacents xs = zip (toList xs) (tail xs)

addFresh :: (MonadError String m, At map)
         => Edit
         -> LensLike m s t map map
         -> Index map
         -> IxValue map
         -> s
         -> m t
addFresh edit lens key val = lens.at key %%~ \case
      Just  _ -> throwError $ descDuplEdit edit
      Nothing -> return $ Just val

addEdge :: (Ord k, Ord v) => ASetter' s (Map k (Set v)) -> (k, v) -> s -> s
addEdge lens (from, to) = lens %~ unionWith union (Data.Map.singleton from (Data.Set.singleton to))

