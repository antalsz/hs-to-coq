{-# LANGUAGE LambdaCase, TemplateHaskell, RecordWildCards, OverloadedStrings, FlexibleContexts, MultiParamTypeClasses, RankNTypes, DeriveGeneric #-}

module HsToCoq.ConvertHaskell.Parameters.Edits (
  Edits(..), typeSynonymTypes, dataTypeArguments, termination, redefinitions, additions, skipped, skippedConstructors, skippedClasses, skippedMethods, skippedModules, importedModules, hasManualNotation, axiomatizedModules, axiomatizedDefinitions, unaxiomatizedDefinitions, additionalScopes, orders, renamings, coinductiveTypes, classKinds, dataKinds, deleteUnusedTypeVariables, rewrites, obligations, renamedModules, simpleClasses, inlinedMutuals, replacedTypes, collapsedLets, inEdits,
  HsNamespace(..), NamespacedIdent(..), Renamings,
  DataTypeArguments(..), dtParameters, dtIndices,
  CoqDefinition(..), definitionSentence,
  anAssertionVariety,
  ScopePlace(..),
  TerminationArgument(..),
  Rewrite(..), Rewrites,
  Edit(..), addEdit, buildEdits,
  useProgram,
) where

import Prelude hiding (tail)

import Control.Lens

import HsToCoq.Util.Generics

import Control.Monad
import Control.Monad.Except
import Data.Semigroup
import Data.List.NonEmpty (NonEmpty(..), toList, tail)
import qualified Data.Text as T
import Data.Tuple

import Data.Map.Strict (Map)
import qualified Data.Map.Strict as M
import Data.Set (Set)
import qualified Data.Set as S

import HsToCoq.Util.GHC.Module

import HsToCoq.Util.FVs
import HsToCoq.Coq.FreeVars ()

import HsToCoq.Coq.Gallina
import HsToCoq.Coq.Gallina.Util
import HsToCoq.Coq.Gallina.Rewrite (Rewrite(..), Rewrites)
import HsToCoq.ConvertHaskell.Axiomatize

--------------------------------------------------------------------------------

data DataTypeArguments = DataTypeArguments { _dtParameters :: ![Qualid]
                                           , _dtIndices    :: ![Qualid] }
                       deriving (Eq, Ord, Show, Read)
makeLenses ''DataTypeArguments

data CoqDefinition = CoqDefinitionDef Definition
                   | CoqFixpointDef   Fixpoint
                   | CoqInductiveDef  Inductive
                   | CoqInstanceDef   InstanceDefinition
                   | CoqAxiomDef      (Qualid, Term) -- Curry?  Uncurry?  A new type?
                   | CoqAssertionDef  (Assertion, Proof) -- Curry?  Uncurry?  A new type?
                   deriving (Eq, Ord, Show, Read)

definitionSentence :: CoqDefinition -> Sentence
definitionSentence (CoqDefinitionDef      def) = DefinitionSentence        def
definitionSentence (CoqFixpointDef        fix) = FixpointSentence          fix
definitionSentence (CoqInductiveDef       ind) = InductiveSentence         ind
definitionSentence (CoqInstanceDef        ind) = InstanceSentence          ind
definitionSentence (CoqAxiomDef           axm) = uncurry typedAxiom        axm
definitionSentence (CoqAssertionDef       apf) = uncurry AssertionSentence apf

anAssertionVariety :: (Assertion, Proof) -> String
anAssertionVariety (Assertion kwd _ _ _, _) = case kwd of
  Theorem     -> "a Theorem"
  Lemma       -> "a Lemma"
  Remark      -> "a Remark"
  Fact        -> "a Fact"
  Corollary   -> "a Corollary"
  Proposition -> "a Proposition"
  Definition  -> "a Definition"
  Example     -> "an Example"

instance HasBV Qualid CoqDefinition where
  bvOf = bvOf . definitionSentence

-- Add more as needed
data ScopePlace = SPValue | SPConstructor
                deriving (Eq, Ord, Enum, Bounded, Show, Read)

data TerminationArgument = WellFounded Order | Deferred | Corecursive
                deriving (Eq, Ord, Show, Read)

data Edit = TypeSynonymTypeEdit           Ident Ident
          | DataTypeArgumentsEdit         Qualid DataTypeArguments
          | TerminationEdit               Qualid TerminationArgument
          | ObligationsEdit               Qualid Tactics
          | RedefinitionEdit              CoqDefinition
          | AddEdit                       ModuleName CoqDefinition
          | SkipEdit                      Qualid
          | SkipConstructorEdit           Qualid
          | SkipClassEdit                 Qualid
          | SkipMethodEdit                Qualid Ident
          | SkipModuleEdit                ModuleName
          | ImportModuleEdit              ModuleName
          | AxiomatizeModuleEdit          ModuleName
          | AxiomatizeDefinitionEdit      Qualid
          | UnaxiomatizeDefinitionEdit    Qualid
          | HasManualNotationEdit         ModuleName
          | AdditionalScopeEdit           ScopePlace Qualid Ident
          | OrderEdit                     (NonEmpty Qualid)
          | RenameEdit                    NamespacedIdent Qualid
          | ClassKindEdit                 Qualid (NonEmpty Term)
          | DataKindEdit                  Qualid (NonEmpty Term)
          | DeleteUnusedTypeVariablesEdit Qualid
          | RewriteEdit                   Rewrite
          | CoinductiveEdit               Qualid
          | RenameModuleEdit              ModuleName ModuleName
          | SimpleClassEdit               Qualid
          | InlineMutualEdit              Qualid
          | SetTypeEdit                   Qualid (Maybe Term)
          | CollapseLetEdit               Qualid
          | InEdit                        Qualid Edit
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

data Edits = Edits { _typeSynonymTypes          :: !(Map Ident Ident)
                   , _dataTypeArguments         :: !(Map Qualid DataTypeArguments)
                   , _termination               :: !(Map Qualid TerminationArgument)
                   , _redefinitions             :: !(Map Qualid CoqDefinition)
                   , _additions                 :: !(Map ModuleName [Sentence])
                   , _skipped                   :: !(Set Qualid)
                   , _skippedConstructors       :: !(Set Qualid)
                   , _skippedClasses            :: !(Set Qualid)
                   , _skippedMethods            :: !(Set (Qualid,Ident))
                   , _skippedModules            :: !(Set ModuleName)
                   , _importedModules           :: !(Set ModuleName)
                   , _axiomatizedModules        :: !(Set ModuleName)
                   , _axiomatizedDefinitions    :: !(Set Qualid)
                   , _unaxiomatizedDefinitions  :: !(Set Qualid)
                   , _hasManualNotation         :: !(Set ModuleName)
                   , _additionalScopes          :: !(Map (ScopePlace, Qualid) Ident)
                   , _orders                    :: !(Map Qualid (Set Qualid))
                   , _classKinds                :: !(Map Qualid (NonEmpty Term))
                   , _dataKinds                 :: !(Map Qualid (NonEmpty Term))
                   , _deleteUnusedTypeVariables :: !(Set Qualid)
                   , _renamings                 :: !Renamings
                   , _rewrites                  :: ![Rewrite]
                   , _obligations               :: !(Map Qualid Tactics)
                   , _coinductiveTypes          :: !(Set Qualid)
                   , _renamedModules            :: !(Map ModuleName ModuleName)
                   , _simpleClasses             :: !(Set Qualid)
                   , _inlinedMutuals            :: !(Set Qualid)
                   , _replacedTypes             :: !(Map Qualid (Maybe Term)) -- Instead of setTypes
                   , _collapsedLets             :: !(Set Qualid)
                   , _inEdits                   :: !(Map Qualid Edits)
                   }
           deriving (Eq, Ord, Show, Generic)
instance Semigroup Edits where (<>)   = (%<>)
instance Monoid    Edits where mempty = gmempty
makeLenses ''Edits

-- Derived edits
useProgram :: Qualid -> Edits -> Bool
useProgram name edits = or
    [ any isWellFounded                      (M.lookup name (_termination edits))
    , any (any isWellFounded . _termination) (M.lookup name (_inEdits edits))
    , name `M.member`_obligations edits
    ]
  where
   isWellFounded (WellFounded {}) = True
   isWellFounded _ = False

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

descDuplEdit :: Edit                    -> String
descDuplEdit = \case
  TypeSynonymTypeEdit           syn        _ -> duplicateI_for  "type synonym result types"            syn
  DataTypeArgumentsEdit         ty         _ -> duplicateQ_for  "data type argument specifications"    ty
  TerminationEdit               what _       -> duplicateQ_for  "termination requests"                 what
  RedefinitionEdit              def          -> duplicateQ_for  "redefinitions"                        (defName def)
  SkipEdit                      what         -> duplicateQ_for  "skips"                                what
  SkipConstructorEdit           con          -> duplicateQ_for  "skipped constructor requests"         con
  SkipClassEdit                 cls          -> duplicateQ_for  "skipped class requests"               cls
  SkipMethodEdit                cls meth     -> duplicate_for   "skipped method requests"              (prettyLocalName cls meth)
  SkipModuleEdit                mod          -> duplicate_for   "skipped module requests"              (moduleNameString mod)
  ImportModuleEdit              mod          -> duplicate_for   "imported module requests"             (moduleNameString mod)
  HasManualNotationEdit         what         -> duplicate_for   "has manual notation"                  (moduleNameString what)
  AxiomatizeModuleEdit          mod          -> duplicate_for   "module axiomatizations"               (moduleNameString mod)
  AxiomatizeDefinitionEdit      what         -> duplicateQ_for  "definition axiomatizations"           what
  UnaxiomatizeDefinitionEdit    what         -> duplicateQ_for  "definition unaxiomatizations"         what
  AdditionalScopeEdit           place name _ -> duplicate_for   "additions of a scope"                 (prettyScoped place name)
  RenameEdit                    hs _         -> duplicate_for   "renamings"                            (prettyNSIdent hs)
  ClassKindEdit                 cls _        -> duplicateQ_for  "class kinds"                          cls
  DataKindEdit                  dat _        -> duplicateQ_for  "data kinds"                           dat
  DeleteUnusedTypeVariablesEdit qid          -> duplicateQ_for  "unused type variables deletions"      qid
  ObligationsEdit               what _       -> duplicateQ_for  "obligation kinds"                     what
  CoinductiveEdit               ty           -> duplicateQ_for  "coinductive data types"               ty
  RenameModuleEdit              m1 _         -> duplicate_for   "renamed modules"                      (moduleNameString m1)
  AddEdit                       _ _          -> error "Add edits are never duplicates"
  RewriteEdit                   _            -> error "Rewrites are never duplicates"
  OrderEdit                     _            -> error "Order edits are never duplicates"
  SimpleClassEdit               cls          -> duplicateQ_for  "simple class requests"                cls
  InlineMutualEdit              fun          -> duplicateQ_for  "inlined mutually recursive functions" fun
  SetTypeEdit                   qid _        -> duplicateQ_for  "set types"                            qid
  CollapseLetEdit               qid          -> duplicateQ_for  "collapsed lets"                       qid
  InEdit                        _ _          -> error "In Edits are never duplicates"
  where
    prettyScoped place name = let pplace = case place of
                                    SPValue       -> "value"
                                    SPConstructor -> "constructor"
                              in pplace ++ ' ' : T.unpack (qualidToIdent name)

    prettyLocalName outer inner = T.unpack $ qualidToIdent outer <> "." <> inner

addEdit :: MonadError String m => Edit -> Edits -> m Edits
addEdit e = case e of
  TypeSynonymTypeEdit           syn  res         -> addFresh e typeSynonymTypes                       syn           res
  DataTypeArgumentsEdit         ty   args        -> addFresh e dataTypeArguments                      ty            args
  TerminationEdit               what ta          -> addFresh e termination                            what          ta
  RedefinitionEdit              def              -> addFresh e redefinitions                          (defName def) def
  SkipEdit                      what             -> addFresh e skipped                                what          ()
  SkipConstructorEdit           con              -> addFresh e skippedConstructors                    con           ()
  SkipClassEdit                 cls              -> addFresh e skippedClasses                         cls           ()
  SkipMethodEdit                cls meth         -> addFresh e skippedMethods                         (cls,meth)    ()
  SkipModuleEdit                mod              -> addFresh e skippedModules                         mod           ()
  ImportModuleEdit              mod              -> addFresh e importedModules                        mod           ()
  HasManualNotationEdit         what             -> addFresh e hasManualNotation                      what          ()
  AxiomatizeModuleEdit          mod              -> addFresh e axiomatizedModules                     mod           ()
  AxiomatizeDefinitionEdit      what             -> addFresh e axiomatizedDefinitions                 what          ()
  UnaxiomatizeDefinitionEdit    what             -> addFresh e unaxiomatizedDefinitions               what          ()
  AdditionalScopeEdit           place name scope -> addFresh e additionalScopes                       (place,name)  scope
  RenameEdit                    hs to            -> addFresh e renamings                              hs            to
  ObligationsEdit               what tac         -> addFresh e obligations                            what          tac
  ClassKindEdit                 cls kinds        -> addFresh e classKinds                             cls           kinds
  DataKindEdit                  cls kinds        -> addFresh e dataKinds                              cls           kinds
  DeleteUnusedTypeVariablesEdit qid              -> addFresh e deleteUnusedTypeVariables              qid           ()
  CoinductiveEdit               ty               -> addFresh e coinductiveTypes                       ty            ()
  RenameModuleEdit              m1 m2            -> addFresh e renamedModules                         m1            m2
  SimpleClassEdit               cls              -> addFresh e simpleClasses                          cls           ()
  InlineMutualEdit              fun              -> addFresh e inlinedMutuals                         fun           ()
  SetTypeEdit                   qid oty          -> addFresh e replacedTypes                          qid           oty
  CollapseLetEdit               qid              -> addFresh e collapsedLets                          qid           ()
  AddEdit                       mod def          -> return . (additions.at mod.non mempty %~ (definitionSentence def:))
  OrderEdit                     idents           -> return . appEndo (foldMap (Endo . addEdge orders . swap) (adjacents idents))
  RewriteEdit                   rewrite          -> return . (rewrites %~ (rewrite:))
  InEdit                        qid edit         -> inEdits.at qid.non mempty %%~ (addEdit edit)


defName :: CoqDefinition -> Qualid
defName (CoqDefinitionDef (DefinitionDef _ x _ _ _))                = x
defName (CoqDefinitionDef (LetDef          x _ _ _))                = x
defName (CoqFixpointDef   (Fixpoint    (FixBody x _ _ _ _ :| _) _)) = x
defName (CoqFixpointDef   (CoFixpoint  (FixBody x _ _ _ _ :| _) _)) = x
defName (CoqInductiveDef  (Inductive   (IndBody x _ _ _   :| _) _)) = x
defName (CoqInductiveDef  (CoInductive (IndBody x _ _ _   :| _) _)) = x
defName (CoqInstanceDef   (InstanceDefinition x _ _ _ _))           = x
defName (CoqInstanceDef   (InstanceTerm       x _ _ _ _))           = x
defName (CoqAxiomDef      (x, _))                                   = x
defName (CoqAssertionDef  (Assertion _ x _ _, _))                   = x

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
addFresh edit lens key val =
  lens.at key %%~ \case
    Just  _ -> throwError $ descDuplEdit edit
    Nothing -> pure $ Just val

addEdge :: (Ord k, Ord v) => ASetter' s (Map k (Set v)) -> (k, v) -> s -> s
addEdge lens (from, to) = lens %~ M.unionWith S.union (M.singleton from (S.singleton to))
