{-# LANGUAGE TupleSections, LambdaCase, RecordWildCards, FlexibleContexts #-}
{-# LANGUAGE StandaloneDeriving, DeriveFunctor, DeriveFoldable, DeriveTraversable #-}

module HsToCoq.ConvertHaskell.Module (
  -- * Convert whole module graphs and modules
  ConvertedModule(..),
  convertModules, convertModule,
  -- * Convert declaration groups
  ConvertedModuleDeclarations(..), convertHsGroup,
  -- * Convert import statements
  Qualification(..), ImportSpec(..), ConvertedImportDecl(..),
  convertImportDecl
) where

import Control.Lens

import Data.Traversable
import Data.Maybe
import Data.List.NonEmpty (NonEmpty(..))
import HsToCoq.Util.Containers

import Control.Monad
import Control.Monad.IO.Class
import qualified Data.Map as M

import HsToCoq.Coq.FreeVars
import HsToCoq.Coq.Gallina

import GHC hiding (Name)
import qualified GHC
import HsToCoq.Util.GHC.Module ()
import Panic
import Bag

import HsToCoq.ConvertHaskell.Parameters.Edits
import HsToCoq.ConvertHaskell.Parameters.Renamings
import HsToCoq.ConvertHaskell.Monad
import HsToCoq.ConvertHaskell.Variables
import HsToCoq.ConvertHaskell.Definitions
import HsToCoq.ConvertHaskell.Expr
import HsToCoq.ConvertHaskell.Sigs
import HsToCoq.ConvertHaskell.Declarations.TyCl
import HsToCoq.ConvertHaskell.Declarations.Instances
import HsToCoq.ConvertHaskell.Declarations.Notations
import HsToCoq.ConvertHaskell.Axiomatize

import FieldLabel
import HsToCoq.Util.GHC (ghcPpr, ghcPutPpr)

--------------------------------------------------------------------------------

data Qualification = UnqualifiedImport
                   | QualifiedImport
                   deriving (Eq, Ord, Enum, Bounded, Show, Read)

-- TODO
data ImportSpec = ExplicitImports [()]
                | ExplicitHiding  [()]
                deriving (Eq, Ord, Show, Read)

data ConvertedImportDecl =
  ConvertedImportDecl { convImportedModule  :: !ModuleName -- TODO: 'Name'?
                      , convImportQualified :: !Qualification
                      , convImportAs        :: !(Maybe ModuleName)
                      , convImportSpec      :: !(Maybe ImportSpec) }
  deriving (Eq, Ord, Show)

convertImportItem :: ConversionMonad m => IE GHC.Name -> m [Ident]
convertImportItem (IEVar       (L _ x)) = pure <$> var ExprNS x
convertImportItem (IEThingAbs  (L _ x)) = pure <$> var TypeNS x
convertImportItem (IEThingAll  (L _ x)) = undefined -- TODO
convertImportItem (IEThingWith (L _ x) NoIEWildcard subitems []) =
  (:) <$> var TypeNS x <*> traverse (var ExprNS . unLoc) subitems
convertImportItem (IEGroup          _ _)                  = pure [] -- Haddock
convertImportItem (IEDoc            _)                    = pure [] -- Haddock
convertImportItem (IEDocNamed       _)                    = pure [] -- Haddock
convertImportItem (IEThingWith      _ (IEWildcard _) _ _) = convUnsupported "import items with `IEWildcard' value"
convertImportItem (IEThingWith      _ _ _ (_:_))          = convUnsupported "import items with field label imports"
convertImportItem (IEModuleContents _)                    = convUnsupported "whole-module exports as import items"

convertImportDecl :: ConversionMonad m => ImportDecl GHC.Name -> m ConvertedImportDecl
convertImportDecl ImportDecl{..} = do
  let convImportedModule  = unLoc ideclName
      convImportQualified = if ideclQualified then QualifiedImport else UnqualifiedImport
      convImportAs        = ideclAs
  unless (isNothing ideclPkgQual) $
    convUnsupported "package-qualified imports"
  -- Ignore:
  --   * Source text (@ideclSourceSrc)@;
  --   * @{-# SOURCE #-}@ imports (@ideclSource@); and
  --   * Module safety annotations (@ideclSafe@).
  -- Also, don't treat the implicit Prelude import specially (@ideclImplicit@).
  convImportSpec <- for ideclHiding $ \(hiding, L _ spec) ->
                      (if hiding then ExplicitHiding else ExplicitImports) <$>
                        traverse ((*>) <$> (liftIO . print <=< traverse (traverse ghcPpr))  <*> ghcPutPpr) spec
  pure ConvertedImportDecl{..}

deriving instance (Show l, Show e) => Show (GenLocated l e)
deriving instance Show a => Show (FieldLbl a)
deriving instance Show IEWildcard
deriving instance Show name => Show (IE name)
deriving instance Functor IE
deriving instance Foldable IE
deriving instance Traversable IE

--------------------------------------------------------------------------------

data ConvertedModuleDeclarations =
  ConvertedModuleDeclarations { convertedTyClDecls    :: ![Sentence]
                              , convertedValDecls     :: ![Sentence]
                              , convertedClsInstDecls :: ![Sentence] }
  deriving (Eq, Ord, Show)

convertHsGroup :: ConversionMonad m => ModuleName -> HsGroup GHC.Name -> m ConvertedModuleDeclarations
convertHsGroup mod HsGroup{..} = do
  convertedTyClDecls <- convertModuleTyClDecls
                     .  map ((Just mod,) . unLoc)
                     $  concatMap group_tyclds hs_tyclds
                          -- Ignore roles
  convertedValDecls  <- -- TODO RENAMER merge with convertLocalBinds / convertModuleValDecls
    case hs_valds of
      ValBindsIn{} ->
        convUnsupported "pre-renaming `ValBindsIn' construct post renaming"
      ValBindsOut binds lsigs -> do
        sigs  <- convertLSigs lsigs
        defns <- fmap M.fromList
              .  (convertTypedBindings
                   (map unLoc $ concatMap (bagToList . snd) binds)
                   sigs
                   ??
                   (Just axiomatizeBinding))
              $  withConvertedBinding
                   (\cdef@ConvertedDefinition{convDefName = name} -> do
                      use (edits.redefinitions.at name) >>= ((name,) <$>) . \case
                        Nothing  ->
                          pure $ withConvertedDefinition
                            (DefinitionDef Global)     (pure . DefinitionSentence)
                            (buildInfixNotations sigs) (map    NotationSentence)
                            cdef
                   
                        Just def ->
                          [definitionSentence def] <$ case def of
                            CoqInductiveDef  _ -> editFailure "cannot redefine a value definition into an Inductive"
                            CoqDefinitionDef _ -> pure ()
                            CoqFixpointDef   _ -> pure ())
                   (\_ _ -> convUnsupported "top-level pattern bindings")
         
        -- TODO RENAMER use RecFlag info to do recursion stuff
        pure . foldMap (foldMap (defns M.!)) . topoSortEnvironment $ NoBinding <$> defns
  convertedClsInstDecls <- convertModuleClsInstDecls [(Just mod, cid) | L _ (ClsInstD cid) <- hs_instds]
  pure ConvertedModuleDeclarations{..}

  where axiomatizeBinding :: GhcMonad m => HsBind GHC.Name -> GhcException -> m (Ident, [Sentence])
        axiomatizeBinding FunBind{..} exn = do
          name <- freeVar $ unLoc fun_id
          pure (name, [translationFailedComment name exn, axiom name])
        axiomatizeBinding _ exn =
          liftIO $ throwGhcExceptionIO exn

--------------------------------------------------------------------------------

data ConvertedModule =
  ConvertedModule { convModName         :: !ModuleName
                  , convModImports      :: ![ConvertedImportDecl]
                  , convModTyClDecls    :: ![Sentence]
                  , convModValDecls     :: ![Sentence]
                  , convModClsInstDecls :: ![Sentence] }
  deriving (Eq, Ord, Show)

convertModule :: ConversionMonad m => ModuleName -> RenamedSource -> m ConvertedModule
convertModule convModName (group, imports, _exports, _docstring) = do
  ConvertedModuleDeclarations { convertedTyClDecls    = convModTyClDecls
                              , convertedValDecls     = convModValDecls
                              , convertedClsInstDecls = convModClsInstDecls }
    <- convertHsGroup convModName group
  convModImports <- traverse (convertImportDecl . unLoc) imports
  pure ConvertedModule{..}

convertModules :: ConversionMonad m => [(ModuleName, RenamedSource)] -> m [NonEmpty ConvertedModule]
convertModules sources = do
  mods <- traverse (uncurry convertModule) sources
  pure $ stronglyConnCompNE
    [ (cm, convModName cm, map convImportedModule $ convModImports cm) | cm <- mods ]
