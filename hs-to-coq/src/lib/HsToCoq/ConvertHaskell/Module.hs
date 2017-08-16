{-# LANGUAGE TupleSections, LambdaCase, RecordWildCards, FlexibleContexts #-}

module HsToCoq.ConvertHaskell.Module (
  ConvertedModules,
  convertModules, convertLModules,
  hsModuleName,
  -- Renamer
  ConvertedModule(..), convertHsGroup, convertHsGroups, convertHsGroups',
  Qualification(..), ImportSpec, ConvertedImportDecl(..), convertImportDecl,
  convertRenamedSource, convertRenamedSources,
) where

import Control.Lens

import Data.Traversable
import Data.Maybe
import Data.List.NonEmpty (NonEmpty(..))
import HsToCoq.Util.Containers

import Control.Monad
import Control.Monad.IO.Class
import qualified Data.Map as M

import HsToCoq.Util.Generics

import HsToCoq.Coq.FreeVars
import HsToCoq.Coq.Gallina

import GHC hiding (Name)
import qualified GHC
import HsToCoq.Util.GHC.Module ()
import Panic
import Bag

import HsToCoq.ConvertHaskell.Parameters.Edits
import HsToCoq.ConvertHaskell.Monad
import HsToCoq.ConvertHaskell.Variables
import HsToCoq.ConvertHaskell.Definitions
import HsToCoq.ConvertHaskell.Expr
import HsToCoq.ConvertHaskell.Sigs
import HsToCoq.ConvertHaskell.Declarations.TyCl
import HsToCoq.ConvertHaskell.Declarations.Value
import HsToCoq.ConvertHaskell.Declarations.Instances
import HsToCoq.ConvertHaskell.Declarations.Notations
import HsToCoq.ConvertHaskell.Axiomatize

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

convertImportDecl :: ConversionMonad m => ImportDecl GHC.Name -> m ConvertedImportDecl
convertImportDecl ImportDecl{..} = do
  let convImportedModule  = unLoc ideclName
      convImportQualified = if ideclQualified then QualifiedImport else UnqualifiedImport
      convImportAs        = ideclAs
  unless (isNothing ideclPkgQual) $
    convUnsupported "package-qualified imports"
  -- Ignore @{-# SOURCE #-}@, safety
  -- Treat implicit Prelude import as explicit
  convImportSpec <- for ideclHiding $ \(hiding, L _ spec) ->
                      (if hiding then ExplicitHiding else ExplicitImports) <$>
                        traverse (const $ pure ()) spec
  pure ConvertedImportDecl{..}

--------------------------------------------------------------------------------

hsModuleName :: HsModule name -> ModuleName
hsModuleName = maybe (mkModuleName "Main") unLoc . hsmodName

type ConvertedModules = [Sentence]

convertModules :: (Foldable f, ConversionMonad m) => f (HsModule RdrName) -> m ConvertedModules
convertModules mods = do

  let forModules convert = convert $ foldMap (\mod -> map (Just $ hsModuleName mod,)
                                                          (everythingOfType_ mod))
                                             mods
  _ <- forModules recordFixitiesWithErrors

  tyClsDecls <-   forModules convertModuleTyClDecls
  valDecls   <-   forModules convertModuleValDecls
  clsInstDecls <- forModules convertModuleClsInstDecls
  return $ tyClsDecls ++ valDecls ++ clsInstDecls

convertLModules :: (Traversable f, ConversionMonad m)
                => f (Located (HsModule RdrName)) -> m ConvertedModules
convertLModules = convertModules . fmap unLoc

type ConvertedModuleDeclarations = [Sentence]

convertHsGroup :: ConversionMonad m => ModuleName -> HsGroup GHC.Name -> m ConvertedModuleDeclarations
convertHsGroup mod HsGroup{..} = do
  convertedTyClDecls' <- convertModuleTyClDecls
                      .  map ((Just mod,) . unLoc)
                      $  concatMap group_tyclds hs_tyclds
                           -- Ignore roles
  convertedValDecls'  <- -- TODO RENAMER merge with convertLocalBinds / convertModuleValDecls
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
  convertedClsInstDecls' <- convertModuleClsInstDecls [(Just mod, cid) | L _ (ClsInstD cid) <- hs_instds]
  pure $ convertedTyClDecls' ++ convertedValDecls' ++ convertedClsInstDecls'

  where axiomatizeBinding :: GhcMonad m => HsBind GHC.Name -> GhcException -> m (Ident, [Sentence])
        axiomatizeBinding FunBind{..} exn = do
          name <- freeVar $ unLoc fun_id
          pure (name, [translationFailedComment name exn, axiom name])
        axiomatizeBinding _ exn =
          liftIO $ throwGhcExceptionIO exn

convertHsGroups :: ConversionMonad m => [(ModuleName, HsGroup GHC.Name)] -> m ConvertedModules
convertHsGroups = fmap concat . mapM (uncurry convertHsGroup)

convertHsGroups' :: ConversionMonad m => [(ModuleName, HsGroup GHC.Name)] -> m [(ModuleName, ConvertedModuleDeclarations)]
convertHsGroups' = traverse $ \(m,g) -> (m,) <$> convertHsGroup m g

data ConvertedModule =
  ConvertedModule { convModName     :: !ModuleName
                  , convModImports  :: ![ConvertedImportDecl]
                  , convModBody     :: ![Sentence]
                  }
  deriving (Eq, Ord, Show)

convertRenamedSource :: ConversionMonad m => ModuleName -> RenamedSource -> m ConvertedModule
convertRenamedSource convModName (group, imports, _exports, _docstring) = do
  convModBody <- convertHsGroup convModName group
  convModImports <- traverse (convertImportDecl . unLoc) imports
  pure $ ConvertedModule{..}

convertRenamedSources :: ConversionMonad m => [(ModuleName, RenamedSource)] -> m [NonEmpty ConvertedModule]
convertRenamedSources sources = do
  mods <- traverse (uncurry convertRenamedSource) sources
  pure $ stronglyConnCompNE
    [ (cm, convModName cm, map convImportedModule $ convModImports cm) | cm <- mods ]
