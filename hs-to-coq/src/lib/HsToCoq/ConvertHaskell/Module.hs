{-# LANGUAGE TupleSections, LambdaCase, RecordWildCards, FlexibleContexts #-}
{-# LANGUAGE StandaloneDeriving, DeriveFunctor, DeriveFoldable, DeriveTraversable, DeriveDataTypeable #-}

module HsToCoq.ConvertHaskell.Module (
  -- * Convert whole module graphs and modules
  ConvertedModule(..),
  convertModules, convertModule,
  -- * Convert declaration groups
  ConvertedModuleDeclarations(..), convertHsGroup,
  -- * Turn import statements into @Require@s, unconditionally
  require,
  -- * Convert import statements (INCOMPLETE -- TODO)
  Qualification(..), ImportSpec(..), ConvertedImportDecl(..),
  convertImportDecl, importDeclSentences,
) where

import Control.Lens

import HsToCoq.Util.Function
import Data.Traversable
import HsToCoq.Util.Traversable
import Data.Maybe
import Data.List.NonEmpty (NonEmpty(..))
import HsToCoq.Util.Containers

import Control.Monad
import Control.Monad.IO.Class
import qualified Data.Set as S
import qualified Data.Map as M

import qualified Data.Text as T

import HsToCoq.Coq.FreeVars
import HsToCoq.Coq.Gallina
import HsToCoq.Coq.Gallina.Util

import GHC hiding (Name)
import qualified GHC
import HsToCoq.Util.GHC.Module ()
import Panic
import Bag

import Data.Generics

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

--------------------------------------------------------------------------------

-- TODO: We're just doing qualified imports for now, so the details here aren't
-- fully finished

data Qualification = UnqualifiedImport
                   | QualifiedImport
                   deriving (Eq, Ord, Enum, Bounded, Show, Read)

data ImportSpec = ExplicitImports [Ident]
                | ExplicitHiding  [Ident]
                deriving (Eq, Ord, Show, Read)

data ConvertedImportDecl =
  ConvertedImportDecl { convImportedModule  :: !ModuleName -- TODO: 'Name'?
                      , convImportQualified :: !Qualification
                      , convImportAs        :: !(Maybe ModuleName)
                      , convImportSpec      :: !(Maybe ImportSpec) }
  deriving (Eq, Ord, Show)

-- TODO: Import all type class instances
convertImportItem :: ConversionMonad m => IE GHC.Name -> m [Ident]
convertImportItem (IEVar       (L _ x)) = pure <$> var ExprNS x
convertImportItem (IEThingAbs  (L _ x)) = pure <$> var TypeNS x
convertImportItem (IEThingAll  (L _ _)) =
  pure [] -- FIXME convUnsupported "(..)-exports"
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
                        foldTraverse (convertImportItem . unLoc) spec
  pure ConvertedImportDecl{..}

importDeclSentences :: ConversionMonad m => ConvertedImportDecl -> m [Sentence]
importDeclSentences ConvertedImportDecl{..} = do
  let moduleToQualid = maybe (throwProgramError "malformed module name") pure
                     . identToQualid . T.pack . moduleNameString
  
  mod <- moduleToQualid convImportedModule
  let importSentence = ModuleSentence $ Require Nothing
                                                (case convImportQualified of
                                                   UnqualifiedImport -> Just Import
                                                   QualifiedImport   -> Nothing)
                                                (mod :| [])
  
  asSentence <- case convImportAs of
    Just short -> do
      coqShort <- moduleToQualid short
      pure [ModuleSentence $ ModuleAssignment coqShort mod]
    Nothing    ->
      pure []
  
  importItems <- case convImportSpec of
    Just (ExplicitImports importItems) -> do
      pure $ [ NotationSentence . NotationBinding $
                 NotationIdentBinding imp (Qualid $ Qualified mod imp)
             | imp <- importItems ]
    Just (ExplicitHiding _) ->
      pure [] -- FIXME convUnsupported "import hiding"
    Nothing ->
      pure []

  pure $  importSentence
       :  asSentence
       ++ importItems

--------------------------------------------------------------------------------

data ConvertedModuleDeclarations =
  ConvertedModuleDeclarations { convertedTyClDecls    :: ![Sentence]
                              , convertedValDecls     :: ![Sentence]
                              , convertedClsInstDecls :: ![Sentence] }
  deriving (Eq, Ord, Show, Data)

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

require :: ModuleName -> Maybe ModuleSentence
require = fmap (Require Nothing Nothing . pure) . identToQualid . T.pack . moduleNameString

--------------------------------------------------------------------------------

data ConvertedModule =
  ConvertedModule { convModName         :: !ModuleName
                  , convModImports      :: ![Sentence]
                  , convModTyClDecls    :: ![Sentence]
                  , convModValDecls     :: ![Sentence]
                  , convModClsInstDecls :: ![Sentence] }
  deriving (Eq, Ord, Show)

-- Module-local
{-
convert_module_with_imports :: ConversionMonad m
                            => ModuleName -> RenamedSource ->
                            m (ConvertedModule, [ConvertedImportDecl])
convert_module_with_imports convModName (group, imports, _exports, _docstring) =
  withCurrentModule convModName $ do
    ConvertedModuleDeclarations { convertedTyClDecls    = convModTyClDecls
                                , convertedValDecls     = convModValDecls
                                , convertedClsInstDecls = convModClsInstDecls }
      <- convertHsGroup convModName group
    convImports    <- traverse (convertImportDecl . unLoc) imports
    convModImports <- foldTraverse importDeclSentences convImports
    pure (ConvertedModule{..}, convImports)
-}

-- Module-local
convert_module_with_requires :: ConversionMonad m
                             => ModuleName -> RenamedSource ->
                             m (ConvertedModule, [ModuleName])
convert_module_with_requires convModName (group, imports, _exports, _docstring) =
  withCurrentModule convModName $ do
    decls@ConvertedModuleDeclarations { convertedTyClDecls    = convModTyClDecls
                                      , convertedValDecls     = convModValDecls
                                      , convertedClsInstDecls = convModClsInstDecls }
      <- convertHsGroup convModName group
    
    let importedModules = map (unLoc . ideclName . unLoc) imports
    -- TODO: Is this the best approach to the problem where instead of
    -- 'Prelude.not', we get 'GHC.Classes.not'?
    let extraModules = map (mkModuleName . T.unpack . qualidToIdent)
                     . mapMaybe (\case Bare      x     -> qualidModule =<< identToQualid x
                                       Qualified mod _ -> Just mod)
                      $ listify (const True :: Qualid -> Bool) decls
    
    let modules =  importedModules
                ++ S.toList (foldr S.delete (S.fromList extraModules) importedModules)
    
    convModImports <-
      traverse
        ( maybe (throwProgramError "malformed module name") (pure . ModuleSentence)
        . require )
        modules
    pure (ConvertedModule{..}, modules)

convertModule :: ConversionMonad m => ModuleName -> RenamedSource -> m ConvertedModule
convertModule = fmap fst .: convert_module_with_requires

convertModules :: ConversionMonad m => [(ModuleName, RenamedSource)] -> m [NonEmpty ConvertedModule]
convertModules sources = do
  mods <- traverse (uncurry convert_module_with_requires) sources
  pure $ stronglyConnCompNE
    [(cmod, convModName cmod, imps) | (cmod, imps) <- mods]
