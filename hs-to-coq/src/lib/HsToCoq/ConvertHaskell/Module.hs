{-# LANGUAGE TupleSections, LambdaCase, RecordWildCards, TypeApplications, FlexibleContexts, DeriveDataTypeable, OverloadedLists, OverloadedStrings, ScopedTypeVariables, MultiWayIf  #-}

module HsToCoq.ConvertHaskell.Module (
  -- * Convert whole module graphs and modules
  ConvertedModule(..),
  convertModules, convertModule, axiomatizeModule,
  -- ** Extract all the declarations from a module
  moduleDeclarations,
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
import Data.Foldable
import HsToCoq.Util.Traversable
import Data.Maybe
import Data.List.NonEmpty (NonEmpty(..))
import HsToCoq.Util.Containers

import Control.Monad
import Control.Monad.IO.Class
import Control.Exception (SomeException)
import qualified Data.Set as S
import qualified Data.Map as M

import qualified Data.Text as T

import HsToCoq.Coq.FreeVars
import HsToCoq.Coq.Gallina
import HsToCoq.Coq.Gallina.Util

import GHC hiding (Name)
import qualified GHC
import HsToCoq.Util.GHC.Module
import Panic
import Bag

import Data.Generics

import HsToCoq.ConvertHaskell.Parameters.Edits
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
  let moduleToQualid mn =
        case identToQualid (moduleNameText mn) of
            Just qi -> pure qi
            Nothing -> throwProgramError $ "malformed module name " ++ moduleNameString mn

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
                              , convertedClsInstDecls :: ![Sentence]
                              , convertedAddedDecls   :: ![Sentence]
                              }
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
                   (\cdef@ConvertedDefinition{convDefName = name} -> ((name,) <$>) $ do
                       r <- use (edits.redefinitions.at name)
                       t <- use (edits.termination.at name)
                       if | Just def <- r               -- redefined
                          -> [definitionSentence def] <$ case def of
                              CoqInductiveDef        _ -> editFailure "cannot redefine a value definition into an Inductive"
                              CoqDefinitionDef       _ -> pure ()
                              CoqFixpointDef         _ -> pure ()
                              CoqProgramFixpointDef  _ -> pure ()
                              CoqInstanceDef         _ -> editFailure "cannot redefine a value definition into an Instance"
                          | Just (order, tactic) <- t  -- turn into Program Fixpoint
                          ->  pure <$> toProgramFixpointSentence cdef order tactic
                          | otherwise                   -- no edit
                          -> pure $ withConvertedDefinition
                              (DefinitionDef Global)     (pure . DefinitionSentence)
                              (buildInfixNotations sigs) (map    NotationSentence)
                              cdef
                   ) (\_ _ -> convUnsupported "top-level pattern bindings")

        -- TODO RENAMER use RecFlag info to do recursion stuff
        pure . foldMap (foldMap (defns M.!)) . topoSortEnvironment $ NoBinding <$> defns
  convertedClsInstDecls <- convertModuleClsInstDecls [(Just mod, cid) | L _ (ClsInstD cid) <- hs_instds]

  convertedAddedDecls <- use (edits.adds.at mod.non [])

  pure ConvertedModuleDeclarations{..}

  where axiomatizeBinding :: GhcMonad m => HsBind GHC.Name -> GhcException -> m (Ident, [Sentence])
        axiomatizeBinding FunBind{..} exn = do
          name <- freeVar $ unLoc fun_id
          pure (name, [translationFailedComment name exn, axiom name])
        axiomatizeBinding _ exn =
          liftIO $ throwGhcExceptionIO exn

axiomatizeHsGroup :: ConversionMonad m => ModuleName -> HsGroup GHC.Name -> m ConvertedModuleDeclarations
axiomatizeHsGroup mod HsGroup{..} = do
  convertedTyClDecls <- convertModuleTyClDecls
                     .  map ((Just mod,) . unLoc)
                     $  concatMap group_tyclds hs_tyclds
                          -- Ignore roles
  convertedValDecls  <-
    case hs_valds of
      ValBindsIn{} ->
        convUnsupported "pre-renaming `ValBindsIn' construct post renaming"
      ValBindsOut binds lsigs -> do
        sigs  <- convertLSigs lsigs `gcatch` const @_ @SomeException (pure M.empty)
        for (map unLoc $ concatMap (bagToList . snd) binds) $ \case
          FunBind{..} -> do
            name <- freeVar $ unLoc fun_id
            pure . typedAxiom name $ sigs^.at name.to (fmap sigType).non bottomType
          _ ->
            convUnsupported "non-type, non-class, non-value definitions in axiomatized modules"
  
  convertedClsInstDecls <- convertModuleClsInstDecls [(Just mod, cid) | L _ (ClsInstD cid) <- hs_instds]

  convertedAddedDecls <- use (edits.adds.at mod.non [])

  pure ConvertedModuleDeclarations{..}

--------------------------------------------------------------------------------

require :: MonadIO f => ModuleName -> f ModuleSentence
require mn = case identToQualid (moduleNameText mn) of
    Just qi -> pure (Require Nothing Nothing (pure qi))
    Nothing -> throwProgramError $ "malformed module name " ++ moduleNameString mn

--------------------------------------------------------------------------------

data ConvertedModule =
  ConvertedModule { convModName         :: !ModuleName
                  , convModImports      :: ![Sentence]
                  , convModTyClDecls    :: ![Sentence]
                  , convModValDecls     :: ![Sentence]
                  , convModClsInstDecls :: ![Sentence]
                  , convModAddedDecls   :: ![Sentence]
                  }
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
convert_module_with_requires_via :: ConversionMonad m
                                 => (ModuleName -> HsGroup GHC.Name -> m ConvertedModuleDeclarations)
                                 -> ModuleName -> RenamedSource ->
                                 m (ConvertedModule, [ModuleName])
convert_module_with_requires_via convGroup convModName (group, _imports, _exports, _docstring) =
  withCurrentModule convModName $ do
    decls@ConvertedModuleDeclarations { convertedTyClDecls    = convModTyClDecls
                                      , convertedValDecls     = convModValDecls
                                      , convertedClsInstDecls = convModClsInstDecls
                                      , convertedAddedDecls   = convModAddedDecls
                                      }
      <- convGroup convModName group

    -- TODO: Is this the best approach to the problem where instead of
    -- 'Prelude.not', we get 'GHC.Classes.not'?
    let extraModules = map (mkModuleName . T.unpack . qualidToIdent)
                     . mapMaybe (\case Bare      x     -> qualidModule =<< identToQualid x
                                       Qualified mod _ -> Just mod)
                      $ listify (const True :: Qualid -> Bool) decls

    modules <- skipModules $ S.toList $ S.fromList extraModules

    convModImports <-
      traverse (\mn -> ModuleSentence <$> require mn) modules
    pure (ConvertedModule{..}, modules)

-- Module-local
convert_module_with_requires :: ConversionMonad m
                             => ModuleName -> RenamedSource ->
                             m (ConvertedModule, [ModuleName])
convert_module_with_requires = convert_module_with_requires_via convertHsGroup

-- Module-local
axiomatize_module_with_requires :: ConversionMonad m
                             => ModuleName -> RenamedSource ->
                             m (ConvertedModule, [ModuleName])
axiomatize_module_with_requires = convert_module_with_requires_via axiomatizeHsGroup

convertModule :: ConversionMonad m => ModuleName -> RenamedSource -> m ConvertedModule
convertModule = fmap fst .: convert_module_with_requires

axiomatizeModule :: ConversionMonad m => ModuleName -> RenamedSource -> m ConvertedModule
axiomatizeModule = fmap fst .: axiomatize_module_with_requires

-- NOT THE SAME as `traverse $ uncurry convertModule`!  Produces connected
-- components and can axiomatize individual modules as per edits
convertModules :: ConversionMonad m => [(ModuleName, RenamedSource)] -> m [NonEmpty ConvertedModule]
convertModules sources = do
  let convThisMod (mod,src) = use (edits.axiomatizedModules.contains mod) >>= \case
                                True  -> axiomatize_module_with_requires mod src
                                False -> convert_module_with_requires    mod src
  mods <- traverse convThisMod sources
  pure $ stronglyConnCompNE
    [(cmod, convModName cmod, imps) | (cmod, imps) <- mods]

moduleDeclarations :: ConversionMonad m => ConvertedModule -> m [Sentence]
moduleDeclarations ConvertedModule{..} = do
  orders <- use $ edits.orders
  let sorted = topoSortSentences orders $
        convModTyClDecls ++ convModValDecls ++ convModClsInstDecls ++ convModAddedDecls
  ax_decls <- usedAxioms sorted
  return $ ax_decls ++ sorted

usedAxioms :: forall m. ConversionMonad m => [Sentence] -> m [Sentence]
usedAxioms decls = do
    axs <- use axioms
    let ax_decls =
          [ AssumptionSentence (Assumption Axiom (UnparenthesizedAssums [i] t))
          | i <- toList (getFreeVars (NoBinding decls))
          , Just t <- return $ M.lookup i axs
          ]

        comment =
          [ CommentSentence (Comment "The Haskell code containes partial or \
             \untranslateable code, which needs the following")
          | not (null ax_decls)
          ]
    return $ comment ++ ax_decls
