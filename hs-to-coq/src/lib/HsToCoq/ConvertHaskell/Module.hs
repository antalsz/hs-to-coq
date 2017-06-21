{-# LANGUAGE TupleSections, LambdaCase, RecordWildCards, FlexibleContexts #-}

module HsToCoq.ConvertHaskell.Module (
  ConvertedModules(..),
  convertModules, convertLModules,
  hsModuleName,
  -- Renamer
  ConvertedModule(..), convertHsGroup, convertHsGroups,
) where

import Control.Lens

import Data.Semigroup

import Control.Monad.IO.Class
import qualified Data.Map as M

import HsToCoq.Util.Generics

import HsToCoq.Coq.FreeVars
import HsToCoq.Coq.Gallina

import GHC
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

hsModuleName :: HsModule name -> ModuleName
hsModuleName = maybe (mkModuleName "Main") unLoc . hsmodName

data ConvertedModules = ConvertedModules { convertedTyClDecls    :: ![Sentence]
                                         , convertedValDecls     :: ![Sentence]
                                         , convertedClsInstDecls :: ![Sentence] }
                      deriving (Eq, Ord, Show)

instance Semigroup ConvertedModules where
  ConvertedModules tcds1 vds1 cids1 <> ConvertedModules tcds2 vds2 cids2 =
    ConvertedModules (tcds1 <> tcds2) (vds1 <> vds2) (cids1 <> cids2)

instance Monoid ConvertedModules where
  mempty  = ConvertedModules mempty mempty mempty
  mappend = (<>)

convertModules :: (Foldable f, ConversionMonad m) => f (HsModule RdrName) -> m ConvertedModules
convertModules mods = do

  let forModules convert = convert $ foldMap (\mod -> map (Just $ hsModuleName mod,)
                                                          (everythingOfType_ mod))
                                             mods
  _ <- forModules recordFixitiesWithErrors

  ConvertedModules <$> forModules convertModuleTyClDecls
                   <*> forModules convertModuleValDecls
                   <*> forModules convertModuleClsInstDecls

convertLModules :: (Traversable f, ConversionMonad m)
                => f (Located (HsModule RdrName)) -> m ConvertedModules
convertLModules = convertModules . fmap unLoc

data ConvertedModule = ConvertedModule { convertedTyClDecls'    :: ![Sentence]
                                       , convertedValDecls'     :: ![Sentence]
                                       , convertedClsInstDecls' :: ![Sentence] }
                      deriving (Eq, Ord, Show)

convertHsGroup :: ConversionMonad m => ModuleName -> HsGroup GHC.Name -> m ConvertedModule
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
  pure ConvertedModule{..}

  where axiomatizeBinding :: GhcMonad m => HsBind GHC.Name -> GhcException -> m (Ident, [Sentence])
        axiomatizeBinding FunBind{..} exn = do
          name <- freeVar $ unLoc fun_id
          pure (name, [translationFailedComment name exn, axiom name])
        axiomatizeBinding _ exn =
          liftIO $ throwGhcExceptionIO exn

convertHsGroups :: ConversionMonad m => [(ModuleName, HsGroup GHC.Name)] -> m ConvertedModules
convertHsGroups = fmap (foldMap pluralize) . traverse (uncurry convertHsGroup) where
  pluralize (ConvertedModule tcds vds cids) = ConvertedModules tcds vds cids
