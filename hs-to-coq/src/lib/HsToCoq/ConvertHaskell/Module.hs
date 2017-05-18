{-# LANGUAGE TupleSections, RecordWildCards, FlexibleContexts #-}

module HsToCoq.ConvertHaskell.Module (
  ConvertedModules(..),
  convertModules, convertLModules,
  hsModuleName
) where

import Data.Semigroup
import Data.Foldable (toList)

import HsToCoq.Util.Generics

import HsToCoq.Coq.Gallina

import GHC
import HsToCoq.Util.GHC.Module ()

import HsToCoq.ConvertHaskell.Monad
import HsToCoq.ConvertHaskell.Declarations.TyCl
import HsToCoq.ConvertHaskell.Declarations.Value
import HsToCoq.ConvertHaskell.Declarations.Instances
import HsToCoq.ConvertHaskell.Sigs

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
