{-# LANGUAGE FlexibleContexts, LambdaCase #-}

module HsToCoq.ProcessFiles (ProcessingMode(..), processFiles) where

import Control.Lens

import Data.Foldable
import Control.Monad
import Control.Monad.IO.Class

import qualified Data.Set as S

import System.Directory

import GHC

import HsToCoq.ConvertHaskell.Monad
import HsToCoq.Util.GHC.Deriving

--------------------------------------------------------------------------------

data ProcessingMode = Recursive | NonRecursive
                    deriving (Eq, Ord, Enum, Bounded, Show, Read)

processFiles :: ConversionMonad m => ProcessingMode -> [FilePath] -> m (Maybe [TypecheckedModule])
processFiles mode files = do
  initForDeriving
  traverse_ (addTarget <=< (guessTarget ?? Nothing)) files
  load LoadAllTargets >>= \case
    Succeeded -> Just <$> do
      filterModules <- case mode of
        Recursive    -> pure pure
        NonRecursive -> do
          let canonicalizePaths trav = traverse (liftIO . canonicalizePath) trav
          filePaths <- S.fromList . map Just <$> canonicalizePaths files
          let moduleFile = canonicalizePaths . ml_hs_file . ms_location
          pure . filterM $ fmap (`S.member` filePaths) . moduleFile
      traverse (addDerivedInstances <=< typecheckModule <=< parseModule)
        =<< skipModulesBy ms_mod_name
        =<< filterModules
        =<< getModuleGraph
    Failed ->
      pure Nothing
