{-# LANGUAGE LambdaCase #-}

module HsToCoq.ProcessFiles (ProcessingMode(..), processFiles) where

import Control.Lens

import Data.Foldable
import Control.Monad
import Control.Monad.IO.Class

import qualified Data.Set as S

import System.Directory

import GHC

--------------------------------------------------------------------------------

data ProcessingMode = Recursive | NonRecursive
                    deriving (Eq, Ord, Enum, Bounded, Show, Read)

processFiles :: GhcMonad m => ProcessingMode -> [FilePath] -> m (Maybe [TypecheckedModule])
processFiles mode files = do
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
      traverse (typecheckModule <=< parseModule) =<< filterModules =<< getModuleGraph
    Failed ->
      pure Nothing
