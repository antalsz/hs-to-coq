{-# LANGUAGE LambdaCase #-}

module HsToCoq.ProcessFiles (
  processFiles,
  processFileFlags, parseFileFlags
) where

import Control.Lens

import Data.Foldable

import Control.Monad
import Control.Monad.IO.Class

import System.FilePath

import GHC
import HeaderInfo
import DynFlags

import HsToCoq.Util.Messages

parseFileFlags :: GhcMonad m
               => ([Located String] -> [Located String] -> m ())
               -> DynFlags -> FilePath
               -> m DynFlags
parseFileFlags handleExtra dflags file = do
  (fileDflags, restOpts, optWarns) <-
    parseDynamicFilePragma dflags =<< liftIO (getOptionsFromFile dflags file)
  handleExtra restOpts optWarns
  void $ setSessionDynFlags fileDflags
  getSessionDynFlags

processFileFlags :: (GhcMonad m, MonadIO m) => DynFlags -> FilePath -> m DynFlags
processFileFlags = parseFileFlags $ \restOpts optWarns -> do
  printAllIfPresent unLoc "Leftover option" restOpts
  printAllIfPresent unLoc "Option warning"  optWarns

processFiles :: GhcMonad m => [FilePath] -> m (Maybe [TypecheckedModule])
processFiles files = do
  traverse_ (addTarget <=< (guessTarget ?? Nothing)) files
  load LoadAllTargets >>= \case
    Succeeded ->
      Just <$> traverse ( (typecheckModule <=< parseModule <=< getModSummary)
                        . mkModuleName . takeBaseName )
                 files
    Failed ->
      pure Nothing
