{-# LANGUAGE LambdaCase #-}

module HsToCoq.ProcessFiles (
  processFile, processFiles,
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

processFile :: GhcMonad m => DynFlags -> FilePath -> m (Maybe TypecheckedModule)
processFile dflags file = do
  -- TODO RENAMER command-line argument
  let ghcPaths = map ("/Users/antal/prog/ghc-8.0.2/compiler/" ++)
               $ words "backpack basicTypes cmm codeGen coreSyn deSugar ghci \
                       \hsSyn iface llvmGen main nativeGen parser prelude \
                       \profiling rename simplCore simplStg specialise stgSyn \
                       \stranal typecheck types utils vectorise stage2/build"
  _ <- setSessionDynFlags $ dflags{ importPaths = ghcPaths ++ importPaths dflags
                                  -- TODO: Do these go here or elsewhere?
                                  , hscTarget   = HscNothing
                                  , ghcLink     = NoLink }
  addTarget =<< guessTarget file Nothing
  load LoadAllTargets >>= \case
    Succeeded ->
      fmap Just $ typecheckModule =<< parseModule =<< getModSummary (mkModuleName $ takeBaseName file)
    Failed ->
      pure Nothing

processFiles :: GhcMonad m => DynFlags -> [FilePath] -> m (Maybe [TypecheckedModule])
processFiles dflags files = do
  -- TODO RENAMER command-line argument
  let ghcPaths = map ("/Users/antal/prog/ghc-8.0.2/compiler/" ++)
               $ words "backpack basicTypes cmm codeGen coreSyn deSugar ghci \
                       \hsSyn iface llvmGen main nativeGen parser prelude \
                       \profiling rename simplCore simplStg specialise stgSyn \
                       \stranal typecheck types utils vectorise stage2/build"
  _ <- setSessionDynFlags $ dflags{ importPaths = ghcPaths ++ importPaths dflags
                                  -- TODO: Do these go here or elsewhere?
                                  , hscTarget   = HscNothing
                                  , ghcLink     = NoLink }
  traverse_ (addTarget <=< (guessTarget ?? Nothing)) files
  load LoadAllTargets >>= \case
    Succeeded ->
      Just <$> traverse ( (typecheckModule <=< parseModule <=< getModSummary)
                        . mkModuleName . takeBaseName )
                 files
    Failed ->
      pure Nothing
