{-# LANGUAGE LambdaCase #-}

module HsToCoq.ProcessFiles (processFile, processFiles, processFileFlags, parseFileFlags) where

import Control.Monad
import Control.Monad.IO.Class
import Control.Monad.Trans.Maybe

import System.FilePath

import GHC
import HeaderInfo
import DynFlags
import qualified GHC.LanguageExtensions as LangExt
import Bag
import HsToCoq.Util.GHC.DoCpp

import HsToCoq.Util.TempFiles
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

processFile :: GhcMonad m => DynFlags -> FilePath -> m (Maybe (Located (HsModule RdrName)))
processFile dflags file = do
  withSrcFile <- do
    dflags' <- processFileFlags dflags file
    pure $ if not $ xopt LangExt.Cpp dflags'
           then \fn -> fn dflags' file
           else \fn -> gWithSystemTempFile (takeFileName file) $ \temp _ -> do
                         liftIO $ doCpp dflags' True file temp
                         dflags'' <- processFileFlags dflags temp
                         fn dflags'' temp
  
  withSrcFile $ \fileDflags srcFile ->
    parser <$> liftIO (readFile srcFile) <*> pure fileDflags <*> pure file >>= \case
      Left  errs          -> Nothing   <$ printMessages "failed" "error" errs
      Right (warns, lmod) -> Just lmod <$ printMessages "succeeded" "warning" warns
  where
    printMessages result msgType =
      printAll' show
                ("Parsing `" ++ file ++ "' " ++ result)
                (" with " ++ msgType)
      . bagToList

processFiles :: GhcMonad m => DynFlags -> [FilePath] -> m (Maybe [Located (HsModule RdrName)])
processFiles dflags = runMaybeT . traverse (MaybeT . processFile dflags)
