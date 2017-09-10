{-# LANGUAGE LambdaCase #-}

module HsToCoq.ProcessFiles (
  processFile, processFiles,
  processFileFlags, parseFileFlags,
  -- Renamer
  tcRnFile, tcRnFiles
) where

import Control.Lens

import Data.Foldable

import Control.Monad
import Control.Monad.IO.Class
import Control.Monad.Trans.Maybe

import System.FilePath

import GHC
import HeaderInfo
import DynFlags
import Bag
import Digraph (flattenSCC)
import Outputable
import qualified GHC.LanguageExtensions as LangExt

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

tcRnFile :: GhcMonad m => DynFlags -> FilePath -> m (Maybe TypecheckedModule)
tcRnFile dflags file = do
  _ <- setSessionDynFlags $ dflags{ -- TODO: Do these go here or elsewhere?
                                    hscTarget   = HscNothing
                                  , ghcLink     = NoLink }
  addTarget =<< guessTarget file Nothing
  load LoadAllTargets >>= \case
    Succeeded -> do
      -- Try to find the module name. Should be the last in the ModuleGraph?
      mod_graph <- getModuleGraph
      let mod_graph_sorted = concatMap flattenSCC $
            topSortModuleGraph True mod_graph Nothing
      let mod_summary = last mod_graph_sorted
      pprTrace "processFiles" (ppr mod_summary) (return ())
      parsed_mod <- parseModule mod_summary
      typechecked_mod <- typecheckModule parsed_mod
      return (Just typechecked_mod)
    Failed ->
      pure Nothing

tcRnFiles :: GhcMonad m => DynFlags -> [FilePath] -> m (Maybe [TypecheckedModule])
tcRnFiles dflags files = do
  _ <- setSessionDynFlags $ dflags{ -- TODO: Do these go here or elsewhere?
                                    hscTarget   = HscNothing
                                  , ghcLink     = NoLink }
  traverse_ (addTarget <=< (guessTarget ?? Nothing)) files
  load LoadAllTargets >>= \case
    Succeeded -> do
      -- Try to find the modules.
      -- Code smell: How likely is it that the filename in the mod_summary is
      -- identical to the one on the command line (e.g. relative vs.
      -- absolute)?
      mod_graph <- getModuleGraph
      let our_mods = [ mod_summary
                     | mod_summary <- mod_graph
                     , Just path <- return $ ml_hs_file $ ms_location mod_summary
                     , path `elem` files
                     ]
      Just <$> traverse (typecheckModule <=< parseModule ) our_mods
    Failed ->
      pure Nothing
