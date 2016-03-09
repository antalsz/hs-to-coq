{-# LANGUAGE LambdaCase #-}

module HsToCoq.CLI (
  processFilesMain,
  convertDecls,
  processArgs,
  prettyPrint
  ) where

import Data.Foldable
import Data.List (intersperse)

import Control.Monad
import Control.Monad.IO.Class

import Data.Data

import System.IO
import System.Environment

import GHC
import DynFlags

import HsToCoq.Util.Generics
import HsToCoq.Util.Messages
import HsToCoq.PrettyPrint
import HsToCoq.Coq.Gallina
import HsToCoq.ProcessFiles
import HsToCoq.ConvertHaskell

prettyPrint :: MonadIO m => Doc -> m ()
prettyPrint = liftIO . displayIO stdout . renderPretty 0.67 120

processArgs :: GhcMonad m => m (DynFlags, [FilePath])
processArgs = do
  (dflags, files, warnings) <- join $
    parseDynamicFlagsCmdLine
      <$> getSessionDynFlags
      <*> (map (mkGeneralLocated "command line") <$> liftIO getArgs)
  printAllIfPresent unLoc "Command-line argument warning" warnings
  void $ setSessionDynFlags dflags
  pure (dflags, map unLoc files)

convertDecls :: (Data a, GhcMonad m) => a -> m ()
convertDecls lmod = convertTyClDecls (everythingOfType_ lmod) >>= liftIO . \case
  [] -> putStrLn "(* No data type declarations to convert. *)"
  ds -> do putStrLn "(* Converted data type declarations: *)"
           traverse_ prettyPrint . intersperse line $
             map ((<> line) . renderGallina) ds

processFilesMain :: GhcMonad m => ([Located (HsModule RdrName)] -> m a) -> m ()
processFilesMain f = traverse_ f =<< uncurry processFiles =<< processArgs
