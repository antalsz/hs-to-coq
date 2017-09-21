{-# LANGUAGE LambdaCase #-}

module HsToCoq.ProcessFiles (processFiles) where

import Control.Lens
import Data.Foldable
import Control.Monad
import System.FilePath
import GHC

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
