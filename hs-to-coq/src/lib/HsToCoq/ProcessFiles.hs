{-# LANGUAGE LambdaCase #-}

module HsToCoq.ProcessFiles (ProcessingMode(..), processFiles) where

import Control.Lens
import Data.Foldable
import Control.Monad
import System.FilePath
import GHC

data ProcessingMode = Recursive | NonRecursive
                    deriving (Eq, Ord, Enum, Bounded, Show, Read)

processFiles :: GhcMonad m => ProcessingMode -> [FilePath] -> m (Maybe [TypecheckedModule])
processFiles mode files = do
  traverse_ (addTarget <=< (guessTarget ?? Nothing)) files
  load LoadAllTargets >>= \case
    Succeeded ->
      fmap Just . traverse (typecheckModule <=< parseModule) =<< case mode of
        Recursive    -> getModuleGraph
        NonRecursive -> traverse (getModSummary . mkModuleName . takeBaseName) files
    Failed ->
      pure Nothing
