module HsToCoq.Util.GHC (
  defaultRunGhc,
  ghcSDoc, ghcPpr, ghcPutPpr
  ) where

import Control.Monad
import Control.Monad.IO.Class

import GHC
import GHC.Paths
import DynFlags
import Outputable

ghcSDoc :: GhcMonad m => SDoc -> m String
ghcSDoc x = showSDoc <$> getSessionDynFlags <*> pure x

ghcPpr :: (GhcMonad m, Outputable a) => a -> m String
ghcPpr x = showPpr <$> getSessionDynFlags <*> pure x

ghcPutPpr :: (GhcMonad m, Outputable a) => a -> m ()
ghcPutPpr = liftIO . putStrLn <=< ghcPpr

defaultRunGhc :: Ghc a -> IO a
defaultRunGhc ghc = defaultErrorHandler defaultFatalMessager defaultFlushOut
                  . runGhc (Just libdir) $ do
                      void $ setSessionDynFlags =<< getSessionDynFlags
                      ghc
