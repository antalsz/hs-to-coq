module HsToCoq.Util.GHC (
  defaultRunGhc,
  ghcSDoc, ghcPpr, ghcPutPpr
  ) where

import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Text.IO as T

import Control.Monad
import Control.Monad.IO.Class

import GHC
import GHC.Paths
import DynFlags
import Outputable

ghcSDoc :: GhcMonad m => SDoc -> m Text
ghcSDoc x = fmap T.pack $ showSDoc <$> getSessionDynFlags <*> pure x

ghcPpr :: (GhcMonad m, Outputable a) => a -> m Text
ghcPpr x = fmap T.pack $ showPpr <$> getSessionDynFlags <*> pure x

ghcPutPpr :: (GhcMonad m, Outputable a) => a -> m ()
ghcPutPpr = liftIO . T.putStrLn <=< ghcPpr

defaultRunGhc :: Ghc a -> IO a
defaultRunGhc ghc = defaultErrorHandler defaultFatalMessager defaultFlushOut
                  . runGhc (Just libdir) $ do
                      void $ setSessionDynFlags =<< getSessionDynFlags
                      ghc
