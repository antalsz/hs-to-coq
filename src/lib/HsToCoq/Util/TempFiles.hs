module HsToCoq.Util.TempFiles (
  gWithTempFile, gWithSystemTempFile,
  gIgnoringIOErrors
  ) where

import Control.Monad.IO.Class

import System.IO
import System.Directory

import GHC
import Exception

-- Based on "System.IO.Temp", from the @temporary@ package

gIgnoringIOErrors :: ExceptionMonad m => m () -> m ()
gIgnoringIOErrors =
  (`gcatch` (const (pure ()) :: Applicative f => IOError -> f ()))

gWithTempFile :: ExceptionMonad m
              => FilePath -> String -> (FilePath -> Handle -> m a) -> m a
gWithTempFile tmpDir template f =
  gbracket (liftIO $ openTempFile tmpDir template)
           (\(tempF, tempH) -> liftIO (hClose tempH)
                            *> gIgnoringIOErrors (liftIO $ removeFile tempF))
           (uncurry f)

gWithSystemTempFile :: ExceptionMonad m
                    => String -> (FilePath -> Handle -> m a) -> m a
gWithSystemTempFile template f =
  liftIO getTemporaryDirectory >>= \tmpDir -> gWithTempFile tmpDir template f
