{-# OPTIONS_GHC -fno-warn-orphans #-}

module HsToCoq.Util.GHC.Exception (module Exception, gWithFile) where

import Control.Monad.IO.Class
import System.IO

import Exception

import qualified Control.Monad.Trans.Identity     as I
import qualified Control.Monad.Trans.Reader       as R
import qualified Control.Monad.Trans.State.Strict as SS
import qualified Control.Monad.Trans.State.Lazy   as SL

instance ExceptionMonad m => ExceptionMonad (I.IdentityT m) where
  m `gcatch` h = I.IdentityT $ I.runIdentityT m `gcatch` (I.runIdentityT . h)

  gmask f = I.IdentityT $ gmask (I.runIdentityT . f . I.mapIdentityT)

instance ExceptionMonad m => ExceptionMonad (R.ReaderT r m) where
  m `gcatch` h = R.ReaderT $ \env ->
    R.runReaderT m env `gcatch` (flip R.runReaderT env . h)

  gmask f = R.ReaderT $ \env ->
    gmask $ flip R.runReaderT env . f . R.mapReaderT

instance ExceptionMonad m => ExceptionMonad (SS.StateT s m) where
  m `gcatch` h = SS.StateT $ \s ->
    SS.runStateT m s `gcatch` (flip SS.runStateT s . h)

  gmask f = SS.StateT $ \s ->
    gmask $ flip SS.runStateT s . f . SS.mapStateT

instance ExceptionMonad m => ExceptionMonad (SL.StateT s m) where
  m `gcatch` h = SL.StateT $ \s ->
    SL.runStateT m s `gcatch` (flip SL.runStateT s . h)

  gmask f = SL.StateT $ \s ->
    gmask $ flip SL.runStateT s . f . SL.mapStateT

-- Other MTL transformers will be added as necessary

gWithFile :: ExceptionMonad m => FilePath -> IOMode -> (Handle -> m r) -> m r
gWithFile file mode = gbracket (liftIO $ openFile file mode) (liftIO . hClose)
