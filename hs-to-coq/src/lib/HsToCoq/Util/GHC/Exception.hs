{-# OPTIONS_GHC -fno-warn-orphans #-}

module HsToCoq.Util.GHC.Exception (module Exception, gWithFile) where

import Control.Monad.IO.Class
import System.IO

import Exception

import qualified Control.Monad.Trans.Identity      as I
import qualified Control.Monad.Trans.Reader        as R
import qualified Control.Monad.Trans.Writer.Strict as WS
import qualified Control.Monad.Trans.Writer.Lazy   as WL
import qualified Control.Monad.Trans.State.Strict  as SS
import qualified Control.Monad.Trans.State.Lazy    as SL
import qualified Control.Monad.Trans.RWS.Strict    as RWSS
import qualified Control.Monad.Trans.RWS.Lazy      as RWSL

instance ExceptionMonad m => ExceptionMonad (I.IdentityT m) where
  gcatch  = I.liftCatch gcatch
  gmask f = I.IdentityT . gmask $ I.runIdentityT . f . I.mapIdentityT

instance ExceptionMonad m => ExceptionMonad (R.ReaderT r m) where
  gcatch  = R.liftCatch gcatch
  gmask f = R.ReaderT $ \env -> gmask $ flip R.runReaderT env . f . R.mapReaderT

instance (ExceptionMonad m, Monoid w) => ExceptionMonad (WS.WriterT w m) where
  gcatch = WS.liftCatch gcatch
  gmask f = WS.WriterT . gmask $ WS.runWriterT . f . WS.mapWriterT

instance (ExceptionMonad m, Monoid w) => ExceptionMonad (WL.WriterT w m) where
  gcatch  = WL.liftCatch gcatch
  gmask f = WL.WriterT . gmask $ WL.runWriterT . f . WL.mapWriterT

instance ExceptionMonad m => ExceptionMonad (SS.StateT s m) where
  gcatch = SS.liftCatch gcatch
  gmask f = SS.StateT $ \s -> gmask $ flip SS.runStateT s . f . SS.mapStateT

instance ExceptionMonad m => ExceptionMonad (SL.StateT s m) where
  gcatch  = SL.liftCatch gcatch
  gmask f = SL.StateT $ \s -> gmask $ flip SL.runStateT s . f . SL.mapStateT

instance (ExceptionMonad m, Monoid w) => ExceptionMonad (RWSS.RWST r w s m) where
  gcatch = RWSS.liftCatch gcatch
  gmask f = RWSS.RWST $ \r s -> gmask $ (\m -> RWSS.runRWST m r s) . f . RWSS.mapRWST

instance (ExceptionMonad m, Monoid w) => ExceptionMonad (RWSL.RWST r w s m) where
  gcatch  = RWSL.liftCatch gcatch
  gmask f = RWSL.RWST $ \r s -> gmask $ (\m -> RWSL.runRWST m r s) . f . RWSL.mapRWST

-- Other MTL transformers will be added as necessary

gWithFile :: ExceptionMonad m => FilePath -> IOMode -> (Handle -> m r) -> m r
gWithFile file mode = gbracket (liftIO $ openFile file mode) (liftIO . hClose)
