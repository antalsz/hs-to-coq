module HsToCoq.Util.Monad.ListT (ListT(), runListT, MonadList(..), listT) where

import Data.Foldable

import Pipes hiding (runListT)
import Pipes.Prelude

import qualified Control.Monad.Trans.Identity           as I
import qualified Control.Monad.Trans.Reader             as R
import qualified Control.Monad.Trans.Writer.Strict      as WS
import qualified Control.Monad.Trans.Writer.Lazy        as WL
import qualified Control.Monad.Trans.State.Strict       as SS
import qualified Control.Monad.Trans.State.Lazy         as SL
import qualified Control.Monad.Trans.RWS.Strict         as RWSS
import qualified Control.Monad.Trans.RWS.Lazy           as RWSL
import qualified Control.Monad.Trans.Maybe              as M
import qualified Control.Monad.Trans.Except             as E
import qualified Control.Monad.Trans.Cont               as C
import qualified Control.Monad.Trans.Variables.Internal as V
import qualified HsToCoq.Util.GHC.Monad                 as GHC

--------------------------------------------------------------------------------

runListT :: Monad m => ListT m a -> m [a]
runListT = toListM . enumerate

class Monad m => MonadList m where
  list :: Foldable t => t a -> m a

instance Monad m => MonadList (ListT m) where
  list = Select . each

listT :: (Monad m, Foldable t) => t (m a) -> ListT m a
listT = Select . traverse_ ((yield =<<) . lift)

--------------------------------------------------------------------------------

instance MonadList m => MonadList (I.IdentityT m) where
  list = lift . list

instance MonadList m => MonadList (R.ReaderT r m) where
  list = lift . list

instance (MonadList m, Monoid w) => MonadList (WS.WriterT w m) where
  list = lift . list

instance (MonadList m, Monoid w) => MonadList (WL.WriterT w m) where
  list = lift . list

instance MonadList m => MonadList (SS.StateT s m) where
  list = lift . list

instance MonadList m => MonadList (SL.StateT s m) where
  list = lift . list

instance (MonadList m, Monoid w) => MonadList (RWSS.RWST r w s m) where
  list = lift . list

instance (MonadList m, Monoid w) => MonadList (RWSL.RWST r w s m) where
  list = lift . list

instance MonadList m => MonadList (M.MaybeT m) where
  list = lift . list

instance MonadList m => MonadList (E.ExceptT e m) where
  list = lift . list

instance MonadList m => MonadList (C.ContT r m) where
  list = lift . list

instance (MonadList m, Ord i) => MonadList (V.VariablesT i d m) where
  list = lift . list

instance MonadList m => MonadList (GHC.GhcT m) where
  list = lift . list
