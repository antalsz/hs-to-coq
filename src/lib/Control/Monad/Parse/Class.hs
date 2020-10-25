{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeFamilies #-}

module Control.Monad.Parse.Class (
  -- * The 'MonadParse' type class
  MonadParse(..),
  -- * Derived 'ParseT' operations
  parseToken, parseCharTokenLookahead,
  -- ** Lower-level operations
  parseChar, parseChars,
) where

import Control.Monad

import HsToCoq.Util.Function

import Data.Text (Text)
import qualified Data.Text as T

import Control.Monad.Trans
import qualified Control.Monad.Trans.Identity      as I
import qualified Control.Monad.Trans.Reader        as R
import qualified Control.Monad.Trans.Writer.Strict as WS
import qualified Control.Monad.Trans.Writer.Lazy   as WL
import qualified Control.Monad.Trans.State.Strict  as SS
import qualified Control.Monad.Trans.State.Lazy    as SL
import qualified Control.Monad.Trans.RWS.Strict    as RWSS
import qualified Control.Monad.Trans.RWS.Lazy      as RWSL
import qualified Control.Monad.Trans.Maybe         as M

import qualified Control.Monad.Trans.Parse as P

--------------------------------------------------------------------------------
-- 'MonadParse'
--------------------------------------------------------------------------------

class MonadPlus m => MonadParse m where
  liftParse  :: P.Parse a -> m a
  peekChar   :: m (Maybe Char)
  atEOF      :: m Bool
  parseError :: String -> m void

  default liftParse :: DeriveMonadParse m t n => P.Parse a -> m a
  liftParse = lift . liftParse

  default peekChar :: DeriveMonadParse m t n => m (Maybe Char)
  peekChar = lift peekChar

  default atEOF :: DeriveMonadParse m t n => m Bool
  atEOF = lift atEOF

  default parseError :: DeriveMonadParse m t n => String -> m void
  parseError = lift . parseError

type DeriveMonadParse m t n = (m ~ t n, MonadTrans t, Monad (t n), MonadParse n)

parseChar :: MonadParse m => (Char -> Bool) -> m Char
parseChar = liftParse . P.parseChar

parseChars :: MonadParse m => (Char -> Bool) -> m Text
parseChars = liftParse . P.parseChars

parseToken :: MonadParse m
           => (Text -> a)
           -> (Char -> Bool)
           -> (Char -> Bool)
           -> m a
parseToken build isFirst isRest =
  build .: T.cons <$> parseChar isFirst <*> parseChars isRest

parseCharTokenLookahead :: MonadParse m
                        => (Text -> a)
                        -> (Char -> Bool)
                        -> (Maybe Char -> Bool)
                        -> m a
parseCharTokenLookahead build isFirst isNext = do
  c <- parseChar isFirst
  guard . isNext =<< peekChar
  pure . build $ T.singleton c

--------------------------------------------------------------------------------
-- Instances
--------------------------------------------------------------------------------

instance Monad m => MonadParse (P.ParseT m) where
  liftParse  = P.liftParse
  peekChar   = P.peekChar
  atEOF      = P.atEOF
  parseError = P.parseError

instance MonadParse m => MonadParse (I.IdentityT m) where
instance MonadParse m => MonadParse (R.ReaderT r m) where
instance (MonadParse m, Monoid w) => MonadParse (WS.WriterT w m) where
instance (MonadParse m, Monoid w) => MonadParse (WL.WriterT w m) where
instance MonadParse m => MonadParse (SS.StateT s m) where
instance MonadParse m => MonadParse (SL.StateT s m) where
instance (MonadParse m, Monoid w) => MonadParse (RWSS.RWST r w s m) where
instance (MonadParse m, Monoid w) => MonadParse (RWSL.RWST r w s m) where
instance MonadParse m => MonadParse (M.MaybeT m) where
