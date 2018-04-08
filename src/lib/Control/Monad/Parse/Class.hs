{-# LANGUAGE FlexibleContexts #-}

module Control.Monad.Parse.Class (
  -- * The 'MonadParse' type class
  MonadParse(..),
  -- * Derived 'ParseT' operations
  parseWithM', parseWith,
  parseToken, parseCharTokenLookahead,
  -- ** Lower-level operations
  parseChar, parseChars,
) where

import Control.Monad
import Control.Monad.Error.Class

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

class (MonadPlus m, MonadError String m) => MonadParse m where
  parseWithM :: (Text -> Either String (a, Text)) -> m a
  peekChar   :: m (Maybe Char)
  atEOF      :: m Bool

parseWithM' :: MonadParse m => String -> (Text -> Maybe (a, Text)) -> m a
parseWithM' msg f = parseWithM $ note msg . f
  where note x = maybe (Left x) Right

parseWith :: MonadParse m => (Text -> (a, Text)) -> m a
parseWith f = parseWithM $ Right . f

parseChar :: MonadParse m => (Char -> Bool) -> m Char
parseChar pred = do
  c <- parseWithM' "unexpected EOF" T.uncons
  guard $ pred c
  pure c

parseChars :: MonadParse m => (Char -> Bool) -> m Text
parseChars pred = parseWith $ T.span pred

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
  parseWithM = P.parseWithM
  peekChar   = P.peekChar
  atEOF      = P.atEOF

instance MonadParse m => MonadParse (I.IdentityT m) where
  parseWithM = lift . parseWithM
  peekChar   = lift peekChar
  atEOF      = lift atEOF

instance MonadParse m => MonadParse (R.ReaderT r m) where
  parseWithM = lift . parseWithM
  peekChar   = lift peekChar
  atEOF      = lift atEOF

instance (MonadParse m, Monoid w) => MonadParse (WS.WriterT w m) where
  parseWithM = lift . parseWithM
  peekChar   = lift peekChar
  atEOF      = lift atEOF

instance (MonadParse m, Monoid w) => MonadParse (WL.WriterT w m) where
  parseWithM = lift . parseWithM
  peekChar   = lift peekChar
  atEOF      = lift atEOF

instance MonadParse m => MonadParse (SS.StateT s m) where
  parseWithM = lift . parseWithM
  peekChar   = lift peekChar
  atEOF      = lift atEOF

instance MonadParse m => MonadParse (SL.StateT s m) where
  parseWithM = lift . parseWithM
  peekChar   = lift peekChar
  atEOF      = lift atEOF

instance (MonadParse m, Monoid w) => MonadParse (RWSS.RWST r w s m) where
  parseWithM = lift . parseWithM
  peekChar   = lift peekChar
  atEOF      = lift atEOF

instance (MonadParse m, Monoid w) => MonadParse (RWSL.RWST r w s m) where
  parseWithM = lift . parseWithM
  peekChar   = lift peekChar
  atEOF      = lift atEOF

instance MonadParse m => MonadParse (M.MaybeT m) where
  parseWithM = lift . parseWithM
  peekChar   = lift peekChar
  atEOF      = lift atEOF
