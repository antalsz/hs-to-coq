{-# LANGUAGE ConstraintKinds, GeneralizedNewtypeDeriving, FlexibleContexts #-}

module Control.Monad.Trans.NewlinesParse (
  -- * The 'NewlinesParse' monad
  NewlinesParse, evalNewlinesParse,
  -- * The 'NewlinesParseT' monad transformer
  NewlinesParseT(..), evalNewlinesParseT,
  -- * The 'MonadNewlinesParse' constraint
  MonadNewlinesParse,
  -- * Newline status
  NewlineStatus(..)
) where

import HsToCoq.Util.Coerce

import HsToCoq.Util.Functor
import Data.Functor.Identity
import Control.Applicative
import Control.Monad
import Control.Monad.Fail
import Control.Monad.Fix
import Control.Monad.State
import Control.Monad.Except
import HsToCoq.Util.Function

import Data.Text (Text)

import qualified Control.Monad.Reader.Class as R
import qualified Control.Monad.Writer.Class as W
import qualified Control.Monad.Cont.Class   as C

import Control.Monad.Trans.Parse
import Control.Monad.Parse.Class

--------------------------------------------------------------------------------
-- Newline-aware parser
--------------------------------------------------------------------------------

type MonadNewlinesParse m = (MonadParse m, MonadState NewlineStatus m)

data NewlineStatus = NewlineSeparators | NewlineWhitespace
                   deriving (Eq, Ord, Enum, Bounded, Show, Read)

newtype NewlinesParseT m a =
  NewlinesParseT { getNewlinesParseT :: ParseT (StateT NewlineStatus m) a }
  deriving ( Functor, Applicative, Monad
           , Alternative, MonadPlus
           , MonadFail, MonadFix, MonadIO
           , MonadParse, MonadState NewlineStatus
           , R.MonadReader r, W.MonadWriter w, C.MonadCont
           )

instance MonadTrans NewlinesParseT where lift = NewlinesParseT #. (lift . lift)

type NewlinesParse = NewlinesParseT Identity

-- Module-local
eval_newline :: Monad m => StateT NewlineStatus m a -> m a
eval_newline = evalStateT ?? NewlineSeparators

evalNewlinesParseT :: Monad m => NewlinesParseT m a -> Text -> m (Either [ParseError] a)
evalNewlinesParseT (NewlinesParseT act) = eval_newline . evalParseT act

evalNewlinesParse :: NewlinesParse a -> Text -> Either [ParseError] a
evalNewlinesParse = runIdentity .: evalNewlinesParseT
