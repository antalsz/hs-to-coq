{-# LANGUAGE MultiParamTypeClasses, FlexibleContexts,
             TypeSynonymInstances, FlexibleInstances,
             OverloadedStrings, GeneralizedNewtypeDeriving  #-}

module Control.Monad.DefinedIdents (
  -- * The 'DefinedIdents' monad
  DefinedIdents, startCollectingBinders, execDefinedIdents
  ) where

import Data.Maybe (fromMaybe)
import Control.Monad.Writer

import Control.Monad.Variables.Internal

import HsToCoq.Coq.Gallina (Ident)

newtype DefinedIdents a = DefinedIdents (Writer (Maybe [Ident]) a)
  deriving (Functor, Applicative, Monad, MonadWriter (Maybe [Ident]))

-- The 'MonadVariables' instance for 'DefinedIdents' tracks what binders
-- scope over 'startCollectingBinders'.
startCollectingBinders :: DefinedIdents ()
startCollectingBinders = tell (Just [])

execDefinedIdents :: DefinedIdents a -> [Ident]
execDefinedIdents (DefinedIdents w) = fromMaybe [] . execWriter $ w

instance MonadVariables Ident () DefinedIdents where
  bind i _ (DefinedIdents x) = DefinedIdents $ censor (fmap (i:)) x
  bound _ = pure Nothing
  frees _ = pure ()
