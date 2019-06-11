{-# LANGUAGE LambdaCase, GeneralizedNewtypeDeriving, FlexibleContexts #-}

module HsToCoq.Coq.Gallina.UseTypeInBinders (
  useTypeInBinders, useTypeInBinders', UTIBError(..), UTIBIsTypeTooShort(..),
  -- ** Monadic version that doesn't consolidate identical typed binders
  useTypeInBindersM
) where

import Control.Lens

import Data.Bifunctor
import Data.Foldable
import Data.Maybe
import Data.List.NonEmpty (NonEmpty(..))
import HsToCoq.Util.Function

import Control.Monad.Except
import Control.Monad.State

import HsToCoq.Coq.Gallina
import HsToCoq.Coq.Gallina.Util

newtype UTIBIsTypeTooShort = UTIBIsTypeTooShort { utibIsTypeTooShort :: Bool }
                           deriving (Eq, Ord, Enum, Bounded, Show, Read)

data UTIBError = UTIBMismatchedGeneralizability
               | UTIBMismatchedExplicitness
               | UTIBMismatchedBoth
               deriving (Eq, Ord, Enum, Bounded, Show, Read)

-- Module-local
drain_binder :: MonadState Term m => m (Maybe BinderInfo)
drain_binder = gets unconsOneBinderFromType >>= \case
  Just (bi, t) -> Just bi <$ put t
  Nothing      -> pure Nothing

-- Module-local
binder_match_errors :: Binder -> BinderInfo -> Maybe UTIBError
binder_match_errors b bi
  | badGeneralizability && badExplicitness = Just UTIBMismatchedBoth
  | badGeneralizability                    = Just UTIBMismatchedGeneralizability
  | badExplicitness                        = Just UTIBMismatchedExplicitness
  | otherwise                              = Nothing
  where
    badGeneralizability = b^.binderGeneralizability /= bi^.biGeneralizability
    badExplicitness     = b^.binderExplicitness     /= bi^.biExplicitness

useTypeInBindersM :: (MonadError UTIBError m, MonadState Term m) => Binders -> m (Binders, UTIBIsTypeTooShort)
useTypeInBindersM (b :| bs) = drain_binder >>= \case
  Nothing                          -> pure (b :| bs, UTIBIsTypeTooShort True)
  Just bi@(BinderInfo g ei _ mtyp) -> do
    traverse_ throwError $ binder_match_errors b bi
    
    let newBinderNamed x = case mtyp of
          Just typ -> Typed    g ei (x :| []) typ
          Nothing  -> Inferred   ei x  -- Without a type, we can't be in the 'Generalizable' case
        
        newNamelessBinder = case mtyp of
          Just typ -> Generalized ei typ
          Nothing  -> error "INTERNAL ERROR: all generalized binders should have a concrete type"
          -- We know that any 'Generalizable' 'Binder's have an actual type, not 'Nothing'
        
        continue b' mb'' = first (b' :|) <$> useTypeInBindersML (maybeToList mb'' ++ bs)
    
    caseOneBinder b
      (\  _ x       -> continue (newBinderNamed x) Nothing)
      (\_ _ x _ mb' -> continue (newBinderNamed x) mb')
      (\  _   _     -> continue newNamelessBinder  Nothing)
  where
    useTypeInBindersML []       = pure ([], UTIBIsTypeTooShort False)
    useTypeInBindersML (b : bs) = first toList <$> useTypeInBindersM (b :| bs)

useTypeInBinders :: Term -> Binders -> Either UTIBError (Term, Binders, UTIBIsTypeTooShort)
useTypeInBinders ty bs = (_2 %~ consolidateTypedBinders) . munge <$> runStateT (useTypeInBindersM bs) ty
  where munge ((bs', short), ty') = (ty', bs', short)

useTypeInBinders' :: Term -> Binders -> Either UTIBError (Term, Binders)
useTypeInBinders' = fmap (\(ty,bs,_) -> (ty,bs)) .: useTypeInBinders
